//! Variable-length object arena backed by word-addressed storage.
//!
//! The arena stores one fixed-size header `H` followed by a variable-length tail
//! of `E` elements for each allocation. Deleted objects stay in place until
//! [`VarArena::compact`] produces a dense copy together with a relocation map.

use core::marker::PhantomData;
use core::mem::{MaybeUninit, align_of, size_of};
use core::{ptr, slice};

/// Handle to one allocation inside a [`VarArena`].
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Handle(u32);

impl Handle {
    /// Sentinel handle value that never refers to a live allocation.
    pub const INVALID: Self = Self(u32::MAX);

    /// Returns the raw word offset stored in this handle.
    pub fn raw(self) -> u32 {
        self.0
    }

    /// Returns whether this handle is the [`INVALID`](Self::INVALID) sentinel.
    pub fn is_invalid(self) -> bool {
        self == Self::INVALID
    }

    /// Returns the raw word offset as a host `usize`.
    fn word(self) -> usize {
        self.0 as usize
    }
}

/// Header contract for objects stored in a [`VarArena`].
///
/// The header carries the logical tail length and the tombstone bit used by the
/// arena's lazy-deletion scheme.
pub trait VarHeader: Copy {
    /// Returns the number of tail elements stored after this header.
    fn tail_len(&self) -> usize;

    /// Returns whether the object has been marked as deleted.
    fn is_deleted(&self) -> bool;

    /// Updates the deleted marker tracked by the arena.
    fn set_deleted(&mut self, deleted: bool);
}

/// Computed in-memory layout for one stored object.
#[derive(Clone, Copy, Debug)]
struct ObjLayout {
    /// Byte offset from the object base to the first tail element.
    tail_offset: usize,
    /// Total storage size for the object, measured in machine words.
    words: usize,
}

/// Rounds `value` up to the next multiple of `align`.
fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

/// Computes the packed storage layout for one header-and-tail object.
fn layout_for<H, E>(len: usize) -> ObjLayout {
    assert!(size_of::<H>() > 0, "zero-sized headers are not supported");
    assert!(
        size_of::<E>() > 0,
        "zero-sized tail elements are not supported"
    );
    assert!(align_of::<H>() <= align_of::<usize>());
    assert!(align_of::<E>() <= align_of::<usize>());

    let tail_offset = align_up(size_of::<H>(), align_of::<E>());
    let tail_bytes = len
        .checked_mul(size_of::<E>())
        .expect("variable tail byte size overflow");
    let object_bytes = tail_offset
        .checked_add(tail_bytes)
        .expect("variable object byte size overflow");
    let words = align_up(object_bytes, size_of::<usize>()) / size_of::<usize>();

    ObjLayout { tail_offset, words }
}

/// Borrowed view of one live object stored in a [`VarArena`].
pub struct ObjRef<'a, H, E> {
    /// Header borrowed from the arena backing storage.
    header: &'a H,
    /// Tail slice borrowed from the arena backing storage.
    elems: &'a [E],
}

impl<'a, H, E> ObjRef<'a, H, E> {
    /// Returns the borrowed header.
    pub fn header(&self) -> &'a H {
        self.header
    }

    /// Returns the borrowed tail elements.
    pub fn elems(&self) -> &'a [E] {
        self.elems
    }

    /// Returns the number of tail elements in this object.
    pub fn len(&self) -> usize {
        self.elems.len()
    }

    /// Returns whether the object has an empty tail.
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }
}

/// Mapping from pre-compaction handles to post-compaction handles.
pub struct RelocMap {
    /// Dense lookup table indexed by the old handle word offset.
    map: Vec<u32>,
}

impl RelocMap {
    /// Marker stored for handles that pointed at deleted objects.
    const DEAD: u32 = u32::MAX;

    /// Returns the relocated handle for one pre-compaction handle.
    pub fn get(&self, old: Handle) -> Option<Handle> {
        self.map
            .get(old.word())
            .copied()
            .filter(|&raw| raw != Self::DEAD)
            .map(Handle)
    }

    /// Rewrites `handle` in place if its object survived compaction.
    pub fn rewrite(&self, handle: &mut Handle) -> bool {
        if let Some(new) = self.get(*handle) {
            *handle = new;
            true
        } else {
            false
        }
    }
}

/// Arena storing fixed-size headers with trailing variable-length tails.
pub struct VarArena<H: VarHeader, E: Copy> {
    /// Raw word storage containing packed objects back-to-back.
    words: Vec<MaybeUninit<usize>>,
    /// Bitset marking which word offsets start an object header.
    starts: Vec<bool>,
    /// Number of words currently occupied by deleted objects.
    wasted_words: usize,
    /// Carries the generic parameters on the packed raw storage.
    _marker: PhantomData<(H, E)>,
}

impl<H: VarHeader, E: Copy> Default for VarArena<H, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: VarHeader, E: Copy> VarArena<H, E> {
    /// Creates an empty arena.
    pub fn new() -> Self {
        let _ = layout_for::<H, E>(0);
        Self {
            words: Vec::new(),
            starts: Vec::new(),
            wasted_words: 0,
            _marker: PhantomData,
        }
    }

    /// Creates an empty arena with capacity measured in machine words.
    pub fn with_capacity_words(capacity_words: usize) -> Self {
        let _ = layout_for::<H, E>(0);
        Self {
            words: Vec::with_capacity(capacity_words),
            starts: Vec::with_capacity(capacity_words),
            wasted_words: 0,
            _marker: PhantomData,
        }
    }

    /// Returns the number of words currently reserved by stored objects.
    pub fn len_words(&self) -> usize {
        self.words.len()
    }

    /// Returns the number of words occupied by deleted objects.
    pub fn wasted_words(&self) -> usize {
        self.wasted_words
    }

    /// Returns whether deleted space is large enough that compaction is likely worthwhile.
    pub fn should_compact(&self) -> bool {
        self.wasted_words.saturating_mul(3) >= self.words.len()
    }

    /// Removes every object from the arena.
    pub fn clear(&mut self) {
        self.words.clear();
        self.starts.clear();
        self.wasted_words = 0;
    }

    /// Allocates one header-and-tail object and returns its handle.
    ///
    /// # Panics
    ///
    /// Panics if `header.is_deleted()` is already true, if `header.len()` does not
    /// match `elems.len()`, or if the packed object would overflow the arena's
    /// address space.
    pub fn alloc(&mut self, header: H, elems: &[E]) -> Handle {
        assert!(!header.is_deleted());
        assert_eq!(header.tail_len(), elems.len());

        let layout = layout_for::<H, E>(elems.len());
        let start = self.words.len();
        let end = start
            .checked_add(layout.words)
            .expect("arena word length overflow");
        assert!(end < u32::MAX as usize);

        self.words.reserve(layout.words);
        self.starts.resize(end, false);
        self.starts[start] = true;

        unsafe {
            let old_len = self.words.len();
            self.words.set_len(old_len + layout.words);

            let base = self.words.as_mut_ptr().add(start).cast::<u8>();
            ptr::write(base.cast::<H>(), header);

            if !elems.is_empty() {
                ptr::copy_nonoverlapping(
                    elems.as_ptr(),
                    base.add(layout.tail_offset).cast::<E>(),
                    elems.len(),
                );
            }
        }

        Handle(start as u32)
    }

    /// Returns whether `handle` currently refers to a live object.
    pub fn contains(&self, handle: Handle) -> bool {
        self.get(handle).is_some()
    }

    /// Returns a borrowed view of one live object.
    pub fn get(&self, handle: Handle) -> Option<ObjRef<'_, H, E>> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let layout = layout_for::<H, E>(header.tail_len());
            if handle.word().checked_add(layout.words)? > self.words.len() {
                return None;
            }

            let elems = self.elems_unchecked(handle, header.tail_len(), layout.tail_offset);
            Some(ObjRef { header, elems })
        }
    }

    /// Returns the tail slice for one live object.
    pub fn elems(&self, handle: Handle) -> Option<&[E]> {
        self.get(handle).map(|obj| obj.elems)
    }

    /// Returns the mutable tail slice for one live object.
    pub fn elems_mut(&mut self, handle: Handle) -> Option<&mut [E]> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let len = header.tail_len();
            let layout = layout_for::<H, E>(len);
            if handle.word().checked_add(layout.words)? > self.words.len() {
                return None;
            }

            Some(self.elems_unchecked_mut(handle, len, layout.tail_offset))
        }
    }

    /// Applies `f` to a copy of the stored header and writes the updated value back.
    ///
    /// The callback may mutate header metadata, but it must preserve the stored tail
    /// length and deleted flag.
    pub fn with_header_mut<R>(&mut self, handle: Handle, f: impl FnOnce(&mut H) -> R) -> Option<R> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let old_len = header.tail_len();
            let old_deleted = header.is_deleted();
            let mut next = *header;
            let result = f(&mut next);

            assert_eq!(next.tail_len(), old_len, "arena object length changed");
            assert_eq!(
                next.is_deleted(),
                old_deleted,
                "deleted bit changed outside remove"
            );

            ptr::write(self.base_mut(handle).cast::<H>(), next);
            Some(result)
        }
    }

    /// Marks one live object as deleted.
    pub fn remove(&mut self, handle: Handle) -> bool {
        if !self.is_start(handle) {
            return false;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return false;
            }

            let layout = layout_for::<H, E>(header.tail_len());
            let mut next = *header;
            next.set_deleted(true);
            ptr::write(self.base_mut(handle).cast::<H>(), next);
            self.wasted_words += layout.words;
            true
        }
    }

    /// Iterates over handles for every live object in storage order.
    pub fn handles(&self) -> Handles<'_, H, E> {
        Handles {
            arena: self,
            cursor: 0,
        }
    }

    /// Compacts live objects into fresh storage and returns the relocation map.
    pub fn compact(&mut self) -> RelocMap {
        let old_words_len = self.words.len();
        let mut reloc = RelocMap {
            map: vec![RelocMap::DEAD; old_words_len],
        };
        let mut new_words =
            Vec::<MaybeUninit<usize>>::with_capacity(old_words_len - self.wasted_words);
        let mut new_starts = Vec::<bool>::with_capacity(old_words_len - self.wasted_words);

        let mut old = 0;
        while old < old_words_len {
            debug_assert!(self.starts[old]);

            let old_handle = Handle(old as u32);
            let header = unsafe { *self.header_unchecked(old_handle) };
            let layout = layout_for::<H, E>(header.tail_len());

            if !header.is_deleted() {
                let new = new_words.len();
                let new_end = new + layout.words;
                new_starts.resize(new_end, false);
                new_starts[new] = true;

                unsafe {
                    new_words.reserve(layout.words);
                    let old_len = new_words.len();
                    new_words.set_len(old_len + layout.words);
                    ptr::copy_nonoverlapping(
                        self.words.as_ptr().add(old),
                        new_words.as_mut_ptr().add(new),
                        layout.words,
                    );
                }

                reloc.map[old] = new as u32;
            }

            old += layout.words;
        }

        self.words = new_words;
        self.starts = new_starts;
        self.wasted_words = 0;
        reloc
    }

    /// Returns whether `handle` points at the start of some allocated object.
    fn is_start(&self, handle: Handle) -> bool {
        !handle.is_invalid() && handle.word() < self.starts.len() && self.starts[handle.word()]
    }

    /// Returns a raw pointer to the first byte of the stored object.
    ///
    /// # Safety
    ///
    /// `handle` must refer to an allocated object start within `self.words`.
    unsafe fn base(&self, handle: Handle) -> *const u8 {
        // SAFETY: the caller guarantees that `handle` points at a valid object
        // start within `self.words`, so offsetting to that word is in-bounds.
        unsafe { self.words.as_ptr().add(handle.word()).cast::<u8>() }
    }

    /// Returns a mutable raw pointer to the first byte of the stored object.
    ///
    /// # Safety
    ///
    /// `handle` must refer to an allocated object start within `self.words`, and no
    /// aliasing references to that object may be used for the duration of the mutable
    /// borrow.
    unsafe fn base_mut(&mut self, handle: Handle) -> *mut u8 {
        // SAFETY: the caller guarantees that `handle` points at a valid object
        // start within `self.words`, so offsetting to that word is in-bounds.
        unsafe { self.words.as_mut_ptr().add(handle.word()).cast::<u8>() }
    }

    /// Returns a shared reference to the stored header without validation.
    ///
    /// # Safety
    ///
    /// `handle` must refer to a live object whose header is valid for `H`.
    unsafe fn header_unchecked(&self, handle: Handle) -> &H {
        let base = unsafe { self.base(handle) };
        // SAFETY: the caller guarantees that `handle` names a live object and its
        // header bytes are initialized with a properly aligned `H`.
        unsafe { &*base.cast::<H>() }
    }

    /// Returns the stored tail slice without validating bounds or liveness.
    ///
    /// # Safety
    ///
    /// `handle` must refer to an object whose tail has length `len`, and
    /// `tail_offset` must be the offset produced by [`layout_for`] for that object.
    unsafe fn elems_unchecked(&self, handle: Handle, len: usize, tail_offset: usize) -> &[E] {
        let base = unsafe { self.base(handle) };
        // SAFETY: the caller guarantees that the object tail starts at
        // `tail_offset`, has `len` initialized elements, and fits within the
        // stored object.
        unsafe { slice::from_raw_parts(base.add(tail_offset).cast::<E>(), len) }
    }

    /// Returns the stored mutable tail slice without validating bounds or liveness.
    ///
    /// # Safety
    ///
    /// `handle` must refer to a uniquely borrowed live object whose tail has length
    /// `len`, and `tail_offset` must be the offset produced by [`layout_for`] for
    /// that object.
    unsafe fn elems_unchecked_mut(
        &mut self,
        handle: Handle,
        len: usize,
        tail_offset: usize,
    ) -> &mut [E] {
        let base = unsafe { self.base_mut(handle) };
        // SAFETY: the caller guarantees unique access to the live object tail,
        // whose initialized elements start at `tail_offset` and span `len`.
        unsafe { slice::from_raw_parts_mut(base.add(tail_offset).cast::<E>(), len) }
    }
}

/// Iterator over live object handles in one [`VarArena`].
pub struct Handles<'a, H: VarHeader, E: Copy> {
    /// Arena being traversed.
    arena: &'a VarArena<H, E>,
    /// Current word cursor within the packed storage.
    cursor: usize,
}

impl<'a, H: VarHeader, E: Copy> Iterator for Handles<'a, H, E> {
    type Item = Handle;

    fn next(&mut self) -> Option<Self::Item> {
        while self.cursor < self.arena.words.len() {
            debug_assert!(self.arena.starts[self.cursor]);

            let handle = Handle(self.cursor as u32);
            let header = unsafe { self.arena.header_unchecked(handle) };
            let layout = layout_for::<H, E>(header.tail_len());
            self.cursor += layout.words;

            if !header.is_deleted() {
                return Some(handle);
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[repr(transparent)]
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    struct Lit(u32);

    #[repr(C)]
    #[derive(Clone, Copy, Debug)]
    struct ClauseHeader {
        len: u32,
        flags: u32,
        activity: f32,
    }

    impl ClauseHeader {
        const DELETED: u32 = 1 << 0;
        const LEARNED: u32 = 1 << 1;

        fn new(len: usize, learned: bool) -> Self {
            let mut flags = 0;
            if learned {
                flags |= Self::LEARNED;
            }
            Self {
                len: len as u32,
                flags,
                activity: 0.0,
            }
        }
    }

    impl VarHeader for ClauseHeader {
        fn tail_len(&self) -> usize {
            self.len as usize
        }

        fn is_deleted(&self) -> bool {
            self.flags & Self::DELETED != 0
        }

        fn set_deleted(&mut self, deleted: bool) {
            if deleted {
                self.flags |= Self::DELETED;
            } else {
                self.flags &= !Self::DELETED;
            }
        }
    }

    #[test]
    fn alloc_get_remove_compact() {
        let mut arena = VarArena::<ClauseHeader, Lit>::new();

        let a = arena.alloc(ClauseHeader::new(2, false), &[Lit(1), Lit(2)]);
        let b = arena.alloc(ClauseHeader::new(3, true), &[Lit(3), Lit(4), Lit(5)]);
        let c = arena.alloc(ClauseHeader::new(1, true), &[Lit(6)]);

        assert_eq!(arena.elems(a).unwrap(), &[Lit(1), Lit(2)]);
        assert_eq!(arena.elems(b).unwrap(), &[Lit(3), Lit(4), Lit(5)]);
        assert_eq!(arena.elems(c).unwrap(), &[Lit(6)]);

        assert!(arena.remove(b));
        assert!(arena.get(b).is_none());

        let reloc = arena.compact();

        let mut a2 = a;
        let mut b2 = b;
        let mut c2 = c;

        assert!(reloc.rewrite(&mut a2));
        assert!(!reloc.rewrite(&mut b2));
        assert!(reloc.rewrite(&mut c2));

        assert_eq!(arena.elems(a2).unwrap(), &[Lit(1), Lit(2)]);
        assert_eq!(arena.elems(c2).unwrap(), &[Lit(6)]);
    }

    #[test]
    fn mutate_header_without_changing_length() {
        let mut arena = VarArena::<ClauseHeader, Lit>::new();
        let h = arena.alloc(ClauseHeader::new(2, true), &[Lit(10), Lit(20)]);

        arena
            .with_header_mut(h, |header| {
                header.activity = 7.0;
            })
            .unwrap();

        assert_eq!(arena.get(h).unwrap().header().activity, 7.0);
    }
}
