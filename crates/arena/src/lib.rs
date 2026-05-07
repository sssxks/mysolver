use core::marker::PhantomData;
use core::mem::{align_of, size_of, MaybeUninit};
use core::{ptr, slice};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Handle(u32);

impl Handle {
    pub const INVALID: Self = Self(u32::MAX);

    pub fn raw(self) -> u32 {
        self.0
    }

    pub fn is_invalid(self) -> bool {
        self == Self::INVALID
    }

    fn word(self) -> usize {
        self.0 as usize
    }
}

pub trait VarHeader: Copy {
    fn len(&self) -> usize;
    fn is_deleted(&self) -> bool;
    fn set_deleted(&mut self, deleted: bool);
}

#[derive(Clone, Copy, Debug)]
struct ObjLayout {
    tail_offset: usize,
    words: usize,
}

fn align_up(value: usize, align: usize) -> usize {
    debug_assert!(align.is_power_of_two());
    (value + align - 1) & !(align - 1)
}

fn layout_for<H, E>(len: usize) -> ObjLayout {
    assert!(size_of::<H>() > 0, "zero-sized headers are not supported");
    assert!(size_of::<E>() > 0, "zero-sized tail elements are not supported");
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

pub struct ObjRef<'a, H, E> {
    header: &'a H,
    elems: &'a [E],
}

impl<'a, H, E> ObjRef<'a, H, E> {
    pub fn header(&self) -> &'a H {
        self.header
    }

    pub fn elems(&self) -> &'a [E] {
        self.elems
    }

    pub fn len(&self) -> usize {
        self.elems.len()
    }

    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }
}

pub struct RelocMap {
    map: Vec<u32>,
}

impl RelocMap {
    const DEAD: u32 = u32::MAX;

    pub fn get(&self, old: Handle) -> Option<Handle> {
        self.map
            .get(old.word())
            .copied()
            .filter(|&raw| raw != Self::DEAD)
            .map(Handle)
    }

    pub fn rewrite(&self, handle: &mut Handle) -> bool {
        if let Some(new) = self.get(*handle) {
            *handle = new;
            true
        } else {
            false
        }
    }
}

pub struct VarArena<H: VarHeader, E: Copy> {
    words: Vec<MaybeUninit<usize>>,
    starts: Vec<bool>,
    wasted_words: usize,
    _marker: PhantomData<(H, E)>,
}

impl<H: VarHeader, E: Copy> Default for VarArena<H, E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: VarHeader, E: Copy> VarArena<H, E> {
    pub fn new() -> Self {
        let _ = layout_for::<H, E>(0);
        Self {
            words: Vec::new(),
            starts: Vec::new(),
            wasted_words: 0,
            _marker: PhantomData,
        }
    }

    pub fn with_capacity_words(capacity_words: usize) -> Self {
        let _ = layout_for::<H, E>(0);
        Self {
            words: Vec::with_capacity(capacity_words),
            starts: Vec::with_capacity(capacity_words),
            wasted_words: 0,
            _marker: PhantomData,
        }
    }

    pub fn len_words(&self) -> usize {
        self.words.len()
    }

    pub fn wasted_words(&self) -> usize {
        self.wasted_words
    }

    pub fn should_compact(&self) -> bool {
        self.wasted_words.saturating_mul(3) >= self.words.len()
    }

    pub fn clear(&mut self) {
        self.words.clear();
        self.starts.clear();
        self.wasted_words = 0;
    }

    pub fn alloc(&mut self, header: H, elems: &[E]) -> Handle {
        assert!(!header.is_deleted());
        assert_eq!(header.len(), elems.len());

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

    pub fn contains(&self, handle: Handle) -> bool {
        self.get(handle).is_some()
    }

    pub fn get(&self, handle: Handle) -> Option<ObjRef<'_, H, E>> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let layout = layout_for::<H, E>(header.len());
            if handle.word().checked_add(layout.words)? > self.words.len() {
                return None;
            }

            let elems = self.elems_unchecked(handle, header.len(), layout.tail_offset);
            Some(ObjRef { header, elems })
        }
    }

    pub fn elems(&self, handle: Handle) -> Option<&[E]> {
        self.get(handle).map(|obj| obj.elems)
    }

    pub fn elems_mut(&mut self, handle: Handle) -> Option<&mut [E]> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let len = header.len();
            let layout = layout_for::<H, E>(len);
            if handle.word().checked_add(layout.words)? > self.words.len() {
                return None;
            }

            Some(self.elems_unchecked_mut(handle, len, layout.tail_offset))
        }
    }

    pub fn with_header_mut<R>(
        &mut self,
        handle: Handle,
        f: impl FnOnce(&mut H) -> R,
    ) -> Option<R> {
        if !self.is_start(handle) {
            return None;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return None;
            }

            let old_len = header.len();
            let old_deleted = header.is_deleted();
            let mut next = *header;
            let result = f(&mut next);

            assert_eq!(next.len(), old_len, "arena object length changed");
            assert_eq!(next.is_deleted(), old_deleted, "deleted bit changed outside remove");

            ptr::write(self.base_mut(handle).cast::<H>(), next);
            Some(result)
        }
    }

    pub fn remove(&mut self, handle: Handle) -> bool {
        if !self.is_start(handle) {
            return false;
        }

        unsafe {
            let header = self.header_unchecked(handle);
            if header.is_deleted() {
                return false;
            }

            let layout = layout_for::<H, E>(header.len());
            let mut next = *header;
            next.set_deleted(true);
            ptr::write(self.base_mut(handle).cast::<H>(), next);
            self.wasted_words += layout.words;
            true
        }
    }

    pub fn handles(&self) -> Handles<'_, H, E> {
        Handles {
            arena: self,
            cursor: 0,
        }
    }

    pub fn compact(&mut self) -> RelocMap {
        let old_words_len = self.words.len();
        let mut reloc = RelocMap {
            map: vec![RelocMap::DEAD; old_words_len],
        };
        let mut new_words = Vec::<MaybeUninit<usize>>::with_capacity(old_words_len - self.wasted_words);
        let mut new_starts = Vec::<bool>::with_capacity(old_words_len - self.wasted_words);

        let mut old = 0;
        while old < old_words_len {
            debug_assert!(self.starts[old]);

            let old_handle = Handle(old as u32);
            let header = unsafe { *self.header_unchecked(old_handle) };
            let layout = layout_for::<H, E>(header.len());

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

    fn is_start(&self, handle: Handle) -> bool {
        !handle.is_invalid()
            && handle.word() < self.starts.len()
            && self.starts[handle.word()]
    }

    unsafe fn base(&self, handle: Handle) -> *const u8 {
        self.words.as_ptr().add(handle.word()).cast::<u8>()
    }

    unsafe fn base_mut(&mut self, handle: Handle) -> *mut u8 {
        self.words.as_mut_ptr().add(handle.word()).cast::<u8>()
    }

    unsafe fn header_unchecked(&self, handle: Handle) -> &H {
        &*self.base(handle).cast::<H>()
    }

    unsafe fn elems_unchecked(
        &self,
        handle: Handle,
        len: usize,
        tail_offset: usize,
    ) -> &[E] {
        slice::from_raw_parts(self.base(handle).add(tail_offset).cast::<E>(), len)
    }

    unsafe fn elems_unchecked_mut(
        &mut self,
        handle: Handle,
        len: usize,
        tail_offset: usize,
    ) -> &mut [E] {
        slice::from_raw_parts_mut(self.base_mut(handle).add(tail_offset).cast::<E>(), len)
    }
}

pub struct Handles<'a, H: VarHeader, E: Copy> {
    arena: &'a VarArena<H, E>,
    cursor: usize,
}

impl<'a, H: VarHeader, E: Copy> Iterator for Handles<'a, H, E> {
    type Item = Handle;

    fn next(&mut self) -> Option<Self::Item> {
        while self.cursor < self.arena.words.len() {
            debug_assert!(self.arena.starts[self.cursor]);

            let handle = Handle(self.cursor as u32);
            let header = unsafe { self.arena.header_unchecked(handle) };
            let layout = layout_for::<H, E>(header.len());
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
        fn len(&self) -> usize {
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
