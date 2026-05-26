//! Arena-backed storage handles and interning helpers.

use std::hash::{BuildHasher, Hash, Hasher};
use std::marker::PhantomData;
use std::ptr::NonNull;

use bumpalo::Bump;
use hashbrown::HashMap;

/// One permanently allocated string payload inside one bump arena.
#[derive(Debug)]
pub struct ArenaStr {
    /// Raw fat pointer to bump-owned string data.
    raw: NonNull<str>,
}

impl ArenaStr {
    /// Reborrows the stored string.
    ///
    /// # Safety
    ///
    /// The owner of this handle must guarantee that `raw` still points to one live
    /// `str` allocation for the duration of the returned borrow.
    pub(crate) unsafe fn as_str<'a>(&self) -> &'a str {
        // SAFETY: callers uphold the arena-liveness invariant.
        unsafe { self.raw.as_ref() }
    }
}

impl Copy for ArenaStr {}

impl Clone for ArenaStr {
    fn clone(&self) -> Self {
        *self
    }
}

impl PartialEq for ArenaStr {
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_str() == other.as_str() }
    }
}

impl Eq for ArenaStr {}

impl Hash for ArenaStr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_str().hash(state) }
    }
}

/// One permanently allocated slice payload inside one bump arena.
#[derive(Debug)]
pub struct ArenaSlice<T> {
    /// Raw fat pointer to bump-owned slice data.
    raw: NonNull<[T]>,
    /// Marker preserving the element type.
    marker: PhantomData<T>,
}

impl<T> ArenaSlice<T> {
    /// Creates one arena slice from one raw bump-owned pointer.
    pub(crate) fn from_raw(raw: NonNull<[T]>) -> Self {
        Self {
            raw,
            marker: PhantomData,
        }
    }

    /// Reborrows the stored slice.
    ///
    /// # Safety
    ///
    /// The owner of this handle must guarantee that `raw` still points to one live
    /// `[T]` allocation for the duration of the returned borrow.
    pub(crate) unsafe fn as_slice<'a>(&self) -> &'a [T] {
        // SAFETY: callers uphold the arena-liveness invariant.
        unsafe { self.raw.as_ref() }
    }
}

impl<T> Copy for ArenaSlice<T> {}

impl<T> Clone for ArenaSlice<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: PartialEq> PartialEq for ArenaSlice<T> {
    fn eq(&self, other: &Self) -> bool {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_slice() == other.as_slice() }
    }
}

impl<T: Eq> Eq for ArenaSlice<T> {}

impl<T: Hash> Hash for ArenaSlice<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // SAFETY: both handles originate from live registry/search arenas.
        unsafe { self.as_slice().hash(state) }
    }
}

/// Hashes one borrowed probe key with the same build-hasher used by one table.
pub(crate) fn make_hash<S: BuildHasher, T: Hash>(hasher: &S, value: &T) -> u64 {
    hasher.hash_one(value)
}

/// Storage for permanent DST payloads.
#[derive(Debug, Default)]
pub struct BumpStorage {
    /// Append-only allocator for names and argument slices.
    bump: Bump,
}

impl BumpStorage {
    /// Allocates one owned string inside the bump arena.
    pub(crate) fn alloc_str(&self, text: &str) -> ArenaStr {
        ArenaStr {
            raw: NonNull::from(self.bump.alloc_str(text)),
        }
    }

    /// Allocates one copied slice inside the bump arena.
    pub(crate) fn alloc_slice<T: Copy>(&self, slice: &[T]) -> ArenaSlice<T> {
        ArenaSlice::from_raw(NonNull::from(self.bump.alloc_slice_copy(slice)))
    }
}

/// One canonical interner table.
#[derive(Debug)]
pub struct Interner<Id, T> {
    /// Stored canonical values in insertion order.
    values: Vec<T>,
    /// Fast lookup by stored value.
    pub(crate) index: HashMap<T, Id>,
}

impl<Id, T> Default for Interner<Id, T> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            index: HashMap::new(),
        }
    }
}

/// Internal helper for interner identifier construction.
pub trait InternId: Copy {
    /// Creates one identifier from a zero-based insertion index.
    fn from_index(index: usize) -> Self;
}

impl<Id: InternId + Eq + Hash, T: Clone + Eq + Hash> Interner<Id, T> {
    /// Interns `value`, returning the existing identifier when present.
    pub(crate) fn intern(&mut self, value: T) -> Id {
        if let Some(&id) = self.index.get(&value) {
            return id;
        }
        let id = Id::from_index(self.values.len());
        self.values.push(value.clone());
        self.index.insert(value, id);
        id
    }

    /// Returns the value named by `id`.
    pub(crate) fn get(&self, index: usize) -> &T {
        &self.values[index]
    }

    /// Returns the number of interned values.
    pub(crate) fn len(&self) -> usize {
        self.values.len()
    }
}
