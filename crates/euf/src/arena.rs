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

/// Result of one interning attempt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct Interned<Id> {
    /// Identifier of the canonical stored value.
    pub(crate) id: Id,
    /// Whether the value was inserted during this call.
    pub(crate) is_new: bool,
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

/// Matches one canonical stored value against its borrowed probe view.
///
/// Each canonical object type defines exactly one family of borrowed query views,
/// optionally parameterized by the borrow lifetime. This keeps interner lookups
/// tied to the actual probe shape used for that stored type instead of exposing an
/// unconstrained "any query type" extension point.
pub(crate) trait MatchesRef {
    /// Borrowed query view used to probe values of this stored type.
    type Query<'a>: Copy + Hash
    where
        Self: 'a;

    /// Returns whether `self` matches `query`.
    fn matches_ref(&self, query: Self::Query<'_>) -> bool;
}

impl<Id: InternId + Eq + Hash, T: Clone + Eq + Hash> Interner<Id, T> {
    /// Interns one borrowed probe, constructing the owned value only on miss.
    ///
    /// # Panics
    ///
    /// Panics in debug builds if `make_value()` does not produce a value matching
    /// `query`. This protects the contract between the borrowed probe and the owned
    /// value inserted into the canonical table.
    pub(crate) fn intern<F>(&mut self, query: T::Query<'_>, make_value: F) -> Interned<Id>
    where
        T: MatchesRef,
        F: FnOnce() -> T,
    {
        if let Some(id) = self.find_ref(query) {
            return Interned { id, is_new: false };
        }

        let value = make_value();
        debug_assert!(
            value.matches_ref(query),
            "intern closure must produce a value matching its query"
        );

        let id = Id::from_index(self.values.len());
        self.values.push(value.clone());
        self.index.insert(value, id);
        Interned { id, is_new: true }
    }
    /// Finds one interned value matching the borrowed `query`.
    pub(crate) fn find_ref(&self, query: T::Query<'_>) -> Option<Id>
    where
        T: MatchesRef,
    {
        let hash = make_hash(self.index.hasher(), &query);
        self.index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(query))
            .map(|(_, &id)| id)
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
