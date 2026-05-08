use crate::Lit;

/// An index into the solver's clause arena.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct ClauseId(usize);

impl ClauseId {
    /// Creates one stable clause identifier from an arena slot.
    pub(crate) fn new(index: usize) -> Self {
        Self(index)
    }

    /// Returns the zero-based index of this clause id inside the arena header table.
    pub(crate) fn index(self) -> usize {
        self.0
    }
}

/// One logical clause header stored in the stable clause-id table.
#[derive(Copy, Clone, Debug)]
pub(crate) struct ClauseHeader {
    /// Offset of the first literal word for this clause inside [`ClauseArena::words`].
    offset: u32,
    /// Packed literal count and clause flags.
    meta: u32,
    /// Clause activity used by learned-clause reduction.
    activity: f64,
}

impl ClauseHeader {
    /// Bit flag stored in the metadata word for learned clauses.
    pub(crate) const LEARNT_BIT: u32 = 1 << 31;
    /// Bit flag stored in the metadata word for lazily deleted clauses.
    pub(crate) const DELETED_BIT: u32 = 1 << 30;
    /// Mask selecting the literal count stored in the metadata word.
    pub(crate) const LEN_MASK: u32 = !(Self::LEARNT_BIT | Self::DELETED_BIT);

    /// Creates one active clause header for a payload beginning at `offset`.
    pub(crate) fn new(offset: usize, len: usize, learnt: bool, activity: f64) -> Self {
        debug_assert!(u32::try_from(offset).is_ok());
        debug_assert!(len <= Self::LEN_MASK as usize);
        Self {
            offset: offset as u32,
            meta: Self::pack_meta(len, learnt, false),
            activity,
        }
    }

    /// Packs the metadata word from the clause length and flag bits.
    pub(crate) fn pack_meta(len: usize, learnt: bool, deleted: bool) -> u32 {
        let mut meta = len as u32;
        if learnt {
            meta |= Self::LEARNT_BIT;
        }
        if deleted {
            meta |= Self::DELETED_BIT;
        }
        meta
    }

    /// Returns the payload offset measured in literal words.
    pub(crate) fn offset(self) -> usize {
        self.offset as usize
    }

    /// Returns the number of literals stored in this clause.
    pub(crate) fn len(self) -> usize {
        (self.meta & Self::LEN_MASK) as usize
    }

    /// Returns whether this clause was learned during search.
    pub(crate) fn is_learnt(self) -> bool {
        (self.meta & Self::LEARNT_BIT) != 0
    }

    /// Returns whether this clause has been lazily deleted.
    pub(crate) fn is_deleted(self) -> bool {
        (self.meta & Self::DELETED_BIT) != 0
    }

    /// Returns the stored clause activity score.
    pub(crate) fn activity(self) -> f64 {
        self.activity
    }

    /// Marks this clause as deleted or active.
    pub(crate) fn set_deleted(&mut self, deleted: bool) {
        if deleted {
            self.meta |= Self::DELETED_BIT;
        } else {
            self.meta &= !Self::DELETED_BIT;
        }
    }

    /// Overwrites the stored clause activity score.
    pub(crate) fn set_activity(&mut self, activity: f64) {
        self.activity = activity;
    }
}

/// An immutable view over one clause header and its literal payload.
#[derive(Debug)]
pub(crate) struct ClauseRef<'a> {
    /// Clause metadata stored in the header table.
    header: &'a ClauseHeader,
    /// Trailing clause literals stored in the payload arena.
    lits: &'a [Lit],
}

impl ClauseRef<'_> {
    /// Returns the number of literals stored in this clause.
    pub(crate) fn len(&self) -> usize {
        self.header.len()
    }

    /// Returns literal `idx` from the clause payload.
    pub(crate) fn lit(&self, idx: usize) -> Lit {
        debug_assert!(idx < self.len());
        self.lits[idx]
    }
}

/// A mutable view over one clause header and its literal payload.
#[derive(Debug)]
pub(crate) struct ClauseMut<'a> {
    /// Clause metadata stored in the header table.
    header: &'a mut ClauseHeader,
    /// Trailing clause literals stored in the payload arena.
    lits: &'a mut [Lit],
}

impl ClauseMut<'_> {
    /// Returns the number of literals stored in this clause.
    pub(crate) fn len(&self) -> usize {
        self.header.len()
    }

    /// Returns literal `idx` from the clause payload.
    pub(crate) fn lit(&self, idx: usize) -> Lit {
        debug_assert!(idx < self.len());
        self.lits[idx]
    }

    /// Swaps two watched literals in place.
    pub(crate) fn swap_lits(&mut self, a: usize, b: usize) {
        debug_assert!(a < self.len());
        debug_assert!(b < self.len());
        self.lits.swap(a, b);
    }
}

/// A clause arena with stable logical headers and relocatable literal payloads.
#[derive(Debug, Default)]
pub(crate) struct ClauseArena {
    /// Stable clause headers indexed by [`ClauseId`].
    headers: Vec<ClauseHeader>,
    /// Dense literal payload storage for all long clauses.
    words: Vec<Lit>,
}

impl ClauseArena {
    /// Creates an empty clause arena.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Allocates one clause header and appends its literal payload.
    pub(crate) fn alloc(&mut self, lits: &[Lit], learnt: bool, activity: f64) -> ClauseId {
        debug_assert!(lits.len() <= ClauseHeader::LEN_MASK as usize);
        let cid = ClauseId::new(self.headers.len());
        let offset = self.words.len();
        self.headers
            .push(ClauseHeader::new(offset, lits.len(), learnt, activity));
        self.words.extend_from_slice(lits);
        cid
    }

    /// Returns the number of allocated clauses, including deleted ones.
    pub(crate) fn len(&self) -> usize {
        self.headers.len()
    }

    /// Returns the stable header for `cid`.
    pub(crate) fn header(&self, cid: ClauseId) -> &ClauseHeader {
        &self.headers[cid.index()]
    }

    /// Returns the stable header for `cid` mutably.
    pub(crate) fn header_mut(&mut self, cid: ClauseId) -> &mut ClauseHeader {
        &mut self.headers[cid.index()]
    }

    /// Returns an immutable view over `cid`.
    pub(crate) fn clause(&self, cid: ClauseId) -> ClauseRef<'_> {
        let header = self.header(cid);
        let range = Self::literal_range_from_header(header);
        ClauseRef {
            header,
            lits: &self.words[range],
        }
    }

    /// Returns a mutable view over `cid`.
    pub(crate) fn clause_mut(&mut self, cid: ClauseId) -> ClauseMut<'_> {
        let (headers, words) = (&mut self.headers, &mut self.words);
        let header = &mut headers[cid.index()];
        let range = Self::literal_range_from_header(header);
        ClauseMut {
            header,
            lits: &mut words[range],
        }
    }

    /// Multiplies every clause activity by `factor`.
    pub(crate) fn scale_activities(&mut self, factor: f64) {
        for header in &mut self.headers {
            header.set_activity(header.activity() * factor);
        }
    }

    /// Returns the literal range described by `header`.
    pub(crate) fn literal_range_from_header(header: &ClauseHeader) -> std::ops::Range<usize> {
        let start = header.offset();
        let end = start + header.len();
        start..end
    }
}
