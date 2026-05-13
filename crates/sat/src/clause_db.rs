use crate::Lit;

/// Minimum amount of dead literal payload before compaction becomes worthwhile.
const MIN_COMPACTION_WASTE_WORDS: usize = 1_024;
/// Fraction of the payload arena that may be dead before triggering compaction.
const COMPACTION_WASTE_DIVISOR: usize = 2;

/// An index into the solver's clause arena.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct ClauseId(u32);

impl ClauseId {
    /// Creates one stable clause identifier from an arena slot.
    pub(crate) fn new(index: u32) -> Self {
        Self(index)
    }

    /// Returns the zero-based index of this clause id inside the arena header table.
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// One logical clause header stored in the stable clause-id table.
///
/// Conceptually, this is `enum ClauseHeader { Occupied { offset: u32, len: u32, learnt: bool, activity: f32 }, Free { next_free: Option<ClauseId> } }`,
#[derive(Copy, Clone, Debug)]
pub(crate) struct ClauseHeader {
    /// Offset of the first literal word for occupied clauses, or the next free slot.
    offset_or_next: u32,
    /// Packed literal count and clause flags.
    meta: u32,
    /// Clause activity used by learned-clause reduction.
    activity: f32,
}

impl ClauseHeader {
    /// Bit flag stored in the metadata word for learned clauses.
    pub(crate) const LEARNT_BIT: u32 = 1 << 31;
    /// Bit flag stored in the metadata word for free header slots.
    pub(crate) const FREE_BIT: u32 = 1 << 30;
    /// Mask selecting the literal count stored in the metadata word.
    pub(crate) const LEN_MASK: u32 = !(Self::LEARNT_BIT | Self::FREE_BIT);
    /// Sentinel stored in `offset_or_next` to terminate the intrusive free list.
    const FREE_LIST_END: u32 = u32::MAX;

    /// Creates one occupied clause header for a payload beginning at `offset`.
    pub(crate) fn new(offset: u32, len: usize, learnt: bool, activity: f32) -> Self {
        assert!(
            len <= Self::LEN_MASK as usize,
            "clause length exceeds ClauseHeader::LEN_MASK",
        );
        Self {
            offset_or_next: offset,
            meta: Self::pack_meta(len as u32, learnt, false),
            activity,
        }
    }

    /// Creates one free header slot that points at the next free clause id.
    pub(crate) fn new_free(next_free: Option<ClauseId>) -> Self {
        Self {
            offset_or_next: next_free.map_or(Self::FREE_LIST_END, |cid| cid.0),
            meta: Self::FREE_BIT,
            activity: 0.0,
        }
    }

    /// Packs the metadata word from the clause length and flag bits.
    pub(crate) fn pack_meta(len: u32, learnt: bool, free: bool) -> u32 {
        let mut meta = len;
        if learnt {
            meta |= Self::LEARNT_BIT;
        }
        if free {
            meta |= Self::FREE_BIT;
        }
        meta
    }

    /// Returns the payload offset measured in literal words.
    pub(crate) fn offset(self) -> usize {
        debug_assert!(!self.is_free());
        self.offset_or_next as usize
    }

    /// Returns the number of literals stored in this clause.
    pub(crate) fn len(self) -> usize {
        debug_assert!(!self.is_free());
        (self.meta & Self::LEN_MASK) as usize
    }

    /// Returns whether this clause was learned during search.
    pub(crate) fn is_learnt(self) -> bool {
        debug_assert!(!self.is_free());
        (self.meta & Self::LEARNT_BIT) != 0
    }

    /// Returns whether this header slot is currently unused.
    pub(crate) fn is_free(self) -> bool {
        (self.meta & Self::FREE_BIT) != 0
    }

    /// Returns the stored clause activity score.
    pub(crate) fn activity(self) -> f32 {
        debug_assert!(!self.is_free());
        self.activity
    }

    /// Returns the next free clause id in the intrusive free list.
    pub(crate) fn next_free(self) -> Option<ClauseId> {
        debug_assert!(self.is_free());
        (self.offset_or_next != Self::FREE_LIST_END).then(|| ClauseId::new(self.offset_or_next))
    }

    /// Overwrites the stored clause activity score.
    pub(crate) fn set_activity(&mut self, activity: f32) {
        debug_assert!(!self.is_free());
        self.activity = activity;
    }

    /// Updates the payload offset after clause compaction.
    pub(crate) fn set_offset(&mut self, offset: u32) {
        debug_assert!(!self.is_free());
        self.offset_or_next = offset;
    }
}

/// An immutable view over one clause header and its literal payload.
#[derive(Debug)]
pub(crate) struct ClauseRef<'a> {
    /// Clause metadata stored in the header table.
    header: &'a ClauseHeader,
    /// Trailing clause literals stored in the payload arena.
    ///
    /// Technically, the length in this fat pointer is redundant, but rust DSTs are
    /// inflexible to build manually.
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
    ///
    /// Technically, the length in this fat pointer is redundant, but rust DSTs are
    /// inflexible to build manually.
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
    /// Head of the intrusive free list inside [`Self::headers`].
    free_head: Option<ClauseId>,
    /// Number of literal words currently stranded behind deleted clauses.
    wasted_words: usize,
}

impl ClauseArena {
    /// Creates an empty clause arena.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Allocates one clause header and appends its literal payload.
    pub(crate) fn alloc(&mut self, lits: &[Lit], learnt: bool, activity: f32) -> ClauseId {
        assert!(
            self.headers.len() < ClauseHeader::FREE_LIST_END as usize,
            "clause arena exhausted u32 ids",
        );
        let offset = u32::try_from(self.words.len()).expect("clause arena exhausted u32 offsets");
        let len = lits.len();

        let cid = if let Some(free_cid) = self.free_head {
            let next_free = self.headers[free_cid.index()].next_free();
            self.free_head = next_free;
            self.headers[free_cid.index()] = ClauseHeader::new(offset, len, learnt, activity);
            free_cid
        } else {
            let next_id =
                u32::try_from(self.headers.len()).expect("clause arena exhausted u32 ids");
            let cid = ClauseId::new(next_id);
            self.headers
                .push(ClauseHeader::new(offset, len, learnt, activity));
            cid
        };

        self.words.extend_from_slice(lits);
        cid
    }

    /// Deletes one clause and recycles its header slot for future allocations.
    pub(crate) fn delete(&mut self, cid: ClauseId) {
        let header = self.headers[cid.index()];
        debug_assert!(!header.is_free());
        self.wasted_words += header.len();
        self.headers[cid.index()] = ClauseHeader::new_free(self.free_head);
        self.free_head = Some(cid);
        self.compact_if_needed();
    }

    /// Returns the number of header slots, including recycled ones.
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
        debug_assert!(!header.is_free());
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
        debug_assert!(!header.is_free());
        let range = Self::literal_range_from_header(header);
        ClauseMut {
            header,
            lits: &mut words[range],
        }
    }

    /// Multiplies every live clause activity by `factor`.
    pub(crate) fn scale_activities(&mut self, factor: f32) {
        for header in &mut self.headers {
            if header.is_free() {
                continue;
            }
            header.set_activity(header.activity() * factor);
        }
    }

    /// Returns the literal range described by `header`.
    pub(crate) fn literal_range_from_header(header: &ClauseHeader) -> std::ops::Range<usize> {
        let start = header.offset();
        let end = start + header.len();
        start..end
    }

    /// Returns the current dead-payload threshold for triggering compaction.
    fn compaction_threshold(&self) -> usize {
        (self.words.len() / COMPACTION_WASTE_DIVISOR).max(MIN_COMPACTION_WASTE_WORDS)
    }

    /// Compacts the literal arena once enough dead payload has accumulated.
    fn compact_if_needed(&mut self) {
        if self.wasted_words < self.compaction_threshold() {
            return;
        }
        self.compact();
    }

    /// Rewrites live literal payloads into one compact arena and refreshes offsets.
    fn compact(&mut self) {
        if self.wasted_words == 0 {
            return;
        }

        let mut words = Vec::with_capacity(self.words.len() - self.wasted_words);
        let old_words = &self.words;

        for header in &mut self.headers {
            if header.is_free() {
                continue;
            }

            let range = Self::literal_range_from_header(header);
            let new_offset =
                u32::try_from(words.len()).expect("clause arena exhausted u32 offsets");
            words.extend_from_slice(&old_words[range]);
            header.set_offset(new_offset);
        }

        self.words = words;
        self.wasted_words = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::{ClauseArena, ClauseId};
    use crate::{Lit, Var};

    fn lit(index: usize) -> Lit {
        Lit::new(Var::from_index(index), false)
    }

    #[test]
    fn delete_reuses_header_slot() {
        let mut arena = ClauseArena::new();
        let a = arena.alloc(&[lit(0), lit(1), lit(2)], false, 0.0);
        let b = arena.alloc(&[lit(3), lit(4), lit(5)], true, 7.0);

        arena.delete(a);
        let c = arena.alloc(&[lit(6), lit(7), lit(8)], true, 9.0);

        assert_eq!(c, a);
        assert_eq!(arena.clause(c).lit(0), lit(6));
        assert_eq!(arena.clause(c).lit(2), lit(8));
        assert_eq!(arena.clause(b).lit(1), lit(4));
        assert!(arena.header(c).is_learnt());
    }

    #[test]
    fn delete_compacts_payload_without_rewriting_clause_ids() {
        let mut arena = ClauseArena::new();

        let make_clause =
            |base: usize| -> Vec<Lit> { (0..600).map(|idx| lit(base + idx)).collect() };

        let a_lits = make_clause(0);
        let b_lits = make_clause(1_000);
        let c_lits = make_clause(2_000);

        let a = arena.alloc(&a_lits, false, 0.0);
        let b = arena.alloc(&b_lits, false, 0.0);
        let c = arena.alloc(&c_lits, true, 3.0);

        arena.delete(a);
        arena.delete(b);

        assert_eq!(arena.header(c).offset(), 0);
        assert_eq!(arena.words.len(), c_lits.len());
        assert_eq!(arena.clause(c).lit(0), c_lits[0]);
        assert_eq!(
            arena.clause(c).lit(c_lits.len() - 1),
            c_lits[c_lits.len() - 1]
        );

        let reused = arena.alloc(&[lit(9_000), lit(9_001), lit(9_002)], false, 0.0);
        assert!(matches!(reused, ClauseId(1) | ClauseId(0)));
    }
}
