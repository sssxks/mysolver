use crate::{Literal, Scope};

/// Minimum amount of dead literal payload before compaction becomes worthwhile.
const MIN_COMPACTION_WASTE_WORDS: usize = 1_024;
/// Fraction of the payload arena that may be dead before triggering compaction.
const COMPACTION_WASTE_DIVISOR: usize = 2;

/// A generational handle into one [`ClauseArena`] slot.
///
/// Resolving a clause id against a particular arena state either yields the live
/// clause occupying this (slot, generation) pair or reports the id as stale.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) struct ClauseId {
    /// Physical slot inside the arena header table.
    slot: u32,
    /// Generation expected to occupy [`Self::slot`].
    generation: u32,
}

impl ClauseId {
    /// Creates one clause identifier from one (slot, generation) pair.
    fn new(slot: u32, generation: u32) -> Self {
        Self { slot, generation }
    }

    /// Returns the zero-based header-table index of this clause id.
    fn slot_index(self) -> usize {
        self.slot as usize
    }

    /// Returns the physical slot named by this clause id.
    pub(crate) fn slot(self) -> u32 {
        self.slot
    }

    /// Returns the generation expected in [`Self::slot`].
    fn generation(self) -> u32 {
        self.generation
    }
}

/// One logical clause slot stored in the clause arena header table.
///
/// Conceptually, this is
/// ```text
/// enum ClauseSlot {
///     Live { generation: u30, offset, len },
///     LiveLearnt { generation: u30, offset, len },
///     Free { generation: u30, next_free_slot: Option<NoMaxU32> },
///     Retired { generation: u30 }
/// }
/// ```
#[derive(Copy, Clone, Debug)]
pub(crate) struct ClauseHeader {
    /// Packed slot state and generation counter.
    generation_state: u32,
    /// Literal count for live clauses.
    len: u32,
    /// Offset of the first literal word for live clauses, or the next free slot.
    offset_or_next: u32,
    /// Scope where this clause remains sound.
    scope: Scope,
}

impl ClauseHeader {
    /// Bits selecting the slot state stored in `generation_state`.
    const STATE_MASK: u32 = 0b11 << 30;
    /// Tag stored for live irredundant clauses.
    const LIVE_STATE: u32 = 0b00 << 30;
    /// Tag stored for live learned clauses.
    const LEARNT_STATE: u32 = 0b01 << 30;
    /// Tag stored for free reusable slots.
    const FREE_STATE: u32 = 0b10 << 30;
    /// Tag stored for permanently retired slots.
    const RETIRED_STATE: u32 = 0b11 << 30;

    /// Mask selecting the generation counter stored in the state word.
    const GENERATION_MASK: u32 = !Self::STATE_MASK;
    /// Largest generation value that still leaves room for state bits.
    const MAX_GENERATION: u32 = Self::GENERATION_MASK;
    /// Sentinel stored in `offset_or_next` to terminate the intrusive free list.
    const FREE_LIST_END: u32 = u32::MAX;

    /// Creates one live irredundant clause header for a payload beginning at `offset`.
    fn new_irredundant(generation: u32, offset: u32, len: u32, scope: Scope) -> Self {
        Self {
            len,
            generation_state: Self::pack_generation_state(generation, Self::LIVE_STATE),
            offset_or_next: offset,
            scope,
        }
    }

    /// Creates one live learned clause header for a payload beginning at `offset`.
    fn new_learnt(generation: u32, offset: u32, len: u32, scope: Scope) -> Self {
        Self {
            len,
            generation_state: Self::pack_generation_state(generation, Self::LEARNT_STATE),
            offset_or_next: offset,
            scope,
        }
    }

    /// Creates one free header slot that points at the next free slot.
    fn new_free(generation: u32, next_free_slot: Option<u32>) -> Self {
        Self {
            len: 0,
            generation_state: Self::pack_generation_state(generation, Self::FREE_STATE),
            offset_or_next: next_free_slot.unwrap_or(Self::FREE_LIST_END),
            scope: Scope::ROOT,
        }
    }

    /// Creates one retired header slot that can no longer be allocated.
    fn new_retired(generation: u32) -> Self {
        Self {
            len: 0,
            generation_state: Self::pack_generation_state(generation, Self::RETIRED_STATE),
            offset_or_next: 0,
            scope: Scope::ROOT,
        }
    }

    /// Packs one generation counter together with the slot state bits.
    #[inline(always)]
    fn pack_generation_state(generation: u32, state: u32) -> u32 {
        assert!(
            generation <= Self::MAX_GENERATION,
            "generation exceeds ClauseHeader::MAX_GENERATION",
        );
        debug_assert_eq!(state & !Self::STATE_MASK, 0);
        generation | state
    }

    /// Returns the generation currently assigned to this slot.
    fn generation(self) -> u32 {
        self.generation_state & Self::GENERATION_MASK
    }

    // state query methods

    /// Returns whether this header slot currently stores a live clause.
    fn is_live(self) -> bool {
        matches!(
            self.generation_state & Self::STATE_MASK,
            Self::LIVE_STATE | Self::LEARNT_STATE
        )
    }

    /// Returns whether this clause was learned during search.
    pub(crate) fn is_learnt(self) -> bool {
        (self.generation_state & Self::STATE_MASK) == Self::LEARNT_STATE
    }

    /// Returns whether this header slot is currently free for reuse.
    fn is_free(self) -> bool {
        (self.generation_state & Self::STATE_MASK) == Self::FREE_STATE
    }

    /// Returns whether this header slot has been retired permanently.
    fn is_retired(self) -> bool {
        (self.generation_state & Self::STATE_MASK) == Self::RETIRED_STATE
    }

    /// Returns the payload offset measured in literal words.
    ///
    /// Preconditoin: this header must be live, i.e. `is_live()` must return `true`.
    fn offset(self) -> usize {
        debug_assert!(self.is_live());
        self.offset_or_next as usize
    }

    /// Updates the payload offset after clause compaction.
    ///
    /// Preconditoin: this header must be live, i.e. `is_live()` must return `true`.
    fn set_offset(&mut self, offset: u32) {
        debug_assert!(self.is_live());
        self.offset_or_next = offset;
    }

    /// Returns the number of literals stored in this clause.
    ///
    /// Preconditoin: this header must be live, i.e. `is_live()` must return `true`.
    pub(crate) fn len(self) -> usize {
        debug_assert!(self.is_live());
        self.len as usize
    }

    /// Returns the scope carried by this live clause.
    pub(crate) fn scope(self) -> Scope {
        debug_assert!(self.is_live());
        self.scope
    }

    /// Returns the next free slot in the intrusive free list.
    ///
    /// Preconditoin: this header must be free, i.e. `is_free()` must return `true`.
    fn next_free_slot(self) -> Option<u32> {
        debug_assert!(self.is_free());
        (self.offset_or_next != Self::FREE_LIST_END).then_some(self.offset_or_next)
    }
}

/// An immutable view over one clause payload.
#[derive(Debug)]
pub(crate) struct ClauseRef<'a> {
    /// Trailing clause literals stored in the payload arena.
    lits: &'a [Literal],
}

impl ClauseRef<'_> {
    /// Returns literal `idx` from the clause payload.
    ///
    /// Preconditoin: `idx` must be less than `len()`.
    pub(crate) fn lit(&self, idx: usize) -> Literal {
        self.lits[idx]
    }
}

/// A mutable view over one clause payload.
#[derive(Debug)]
pub(crate) struct ClauseMut<'a> {
    /// Trailing clause literals stored in the payload arena.
    lits: &'a mut [Literal],
}

impl ClauseMut<'_> {
    /// Returns the number of literals stored in this clause.
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }

    /// Returns literal `idx` from the clause payload.
    ///
    /// Preconditoin: `idx` must be less than `len()`.
    pub(crate) fn lit(&self, idx: usize) -> Literal {
        self.lits[idx]
    }

    /// Swaps two watched literals in place.
    pub(crate) fn swap_lits(&mut self, a: usize, b: usize) {
        self.lits.swap(a, b);
    }
}

/// A clause arena with stable physical slots and relocatable literal payloads.
#[derive(Debug, Default)]
pub(crate) struct ClauseArena {
    /// Clause slots indexed by [`ClauseId::slot`].
    headers: Vec<ClauseHeader>,
    /// VSIDS activity per physical clause slot.
    ///
    /// Only live learned clauses carry a meaningful value here. Free, retired, and
    /// irredundant slots keep arbitrary values.
    activities: Vec<f32>,
    /// LBD score per physical clause slot.
    ///
    /// Only live learned clauses carry a positive value here. Free, retired, and
    /// irredundant slots keep arbitrary values.
    lbds: Vec<u32>,

    /// Dense literal payload storage for all long clauses.
    words: Vec<Literal>,
    /// Head of the intrusive free list inside [`Self::headers`].
    free_head: Option<u32>,
    /// Number of literal words currently stranded behind deleted clauses.
    wasted_words: usize,
}

impl ClauseArena {
    /// Creates an empty clause arena.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Allocates one irredundant clause slot and appends its literal payload.
    pub(crate) fn alloc_irredundant(&mut self, lits: &[Literal], scope: Scope) -> ClauseId {
        self.alloc_with(lits, ClauseHeader::new_irredundant, 0.0, 0, scope)
    }

    /// Allocates one learned clause slot and appends its literal payload.
    ///
    /// Learned clauses must carry a positive LBD score.
    pub(crate) fn alloc_learnt(
        &mut self,
        lits: &[Literal],
        activity: f32,
        lbd: u32,
        scope: Scope,
    ) -> ClauseId {
        assert!(lbd > 0, "learned clauses must store a positive LBD");
        self.alloc_with(lits, ClauseHeader::new_learnt, activity, lbd, scope)
    }

    /// Allocates one clause slot and appends its literal payload.
    fn alloc_with(
        &mut self,
        lits: &[Literal],
        make_header: impl Fn(u32, u32, u32, Scope) -> ClauseHeader,
        activity: f32,
        lbd: u32,
        scope: Scope,
    ) -> ClauseId {
        assert!(
            self.headers.len() < ClauseHeader::FREE_LIST_END as usize,
            "clause arena exhausted u32 ids",
        );
        let offset = u32::try_from(self.words.len()).expect("clause arena exhausted u32 offsets");
        let len = u32::try_from(lits.len()).expect("clause length exceeds u32::MAX");

        let cid = if let Some(free_slot) = self.free_head {
            let header = self.headers[free_slot as usize];
            debug_assert!(header.is_free());
            let next_free = header.next_free_slot();
            self.free_head = next_free;
            let generation = header.generation();
            self.headers[free_slot as usize] = make_header(generation, offset, len, scope);
            self.activities[free_slot as usize] = activity;
            self.lbds[free_slot as usize] = lbd;
            ClauseId::new(free_slot, generation)
        } else {
            let slot = u32::try_from(self.headers.len()).expect("clause arena exhausted u32 ids");
            let generation = 0;
            let cid = ClauseId::new(slot, generation);
            self.headers
                .push(make_header(generation, offset, len, scope));
            self.activities.push(activity);
            self.lbds.push(lbd);
            cid
        };

        self.words.extend_from_slice(lits);
        cid
    }

    /// Deletes one live clause and either recycles or retires its slot.
    pub(crate) fn delete(&mut self, cid: ClauseId) {
        let slot = self.live_slot(cid);
        let header = self.headers[slot];
        self.wasted_words += header.len();

        if header.generation() < ClauseHeader::MAX_GENERATION {
            let next_generation = header.generation() + 1;
            self.headers[slot] = ClauseHeader::new_free(next_generation, self.free_head);
            self.activities[slot] = 0.0;
            self.lbds[slot] = 0;
            self.free_head = Some(cid.slot());
        } else {
            self.headers[slot] = ClauseHeader::new_retired(header.generation());
            self.activities[slot] = 0.0;
            self.lbds[slot] = 0;
        }

        self.compact_if_needed();
    }

    /// Returns the total number of slots, including free and retired ones.
    pub(crate) fn slot_count(&self) -> usize {
        self.headers.len()
    }

    /// Returns the number of live irredundant and learned long clauses.
    pub(crate) fn live_clause_counts(&self) -> (usize, usize) {
        let mut irredundant = 0usize;
        let mut learnt = 0usize;

        for header in &self.headers {
            if !header.is_live() {
                continue;
            }

            if header.is_learnt() {
                learnt += 1;
            } else {
                irredundant += 1;
            }
        }

        (irredundant, learnt)
    }

    /// Returns the number of literal words currently stored in the arena payload.
    #[cfg(feature = "telemetry")]
    pub(crate) fn word_count(&self) -> usize {
        self.words.len()
    }

    /// Returns the number of literal words stranded behind deleted clauses.
    #[cfg(feature = "telemetry")]
    pub(crate) fn wasted_word_count(&self) -> usize {
        self.wasted_words
    }

    /// Returns the live slot index named by `cid`, if any.
    ///
    /// Returns `None` when `cid` is stale, i.e. when the slot is currently free
    /// or retired, or when the slot has been reused for another clause since
    /// `cid`'s generation was recorded.
    ///
    /// # Panics
    /// Panics if slot index is out of bounds.
    #[inline(always)]
    fn try_live_slot(&self, cid: ClauseId) -> Option<usize> {
        // Slots are never truncated, so out-of-bounds signals a caller bug rather
        // than a stale id, which is expected and tracked generationally.
        let header = self
            .headers
            .get(cid.slot_index())
            .unwrap_or_else(|| panic!("clause slot out of bounds: {}", cid.slot()));
        // header is free or retired or header is already reused for another generation.
        if header.is_free() || header.is_retired() || header.generation() != cid.generation() {
            None
        } else {
            Some(cid.slot_index())
        }
    }

    /// Returns whether `cid` still resolves to a live clause.
    pub(crate) fn is_live(&self, cid: ClauseId) -> bool {
        self.try_live_slot(cid).is_some()
    }

    /// Returns the live slot index named by `cid`, panicking if the id is stale.
    #[inline(always)]
    pub(crate) fn live_slot(&self, cid: ClauseId) -> usize {
        self.try_live_slot(cid)
            .unwrap_or_else(|| panic!("stale clause id: {cid:?}"))
    }

    /// Returns the live header for `cid`, if the id is not stale.
    #[inline(always)]
    fn try_header(&self, cid: ClauseId) -> Option<&ClauseHeader> {
        let slot = self.try_live_slot(cid)?;
        Some(&self.headers[slot])
    }

    /// Returns the live header for `cid`, panicking if the id is stale.
    pub(crate) fn header(&self, cid: ClauseId) -> &ClauseHeader {
        let slot = self.live_slot(cid);
        &self.headers[slot]
    }

    /// Returns every live long clause whose scope is deeper than `scope`.
    pub(crate) fn live_clauses_above_scope(&self, scope: Scope) -> Vec<ClauseId> {
        self.headers
            .iter()
            .enumerate()
            .filter_map(|(slot, header)| {
                if header.is_live() && header.scope() > scope {
                    Some(ClauseId::new(slot as u32, header.generation()))
                } else {
                    None
                }
            })
            .collect()
    }

    /// Returns the stored activity score for one live learned clause.
    pub(crate) fn activity(&self, cid: ClauseId) -> f32 {
        let slot = self.live_slot(cid);
        let header = self.headers[slot];
        debug_assert!(header.is_learnt());
        self.activities[slot]
    }

    /// Overwrites the stored activity score for one live learned clause.
    pub(crate) fn set_activity(&mut self, cid: ClauseId, activity: f32) {
        let slot = self.live_slot(cid);
        let header = self.headers[slot];
        debug_assert!(header.is_learnt());
        self.activities[slot] = activity;
    }

    /// Returns the stored LBD score for one live clause.
    ///
    /// Irredundant clauses always report `0`.
    pub(crate) fn lbd(&self, cid: ClauseId) -> u32 {
        let slot = self.live_slot(cid);
        self.lbds[slot]
    }

    /// Overwrites the stored LBD score for one live learned clause.
    pub(crate) fn set_lbd(&mut self, cid: ClauseId, lbd: u32) {
        let slot = self.live_slot(cid);
        let header = self.headers[slot];
        debug_assert!(header.is_learnt());
        debug_assert!(lbd > 0);
        self.lbds[slot] = lbd;
    }

    /// Returns an immutable view over `cid`, if the id is not stale.
    #[inline(always)]
    fn try_clause(&self, cid: ClauseId) -> Option<ClauseRef<'_>> {
        let header = self.try_header(cid)?;
        let range = Self::literal_range_from_header(header);
        Some(ClauseRef {
            lits: &self.words[range],
        })
    }

    /// Returns an immutable view over `cid`, panicking if the id is stale.
    pub(crate) fn clause(&self, cid: ClauseId) -> ClauseRef<'_> {
        self.try_clause(cid)
            .unwrap_or_else(|| panic!("stale clause id: {cid:?}"))
    }

    /// Returns a mutable view over `cid`, if the id is not stale.
    pub(crate) fn try_clause_mut(&mut self, cid: ClauseId) -> Option<ClauseMut<'_>> {
        let slot = self.try_live_slot(cid)?;
        let range = Self::literal_range_from_header(&self.headers[slot]);
        Some(ClauseMut {
            lits: &mut self.words[range],
        })
    }

    /// Multiplies every live clause activity by `factor`.
    pub(crate) fn scale_activities(&mut self, factor: f32) {
        for (slot, header) in self.headers.iter().copied().enumerate() {
            if header.is_learnt() {
                self.activities[slot] *= factor;
            }
        }
    }

    /// Returns the literal range described by `header`.
    fn literal_range_from_header(header: &ClauseHeader) -> std::ops::Range<usize> {
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

        // compact with header-slot order, instead of old payload order,
        // at the cost of reallocating a new buffer, since compact is infrequent.
        // this should be more cache friendly as opposed to mut-inline-compaction,
        // which trades non-sequential live payload for no reallocation.
        let mut words = Vec::with_capacity(self.words.len() - self.wasted_words);
        let old_words = &self.words;

        for header in &mut self.headers {
            if !header.is_live() {
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
    use super::ClauseArena;
    use crate::{Literal, Scope, Var};

    fn lit(index: usize) -> Literal {
        Literal::new(Var::from_index(index), false)
    }

    #[test]
    fn delete_reuses_header_slot_and_bumps_generation() {
        let mut arena = ClauseArena::new();
        let a = arena.alloc_irredundant(&[lit(0), lit(1), lit(2)], Scope::ROOT);
        let b = arena.alloc_learnt(&[lit(3), lit(4), lit(5)], 7.0, 5, Scope::ROOT);

        arena.delete(a);
        let c = arena.alloc_learnt(&[lit(6), lit(7), lit(8)], 9.0, 2, Scope::ROOT);

        assert_eq!(c.slot(), a.slot());
        assert_ne!(c, a);
        assert_eq!(c.generation(), a.generation() + 1);
        assert!(!arena.is_live(a));
        assert_eq!(arena.clause(c).lit(0), lit(6));
        assert_eq!(arena.clause(c).lit(2), lit(8));
        assert_eq!(arena.clause(b).lit(1), lit(4));
        assert!(arena.header(c).is_learnt());
        assert_eq!(arena.lbd(c), 2);
        assert_eq!(arena.lbd(b), 5);
    }

    #[test]
    fn delete_compacts_payload_without_rewriting_live_clause_ids() {
        let mut arena = ClauseArena::new();

        let make_clause =
            |base: usize| -> Vec<Literal> { (0..600).map(|idx| lit(base + idx)).collect() };

        let a_lits = make_clause(0);
        let b_lits = make_clause(1_000);
        let c_lits = make_clause(2_000);

        let a = arena.alloc_irredundant(&a_lits, Scope::ROOT);
        let b = arena.alloc_irredundant(&b_lits, Scope::ROOT);
        let c = arena.alloc_learnt(&c_lits, 3.0, 4, Scope::ROOT);

        arena.delete(a);
        arena.delete(b);

        assert_eq!(arena.header(c).offset(), 0);
        assert_eq!(arena.words.len(), c_lits.len());
        assert_eq!(arena.clause(c).lit(0), c_lits[0]);
        assert_eq!(
            arena.clause(c).lit(c_lits.len() - 1),
            c_lits[c_lits.len() - 1]
        );

        let reused = arena.alloc_irredundant(&[lit(9_000), lit(9_001), lit(9_002)], Scope::ROOT);
        assert!(matches!(reused.slot(), 0 | 1));
        assert_eq!(reused.generation(), 1);
    }

    #[test]
    fn delete_retires_slot_when_generation_overflows() {
        let mut arena = ClauseArena::new();
        let cid = arena.alloc_irredundant(&[lit(0), lit(1), lit(2)], Scope::ROOT);
        let retired = super::ClauseId::new(cid.slot(), super::ClauseHeader::MAX_GENERATION);
        arena.headers[cid.slot_index()] = super::ClauseHeader::new_irredundant(
            super::ClauseHeader::MAX_GENERATION,
            0,
            3,
            Scope::ROOT,
        );

        arena.delete(retired);

        assert!(arena.headers[cid.slot_index()].is_retired());
        assert!(!arena.is_live(retired));
        assert!(arena.free_head.is_none());
    }
}
