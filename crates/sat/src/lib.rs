//! A small conflict-driven clause learning SAT solver.
//!
//! The crate exposes a [`Solver`] for programmatic construction of CNF formulas and
//! a [`parse_dimacs`] helper for loading formulas from DIMACS CNF text.

use std::cmp::Ordering;
use std::mem;
use std::ops::Not;

/// A zero-based propositional variable identifier.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Var(u32);

impl Var {
    /// Returns the zero-based index of this variable.
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// A propositional literal encoded as `var << 1 | negated`.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Lit(u32);

impl Lit {
    /// Creates a literal from a variable and its sign.
    pub fn new(var: Var, negated: bool) -> Self {
        Self((var.0 << 1) | negated as u32)
    }

    /// Returns the underlying variable.
    pub fn var(self) -> Var {
        Var(self.0 >> 1)
    }

    /// Returns whether the literal is negated.
    pub fn is_negated(self) -> bool {
        (self.0 & 1) != 0
    }

    /// Returns the zero-based packed literal index.
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Converts a non-zero DIMACS integer into a literal.
    ///
    /// Positive integers map to positive literals and negative integers map to
    /// negated literals.
    ///
    /// # Panics
    ///
    /// Panics if `x == 0`, because `0` is the DIMACS clause terminator rather than
    /// a literal.
    pub fn from_dimacs(x: i32) -> Self {
        assert!(x != 0);
        let v = Var(x.unsigned_abs() - 1);
        Lit::new(v, x < 0)
    }
}

impl Not for Lit {
    type Output = Lit;

    fn not(self) -> Lit {
        Lit(self.0 ^ 1)
    }
}

/// A three-valued boolean used for partial assignments.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum LBool {
    /// The value is assigned to false.
    False,
    /// The value is currently unassigned.
    Undef,
    /// The value is assigned to true.
    True,
}

/// An index into the solver's clause arena.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub struct ClauseId(usize);

/// The reason why a variable assignment was enqueued.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Reason {
    /// The assignment was a decision or top-level unit without a stored antecedent.
    None,
    /// The assignment came from a binary clause represented by its two literals.
    Binary(Lit, Lit),
    /// The assignment came from a long clause stored in the clause arena.
    Clause(ClauseId),
}

/// A watched-literal entry attached to a literal's watch list.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Watcher {
    /// Watches a binary clause via the other literal in the clause.
    Binary {
        /// The other literal in the watched binary clause.
        other: Lit,
    },
    /// Watches a long clause together with a blocker literal.
    Long {
        /// The watched long clause.
        clause: ClauseId,
        /// A literal that can satisfy the clause without reopening it.
        blocker: Lit,
    },
}

/// A packed arena storing MiniSAT-style clause headers followed by trailing
/// literal words.
#[derive(Debug, Default)]
struct ClauseArena {
    /// Packed `u32` words containing clause headers and literals.
    words: Vec<u32>,
    /// Header start offsets for each allocated clause id.
    offsets: Vec<usize>,
}

impl ClauseArena {
    /// Number of `u32` words stored in each clause header.
    const HEADER_WORDS: usize = 3;
    /// Bit flag stored in the metadata word for learned clauses.
    const LEARNT_BIT: u32 = 1 << 31;
    /// Bit flag stored in the metadata word for lazily deleted clauses.
    const DELETED_BIT: u32 = 1 << 30;
    /// Mask selecting the literal count stored in the metadata word.
    const LEN_MASK: u32 = !(Self::LEARNT_BIT | Self::DELETED_BIT);

    /// Creates an empty packed clause arena.
    fn new() -> Self {
        Self::default()
    }

    /// Allocates one packed clause and returns its dense arena handle.
    fn alloc(&mut self, lits: &[Lit], learnt: bool, activity: f64) -> ClauseId {
        debug_assert!(lits.len() <= Self::LEN_MASK as usize);
        let cid = ClauseId(self.offsets.len());
        let start = self.words.len();
        self.offsets.push(start);
        self.words.push(Self::pack_meta(lits.len(), learnt, false));
        self.write_activity_words(activity);
        self.words.extend(lits.iter().map(|lit| lit.0));
        cid
    }

    /// Returns the number of allocated clauses, including deleted ones.
    fn len(&self) -> usize {
        self.offsets.len()
    }

    /// Returns the number of literals stored in `cid`.
    fn lit_len(&self, cid: ClauseId) -> usize {
        (self.meta(cid) & Self::LEN_MASK) as usize
    }

    /// Returns whether `cid` is a learned clause.
    fn is_learnt(&self, cid: ClauseId) -> bool {
        (self.meta(cid) & Self::LEARNT_BIT) != 0
    }

    /// Returns whether `cid` has been lazily deleted.
    fn is_deleted(&self, cid: ClauseId) -> bool {
        (self.meta(cid) & Self::DELETED_BIT) != 0
    }

    /// Marks `cid` as deleted or active without changing its other metadata.
    fn set_deleted(&mut self, cid: ClauseId, deleted: bool) {
        let start = self.offsets[cid.0];
        let mut meta = self.words[start];
        if deleted {
            meta |= Self::DELETED_BIT;
        } else {
            meta &= !Self::DELETED_BIT;
        }
        self.words[start] = meta;
    }

    /// Returns the clause activity currently stored in `cid`.
    fn activity(&self, cid: ClauseId) -> f64 {
        let start = self.offsets[cid.0] + 1;
        let lo = self.words[start] as u64;
        let hi = self.words[start + 1] as u64;
        f64::from_bits(lo | (hi << 32))
    }

    /// Overwrites the activity score stored in `cid`.
    fn set_activity(&mut self, cid: ClauseId, activity: f64) {
        let start = self.offsets[cid.0] + 1;
        let bits = activity.to_bits();
        self.words[start] = bits as u32;
        self.words[start + 1] = (bits >> 32) as u32;
    }

    /// Multiplies every clause activity by `factor`.
    fn scale_activities(&mut self, factor: f64) {
        for raw in 0..self.len() {
            let cid = ClauseId(raw);
            self.set_activity(cid, self.activity(cid) * factor);
        }
    }

    /// Returns literal `idx` from `cid`.
    fn lit(&self, cid: ClauseId, idx: usize) -> Lit {
        debug_assert!(idx < self.lit_len(cid));
        let start = self.lits_start(cid);
        Lit(self.words[start + idx])
    }

    /// Swaps two literals inside `cid`.
    fn swap_lits(&mut self, cid: ClauseId, a: usize, b: usize) {
        debug_assert!(a < self.lit_len(cid));
        debug_assert!(b < self.lit_len(cid));
        let start = self.lits_start(cid);
        self.words.swap(start + a, start + b);
    }

    /// Visits each literal in `cid` in stored order.
    fn visit_lits(&self, cid: ClauseId, mut visit: impl FnMut(Lit)) {
        let start = self.lits_start(cid);
        let end = start + self.lit_len(cid);
        for &raw in &self.words[start..end] {
            visit(Lit(raw));
        }
    }

    /// Packs the header metadata word.
    fn pack_meta(len: usize, learnt: bool, deleted: bool) -> u32 {
        let mut meta = len as u32;
        if learnt {
            meta |= Self::LEARNT_BIT;
        }
        if deleted {
            meta |= Self::DELETED_BIT;
        }
        meta
    }

    /// Returns the metadata word stored for `cid`.
    fn meta(&self, cid: ClauseId) -> u32 {
        self.words[self.offsets[cid.0]]
    }

    /// Returns the starting word index of `cid`'s literal payload.
    fn lits_start(&self, cid: ClauseId) -> usize {
        self.offsets[cid.0] + Self::HEADER_WORDS
    }

    /// Appends the two packed `u32` words for an activity value.
    fn write_activity_words(&mut self, activity: f64) {
        let bits = activity.to_bits();
        self.words.push(bits as u32);
        self.words.push((bits >> 32) as u32);
    }
}

/// A conflict discovered during propagation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum Conflict {
    /// A conflict caused by a falsified binary clause.
    Binary(Lit, Lit),
    /// A conflict caused by a falsified long clause.
    Clause(ClauseId),
}

/// The result of updating a watched long clause.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum LongAction {
    /// Drop the watcher because the clause has been deleted.
    Drop,
    /// Keep the watcher on the current literal with an updated blocker.
    Keep {
        /// A literal currently satisfying or otherwise blocking the clause.
        blocker: Lit,
    },
    /// Move the watcher to a different literal.
    Move {
        /// The literal that should receive the moved watcher.
        new_watch: Lit,
        /// The blocker paired with the moved watcher.
        blocker: Lit,
    },
    /// The clause became unit and now forces the given literal.
    Unit {
        /// The unit literal implied by the clause.
        lit: Lit,
    },
    /// The clause became conflicting under the current assignment.
    Conflict,
}

/// A clause-like source used during conflict analysis.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AnalyzeSource {
    /// Treat a binary clause as an analysis source.
    Binary(Lit, Lit),
    /// Treat a long clause as an analysis source.
    Clause(ClauseId),
}

/// The outcome of a SAT solve attempt.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SatResult {
    /// The formula is satisfiable.
    Sat,
    /// The formula is unsatisfiable.
    Unsat,
}

/// A max-heap over decision variables ordered by activity.
#[derive(Debug)]
struct VarHeap {
    /// Heap storage containing variable identifiers.
    heap: Vec<Var>,
    /// Heap positions indexed by variable, or `-1` when absent.
    pos: Vec<i32>,
}

impl VarHeap {
    /// Creates an empty activity heap.
    fn new() -> Self {
        Self {
            heap: Vec::new(),
            pos: Vec::new(),
        }
    }

    /// Reserves a position slot for a newly created variable.
    fn new_var(&mut self) {
        self.pos.push(-1);
    }

    /// Returns whether the heap currently contains `v`.
    fn contains(&self, v: Var) -> bool {
        self.pos[v.index()] >= 0
    }

    /// Inserts `v` into the heap unless it is already present.
    fn insert(&mut self, v: Var, activity: &[f64]) {
        if self.contains(v) {
            return;
        }
        self.pos[v.index()] = self.heap.len() as i32;
        self.heap.push(v);
        self.percolate_up(self.heap.len() - 1, activity);
    }

    /// Reorders `v` upward after its activity has increased.
    fn increase(&mut self, v: Var, activity: &[f64]) {
        if self.contains(v) {
            self.percolate_up(self.pos[v.index()] as usize, activity);
        }
    }

    /// Removes and returns the highest-activity variable, if any.
    fn pop_max(&mut self, activity: &[f64]) -> Option<Var> {
        if self.heap.is_empty() {
            return None;
        }
        let out = self.heap[0];
        let last = self.heap.pop().unwrap();
        self.pos[out.index()] = -1;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.pos[last.index()] = 0;
            self.percolate_down(0, activity);
        }
        Some(out)
    }

    /// Returns whether `a` should be ordered below `b`.
    fn less(a: Var, b: Var, activity: &[f64]) -> bool {
        activity[a.index()] < activity[b.index()]
    }

    /// Moves the element at `i` upward until the heap invariant is restored.
    fn percolate_up(&mut self, mut i: usize, activity: &[f64]) {
        let x = self.heap[i];
        while i > 0 {
            let p = (i - 1) >> 1;
            if !Self::less(self.heap[p], x, activity) {
                break;
            }
            self.heap[i] = self.heap[p];
            self.pos[self.heap[i].index()] = i as i32;
            i = p;
        }
        self.heap[i] = x;
        self.pos[x.index()] = i as i32;
    }

    /// Moves the element at `i` downward until the heap invariant is restored.
    fn percolate_down(&mut self, mut i: usize, activity: &[f64]) {
        let x = self.heap[i];
        loop {
            let l = (i << 1) + 1;
            if l >= self.heap.len() {
                break;
            }
            let r = l + 1;
            let best = if r < self.heap.len() && Self::less(self.heap[l], self.heap[r], activity) {
                r
            } else {
                l
            };
            if !Self::less(x, self.heap[best], activity) {
                break;
            }
            self.heap[i] = self.heap[best];
            self.pos[self.heap[i].index()] = i as i32;
            i = best;
        }
        self.heap[i] = x;
        self.pos[x.index()] = i as i32;
    }
}

/// A CDCL SAT solver over CNF formulas.
#[derive(Debug)]
pub struct Solver {
    /// Whether the clause database is still known to be consistent.
    ok: bool,
    /// The number of variables allocated in the solver.
    nvars: usize,

    /// Current assignment for each variable.
    assigns: Vec<LBool>,
    /// Decision level at which each variable was assigned.
    level: Vec<usize>,
    /// Antecedent reason for each assignment.
    reason: Vec<Reason>,
    /// Saved branching polarity for phase saving.
    phase: Vec<bool>,
    /// Count of variables that are currently assigned.
    assigned_count: usize,

    /// Assignment trail in chronological order.
    trail: Vec<Lit>,
    /// Trail indices that start each decision level.
    trail_lim: Vec<usize>,
    /// Read cursor into `trail` for propagation.
    qhead: usize,

    /// Watch lists indexed by packed literal.
    watches: Vec<Vec<Watcher>>,
    /// Arena storing all long clauses.
    clauses: ClauseArena,
    /// Active learned clauses eligible for reduction.
    learnts: Vec<ClauseId>,

    /// VSIDS activity per variable.
    var_activity: Vec<f64>,
    /// Current increment added when bumping variable activity.
    var_inc: f64,
    /// Multiplicative decay factor for variable activity.
    var_decay: f64,
    /// Heap of unassigned decision candidates.
    order: VarHeap,

    /// Current increment added when bumping clause activity.
    clause_inc: f64,
    /// Multiplicative decay factor for clause activity.
    clause_decay: f64,

    /// Temporary marks used during conflict analysis.
    seen: Vec<bool>,
    /// Variables marked during conflict analysis for later cleanup.
    analyze_stack: Vec<Var>,
    /// Reusable literal buffer for clause-based conflict analysis.
    analyze_lits: Vec<Lit>,

    /// Number of conflicts seen during the current search.
    conflicts: usize,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    /// Creates an empty solver with no variables or clauses.
    pub fn new() -> Self {
        Self {
            ok: true,
            nvars: 0,
            assigns: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            phase: Vec::new(),
            assigned_count: 0,
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            watches: Vec::new(),
            clauses: ClauseArena::new(),
            learnts: Vec::new(),
            var_activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            order: VarHeap::new(),
            clause_inc: 1.0,
            clause_decay: 0.999,
            seen: Vec::new(),
            analyze_stack: Vec::new(),
            analyze_lits: Vec::new(),
            conflicts: 0,
        }
    }

    /// Creates a solver preallocated with `n` variables.
    pub fn with_vars(n: usize) -> Self {
        let mut s = Self::new();
        for _ in 0..n {
            s.new_var();
        }
        s
    }

    /// Adds a fresh variable and returns its identifier.
    pub fn new_var(&mut self) -> Var {
        let v = Var(self.nvars as u32);
        self.nvars += 1;
        self.assigns.push(LBool::Undef);
        self.level.push(0);
        self.reason.push(Reason::None);
        self.phase.push(true);
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        self.var_activity.push(0.0);
        self.seen.push(false);
        self.order.new_var();
        self.order.insert(v, &self.var_activity);
        v
    }

    /// Returns the number of variables currently known to the solver.
    pub fn num_vars(&self) -> usize {
        self.nvars
    }

    /// Returns the current decision level.
    pub fn decision_level(&self) -> usize {
        self.trail_lim.len()
    }

    /// Returns the current truth value of `lit`, if assigned.
    ///
    /// The return value is `Some(true)` when `lit` is satisfied, `Some(false)` when
    /// `lit` is falsified, and `None` when its variable is unassigned.
    pub fn value_lit_public(&self, lit: Lit) -> Option<bool> {
        match self.value_lit(lit) {
            LBool::True => Some(true),
            LBool::False => Some(false),
            LBool::Undef => None,
        }
    }

    /// Returns a complete model when the solver currently holds one.
    ///
    /// The model is indexed by variable and contains the underlying variable value,
    /// not literal satisfaction.
    pub fn model(&self) -> Option<Vec<bool>> {
        if !self.ok || self.assigned_count != self.nvars {
            return None;
        }
        Some(self.assigns.iter().map(|v| *v == LBool::True).collect())
    }

    /// Adds a CNF clause to the database.
    ///
    /// The method returns `false` when the clause makes the formula immediately
    /// inconsistent; otherwise it returns `true`. Tautological and already-satisfied
    /// clauses are ignored.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        if !self.ok {
            return false;
        }
        let Some(mut ps) = self.prepare_clause(lits) else {
            return true;
        };
        match ps.len() {
            0 => {
                self.ok = false;
                false
            }
            1 => {
                if !self.enqueue(ps[0], Reason::None) {
                    self.ok = false;
                    return false;
                }
                true
            }
            2 => {
                self.attach_binary(ps[0], ps[1]);
                true
            }
            _ => {
                self.attach_long(mem::take(&mut ps), false);
                true
            }
        }
    }

    /// Searches for a satisfying assignment for the current formula.
    pub fn solve(&mut self) -> SatResult {
        if !self.ok {
            return SatResult::Unsat;
        }

        let mut restart_conflicts = 0usize;
        let mut restart_limit = 100usize;
        let mut next_reduce = 2_000usize;

        loop {
            if let Some(conflict) = self.propagate() {
                self.conflicts += 1;
                restart_conflicts += 1;

                if self.decision_level() == 0 {
                    self.ok = false;
                    return SatResult::Unsat;
                }

                let (learnt, backtrack_level) = self.analyze(conflict);
                self.cancel_until(backtrack_level);
                self.add_learnt_clause(learnt);
                self.var_decay_activity();
                self.clause_decay_activity();

                if self.conflicts >= next_reduce {
                    self.reduce_db();
                    next_reduce += 2_000;
                }

                continue;
            }

            if self.assigned_count == self.nvars {
                return SatResult::Sat;
            }

            if restart_conflicts >= restart_limit {
                self.cancel_until(0);
                restart_conflicts = 0;
                restart_limit = ((restart_limit as f64) * 1.5) as usize + 1;
                continue;
            }

            let Some(next) = self.pick_branch_lit() else {
                return SatResult::Sat;
            };
            self.new_decision_level();
            let _ = self.enqueue(next, Reason::None);
        }
    }

    /// Normalizes a clause under the current assignment.
    ///
    /// Satisfied clauses return `None`. Otherwise the result is sorted, duplicate-free,
    /// and stripped of literals already known to be false. Tautologies also return
    /// `None`.
    fn prepare_clause(&self, lits: &[Lit]) -> Option<Vec<Lit>> {
        let mut ps = Vec::with_capacity(lits.len());
        for &lit in lits {
            match self.value_lit(lit) {
                LBool::True => return None,
                LBool::False => {}
                LBool::Undef => ps.push(lit),
            }
        }

        ps.sort_unstable_by_key(|lit| lit.index());

        let mut out = Vec::with_capacity(ps.len());
        let mut prev: Option<Lit> = None;
        for lit in ps {
            if prev == Some(lit) {
                continue;
            }
            if let Some(p) = prev
                && p.var() == lit.var()
                && p.is_negated() != lit.is_negated()
            {
                return None;
            }
            out.push(lit);
            prev = Some(lit);
        }
        Some(out)
    }

    /// Attaches a binary clause to both of its watch lists.
    fn attach_binary(&mut self, a: Lit, b: Lit) {
        self.watches[a.index()].push(Watcher::Binary { other: b });
        self.watches[b.index()].push(Watcher::Binary { other: a });
    }

    /// Stores and watches a long clause, optionally marking it as learned.
    fn attach_long(&mut self, lits: Vec<Lit>, learnt: bool) -> ClauseId {
        debug_assert!(lits.len() >= 3);
        let w0 = lits[0];
        let w1 = lits[1];
        let cid = self.clauses.alloc(&lits, learnt, 0.0);
        self.watches[w0.index()].push(Watcher::Long {
            clause: cid,
            blocker: w1,
        });
        self.watches[w1.index()].push(Watcher::Long {
            clause: cid,
            blocker: w0,
        });
        if learnt {
            self.learnts.push(cid);
            self.clauses.set_activity(cid, self.clause_inc);
        }
        cid
    }

    /// Inserts a learned clause and enqueues its asserting literal.
    fn add_learnt_clause(&mut self, mut lits: Vec<Lit>) {
        debug_assert!(!lits.is_empty());
        if lits.len() > 1 {
            let mut max_i = 1;
            for i in 2..lits.len() {
                if self.level[lits[i].var().index()] > self.level[lits[max_i].var().index()] {
                    max_i = i;
                }
            }
            lits.swap(1, max_i);
        }

        match lits.len() {
            1 => {
                let _ = self.enqueue(lits[0], Reason::None);
            }
            2 => {
                self.attach_binary(lits[0], lits[1]);
                let _ = self.enqueue(lits[0], Reason::Binary(lits[0], lits[1]));
            }
            _ => {
                let cid = self.attach_long(lits, true);
                let lit = self.clauses.lit(cid, 0);
                let _ = self.enqueue(lit, Reason::Clause(cid));
            }
        }
    }

    /// Assigns `lit` if it is undefined and checks for immediate contradiction.
    fn enqueue(&mut self, lit: Lit, reason: Reason) -> bool {
        match self.value_lit(lit) {
            LBool::True => true,
            LBool::False => false,
            LBool::Undef => {
                let v = lit.var().index();
                self.assigns[v] = if lit.is_negated() {
                    LBool::False
                } else {
                    LBool::True
                };
                self.level[v] = self.decision_level();
                self.reason[v] = reason;
                self.phase[v] = !lit.is_negated();
                self.trail.push(lit);
                self.assigned_count += 1;
                true
            }
        }
    }

    /// Evaluates the current truth value of `lit`.
    fn value_lit(&self, lit: Lit) -> LBool {
        Self::value_lit_in(&self.assigns, lit)
    }

    /// Evaluates `lit` against an arbitrary assignment slice.
    fn value_lit_in(assigns: &[LBool], lit: Lit) -> LBool {
        match assigns[lit.var().index()] {
            LBool::Undef => LBool::Undef,
            LBool::True => {
                if lit.is_negated() {
                    LBool::False
                } else {
                    LBool::True
                }
            }
            LBool::False => {
                if lit.is_negated() {
                    LBool::True
                } else {
                    LBool::False
                }
            }
        }
    }

    /// Propagates all pending assignments until fixpoint or conflict.
    fn propagate(&mut self) -> Option<Conflict> {
        while self.qhead < self.trail.len() {
            let lit = self.trail[self.qhead];
            self.qhead += 1;
            let false_lit = !lit;
            let watch_idx = false_lit.index();

            let mut ws = mem::take(&mut self.watches[watch_idx]);
            let mut out = 0usize;
            let mut i = 0usize;

            while i < ws.len() {
                let watcher = ws[i];
                let mut keep: Option<Watcher> = None;
                let mut conflict: Option<Conflict> = None;

                match watcher {
                    Watcher::Binary { other } => match self.value_lit(other) {
                        LBool::True => {
                            keep = Some(watcher);
                        }
                        LBool::Undef => {
                            keep = Some(watcher);
                            if !self.enqueue(other, Reason::Binary(false_lit, other)) {
                                conflict = Some(Conflict::Binary(false_lit, other));
                            }
                        }
                        LBool::False => {
                            keep = Some(watcher);
                            conflict = Some(Conflict::Binary(false_lit, other));
                        }
                    },
                    Watcher::Long { clause, blocker } => {
                        if self.value_lit(blocker) == LBool::True {
                            keep = Some(watcher);
                        } else {
                            match self.process_long_watch(clause, false_lit) {
                                LongAction::Drop => {}
                                LongAction::Keep { blocker } => {
                                    keep = Some(Watcher::Long { clause, blocker });
                                }
                                LongAction::Move { new_watch, blocker } => {
                                    self.watches[new_watch.index()]
                                        .push(Watcher::Long { clause, blocker });
                                }
                                LongAction::Unit { lit } => {
                                    keep = Some(Watcher::Long {
                                        clause,
                                        blocker: lit,
                                    });
                                    if !self.enqueue(lit, Reason::Clause(clause)) {
                                        conflict = Some(Conflict::Clause(clause));
                                    }
                                }
                                LongAction::Conflict => {
                                    keep = Some(Watcher::Long {
                                        clause,
                                        blocker: false_lit,
                                    });
                                    conflict = Some(Conflict::Clause(clause));
                                }
                            }
                        }
                    }
                }

                if let Some(w) = keep {
                    ws[out] = w;
                    out += 1;
                }

                if let Some(c) = conflict {
                    i += 1;
                    while i < ws.len() {
                        ws[out] = ws[i];
                        out += 1;
                        i += 1;
                    }
                    ws.truncate(out);
                    self.watches[watch_idx] = ws;
                    return Some(c);
                }

                i += 1;
            }

            ws.truncate(out);
            self.watches[watch_idx] = ws;
        }
        None
    }

    /// Reprocesses a watched long clause whose second watcher became false.
    fn process_long_watch(&mut self, cid: ClauseId, false_lit: Lit) -> LongAction {
        let assigns = &self.assigns;
        if self.clauses.is_deleted(cid) {
            return LongAction::Drop;
        }

        if self.clauses.lit(cid, 0) == false_lit {
            self.clauses.swap_lits(cid, 0, 1);
        }
        debug_assert_eq!(self.clauses.lit(cid, 1), false_lit);

        let other = self.clauses.lit(cid, 0);
        if Self::value_lit_in(assigns, other) == LBool::True {
            return LongAction::Keep { blocker: other };
        }

        for k in 2..self.clauses.lit_len(cid) {
            let candidate = self.clauses.lit(cid, k);
            if Self::value_lit_in(assigns, candidate) != LBool::False {
                self.clauses.swap_lits(cid, 1, k);
                let new_watch = self.clauses.lit(cid, 1);
                return LongAction::Move {
                    new_watch,
                    blocker: other,
                };
            }
        }

        match Self::value_lit_in(assigns, other) {
            LBool::Undef => LongAction::Unit { lit: other },
            LBool::False => LongAction::Conflict,
            LBool::True => LongAction::Keep { blocker: other },
        }
    }

    /// Starts a new decision level at the current trail position.
    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
    }

    /// Backtracks to `level`, undoing assignments above it.
    fn cancel_until(&mut self, level: usize) {
        if self.decision_level() <= level {
            return;
        }
        let keep = self.trail_lim[level];
        for i in (keep..self.trail.len()).rev() {
            let lit = self.trail[i];
            let v = lit.var();
            let vi = v.index();
            self.assigns[vi] = LBool::Undef;
            self.reason[vi] = Reason::None;
            self.level[vi] = 0;
            self.assigned_count -= 1;
            self.order.insert(v, &self.var_activity);
        }
        self.trail.truncate(keep);
        self.trail_lim.truncate(level);
        self.qhead = self.trail.len();
    }

    /// Picks the next unassigned branching literal according to activity and phase.
    fn pick_branch_lit(&mut self) -> Option<Lit> {
        while let Some(v) = self.order.pop_max(&self.var_activity) {
            if self.assigns[v.index()] == LBool::Undef {
                return Some(Lit::new(v, !self.phase[v.index()]));
            }
        }
        None
    }

    /// Performs first-UIP conflict analysis and returns the learned clause.
    ///
    /// The tuple contains the learned clause and the backtrack level for its second
    /// highest decision level literal.
    fn analyze(&mut self, conflict: Conflict) -> (Vec<Lit>, usize) {
        let current_level = self.decision_level();
        let mut learnt = Vec::with_capacity(16);
        learnt.push(Lit(0));

        let mut path_count = 0usize;
        let mut trail_idx = self.trail.len();
        let mut source = self.conflict_source(conflict);
        let mut resolved: Option<Var> = None;

        loop {
            if let AnalyzeSource::Clause(cid) = source {
                self.bump_clause_activity(cid);
            }

            self.visit_source_lits(source, |this, q| {
                let v = q.var();
                if resolved == Some(v) {
                    return;
                }
                let vi = v.index();
                if !this.seen[vi] && this.level[vi] > 0 {
                    this.seen[vi] = true;
                    this.analyze_stack.push(v);
                    this.bump_var_activity(v);
                    if this.level[vi] == current_level {
                        path_count += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            });

            let p = loop {
                trail_idx -= 1;
                let p = self.trail[trail_idx];
                if self.seen[p.var().index()] {
                    break p;
                }
            };

            let pv = p.var();
            self.seen[pv.index()] = false;
            path_count -= 1;

            if path_count == 0 {
                learnt[0] = !p;
                break;
            }

            resolved = Some(pv);
            source = match self.reason[pv.index()] {
                Reason::Binary(a, b) => AnalyzeSource::Binary(a, b),
                Reason::Clause(cid) => AnalyzeSource::Clause(cid),
                Reason::None => {
                    learnt[0] = !p;
                    break;
                }
            };
        }

        for v in self.analyze_stack.drain(..) {
            self.seen[v.index()] = false;
        }

        let mut backtrack_level = 0usize;
        if learnt.len() > 1 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var().index()] > self.level[learnt[max_i].var().index()] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            backtrack_level = self.level[learnt[1].var().index()];
        }

        (learnt, backtrack_level)
    }

    /// Converts a propagated conflict into a clause-like analysis source.
    fn conflict_source(&self, conflict: Conflict) -> AnalyzeSource {
        match conflict {
            Conflict::Binary(a, b) => AnalyzeSource::Binary(a, b),
            Conflict::Clause(cid) => AnalyzeSource::Clause(cid),
        }
    }

    /// Visits the literals that participate in an analysis source.
    fn visit_source_lits(&mut self, source: AnalyzeSource, mut visit: impl FnMut(&mut Self, Lit)) {
        match source {
            AnalyzeSource::Binary(a, b) => {
                visit(self, a);
                visit(self, b);
            }
            AnalyzeSource::Clause(cid) => {
                let mut lits = mem::take(&mut self.analyze_lits);
                lits.clear();
                self.clauses.visit_lits(cid, |lit| lits.push(lit));
                for lit in lits.iter().copied() {
                    visit(self, lit);
                }
                self.analyze_lits = lits;
            }
        }
    }

    /// Increases the activity score of `v` and updates heap order.
    fn bump_var_activity(&mut self, v: Var) {
        let vi = v.index();
        self.var_activity[vi] += self.var_inc;
        if self.var_activity[vi] > 1e100 {
            for a in &mut self.var_activity {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.order.increase(v, &self.var_activity);
    }

    /// Applies variable activity decay for future bumps.
    fn var_decay_activity(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    /// Increases the activity score of a learned clause.
    fn bump_clause_activity(&mut self, cid: ClauseId) {
        if !self.clauses.is_learnt(cid) || self.clauses.is_deleted(cid) {
            return;
        }
        let new_activity = self.clauses.activity(cid) + self.clause_inc;
        self.clauses.set_activity(cid, new_activity);
        if new_activity > 1e20 {
            self.clauses.scale_activities(1e-20);
            self.clause_inc *= 1e-20;
        }
    }

    /// Applies clause activity decay for future bumps.
    fn clause_decay_activity(&mut self) {
        self.clause_inc *= 1.0 / self.clause_decay;
    }

    /// Deletes the least useful half of removable learned clauses.
    fn reduce_db(&mut self) {
        if self.learnts.len() < 128 {
            return;
        }

        let mut locked = vec![false; self.clauses.len()];
        for &reason in &self.reason {
            if let Reason::Clause(cid) = reason {
                locked[cid.0] = true;
            }
        }

        let mut candidates: Vec<ClauseId> = self
            .learnts
            .iter()
            .copied()
            .filter(|&cid| {
                !self.clauses.is_deleted(cid) && self.clauses.lit_len(cid) > 2 && !locked[cid.0]
            })
            .collect();

        candidates.sort_by(|&a, &b| {
            self.clauses
                .activity(a)
                .partial_cmp(&self.clauses.activity(b))
                .unwrap_or(Ordering::Equal)
        });

        let remove = candidates.len() / 2;
        for cid in candidates.into_iter().take(remove) {
            self.clauses.set_deleted(cid, true);
        }

        self.learnts.retain(|&cid| !self.clauses.is_deleted(cid));
    }
}

/// Parses a DIMACS CNF document into a [`Solver`].
///
/// The returned solver already contains the declared variables and clauses but does
/// not run search automatically.
pub fn parse_dimacs(input: &str) -> Result<Solver, String> {
    let mut declared_vars: Option<usize> = None;
    let mut declared_clauses: Option<usize> = None;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut current: Vec<Lit> = Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(format!("bad problem line: {line}"));
            }
            declared_vars = Some(
                parts[2]
                    .parse()
                    .map_err(|_| format!("bad var count: {}", parts[2]))?,
            );
            declared_clauses = Some(
                parts[3]
                    .parse()
                    .map_err(|_| format!("bad clause count: {}", parts[3]))?,
            );
            continue;
        }

        for tok in line.split_whitespace() {
            let x: i32 = tok
                .parse()
                .map_err(|_| format!("bad integer token: {tok}"))?;
            if x == 0 {
                clauses.push(mem::take(&mut current));
            } else {
                current.push(Lit::from_dimacs(x));
            }
        }
    }

    if !current.is_empty() {
        return Err("last clause is missing trailing 0".to_string());
    }

    let nvars = declared_vars.ok_or_else(|| "missing p cnf line".to_string())?;
    if let Some(nclauses) = declared_clauses
        && nclauses != clauses.len()
    {
        return Err(format!(
            "declared {nclauses} clauses, parsed {}",
            clauses.len()
        ));
    }

    let mut solver = Solver::with_vars(nvars);
    for clause in clauses {
        for lit in &clause {
            if lit.var().index() >= nvars {
                return Err(format!(
                    "literal uses variable {} beyond declared {nvars}",
                    lit.var().index() + 1
                ));
            }
        }
        solver.add_clause(&clause);
    }
    Ok(solver)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(v: Var) -> Lit {
        Lit::new(v, false)
    }

    fn nlit(v: Var) -> Lit {
        Lit::new(v, true)
    }

    #[test]
    fn unit_sat() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert!(s.add_clause(&[lit(x)]));
        assert_eq!(s.solve(), SatResult::Sat);
        assert_eq!(s.value_lit_public(lit(x)), Some(true));
    }

    #[test]
    fn direct_unsat() {
        let mut s = Solver::new();
        let x = s.new_var();
        assert!(s.add_clause(&[lit(x)]));
        assert!(!s.add_clause(&[nlit(x)]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn xor_unsat() {
        let mut s = Solver::new();
        let a = s.new_var();
        let b = s.new_var();
        assert!(s.add_clause(&[lit(a), lit(b)]));
        assert!(s.add_clause(&[nlit(a), lit(b)]));
        assert!(s.add_clause(&[lit(a), nlit(b)]));
        assert!(s.add_clause(&[nlit(a), nlit(b)]));
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn dimacs_sat() {
        let input = "p cnf 3 2\n1 -2 0\n2 3 0\n";
        let mut s = parse_dimacs(input).unwrap();
        assert_eq!(s.solve(), SatResult::Sat);
    }
}
