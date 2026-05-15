use std::mem;

use crate::Lit;
use crate::clause_db::ClauseId;
use crate::telemetry;

use super::{LBool, Reason, Solver};

/// A watched-literal entry attached to a literal's watch list.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Watcher {
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

/// A conflict discovered during propagation.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum Conflict {
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

impl Solver {
    /// Assigns `lit` if it is undefined and checks for immediate contradiction.
    pub(crate) fn enqueue(&mut self, lit: Lit, reason: Reason) -> bool {
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
                if !matches!(reason, Reason::None) {
                    telemetry::record_propagation();
                }
                true
            }
        }
    }

    /// Evaluates the current truth value of `lit`.
    pub(crate) fn value_lit(&self, lit: Lit) -> LBool {
        Self::value_lit_in(&self.assigns, lit)
    }

    /// Evaluates `lit` against an arbitrary assignment slice.
    pub(crate) fn value_lit_in(assigns: &[LBool], lit: Lit) -> LBool {
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
    pub(crate) fn propagate(&mut self) -> Option<Conflict> {
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
        // This cid may be stale. If so, delete it from the watch list.
        let Some(mut clause) = self.clauses.try_clause_mut(cid) else {
            return LongAction::Drop;
        };
        let assigns = &self.assigns;

        if clause.lit(0) == false_lit {
            clause.swap_lits(0, 1);
        }
        debug_assert_eq!(clause.lit(1), false_lit);

        let other = clause.lit(0);
        if Self::value_lit_in(assigns, other) == LBool::True {
            return LongAction::Keep { blocker: other };
        }

        for k in 2..clause.len() {
            let candidate = clause.lit(k);
            if Self::value_lit_in(assigns, candidate) != LBool::False {
                clause.swap_lits(1, k);
                let new_watch = clause.lit(1);
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
}
