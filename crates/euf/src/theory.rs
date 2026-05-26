//! SAT-facing EUF theory integration.

use std::collections::VecDeque;

use sat::{AssertionLevel, Lit, Theory, TheoryClause, TheoryClauseKind, Var};

use crate::AtomLiteralKind;
use crate::registry::Registry;
use crate::search_state::{
    DiseqInput, DisequalityEntry, MergeEdge, MergeInput, MergeReason, SearchState, Undo,
};
use crate::types::{
    AtomRef, EClassId, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef, TheoryAtomId,
};

/// The EUF theory module exposed to the SAT engine.
#[derive(Debug, Default)]
pub struct EufTheory {
    /// Permanent canonical registry.
    registry: Registry,

    /// Search-local congruence closure state.
    search: SearchState,

    /// Forward map from theory atoms to SAT variables.
    theory_atom_to_var: Vec<Var>,
    /// Reverse map from SAT variables to theory atoms.
    var_to_theory_atom: Vec<Option<TheoryAtomId>>,
    /// Queue of assigned theory literals not yet processed by EUF.
    pending_assignments: VecDeque<Lit>,

    /// Search-local atom assignment cache.
    atom_value: Vec<Option<bool>>,
    /// Search-local assigned atom trail.
    atom_trail: Vec<TheoryAtomId>,
    /// Search-local decision-level starts for `atom_trail`.
    atom_trail_lim: Vec<usize>,
}

impl EufTheory {
    /// Creates one empty theory object.
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns one sort.
    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId {
        self.registry.intern_sort(sort)
    }

    /// Interns one symbol.
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId {
        self.registry.intern_symbol(symbol)
    }

    /// Interns one term.
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        self.registry.intern_term(term, sort)
    }

    /// Interns one equality atom and binds it to `sat_var`.
    pub fn intern_equality_atom(&mut self, lhs: TermId, rhs: TermId, sat_var: Var) -> TheoryAtomId {
        let atom = self.registry.intern_atom(AtomRef::Eq(lhs, rhs));

        if self.theory_atom_to_var.len() <= atom.index() {
            self.theory_atom_to_var.resize(atom.index() + 1, sat_var);
        }
        let existing = self.theory_atom_to_var[atom.index()];
        assert_eq!(
            existing, sat_var,
            "canonical theory atom cannot be bound to multiple SAT variables",
        );

        if self.var_to_theory_atom.len() <= sat_var.index() {
            self.var_to_theory_atom.resize(sat_var.index() + 1, None);
        }
        match self.var_to_theory_atom[sat_var.index()] {
            Some(existing_atom) => assert_eq!(existing_atom, atom),
            None => self.var_to_theory_atom[sat_var.index()] = Some(atom),
        }
        atom
    }

    /// Returns the canonical atom, if any, bound to `var`.
    pub fn theory_atom_for_var(&self, var: Var) -> Option<TheoryAtomId> {
        self.var_to_theory_atom.get(var.index()).copied().flatten()
    }

    /// Decodes one SAT literal as one EUF atom literal, if applicable.
    pub fn atom_literal_kind(&self, lit: Lit) -> Option<AtomLiteralKind> {
        let atom = self.theory_atom_for_var(lit.var())?;
        match self.registry.atom_ref(atom) {
            AtomRef::Eq(lhs, rhs) => Some(AtomLiteralKind::Eq {
                lhs,
                rhs,
                positive: !lit.is_negated(),
            }),
        }
    }

    /// Processes all theory assignments currently buffered from SAT.
    fn process_pending_assignments(&mut self) {
        while let Some(lit) = self.pending_assignments.pop_front() {
            let Some(atom) = self.theory_atom_for_var(lit.var()) else {
                continue;
            };
            let value = !lit.is_negated();
            if self.atom_value.len() <= atom.index() {
                self.atom_value.resize(atom.index() + 1, None);
            }
            self.atom_value[atom.index()] = Some(value);
            self.atom_trail.push(atom);

            match self.atom_literal_kind(lit) {
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: true,
                }) => {
                    self.search.enqueue_input_equality(MergeInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.saturate();
                }
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: false,
                }) => {
                    self.search.enqueue_input_disequality(DiseqInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.check_active_disequalities();
                }
                None => {}
            }
        }
    }

    /// Saturates the current congruence state.
    fn saturate(&mut self) {
        loop {
            while let Some(input) = self.search.pending_merges.pop_front() {
                self.merge_input(input);
                self.repair_congruence();
                self.check_active_disequalities();
            }

            self.process_pending_atom_triggers();

            if self.search.pending_merges.is_empty()
                && self.search.pending_repairs.is_empty()
                && self.search.pending_atom_qhead == self.search.pending_atom_triggers.len()
            {
                return;
            }
        }
    }

    /// Applies one input equality merge.
    fn merge_input(&mut self, input: MergeInput) {
        let lhs_root = self.search.find(input.lhs);
        let rhs_root = self.search.find(input.rhs);
        if lhs_root == rhs_root {
            return;
        }
        let merged_root = self.search.union_roots(lhs_root, rhs_root);
        self.search.merge_edges.push(MergeEdge {
            lhs: input.lhs,
            rhs: input.rhs,
            reason: MergeReason::InputEq {
                reason_lit: input.reason_lit,
            },
        });
        self.enqueue_repairs_for_class(merged_root);
        self.enqueue_atom_triggers_for_class(merged_root);
    }

    /// Applies one congruence-driven merge.
    fn merge_due_to_congruence(&mut self, lhs_parent: TermId, rhs_parent: TermId) {
        let lhs_root = self.search.find(lhs_parent);
        let rhs_root = self.search.find(rhs_parent);
        if lhs_root == rhs_root {
            return;
        }
        let merged_root = self.search.union_roots(lhs_root, rhs_root);
        self.search.merge_edges.push(MergeEdge {
            lhs: lhs_parent,
            rhs: rhs_parent,
            reason: MergeReason::Congruence {
                left_parent: lhs_parent,
                right_parent: rhs_parent,
            },
        });
        self.enqueue_repairs_for_class(merged_root);
        self.enqueue_atom_triggers_for_class(merged_root);
    }

    /// Repairs congruence closure after recent merges.
    fn repair_congruence(&mut self) {
        while let Some(parent) = self.search.pending_repairs.pop_front() {
            self.repair_parent_app(parent);
        }
    }

    /// Enqueues parent applications of one changed class.
    fn enqueue_repairs_for_class(&mut self, root: EClassId) {
        let mut current = Some(self.search.class_head[root.index()]);
        while let Some(term) = current {
            for &parent in self.registry.parent_apps(term) {
                self.search.pending_repairs.push_back(parent);
            }
            current = self.search.next_in_class[term.index()];
        }
    }

    /// Enqueues atom triggers attached to one changed class.
    fn enqueue_atom_triggers_for_class(&mut self, root: EClassId) {
        let mut current = Some(self.search.class_head[root.index()]);
        while let Some(term) = current {
            for &atom in self.registry.term_atoms(term) {
                self.search.enqueue_atom_trigger(atom);
            }
            current = self.search.next_in_class[term.index()];
        }
    }

    /// Rechecks one parent application under current child representatives.
    fn repair_parent_app(&mut self, parent: TermId) {
        let existing = match self.registry.term_ref(parent) {
            TermRef::Const(_) => return,
            TermRef::App { .. } => self.search.find_congruent_parent(&self.registry, parent),
        };

        if let Some(existing) = existing {
            if self.search.find(existing) != self.search.find(parent) {
                self.merge_due_to_congruence(existing, parent);
            }
            return;
        }

        let Some(fun) = self
            .search
            .fill_congruence_sig_scratch(&self.registry, parent)
        else {
            return;
        };
        let owned = self.search.own_current_congruence_sig(fun);
        self.search
            .undo_log
            .push(Undo::CongruenceInsert { key: owned.clone() });
        self.search.congruence_table.insert(owned, parent);
    }

    /// Emits conflicts for any active disequality that is now violated.
    fn check_active_disequalities(&mut self) {
        let mut explanation = Vec::new();
        for &diseq in &self.search.active_disequalities {
            if self.search.find(diseq.lhs) != self.search.find(diseq.rhs) {
                continue;
            }
            self.search
                .explain_conflict(&self.registry, diseq, &mut explanation);
            self.search.pending_clauses.push(self.build_theory_clause(
                &explanation,
                None,
                TheoryClauseKind::ConflictExplanation,
            ));
            break;
        }
    }

    /// Processes every affected atom trigger.
    fn process_pending_atom_triggers(&mut self) {
        while self.search.pending_atom_qhead < self.search.pending_atom_triggers.len() {
            let atom = self.search.pending_atom_triggers[self.search.pending_atom_qhead];
            self.search.pending_atom_qhead += 1;
            self.search.atom_is_enqueued[atom.index()] = false;
            self.evaluate_atom_trigger(atom);
        }
    }

    /// Re-evaluates one registered atom under current equality classes.
    fn evaluate_atom_trigger(&mut self, atom: TheoryAtomId) {
        let AtomRef::Eq(lhs, rhs) = self.registry.atom_ref(atom);
        let Some(&sat_var) = self.theory_atom_to_var.get(atom.index()) else {
            return;
        };
        let lit = Lit::new(sat_var, false);
        let equal_now = self.search.find(lhs) == self.search.find(rhs);
        let current_value = self.atom_value.get(atom.index()).copied().flatten();

        if equal_now && current_value.is_none() {
            let mut support = Vec::new();
            self.search
                .explain_equality(&self.registry, lhs, rhs, &mut support);
            self.search.pending_clauses.push(self.build_theory_clause(
                &support,
                Some(lit),
                TheoryClauseKind::PropagationExplanation,
            ));
        }

        if equal_now && current_value == Some(false) {
            let diseq = DisequalityEntry {
                lhs,
                rhs,
                reason_lit: !lit,
            };
            let mut support = Vec::new();
            self.search
                .explain_conflict(&self.registry, diseq, &mut support);
            self.search.pending_clauses.push(self.build_theory_clause(
                &support,
                None,
                TheoryClauseKind::ConflictExplanation,
            ));
        }
    }

    /// Builds one SAT-facing theory clause from already explained premise literals.
    fn build_theory_clause(
        &self,
        premises: &[Lit],
        propagated: Option<Lit>,
        kind: TheoryClauseKind,
    ) -> TheoryClause {
        let mut lits = Vec::with_capacity(premises.len() + usize::from(propagated.is_some()));
        for &premise in premises {
            lits.push(!premise);
        }
        if let Some(propagated) = propagated {
            lits.push(propagated);
        }
        TheoryClause {
            lits: lits.into_boxed_slice(),
            assertion_level: AssertionLevel::ROOT,
            kind,
        }
    }
}

impl Theory for EufTheory {
    fn notify_search_start(&mut self) {
        self.search.reset_for_registry(&self.registry);
        self.pending_assignments.clear();
        self.atom_value.clear();
        self.atom_value.resize(self.registry.num_atoms(), None);
        self.atom_trail.clear();
        self.atom_trail_lim.clear();
    }

    fn notify_new_decision_level(&mut self) {
        self.search.push_sat_level();
        self.atom_trail_lim.push(self.atom_trail.len());
    }

    fn notify_assignment(&mut self, lit: Lit) {
        if self.theory_atom_for_var(lit.var()).is_some() {
            self.pending_assignments.push_back(lit);
        }
    }

    fn notify_backtrack(&mut self, level: usize) {
        self.search.pop_sat_levels(level);
        while self.atom_trail_lim.len() > level {
            let keep = self.atom_trail_lim.pop().expect("checked above");
            while self.atom_trail.len() > keep {
                let atom = self.atom_trail.pop().expect("checked above");
                self.atom_value[atom.index()] = None;
            }
        }
    }

    fn drain_clauses(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn final_check(&mut self, out: &mut Vec<TheoryClause>) {
        self.process_pending_assignments();
        self.saturate();
        out.append(&mut self.search.pending_clauses);
    }

    fn has_pending_work(&self) -> bool {
        !self.pending_assignments.is_empty()
            || !self.search.pending_clauses.is_empty()
            || !self.search.pending_merges.is_empty()
            || !self.search.pending_repairs.is_empty()
            || self.search.pending_atom_qhead < self.search.pending_atom_triggers.len()
    }
}

#[cfg(test)]
mod tests {
    use sat::{Lit, Var};

    use super::EufTheory;
    use crate::{SortRef, SymbolRef, TermRef};

    /// Creates one positive Boolean literal for `var`.
    fn bool_lit(var: Var) -> Lit {
        Lit::new(var, false)
    }

    /// Creates one negated Boolean literal for `var`.
    fn neg_bool_lit(var: Var) -> Lit {
        Lit::new(var, true)
    }

    #[test]
    fn registry_interns_terms_and_atoms_canonically() {
        let mut theory = EufTheory::new();
        let mut sat = sat::Solver::new();
        let bool_sort = theory.intern_sort(SortRef::Bool);
        let u_sort = theory.intern_sort(SortRef::Uninterpreted { name: "U" });
        let f = theory.intern_symbol(SymbolRef {
            name: "f",
            arg_sorts: &[u_sort],
            result_sort: u_sort,
        });
        let a_sym = theory.intern_symbol(SymbolRef {
            name: "a",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let a = theory.intern_term(TermRef::Const(a_sym), u_sort);
        let fa = theory.intern_term(TermRef::App { fun: f, args: &[a] }, u_sort);

        assert_eq!(theory.registry.term_sort(fa), u_sort);
        assert_eq!(theory.registry.bool_sort(), bool_sort);

        let sat_var = sat.new_var();
        let atom = theory.intern_equality_atom(fa, a, sat_var);
        assert_eq!(theory.theory_atom_for_var(sat_var), Some(atom));
    }

    #[test]
    fn theory_reports_conflict_for_negative_congruence_atom() {
        let mut sat = sat::Solver::new();
        let mut theory = EufTheory::new();
        let u_sort = theory.intern_sort(SortRef::Uninterpreted { name: "U" });
        let f = theory.intern_symbol(SymbolRef {
            name: "f",
            arg_sorts: &[u_sort],
            result_sort: u_sort,
        });
        let a_sym = theory.intern_symbol(SymbolRef {
            name: "a",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let b_sym = theory.intern_symbol(SymbolRef {
            name: "b",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let a = theory.intern_term(TermRef::Const(a_sym), u_sort);
        let b = theory.intern_term(TermRef::Const(b_sym), u_sort);
        let fa = theory.intern_term(TermRef::App { fun: f, args: &[a] }, u_sort);
        let fb = theory.intern_term(TermRef::App { fun: f, args: &[b] }, u_sort);

        let ab_var = sat.new_var();
        let fafb_var = sat.new_var();
        let ab = bool_lit(ab_var);
        let not_fafb = neg_bool_lit(fafb_var);
        theory.intern_equality_atom(a, b, ab_var);
        theory.intern_equality_atom(fa, fb, fafb_var);

        let _ = sat.add_clause(&[ab]);
        let _ = sat.add_clause(&[not_fafb]);

        assert_eq!(
            sat.solve_with_assumptions(&[], &mut theory),
            sat::SatResult::Unsat
        );
    }
}
