//! SAT-facing EUF theory integration.

use sat::{Lit, Scope, Theory, TheoryClause, TheoryClauseKind, Var};

use crate::registry::Registry;
use crate::search_state::{
    ClassMerge, DiseqInput, DisequalityEntry, MergeInput, MergeReason, SearchState,
};
use crate::telemetry;
use crate::types::{
    AtomLiteralKind, AtomRef, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef, TheoryAtomId,
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
}

impl EufTheory {
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
    fn theory_atom_for_var(&self, var: Var) -> Option<TheoryAtomId> {
        self.var_to_theory_atom.get(var.index()).copied().flatten()
    }

    /// Decodes one SAT literal as one EUF atom literal, if applicable.
    fn atom_literal_kind(&self, lit: Lit) -> Option<AtomLiteralKind> {
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
        while let Some(lit) = self.search.pop_pending_assignment() {
            let Some(atom) = self.theory_atom_for_var(lit.var()) else {
                continue;
            };
            let value = !lit.is_negated();
            self.search.assign_theory_atom(atom, value);

            match self.atom_literal_kind(lit) {
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: true,
                }) => {
                    telemetry::record_input_equality();
                    self.search.enqueue_input_equality(MergeInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                }
                Some(AtomLiteralKind::Eq {
                    lhs,
                    rhs,
                    positive: false,
                }) => {
                    telemetry::record_input_disequality();
                    let diseq = self.search.enqueue_input_disequality(DiseqInput {
                        lhs,
                        rhs,
                        reason_lit: lit,
                    });
                    self.check_disequality(diseq);
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
                if self.has_pending_conflict() {
                    return;
                }
                self.repair_congruence();
                if self.has_pending_conflict() {
                    return;
                }
            }

            self.process_pending_atom_triggers();
            if self.has_pending_conflict() {
                return;
            }

            if self.search.pending_merges.is_empty()
                && self.search.pending_repairs.is_empty()
                && self.search.pending_atom_qhead == self.search.pending_atom_triggers.len()
            {
                return;
            }
        }
    }

    /// Returns whether EUF has already produced a conflict for the current SAT
    /// synchronization point.
    fn has_pending_conflict(&self) -> bool {
        self.search
            .pending_clauses
            .iter()
            .any(|clause| clause.kind == TheoryClauseKind::ConflictExplanation)
    }

    /// Applies one input equality merge.
    fn merge_input(&mut self, input: MergeInput) {
        let lhs_root = self.search.find(input.lhs);
        let rhs_root = self.search.find(input.rhs);
        if lhs_root == rhs_root {
            return;
        }
        let merge = self.search.union_roots(&self.registry, lhs_root, rhs_root);
        self.search.push_merge_edge(
            input.lhs,
            input.rhs,
            MergeReason::InputEq {
                reason_lit: input.reason_lit,
            },
        );
        self.after_class_merge(merge);
    }

    /// Applies one congruence-driven merge.
    fn merge_due_to_congruence(&mut self, lhs_parent: TermId, rhs_parent: TermId) {
        let lhs_root = self.search.find(lhs_parent);
        let rhs_root = self.search.find(rhs_parent);
        if lhs_root == rhs_root {
            return;
        }
        telemetry::record_congruence_merge();
        let merge = self.search.union_roots(&self.registry, lhs_root, rhs_root);
        self.search.push_merge_edge(
            lhs_parent,
            rhs_parent,
            MergeReason::Congruence {
                left_parent: lhs_parent,
                right_parent: rhs_parent,
            },
        );
        self.after_class_merge(merge);
    }

    /// Emits any conflict found while queueing work for one successful merge.
    fn after_class_merge(&mut self, merge: ClassMerge) {
        debug_assert_eq!(
            self.search.find(TermId::from_index(merge.absorbed.index())),
            merge.survivor,
        );
        if let Some(diseq) = merge.disequality_conflict {
            self.emit_disequality_conflict(diseq);
        }
    }

    /// Repairs congruence closure after recent merges.
    fn repair_congruence(&mut self) {
        while let Some(parent) = self.search.pending_repairs.pop_front() {
            self.repair_parent_app(parent);
        }
    }

    /// Rechecks one parent application under current child representatives.
    fn repair_parent_app(&mut self, parent: TermId) {
        if self.registry.term_ref(parent).args.is_empty() {
            return;
        }
        let existing = self.search.find_congruent_parent(&self.registry, parent);

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
        self.search.signature_log.push(owned.clone());
        self.search.signatures.insert(owned, parent);
    }

    /// Emits a conflict if one active disequality is currently violated.
    fn check_disequality(&mut self, diseq: DisequalityEntry) {
        if self.search.find(diseq.lhs) == self.search.find(diseq.rhs) {
            self.emit_disequality_conflict(diseq);
        }
    }

    /// Emits one conflict clause for a violated disequality.
    fn emit_disequality_conflict(&mut self, diseq: DisequalityEntry) {
        let mut explanation = Vec::new();
        self.search
            .explain_conflict(&self.registry, diseq, &mut explanation);
        telemetry::record_theory_conflict();
        self.search.pending_clauses.push(self.build_theory_clause(
            &explanation,
            None,
            TheoryClauseKind::ConflictExplanation,
        ));
    }

    /// Processes every affected atom trigger.
    fn process_pending_atom_triggers(&mut self) {
        while self.search.pending_atom_qhead < self.search.pending_atom_triggers.len() {
            let atom = self.search.pending_atom_triggers[self.search.pending_atom_qhead];
            self.search.pending_atom_qhead += 1;
            self.search.atom_is_enqueued[atom.index()] = false;
            self.evaluate_atom_trigger(atom);
            if self.has_pending_conflict() {
                return;
            }
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
        let current_value = self.search.atom_value(atom);

        if equal_now && current_value.is_none() {
            let mut support = Vec::new();
            self.search
                .explain_equality(&self.registry, lhs, rhs, &mut support);
            telemetry::record_theory_propagation();
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
            telemetry::record_theory_conflict();
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
            scope: Scope::ROOT,
            kind,
        }
    }

    /// Captures the current EUF gauges for one telemetry sample boundary.
    #[cfg(feature = "telemetry")]
    pub fn telemetry_gauges(&self) -> telemetry::Gauges {
        telemetry::Gauges {
            registry_terms: self.registry.num_terms() as u64,
            registry_atoms: self.registry.num_atoms() as u64,
            pending_assignments: self.search.pending_assignment_count() as u64,
            assigned_atoms: self.search.assigned_atom_count() as u64,
            pending_merges: self.search.pending_merges.len() as u64,
            pending_repairs: self.search.pending_repairs.len() as u64,
            pending_atom_triggers: self
                .search
                .pending_atom_triggers
                .len()
                .saturating_sub(self.search.pending_atom_qhead)
                as u64,
            pending_theory_clauses: self.search.pending_clauses.len() as u64,
            active_disequalities: self.search.active_disequalities.len() as u64,
            congruence_table_entries: self.search.signatures.len() as u64,
        }
    }
}

impl Theory for EufTheory {
    fn notify_search_start(&mut self) {
        self.search.reset_for_registry(&self.registry);
    }

    fn notify_new_level(&mut self) {
        self.search.push_level();
    }

    fn notify_assignment(&mut self, lit: Lit) {
        if self.theory_atom_for_var(lit.var()).is_some() {
            self.search.enqueue_pending_assignment(lit);
        }
    }

    fn notify_backtrack(&mut self, level: sat::Level) {
        self.search.pop_levels(level);
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
        self.search.has_pending_work()
    }

    #[cfg(feature = "telemetry")]
    fn maybe_emit_telemetry_sample(&self, sat_gauges: sat::telemetry::Gauges) {
        telemetry::maybe_emit_sample(sat_gauges, self.telemetry_gauges());
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
        let mut theory = EufTheory::default();
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
        let a = theory.intern_term(TermRef::nullary(a_sym), u_sort);
        let fa = theory.intern_term(TermRef { fun: f, args: &[a] }, u_sort);

        assert_eq!(theory.registry.term_sort(fa), u_sort);
        assert_eq!(theory.intern_sort(SortRef::Bool), bool_sort);

        let sat_var = sat.new_var();
        let atom = theory.intern_equality_atom(fa, a, sat_var);
        assert_eq!(theory.theory_atom_for_var(sat_var), Some(atom));
    }

    #[test]
    fn theory_reports_conflict_for_negative_congruence_atom() {
        let mut sat = sat::Solver::new();
        let mut theory = EufTheory::default();
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
        let a = theory.intern_term(TermRef::nullary(a_sym), u_sort);
        let b = theory.intern_term(TermRef::nullary(b_sym), u_sort);
        let fa = theory.intern_term(TermRef { fun: f, args: &[a] }, u_sort);
        let fb = theory.intern_term(TermRef { fun: f, args: &[b] }, u_sort);

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

    #[test]
    fn theory_repairs_congruence_through_transitive_input_merges() {
        let mut sat = sat::Solver::new();
        let mut theory = EufTheory::default();
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
        let c_sym = theory.intern_symbol(SymbolRef {
            name: "c",
            arg_sorts: &[],
            result_sort: u_sort,
        });
        let a = theory.intern_term(TermRef::nullary(a_sym), u_sort);
        let b = theory.intern_term(TermRef::nullary(b_sym), u_sort);
        let c = theory.intern_term(TermRef::nullary(c_sym), u_sort);
        let fa = theory.intern_term(TermRef { fun: f, args: &[a] }, u_sort);
        let fc = theory.intern_term(TermRef { fun: f, args: &[c] }, u_sort);

        let ab_var = sat.new_var();
        let bc_var = sat.new_var();
        let fafc_var = sat.new_var();
        let ab = bool_lit(ab_var);
        let bc = bool_lit(bc_var);
        let not_fafc = neg_bool_lit(fafc_var);
        theory.intern_equality_atom(a, b, ab_var);
        theory.intern_equality_atom(b, c, bc_var);
        theory.intern_equality_atom(fa, fc, fafc_var);

        let _ = sat.add_clause(&[ab]);
        let _ = sat.add_clause(&[bc]);
        let _ = sat.add_clause(&[not_fafc]);

        assert_eq!(
            sat.solve_with_assumptions(&[], &mut theory),
            sat::SatResult::Unsat
        );
    }
}
