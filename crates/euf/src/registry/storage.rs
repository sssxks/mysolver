//! Permanent registry implementation.
//!
//! This file owns the canonical object tables and the solver-lifetime arena that
//! backs variable-sized payloads such as names and argument lists.

use crate::arena::{BumpStorage, Interned, Interner};
use crate::types::{AtomRef, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef, TheoryAtomId};

use super::object::{Atom, Sort, Symbol, Term};

/// Permanent registry of canonical terms, symbols, sorts, and atoms.
#[derive(Debug, Default)]
pub struct Registry {
    /// Solver-lifetime payload storage.
    storage: BumpStorage,

    /// Canonical sort table.
    sorts: Interner<SortId, Sort>,
    /// Canonical symbol table.
    symbols: Interner<SymbolId, Symbol>,
    /// Canonical term table.
    terms: Interner<TermId, Term>,
    /// Canonical atom table.
    atoms: Interner<TheoryAtomId, Atom>,

    /// Derived sort for each interned term.
    term_sort: Vec<SortId>,
    /// Permanent atom incidence lists.
    term_atoms: Vec<Vec<TheoryAtomId>>,
    /// Permanent structural parent use-lists.
    parent_apps: Vec<Vec<TermId>>,
}

impl Registry {
    /// Interns one sort.
    pub(crate) fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId {
        self.sorts
            .intern(sort, || match sort {
                SortRef::Bool => Sort::Bool,
                SortRef::Uninterpreted { name } => Sort::Uninterpreted {
                    name: self.storage.alloc_str(name),
                },
            })
            .id
    }

    /// Interns one symbol.
    pub(crate) fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId {
        self.symbols
            .intern(symbol, || Symbol {
                name: self.storage.alloc_str(symbol.name),
                arg_sorts: self.storage.alloc_slice(symbol.arg_sorts),
                result_sort: symbol.result_sort,
            })
            .id
    }

    /// Interns one term together with its already-known sort.
    pub(crate) fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        let symbol = self.symbols.get(term.fun.index());
        // SAFETY: `Symbol` is registry-private, so `arg_sorts` can only point into
        // `self.storage`.
        let expected_arg_sorts = unsafe { symbol.arg_sorts.as_slice() };
        assert_eq!(
            expected_arg_sorts.len(),
            term.args.len(),
            "term arity must match the declared symbol signature",
        );
        assert_eq!(
            symbol.result_sort, sort,
            "term sort must match the declared symbol result sort",
        );
        for (&arg, &expected_sort) in term.args.iter().zip(expected_arg_sorts.iter()) {
            let Some(&actual_sort) = self.term_sort.get(arg.index()) else {
                panic!("term arguments must already be interned");
            };
            assert_eq!(
                actual_sort, expected_sort,
                "term argument sort must match the declared symbol signature",
            );
        }

        let interned = self.terms.intern(term, || Term {
            fun: term.fun,
            args: self.storage.alloc_slice(term.args),
        });

        let Interned { id, is_new } = interned;

        if is_new {
            self.term_sort.push(sort);
            self.term_atoms.push(Vec::new());
            self.parent_apps.push(Vec::new());

            for &arg in term.args {
                self.parent_apps[arg.index()].push(id);
            }
        }

        id
    }

    /// Interns one theory atom.
    pub(crate) fn intern_atom(&mut self, atom: AtomRef) -> TheoryAtomId {
        let normalized = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => Atom::Eq(rhs, lhs),
            AtomRef::Eq(lhs, rhs) => Atom::Eq(lhs, rhs),
        };
        let query = match normalized {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        };
        let Interned { id, is_new } = self.atoms.intern(query, || normalized);

        if is_new {
            let Atom::Eq(lhs, rhs) = normalized;
            self.term_atoms[lhs.index()].push(id);
            if lhs != rhs {
                self.term_atoms[rhs.index()].push(id);
            }
        }

        id
    }

    /// Returns one borrowed view over the canonical term named by `id`.
    pub(crate) fn term_ref(&self, id: TermId) -> TermRef<'_> {
        let term = self.terms.get(id.index());
        TermRef {
            fun: term.fun,
            // SAFETY: `Term` is registry-private, so `args` can only point into
            // `self.storage`.
            args: unsafe { term.args.as_slice() },
        }
    }

    /// Returns one borrowed view over the canonical atom named by `id`.
    pub(crate) fn atom_ref(&self, id: TheoryAtomId) -> AtomRef {
        match *self.atoms.get(id.index()) {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        }
    }

    /// Returns the number of canonical terms.
    pub(crate) fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Returns the number of canonical atoms.
    pub(crate) fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    /// Returns the sort of one interned term.
    #[cfg(test)]
    pub(crate) fn term_sort(&self, id: TermId) -> SortId {
        self.term_sort[id.index()]
    }

    /// Returns the permanent incidence list for `id`.
    pub(crate) fn term_atoms(&self, id: TermId) -> &[TheoryAtomId] {
        &self.term_atoms[id.index()]
    }

    /// Returns the permanent structural parent list for `id`.
    pub(crate) fn parent_apps(&self, id: TermId) -> &[TermId] {
        &self.parent_apps[id.index()]
    }
}
