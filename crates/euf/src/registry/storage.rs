//! Permanent registry implementation.
//!
//! This file owns the canonical object tables and the solver-lifetime arena that
//! backs variable-sized payloads such as names and argument lists.

use crate::arena::{BumpStorage, Interned, Interner};
use crate::types::{AtomRef, Sort, SortRef, Symbol, SymbolRef, Term, TermRef, TheoryAtom};

use super::object::{AtomEntry, SortEntry, SymbolEntry, TermEntry};

/// Permanent registry of canonical terms, symbols, sorts, and atoms.
#[derive(Debug, Default)]
pub struct Registry {
    /// Solver-lifetime payload storage.
    storage: BumpStorage,

    /// Canonical sort table.
    sorts: Interner<Sort, SortEntry>,
    /// Canonical symbol table.
    symbols: Interner<Symbol, SymbolEntry>,
    /// Canonical term table.
    terms: Interner<Term, TermEntry>,
    /// Canonical atom table.
    atoms: Interner<TheoryAtom, AtomEntry>,

    /// Derived sort for each interned term.
    term_sort: Vec<Sort>,
    /// Permanent atom incidence lists.
    term_atoms: Vec<Vec<TheoryAtom>>,
    /// Permanent structural parent use-lists.
    parent_apps: Vec<Vec<Term>>,
}

impl Registry {
    /// Interns one sort.
    pub(crate) fn intern_sort(&mut self, sort: SortRef<'_>) -> Sort {
        self.sorts
            .intern(sort, || match sort {
                SortRef::Bool => SortEntry::Bool,
                SortRef::Uninterpreted { name } => SortEntry::Uninterpreted {
                    name: self.storage.alloc_str(name),
                },
            })
            .key
    }

    /// Interns one symbol.
    pub(crate) fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> Symbol {
        self.symbols
            .intern(symbol, || SymbolEntry {
                name: self.storage.alloc_str(symbol.name),
                arg_sorts: self.storage.alloc_slice(symbol.arg_sorts),
                result_sort: symbol.result_sort,
            })
            .key
    }

    /// Interns one term together with its already-known sort.
    pub(crate) fn intern_term(&mut self, term: TermRef<'_>, sort: Sort) -> Term {
        let symbol = self.symbols.get(term.fun.index());
        // SAFETY: `SymbolEntry` is registry-private, so `arg_sorts` can only point into
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

        let interned = self.terms.intern(term, || TermEntry {
            fun: term.fun,
            args: self.storage.alloc_slice(term.args),
        });

        let Interned { key, is_new } = interned;

        if is_new {
            self.term_sort.push(sort);
            self.term_atoms.push(Vec::new());
            self.parent_apps.push(Vec::new());

            for &arg in term.args {
                self.parent_apps[arg.index()].push(key);
            }
        }

        key
    }

    /// Interns one theory atom.
    pub(crate) fn intern_atom(&mut self, atom: AtomRef) -> TheoryAtom {
        let normalized = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => AtomEntry::Eq(rhs, lhs),
            AtomRef::Eq(lhs, rhs) => AtomEntry::Eq(lhs, rhs),
        };
        let query = match normalized {
            AtomEntry::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        };
        let Interned { key, is_new } = self.atoms.intern(query, || normalized);

        if is_new {
            let AtomEntry::Eq(lhs, rhs) = normalized;
            self.term_atoms[lhs.index()].push(key);
            if lhs != rhs {
                self.term_atoms[rhs.index()].push(key);
            }
        }

        key
    }

    /// Returns one borrowed view over the canonical term.
    pub(crate) fn term_ref(&self, term_key: Term) -> TermRef<'_> {
        let term = self.terms.get(term_key.index());
        TermRef {
            fun: term.fun,
            // SAFETY: `TermEntry` is registry-private, so `args` can only point into
            // `self.storage`.
            args: unsafe { term.args.as_slice() },
        }
    }

    /// Returns one borrowed view over the canonical atom.
    pub(crate) fn atom_ref(&self, atom: TheoryAtom) -> AtomRef {
        match *self.atoms.get(atom.index()) {
            AtomEntry::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
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
    pub(crate) fn term_sort(&self, term: Term) -> Sort {
        self.term_sort[term.index()]
    }

    /// Returns the permanent incidence list for `term`.
    pub(crate) fn term_atoms(&self, term: Term) -> &[TheoryAtom] {
        &self.term_atoms[term.index()]
    }

    /// Returns the permanent structural parent list for `term`.
    pub(crate) fn parent_apps(&self, term: Term) -> &[Term] {
        &self.parent_apps[term.index()]
    }
}
