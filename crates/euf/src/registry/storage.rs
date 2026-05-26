//! Permanent registry implementation.
//!
//! This file owns the canonical object tables and the solver-lifetime arena that
//! backs variable-sized payloads such as names and argument lists.

use crate::arena::{Interner, BumpStorage, make_hash};
use crate::ids::{AtomRef, SortId, SortRef, SymbolId, SymbolRef, TermId, TermRef, TheoryAtomId};

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
    /// Lazily created Boolean sort.
    bool_sort: Option<SortId>,
    /// Lazily created canonical true term.
    true_term: Option<TermId>,
}

impl Registry {
    /// Interns one sort.
    pub fn intern_sort(&mut self, sort: SortRef<'_>) -> SortId {
        if let Some(id) = self.find_sort(sort) {
            return id;
        }
        let owned = match sort {
            SortRef::Bool => Sort::Bool,
            SortRef::Uninterpreted { name } => Sort::Uninterpreted {
                name: self.storage.alloc_str(name),
            },
        };
        let id = self.sorts.intern(owned);
        if matches!(sort, SortRef::Bool) {
            self.bool_sort = Some(id);
        }
        id
    }

    /// Interns one symbol.
    pub fn intern_symbol(&mut self, symbol: SymbolRef<'_>) -> SymbolId {
        if let Some(id) = self.find_symbol(symbol) {
            return id;
        }
        let owned = Symbol {
            name: self.storage.alloc_str(symbol.name),
            arg_sorts: self.storage.alloc_slice(symbol.arg_sorts),
            result_sort: symbol.result_sort,
        };
        self.symbols.intern(owned)
    }

    /// Interns one term together with its already-known sort.
    pub fn intern_term(&mut self, term: TermRef<'_>, sort: SortId) -> TermId {
        if let Some(id) = self.find_term(term) {
            return id;
        }
        let owned = match term {
            TermRef::Const(symbol) => Term::Const(symbol),
            TermRef::App { fun, args } => Term::App {
                fun,
                args: self.storage.alloc_slice(args),
            },
        };
        let id = self.terms.intern(owned);
        self.term_sort.push(sort);
        self.term_atoms.push(Vec::new());
        self.parent_apps.push(Vec::new());

        if let TermRef::App { args, .. } = term {
            for &arg in args {
                self.parent_apps[arg.index()].push(id);
            }
        }

        id
    }

    /// Interns one theory atom.
    pub fn intern_atom(&mut self, atom: AtomRef) -> TheoryAtomId {
        let normalized = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => Atom::Eq(rhs, lhs),
            AtomRef::Eq(lhs, rhs) => Atom::Eq(lhs, rhs),
        };
        if let Some(id) = self.find_atom(match normalized {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        }) {
            return id;
        }
        let id = self.atoms.intern(normalized);
        let Atom::Eq(lhs, rhs) = normalized;
        self.term_atoms[lhs.index()].push(id);
        if lhs != rhs {
            self.term_atoms[rhs.index()].push(id);
        }
        id
    }

    /// Finds one previously interned sort.
    pub fn find_sort(&self, sort: SortRef<'_>) -> Option<SortId> {
        let hash = make_hash(self.sorts.index.hasher(), &sort);
        self.sorts
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(sort))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned symbol.
    pub fn find_symbol(&self, symbol: SymbolRef<'_>) -> Option<SymbolId> {
        let hash = make_hash(self.symbols.index.hasher(), &symbol);
        self.symbols
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(symbol))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned term.
    pub fn find_term(&self, term: TermRef<'_>) -> Option<TermId> {
        let hash = make_hash(self.terms.index.hasher(), &term);
        self.terms
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(term))
            .map(|(_, &id)| id)
    }

    /// Finds one previously interned atom.
    pub fn find_atom(&self, atom: AtomRef) -> Option<TheoryAtomId> {
        let atom = match atom {
            AtomRef::Eq(lhs, rhs) if rhs < lhs => AtomRef::Eq(rhs, lhs),
            other => other,
        };
        let hash = make_hash(self.atoms.index.hasher(), &atom);
        self.atoms
            .index
            .raw_entry()
            .from_hash(hash, |stored| stored.matches_ref(atom))
            .map(|(_, &id)| id)
    }

    /// Returns one borrowed view over the canonical sort named by `id`.
    pub fn sort_ref(&self, id: SortId) -> SortRef<'_> {
        match self.sorts.get(id.index()) {
            Sort::Bool => SortRef::Bool,
            Sort::Uninterpreted { name } => {
                // SAFETY: `Sort` is registry-private, so `name` can only point into
                // `self.storage`.
                SortRef::Uninterpreted {
                    name: unsafe { name.as_str() },
                }
            }
        }
    }

    /// Returns one borrowed view over the canonical symbol named by `id`.
    pub fn symbol_ref(&self, id: SymbolId) -> SymbolRef<'_> {
        let symbol = self.symbols.get(id.index());
        SymbolRef {
            // SAFETY: `Symbol` is registry-private, so `name` can only point into
            // `self.storage`.
            name: unsafe { symbol.name.as_str() },
            // SAFETY: `Symbol` is registry-private, so `arg_sorts` can only point
            // into `self.storage`.
            arg_sorts: unsafe { symbol.arg_sorts.as_slice() },
            result_sort: symbol.result_sort,
        }
    }

    /// Returns one borrowed view over the canonical term named by `id`.
    pub fn term_ref(&self, id: TermId) -> TermRef<'_> {
        match self.terms.get(id.index()) {
            Term::Const(symbol) => TermRef::Const(*symbol),
            Term::App { fun, args } => TermRef::App {
                fun: *fun,
                // SAFETY: `Term` is registry-private, so `args` can only point into
                // `self.storage`.
                args: unsafe { args.as_slice() },
            },
        }
    }

    /// Returns one borrowed view over the canonical atom named by `id`.
    pub fn atom_ref(&self, id: TheoryAtomId) -> AtomRef {
        match *self.atoms.get(id.index()) {
            Atom::Eq(lhs, rhs) => AtomRef::Eq(lhs, rhs),
        }
    }

    /// Returns the number of canonical terms.
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Returns the number of canonical atoms.
    pub fn num_atoms(&self) -> usize {
        self.atoms.len()
    }

    /// Returns the sort of one interned term.
    pub fn term_sort(&self, id: TermId) -> SortId {
        self.term_sort[id.index()]
    }

    /// Returns the permanent incidence list for `id`.
    pub fn term_atoms(&self, id: TermId) -> &[TheoryAtomId] {
        &self.term_atoms[id.index()]
    }

    /// Returns the permanent structural parent list for `id`.
    pub fn parent_apps(&self, id: TermId) -> &[TermId] {
        &self.parent_apps[id.index()]
    }

    /// Returns the canonical Boolean sort, creating it on demand.
    pub fn bool_sort(&mut self) -> SortId {
        if let Some(sort) = self.bool_sort {
            return sort;
        }
        self.intern_sort(SortRef::Bool)
    }

    /// Returns the canonical Boolean true term, creating it on demand.
    pub fn true_term(&mut self) -> TermId {
        if let Some(term) = self.true_term {
            return term;
        }
        let bool_sort = self.bool_sort();
        let symbol = self.intern_symbol(SymbolRef {
            name: "true",
            arg_sorts: &[],
            result_sort: bool_sort,
        });
        let term = self.intern_term(TermRef::Const(symbol), bool_sort);
        self.true_term = Some(term);
        term
    }
}
