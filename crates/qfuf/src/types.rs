/// One parsed S-expression.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SExpr {
    /// One atom token.
    Atom(Box<str>),
    /// One list form.
    List(Vec<SExpr>),
}

/// One supported SMT-LIB command.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Command {
    /// `(set-logic ...)`
    SetLogic(Box<str>),
    /// `(set-info ...)`
    SetInfo,
    /// `(declare-sort name 0)`
    DeclareSort {
        /// Declared sort name.
        name: Box<str>,
    },
    /// `(declare-fun name (args...) result)`
    DeclareFun {
        /// Declared function name.
        name: Box<str>,
        /// Declared argument sort names.
        args: Vec<Box<str>>,
        /// Declared result sort name.
        result: Box<str>,
    },
    /// `(declare-const name sort)`
    DeclareConst {
        /// Declared constant name.
        name: Box<str>,
        /// Declared constant sort name.
        sort: Box<str>,
    },
    /// `(assert expr)`
    Assert(SExpr),
    /// `(push 1)`
    Push(u32),
    /// `(pop 1)`
    Pop(u32),
    /// `(check-sat)`
    CheckSat,
    /// `(exit)`
    Exit,
}

/// One declared function symbol.
#[derive(Copy, Clone, Debug)]
pub(crate) struct FunDecl {
    /// Canonical symbol identifier.
    pub(crate) symbol: euf::SymbolId,
    /// Declared argument count.
    pub(crate) arity: u32,
    /// Result sort.
    pub(crate) result_sort: euf::SortId,
}

/// One lowered Boolean subexpression.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum BoolView {
    /// Constant true.
    True,
    /// Constant false.
    False,
    /// Existing SAT literal.
    Lit(sat::Lit),
}

/// One local `let` binding visible while lowering one expression subtree.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum LocalBinding {
    /// One Boolean binding cached as a SAT-level Boolean view.
    Bool(BoolView),
    /// One term binding cached as a canonical term and its sort.
    Term {
        /// Canonical term identifier.
        term: euf::TermId,
        /// Sort of the cached term.
        sort: euf::SortId,
    },
}

/// Negates one lowered Boolean view.
pub(crate) fn negate_view(view: BoolView) -> BoolView {
    match view {
        BoolView::True => BoolView::False,
        BoolView::False => BoolView::True,
        BoolView::Lit(lit) => BoolView::Lit(!lit),
    }
}
