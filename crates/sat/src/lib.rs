use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ENodeId(u32);

impl ENodeId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FunId(u32);

impl FunId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BoolVar(u32);

impl BoolVar {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ClauseId(u32);

impl ClauseId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lit {
    var: BoolVar,
    neg: bool,
}

impl Lit {
    pub fn positive(var: BoolVar) -> Self {
        Self { var, neg: false }
    }

    pub fn negative(var: BoolVar) -> Self {
        Self { var, neg: true }
    }

    pub fn var(self) -> BoolVar {
        self.var
    }

    pub fn is_negative(self) -> bool {
        self.neg
    }

    pub fn negated(self) -> Self {
        Self {
            var: self.var,
            neg: !self.neg,
        }
    }

    fn watch_index(self) -> usize {
        self.var.index() * 2 + usize::from(self.neg)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LBool {
    Undef,
    True,
    False,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveResult {
    Sat,
    Unsat,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reason {
    Clause(ClauseId),
}

#[derive(Clone, Debug)]
struct Assignment {
    value: LBool,
    level: usize,
    reason: Option<Reason>,
}

#[derive(Clone, Debug)]
struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
}

#[derive(Default)]
struct SatCore {
    assigns: Vec<Assignment>,
    clauses: Vec<Clause>,
    watches: Vec<Vec<ClauseId>>,
    trail: Vec<Lit>,
    trail_head: usize,
    level_starts: Vec<usize>,
    immediate_conflict: Option<ClauseId>,
}

impl SatCore {
    fn new() -> Self {
        Self::default()
    }

    fn new_var(&mut self) -> BoolVar {
        let var = BoolVar(self.assigns.len() as u32);
        self.assigns.push(Assignment {
            value: LBool::Undef,
            level: 0,
            reason: None,
        });
        self.watches.push(Vec::new());
        self.watches.push(Vec::new());
        var
    }

    fn decision_level(&self) -> usize {
        self.level_starts.len()
    }

    fn new_decision_level(&mut self) {
        self.level_starts.push(self.trail.len());
    }

    fn value_var(&self, var: BoolVar) -> LBool {
        self.assigns[var.index()].value
    }

    fn value_lit(&self, lit: Lit) -> LBool {
        match self.value_var(lit.var) {
            LBool::Undef => LBool::Undef,
            LBool::True => {
                if lit.neg {
                    LBool::False
                } else {
                    LBool::True
                }
            }
            LBool::False => {
                if lit.neg {
                    LBool::True
                } else {
                    LBool::False
                }
            }
        }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<Reason>) -> bool {
        match self.value_lit(lit) {
            LBool::True => true,
            LBool::False => false,
            LBool::Undef => {
                let level = self.decision_level();
                let assignment = &mut self.assigns[lit.var.index()];
                assignment.value = if lit.neg { LBool::False } else { LBool::True };
                assignment.level = level;
                assignment.reason = reason;
                self.trail.push(lit);
                true
            }
        }
    }

    fn add_clause(&mut self, lits: Vec<Lit>, learnt: bool) -> ClauseId {
        let id = ClauseId(self.clauses.len() as u32);
        self.clauses.push(Clause { lits, learnt });
        self.attach_clause(id);
        id
    }

    fn add_problem_clause(&mut self, lits: Vec<Lit>) {
        let id = self.add_clause(lits, false);
        if self.clauses[id.index()].lits.is_empty() {
            self.immediate_conflict = Some(id);
            return;
        }
        if self.clauses[id.index()].lits.len() == 1 {
            let lit = self.clauses[id.index()].lits[0];
            if !self.enqueue(lit, Some(Reason::Clause(id))) {
                self.immediate_conflict = Some(id);
            }
        }
    }

    fn attach_clause(&mut self, id: ClauseId) {
        let lits = &self.clauses[id.index()].lits;
        match lits.len() {
            0 => {}
            1 => self.watches[lits[0].watch_index()].push(id),
            _ => {
                self.watches[lits[0].watch_index()].push(id);
                self.watches[lits[1].watch_index()].push(id);
            }
        }
    }

    fn propagate(&mut self) -> Option<ClauseId> {
        if let Some(conflict) = self.immediate_conflict {
            return Some(conflict);
        }

        while self.trail_head < self.trail.len() {
            let assigned = self.trail[self.trail_head];
            self.trail_head += 1;
            let false_lit = assigned.negated();
            let watch_index = false_lit.watch_index();
            let old_watch_list = std::mem::take(&mut self.watches[watch_index]);
            let mut cursor = 0;

            while cursor < old_watch_list.len() {
                let cid = old_watch_list[cursor];
                cursor += 1;

                match self.propagate_watched_clause(cid, false_lit) {
                    WatchResult::KeepWatching => self.watches[watch_index].push(cid),
                    WatchResult::MovedWatch => {}
                    WatchResult::Conflict => {
                        self.watches[watch_index].push(cid);
                        self.watches[watch_index].extend_from_slice(&old_watch_list[cursor..]);
                        return Some(cid);
                    }
                }
            }
        }

        None
    }

    fn propagate_watched_clause(&mut self, cid: ClauseId, false_lit: Lit) -> WatchResult {
        let len = self.clauses[cid.index()].lits.len();
        if len == 0 {
            return WatchResult::Conflict;
        }

        if len == 1 {
            let unit = self.clauses[cid.index()].lits[0];
            return match self.value_lit(unit) {
                LBool::True => WatchResult::KeepWatching,
                LBool::Undef => {
                    if self.enqueue(unit, Some(Reason::Clause(cid))) {
                        WatchResult::KeepWatching
                    } else {
                        WatchResult::Conflict
                    }
                }
                LBool::False => WatchResult::Conflict,
            };
        }

        let (false_pos, other_pos) = {
            let lits = &self.clauses[cid.index()].lits;
            if lits[0] == false_lit {
                (0, 1)
            } else if lits[1] == false_lit {
                (1, 0)
            } else {
                return WatchResult::KeepWatching;
            }
        };

        let other_lit = self.clauses[cid.index()].lits[other_pos];
        if self.value_lit(other_lit) == LBool::True {
            return WatchResult::KeepWatching;
        }

        for i in 2..len {
            let candidate = self.clauses[cid.index()].lits[i];
            if self.value_lit(candidate) != LBool::False {
                self.clauses[cid.index()].lits.swap(false_pos, i);
                self.watches[candidate.watch_index()].push(cid);
                return WatchResult::MovedWatch;
            }
        }

        match self.value_lit(other_lit) {
            LBool::True => WatchResult::KeepWatching,
            LBool::Undef => {
                if self.enqueue(other_lit, Some(Reason::Clause(cid))) {
                    WatchResult::KeepWatching
                } else {
                    WatchResult::Conflict
                }
            }
            LBool::False => WatchResult::Conflict,
        }
    }

    fn cancel_until(&mut self, target_level: usize) {
        while self.decision_level() > target_level {
            let start = self.level_starts.pop().unwrap();
            for lit in self.trail.drain(start..).rev() {
                let assignment = &mut self.assigns[lit.var.index()];
                assignment.value = LBool::Undef;
                assignment.level = 0;
                assignment.reason = None;
            }
            self.trail_head = self.trail_head.min(self.trail.len());
        }
    }

    fn pick_branch_lit(&self) -> Option<Lit> {
        self.assigns
            .iter()
            .enumerate()
            .find(|(_, a)| a.value == LBool::Undef)
            .map(|(idx, _)| Lit::positive(BoolVar(idx as u32)))
    }

    fn all_assigned(&self) -> bool {
        self.assigns.iter().all(|a| a.value != LBool::Undef)
    }

    fn analyze(&self, conflict: ClauseId) -> (Vec<Lit>, usize) {
        let current_level = self.decision_level();
        let mut seen = vec![false; self.assigns.len()];
        let mut learnt_tail = Vec::new();
        let mut path_count = 0usize;
        let mut clause_lits = self.clauses[conflict.index()].lits.clone();
        let mut skip_var = None;
        let mut trail_idx = self.trail.len();
        let asserting_lit;

        loop {
            for &lit in &clause_lits {
                if Some(lit.var) == skip_var {
                    continue;
                }
                let var = lit.var;
                if seen[var.index()] {
                    continue;
                }
                let level = self.assigns[var.index()].level;
                if level == 0 {
                    continue;
                }
                seen[var.index()] = true;
                if level == current_level {
                    path_count += 1;
                } else {
                    learnt_tail.push(lit);
                }
            }

            let p = loop {
                trail_idx -= 1;
                let lit = self.trail[trail_idx];
                if seen[lit.var.index()] {
                    break lit;
                }
            };

            seen[p.var.index()] = false;
            path_count -= 1;

            if path_count == 0 {
                asserting_lit = p.negated();
                break;
            }

            skip_var = Some(p.var);
            clause_lits = match self.assigns[p.var.index()].reason {
                Some(Reason::Clause(reason)) => self.clauses[reason.index()].lits.clone(),
                None => Vec::new(),
            };
        }

        let mut learnt = Vec::with_capacity(1 + learnt_tail.len());
        learnt.push(asserting_lit);
        learnt.extend(learnt_tail);

        let backtrack_level = learnt
            .iter()
            .skip(1)
            .map(|lit| self.assigns[lit.var.index()].level)
            .max()
            .unwrap_or(0);

        (learnt, backtrack_level)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WatchResult {
    KeepWatching,
    MovedWatch,
    Conflict,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AppKey {
    fun: FunId,
    args: Vec<ENodeId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AppSignature {
    fun: FunId,
    arg_roots: Vec<ENodeId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct EqKey {
    a: ENodeId,
    b: ENodeId,
}

impl EqKey {
    fn new(a: ENodeId, b: ENodeId) -> Self {
        if a <= b {
            Self { a, b }
        } else {
            Self { a: b, b: a }
        }
    }
}

#[derive(Clone, Debug)]
struct ENode {
    fun: FunId,
    args: Vec<ENodeId>,
    root: ENodeId,
    next: ENodeId,

    /// Number of nodes in this equivalence class.
    ///
    /// This field is meaningful only when this node is the current representative.
    class_size_if_root: u32,

    /// Syntactic parent applications that directly mention this node as an argument.
    ///
    /// This is meaningful for every node, not just representatives. Class-level parents
    /// are obtained by traversing the intrusive class list and concatenating each member's
    /// parent list.
    parents: Vec<ENodeId>,
}

#[derive(Clone, Debug)]
struct Diseq {
    lhs: ENodeId,
    rhs: ENodeId,
    reason_lit: Lit,
}

#[derive(Clone, Debug)]
struct PendingMerge {
    lhs: ENodeId,
    rhs: ENodeId,
    reason: MergeReason,
}

#[derive(Clone, Debug)]
enum MergeReason {
    Input(Lit),
    Congruence { lhs_app: ENodeId, rhs_app: ENodeId },
}

#[derive(Clone, Debug)]
struct EqEdge {
    lhs: ENodeId,
    rhs: ENodeId,
    reason: MergeReason,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct EqEdgeId(u32);

impl EqEdgeId {
    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Debug)]
enum EufUndo {
    Merge {
        absorbed_root: ENodeId,
        absorbing_root: ENodeId,

        /// Size of `absorbing_root` before it absorbed `absorbed_root`.
        ///
        /// Undo restores this value after splitting the intrusive cyclic class list.
        absorbing_root_size_before_merge: u32,
        edge: EqEdgeId,
    },
}

#[derive(Clone, Copy, Debug)]
struct EufScope {
    undo_len: usize,
    signature_log_len: usize,
    pending_len: usize,
    diseq_len: usize,
}

#[derive(Default)]
struct EGraph {
    fun_ids: HashMap<String, FunId>,
    fun_names: Vec<String>,

    app_ids: HashMap<AppKey, ENodeId>,
    enodes: Vec<ENode>,

    signatures: HashMap<AppSignature, ENodeId>,

    /// Append-only log of normalized application signatures inserted after merges.
    ///
    /// A signature is derived from the current representatives of an application's
    /// arguments. We never rewrite `ENode.args`, and we also avoid deleting old
    /// signatures when classes merge. Old signatures simply become stale because
    /// future lookups use current representatives. Backtracking removes only the
    /// signatures inserted after the target scope. This is the cvc5-style
    /// alternative to rebuilding the whole signature table on every backjump.
    signature_log: Vec<AppSignature>,

    pending: Vec<PendingMerge>,
    diseqs: Vec<Diseq>,

    undo: Vec<EufUndo>,
    scopes: Vec<EufScope>,

    edges: Vec<EqEdge>,
    adjacency: Vec<Vec<EqEdgeId>>,

    marks: Vec<u32>,
    mark_stamp: u32,
}

impl EGraph {
    fn new() -> Self {
        Self::default()
    }

    fn fun(&mut self, name: impl Into<String>) -> FunId {
        let name = name.into();
        if let Some(&fun) = self.fun_ids.get(&name) {
            return fun;
        }
        let fun = FunId(self.fun_names.len() as u32);
        self.fun_ids.insert(name.clone(), fun);
        self.fun_names.push(name);
        fun
    }

    fn constant(&mut self, name: impl Into<String>) -> ENodeId {
        let fun = self.fun(name);
        self.app(fun, &[])
    }

    fn app_named(&mut self, name: impl Into<String>, args: &[ENodeId]) -> ENodeId {
        let fun = self.fun(name);
        self.app(fun, args)
    }

    fn app(&mut self, fun: FunId, args: &[ENodeId]) -> ENodeId {
        let key = AppKey {
            fun,
            args: args.to_vec(),
        };
        if let Some(&id) = self.app_ids.get(&key) {
            return id;
        }

        let id = ENodeId(self.enodes.len() as u32);
        self.enodes.push(ENode {
            fun,
            args: args.to_vec(),
            root: id,
            next: id,
            class_size_if_root: 1,
            parents: Vec::new(),
        });
        self.adjacency.push(Vec::new());
        self.marks.push(0);
        self.app_ids.insert(key, id);

        for &arg in args {
            self.enodes[arg.index()].parents.push(id);
        }

        if !args.is_empty() {
            self.insert_signature_or_schedule_merge(id);
            self.propagate_pending();
        }

        id
    }

    fn push_level(&mut self) {
        self.scopes.push(EufScope {
            undo_len: self.undo.len(),
            signature_log_len: self.signature_log.len(),
            pending_len: self.pending.len(),
            diseq_len: self.diseqs.len(),
        });
    }

    fn pop_to_level(&mut self, target_level: usize) {
        while self.scopes.len() > target_level {
            let scope = self.scopes.pop().unwrap();

            self.pending.truncate(scope.pending_len);
            self.pop_signatures_to(scope.signature_log_len);

            while self.undo.len() > scope.undo_len {
                let undo = self.undo.pop().unwrap();
                self.undo_one(undo);
            }

            self.diseqs.truncate(scope.diseq_len);
        }
    }

    fn root(&self, node: ENodeId) -> ENodeId {
        self.enodes[node.index()].root
    }

    fn are_equal(&self, lhs: ENodeId, rhs: ENodeId) -> bool {
        self.root(lhs) == self.root(rhs)
    }

    fn class_members(&self, root: ENodeId) -> Vec<ENodeId> {
        let mut result = Vec::new();
        let mut current = root;
        loop {
            result.push(current);
            current = self.enodes[current.index()].next;
            if current == root {
                break;
            }
        }
        result
    }

    fn assert_eq(&mut self, lhs: ENodeId, rhs: ENodeId, reason_lit: Lit) -> Option<Vec<Lit>> {
        self.pending.push(PendingMerge {
            lhs,
            rhs,
            reason: MergeReason::Input(reason_lit),
        });
        self.propagate_pending();
        self.find_disequality_conflict()
    }

    fn assert_ne(&mut self, lhs: ENodeId, rhs: ENodeId, reason_lit: Lit) -> Option<Vec<Lit>> {
        if self.are_equal(lhs, rhs) {
            return Some(self.explain_diseq_conflict(lhs, rhs, reason_lit));
        }
        self.diseqs.push(Diseq {
            lhs,
            rhs,
            reason_lit,
        });
        None
    }

    fn propagate_pending(&mut self) {
        while let Some(pending) = self.pending.pop() {
            self.merge(pending.lhs, pending.rhs, pending.reason);
        }
    }

    fn merge(&mut self, lhs: ENodeId, rhs: ENodeId, reason: MergeReason) {
        let mut absorbed_root = self.root(lhs);
        let mut absorbing_root = self.root(rhs);
        if absorbed_root == absorbing_root {
            return;
        }

        if self.enodes[absorbed_root.index()].class_size_if_root
            > self.enodes[absorbing_root.index()].class_size_if_root
        {
            std::mem::swap(&mut absorbed_root, &mut absorbing_root);
        }

        let affected_parents = self.collect_affected_parents(absorbed_root);

        let edge = self.add_edge(lhs, rhs, reason.clone());
        let absorbing_root_size_before_merge =
            self.enodes[absorbing_root.index()].class_size_if_root;
        self.undo.push(EufUndo::Merge {
            absorbed_root,
            absorbing_root,
            absorbing_root_size_before_merge,
            edge,
        });

        for member in self.class_members(absorbed_root) {
            self.enodes[member.index()].root = absorbing_root;
        }

        self.swap_next(absorbed_root, absorbing_root);
        let absorbed_size = self.enodes[absorbed_root.index()].class_size_if_root;
        self.enodes[absorbing_root.index()].class_size_if_root += absorbed_size;

        for parent in affected_parents {
            self.insert_signature_or_schedule_merge(parent);
        }
    }

    fn undo_one(&mut self, undo: EufUndo) {
        match undo {
            EufUndo::Merge {
                absorbed_root,
                absorbing_root,
                absorbing_root_size_before_merge,
                edge,
            } => {
                self.pop_edge(edge);
                self.enodes[absorbing_root.index()].class_size_if_root =
                    absorbing_root_size_before_merge;
                self.swap_next(absorbed_root, absorbing_root);
                for member in self.class_members(absorbed_root) {
                    self.enodes[member.index()].root = absorbed_root;
                }
            }
        }
    }

    fn add_edge(&mut self, lhs: ENodeId, rhs: ENodeId, reason: MergeReason) -> EqEdgeId {
        let id = EqEdgeId(self.edges.len() as u32);
        self.edges.push(EqEdge { lhs, rhs, reason });
        self.adjacency[lhs.index()].push(id);
        self.adjacency[rhs.index()].push(id);
        id
    }

    fn pop_edge(&mut self, edge: EqEdgeId) {
        let data = self.edges.pop().unwrap();
        debug_assert_eq!(edge.index(), self.edges.len());
        debug_assert_eq!(self.adjacency[data.lhs.index()].pop(), Some(edge));
        debug_assert_eq!(self.adjacency[data.rhs.index()].pop(), Some(edge));
    }

    fn swap_next(&mut self, lhs: ENodeId, rhs: ENodeId) {
        let lhs_next = self.enodes[lhs.index()].next;
        let rhs_next = self.enodes[rhs.index()].next;
        self.enodes[lhs.index()].next = rhs_next;
        self.enodes[rhs.index()].next = lhs_next;
    }

    fn collect_affected_parents(&mut self, absorbed_root: ENodeId) -> Vec<ENodeId> {
        let stamp = self.fresh_mark_stamp();
        let mut result = Vec::new();
        for member in self.class_members(absorbed_root) {
            let parents = self.enodes[member.index()].parents.clone();
            for parent in parents {
                let mark = &mut self.marks[parent.index()];
                if *mark != stamp {
                    *mark = stamp;
                    result.push(parent);
                }
            }
        }
        result
    }

    fn fresh_mark_stamp(&mut self) -> u32 {
        self.mark_stamp = self.mark_stamp.wrapping_add(1);
        if self.mark_stamp == 0 {
            self.marks.fill(0);
            self.mark_stamp = 1;
        }
        self.mark_stamp
    }

    fn signature(&self, node: ENodeId) -> Option<AppSignature> {
        let enode = &self.enodes[node.index()];
        if enode.args.is_empty() {
            return None;
        }
        Some(AppSignature {
            fun: enode.fun,
            arg_roots: enode.args.iter().map(|&arg| self.root(arg)).collect(),
        })
    }

    fn insert_signature_or_schedule_merge(&mut self, node: ENodeId) {
        let Some(sig) = self.signature(node) else {
            return;
        };
        if let Some(existing) = self.signatures.get(&sig).copied() {
            if self.root(existing) != self.root(node) {
                self.pending.push(PendingMerge {
                    lhs: existing,
                    rhs: node,
                    reason: MergeReason::Congruence {
                        lhs_app: existing,
                        rhs_app: node,
                    },
                });
            }
        } else {
            self.store_signature(sig, node);
        }
    }

    fn store_signature(&mut self, sig: AppSignature, node: ENodeId) {
        let old = self.signatures.insert(sig.clone(), node);
        debug_assert!(old.is_none());
        self.signature_log.push(sig);
    }

    fn pop_signatures_to(&mut self, target_len: usize) {
        while self.signature_log.len() > target_len {
            let sig = self.signature_log.pop().unwrap();
            self.signatures.remove(&sig);
        }
    }

    fn find_disequality_conflict(&self) -> Option<Vec<Lit>> {
        for diseq in &self.diseqs {
            if self.are_equal(diseq.lhs, diseq.rhs) {
                return Some(self.explain_diseq_conflict(diseq.lhs, diseq.rhs, diseq.reason_lit));
            }
        }
        None
    }

    fn explain_diseq_conflict(&self, lhs: ENodeId, rhs: ENodeId, diseq_lit: Lit) -> Vec<Lit> {
        let premises = self.explain_eq(lhs, rhs);
        let mut clause = Vec::with_capacity(premises.len() + 1);
        for lit in premises {
            clause.push(lit.negated());
        }
        clause.push(diseq_lit.negated());
        clause
    }

    fn explain_eq_clause_for_propagation(
        &self,
        lhs: ENodeId,
        rhs: ENodeId,
        propagated: Lit,
    ) -> Vec<Lit> {
        let premises = self.explain_eq(lhs, rhs);
        let mut clause = Vec::with_capacity(premises.len() + 1);
        for lit in premises {
            clause.push(lit.negated());
        }
        clause.push(propagated);
        clause
    }

    fn explain_eq(&self, lhs: ENodeId, rhs: ENodeId) -> Vec<Lit> {
        if lhs == rhs {
            return Vec::new();
        }
        debug_assert!(self.are_equal(lhs, rhs));
        let mut out = HashSet::new();
        let mut active = HashSet::new();
        self.explain_eq_rec(lhs, rhs, &mut out, &mut active);
        out.into_iter().collect()
    }

    fn explain_eq_rec(
        &self,
        lhs: ENodeId,
        rhs: ENodeId,
        out: &mut HashSet<Lit>,
        active: &mut HashSet<EqKey>,
    ) {
        if lhs == rhs {
            return;
        }
        let key = EqKey::new(lhs, rhs);
        if !active.insert(key) {
            return;
        }

        let path = self.find_equality_path(lhs, rhs);
        for edge in path {
            self.explain_edge(edge, out, active);
        }

        active.remove(&key);
    }

    fn explain_edge(
        &self,
        edge: EqEdgeId,
        out: &mut HashSet<Lit>,
        active: &mut HashSet<EqKey>,
    ) {
        match &self.edges[edge.index()].reason {
            MergeReason::Input(lit) => {
                out.insert(*lit);
            }
            MergeReason::Congruence { lhs_app, rhs_app } => {
                let lhs_node = &self.enodes[lhs_app.index()];
                let rhs_node = &self.enodes[rhs_app.index()];
                debug_assert_eq!(lhs_node.fun, rhs_node.fun);
                debug_assert_eq!(lhs_node.args.len(), rhs_node.args.len());
                for (&lhs_arg, &rhs_arg) in lhs_node.args.iter().zip(&rhs_node.args) {
                    if self.root(lhs_arg) != self.root(rhs_arg) {
                        continue;
                    }
                    self.explain_eq_rec(lhs_arg, rhs_arg, out, active);
                }
            }
        }
    }

    fn find_equality_path(&self, lhs: ENodeId, rhs: ENodeId) -> Vec<EqEdgeId> {
        let mut queue = VecDeque::new();
        let mut seen = vec![false; self.enodes.len()];
        let mut prev: Vec<Option<(ENodeId, EqEdgeId)>> = vec![None; self.enodes.len()];

        seen[lhs.index()] = true;
        queue.push_back(lhs);

        while let Some(current) = queue.pop_front() {
            if current == rhs {
                break;
            }
            for &edge in &self.adjacency[current.index()] {
                let data = &self.edges[edge.index()];
                let next = if data.lhs == current { data.rhs } else { data.lhs };
                if !seen[next.index()] {
                    seen[next.index()] = true;
                    prev[next.index()] = Some((current, edge));
                    queue.push_back(next);
                }
            }
        }

        debug_assert!(seen[rhs.index()]);
        let mut path = Vec::new();
        let mut current = rhs;
        while current != lhs {
            let (p, edge) = prev[current.index()].expect("missing equality explanation path");
            path.push(edge);
            current = p;
        }
        path
    }

    fn format_term(&self, node: ENodeId) -> String {
        let enode = &self.enodes[node.index()];
        let name = &self.fun_names[enode.fun.index()];
        if enode.args.is_empty() {
            return name.clone();
        }
        let args = enode
            .args
            .iter()
            .map(|&arg| self.format_term(arg))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{name}({args})")
    }
}

pub struct Solver {
    sat: SatCore,
    egraph: EGraph,
    eq_vars: HashMap<EqKey, BoolVar>,
    var_eqs: Vec<Option<EqKey>>,
    theory_head: usize,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        Self {
            sat: SatCore::new(),
            egraph: EGraph::new(),
            eq_vars: HashMap::new(),
            var_eqs: Vec::new(),
            theory_head: 0,
        }
    }

    pub fn fun(&mut self, name: impl Into<String>) -> FunId {
        self.egraph.fun(name)
    }

    pub fn constant(&mut self, name: impl Into<String>) -> ENodeId {
        self.egraph.constant(name)
    }

    pub fn app(&mut self, fun: FunId, args: &[ENodeId]) -> ENodeId {
        self.egraph.app(fun, args)
    }

    pub fn app_named(&mut self, name: impl Into<String>, args: &[ENodeId]) -> ENodeId {
        self.egraph.app_named(name, args)
    }

    pub fn new_bool(&mut self) -> Lit {
        let var = self.sat.new_var();
        self.var_eqs.push(None);
        Lit::positive(var)
    }

    pub fn eq_lit(&mut self, lhs: ENodeId, rhs: ENodeId) -> Lit {
        let key = EqKey::new(lhs, rhs);
        if let Some(&var) = self.eq_vars.get(&key) {
            return Lit::positive(var);
        }
        let var = self.sat.new_var();
        self.var_eqs.push(Some(key));
        self.eq_vars.insert(key, var);
        Lit::positive(var)
    }

    pub fn add_clause(&mut self, lits: &[Lit]) {
        self.sat.add_problem_clause(lits.to_vec());
    }

    pub fn solve(&mut self) -> SolveResult {
        loop {
            if let Some(conflict) = self.propagate() {
                if self.sat.decision_level() == 0 {
                    return SolveResult::Unsat;
                }
                let (learnt, backtrack_level) = self.sat.analyze(conflict);
                self.backtrack(backtrack_level);
                let cid = self.sat.add_clause(learnt.clone(), true);
                let asserting = learnt[0];
                if !self.sat.enqueue(asserting, Some(Reason::Clause(cid))) {
                    return SolveResult::Unsat;
                }
                continue;
            }

            if self.sat.all_assigned() {
                return SolveResult::Sat;
            }

            let Some(decision) = self.sat.pick_branch_lit() else {
                return SolveResult::Sat;
            };
            self.sat.new_decision_level();
            self.egraph.push_level();
            if !self.sat.enqueue(decision, None) {
                return SolveResult::Unsat;
            }
        }
    }

    fn propagate(&mut self) -> Option<ClauseId> {
        loop {
            if let Some(conflict) = self.sat.propagate() {
                return Some(conflict);
            }

            if let Some(conflict) = self.propagate_theory_assignments() {
                return Some(conflict);
            }

            if let Some(conflict_or_progress) = self.propagate_theory_equalities() {
                match conflict_or_progress {
                    TheoryStep::Conflict(cid) => return Some(cid),
                    TheoryStep::Progress => continue,
                }
            }

            return None;
        }
    }

    fn propagate_theory_assignments(&mut self) -> Option<ClauseId> {
        while self.theory_head < self.sat.trail.len() {
            let lit = self.sat.trail[self.theory_head];
            self.theory_head += 1;

            let Some(key) = self.var_eqs[lit.var.index()] else {
                continue;
            };

            let conflict_clause = if lit.neg {
                self.egraph.assert_ne(key.a, key.b, lit)
            } else {
                self.egraph.assert_eq(key.a, key.b, lit)
            };

            if let Some(clause_lits) = conflict_clause {
                let cid = self.sat.add_clause(clause_lits, true);
                return Some(cid);
            }
        }
        None
    }

    fn propagate_theory_equalities(&mut self) -> Option<TheoryStep> {
        let atoms = self
            .eq_vars
            .iter()
            .map(|(&key, &var)| (key, var))
            .collect::<Vec<_>>();

        for (key, var) in atoms {
            if !self.egraph.are_equal(key.a, key.b) {
                continue;
            }

            let lit = Lit::positive(var);
            match self.sat.value_lit(lit) {
                LBool::True => {}
                LBool::False => {
                    let assigned_diseq = lit.negated();
                    let clause = self
                        .egraph
                        .explain_diseq_conflict(key.a, key.b, assigned_diseq);
                    let cid = self.sat.add_clause(clause, true);
                    return Some(TheoryStep::Conflict(cid));
                }
                LBool::Undef => {
                    let clause = self
                        .egraph
                        .explain_eq_clause_for_propagation(key.a, key.b, lit);
                    let cid = self.sat.add_clause(clause, true);
                    if !self.sat.enqueue(lit, Some(Reason::Clause(cid))) {
                        return Some(TheoryStep::Conflict(cid));
                    }
                    return Some(TheoryStep::Progress);
                }
            }
        }

        None
    }

    fn backtrack(&mut self, target_level: usize) {
        self.sat.cancel_until(target_level);
        self.theory_head = self.theory_head.min(self.sat.trail.len());
        self.egraph.pop_to_level(target_level);
    }

    pub fn value(&self, lit: Lit) -> Option<bool> {
        match self.sat.value_lit(lit) {
            LBool::True => Some(true),
            LBool::False => Some(false),
            LBool::Undef => None,
        }
    }

    pub fn are_equal(&self, lhs: ENodeId, rhs: ENodeId) -> bool {
        self.egraph.are_equal(lhs, rhs)
    }

    pub fn format_term(&self, node: ENodeId) -> String {
        self.egraph.format_term(node)
    }

    pub fn learnt_clause_count(&self) -> usize {
        self.sat.clauses.iter().filter(|c| c.learnt).count()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TheoryStep {
    Conflict(ClauseId),
    Progress,
}

#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn signature_log_removes_merge_created_lookup_on_pop() {
        let mut e = EGraph::new();
        let f = e.fun("f");
        let a = e.constant("a");
        let b = e.constant("b");
        let _fa = e.app(f, &[a]);

        let base_log_len = e.signature_log.len();
        let stale_after_merge = AppSignature {
            fun: f,
            arg_roots: vec![b],
        };
        assert!(!e.signatures.contains_key(&stale_after_merge));

        e.push_level();
        e.assert_eq(a, b, Lit::positive(BoolVar(0)));

        assert!(e.signatures.contains_key(&stale_after_merge));
        assert!(e.signature_log.len() > base_log_len);

        e.pop_to_level(0);

        assert_eq!(e.signature_log.len(), base_log_len);
        assert!(!e.signatures.contains_key(&stale_after_merge));
        assert!(!e.are_equal(a, b));
    }

    #[test]
    fn pure_sat_unsat() {
        let mut s = Solver::new();
        let p = s.new_bool();
        s.add_clause(&[p]);
        s.add_clause(&[p.negated()]);
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn pure_sat_sat() {
        let mut s = Solver::new();
        let p = s.new_bool();
        let q = s.new_bool();
        s.add_clause(&[p, q]);
        s.add_clause(&[p.negated(), q]);
        assert_eq!(s.solve(), SolveResult::Sat);
        assert_eq!(s.value(q), Some(true));
    }

    #[test]
    fn direct_euf_conflict() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let a = s.constant("a");
        let b = s.constant("b");
        let fa = s.app(f, &[a]);
        let fb = s.app(f, &[b]);

        let ab = s.eq_lit(a, b);
        let fafb = s.eq_lit(fa, fb);

        s.add_clause(&[ab]);
        s.add_clause(&[fafb.negated()]);

        assert_eq!(s.solve(), SolveResult::Unsat);
        assert!(s.learnt_clause_count() > 0);
    }

    #[test]
    fn transitive_euf_conflict() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let a = s.constant("a");
        let b = s.constant("b");
        let c = s.constant("c");
        let fa = s.app(f, &[a]);
        let fc = s.app(f, &[c]);

        let ab = s.eq_lit(a, b);
        let bc = s.eq_lit(b, c);
        let fafc = s.eq_lit(fa, fc);

        s.add_clause(&[ab]);
        s.add_clause(&[bc]);
        s.add_clause(&[fafc.negated()]);

        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn cdcl_learns_from_theory_conflict() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let a = s.constant("a");
        let b = s.constant("b");
        let fa = s.app(f, &[a]);
        let fb = s.app(f, &[b]);

        let p = s.new_bool();
        let ab = s.eq_lit(a, b);
        let fafb = s.eq_lit(fa, fb);

        s.add_clause(&[p, ab]);
        s.add_clause(&[p.negated(), ab]);
        s.add_clause(&[fafb.negated()]);

        assert_eq!(s.solve(), SolveResult::Unsat);
        assert!(s.learnt_clause_count() > 0);
    }

    #[test]
    fn sat_with_unconstrained_uf_terms() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let a = s.constant("a");
        let b = s.constant("b");
        let fa = s.app(f, &[a]);
        let fb = s.app(f, &[b]);

        let ab = s.eq_lit(a, b);
        let fafb = s.eq_lit(fa, fb);

        s.add_clause(&[ab.negated()]);
        s.add_clause(&[fafb.negated()]);

        assert_eq!(s.solve(), SolveResult::Sat);
    }

    #[test]
    fn theory_propagates_positive_equality() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let a = s.constant("a");
        let b = s.constant("b");
        let fa = s.app(f, &[a]);
        let fb = s.app(f, &[b]);

        let ab = s.eq_lit(a, b);
        let fafb = s.eq_lit(fa, fb);

        s.add_clause(&[ab]);
        assert_eq!(s.solve(), SolveResult::Sat);
        assert_eq!(s.value(fafb), Some(true));
    }

    #[test]
    fn nested_congruence_explanation() {
        let mut s = Solver::new();
        let f = s.fun("f");
        let g = s.fun("g");
        let a = s.constant("a");
        let b = s.constant("b");
        let ga = s.app(g, &[a]);
        let gb = s.app(g, &[b]);
        let fga = s.app(f, &[ga]);
        let fgb = s.app(f, &[gb]);

        let ab = s.eq_lit(a, b);
        let fg = s.eq_lit(fga, fgb);

        s.add_clause(&[ab]);
        s.add_clause(&[fg.negated()]);

        assert_eq!(s.solve(), SolveResult::Unsat);
    }
}
