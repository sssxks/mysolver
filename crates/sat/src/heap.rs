use crate::Var;

/// A max-heap over decision variables ordered by activity.
#[derive(Debug)]
pub(crate) struct VarHeap {
    /// Heap storage containing variable identifiers.
    heap: Vec<Var>,
    /// Heap positions indexed by variable, or `-1` when absent.
    pos: Vec<i32>,
}

impl VarHeap {
    /// Creates an empty activity heap.
    pub(crate) fn new() -> Self {
        Self {
            heap: Vec::new(),
            pos: Vec::new(),
        }
    }

    /// Reserves a position slot for a newly created variable.
    pub(crate) fn new_var(&mut self) {
        self.pos.push(-1);
    }

    /// Returns whether the heap currently contains `v`.
    pub(crate) fn contains(&self, v: Var) -> bool {
        self.pos[v.index()] >= 0
    }

    /// Inserts `v` into the heap unless it is already present.
    pub(crate) fn insert(&mut self, v: Var, activity: &[f64]) {
        if self.contains(v) {
            return;
        }
        self.pos[v.index()] = self.heap.len() as i32;
        self.heap.push(v);
        self.percolate_up(self.heap.len() - 1, activity);
    }

    /// Reorders `v` upward after its activity has increased.
    pub(crate) fn increase(&mut self, v: Var, activity: &[f64]) {
        if self.contains(v) {
            self.percolate_up(self.pos[v.index()] as usize, activity);
        }
    }

    /// Removes and returns the highest-activity variable, if any.
    pub(crate) fn pop_max(&mut self, activity: &[f64]) -> Option<Var> {
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
