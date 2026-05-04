/// Deterministic work budget counted in abstract solver steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fuel {
    /// Remaining checkpoint count before the next checkpoint interrupts the run.
    remaining: u64,
}

impl Fuel {
    /// Creates a budget that allows exactly `remaining` successful checkpoints.
    pub fn new(remaining: u64) -> Self {
        Self { remaining }
    }

    /// Returns the number of checkpoints still available.
    pub fn remaining(self) -> u64 {
        self.remaining
    }

    fn checkpoint(&mut self) -> bool {
        if self.remaining == 0 {
            return false;
        }
        self.remaining -= 1;
        true
    }
}
