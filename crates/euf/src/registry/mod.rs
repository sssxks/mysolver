//! Permanent registry storage and its private canonical object model.
//!
//! This module deliberately keeps the arena-backed canonical object types private to
//! the `registry` module. Those objects contain raw arena handles such as
//! [`crate::arena::ArenaStr`] and [`crate::arena::ArenaSlice`], so methods like
//! `matches_ref()` may safely reborrow those handles only because callers outside this
//! module cannot construct canonical objects with shorter-lived arena storage.
//!
//! Public and crate-visible code should interact with the registry through handles
//! such as [`crate::Sort`] and borrowed query views such as [`crate::SortRef`],
//! leaving ownership and arena-liveness invariants confined to this module.

mod object;
mod storage;

pub use storage::Registry;
