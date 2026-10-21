//! Pass 3's clique transport: a port of `Ix/Compile/Pass/Clique/**`
//! (unwired library code).
//!
//! | Lean | Rust |
//! |---|---|
//! | `Clique/Basic.lean`, `Dag.lean` | [`basic`] |
//! | `Clique/Bounds.lean` | [`bounds`] |
//! | `Clique/Packing.lean`, `PackingMatch.lean` | [`packing`] |
//! | `Clique/Telescope.lean`, `Whnf.lean` | [`telescope`] |
//! | `Clique/WF.lean`, `WFSchema.lean`, `WFMatcher.lean`, `WFConjugation.lean` | [`wf`] |
//! | `Clique/Plan.lean` | [`plan`] |
//! | `Clique/Table.lean` | [`table`] |
//!
//! `Dag.lean`'s de Bruijn and locally nameless helpers are
//! [`super::expr`]'s (re-exported by [`basic`]); [`basic`] has its walks
//! over distinct subterms.

pub mod basic;
pub mod bounds;
pub mod packing;
pub mod plan;
pub mod table;
pub mod telescope;
pub mod wf;
