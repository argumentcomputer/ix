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
//! | `Clique/Structural.lean` | [`structural`] |
//! | `Clique/StructuralEq.lean` | [`structural_eq`] |
//! | `Clique/PartialFixpoint.lean`, `PFConjugation.lean` | [`pf`] |
//! | `Clique/Plan.lean` | [`plan`] |
//! | `Clique/Table.lean` | [`table`] |
//! | `Clique/Order.lean`; `Canon/Order.lean`, `Classes.lean`, `Clique.lean` (definitions) | [`order`] |
//! | `Clique/Transport.lean` | [`transport`] |
//! | `Clique/Recover.lean` | [`recover`] |
//! | `Clique/PlanClique.lean` | [`plan_clique`] |
//! | `Clique/Hook.lean` | [`hook`] |
//!
//! `Dag.lean`'s de Bruijn and locally nameless helpers are
//! [`super::expr`]'s (re-exported by [`basic`]); [`basic`] has its walks
//! over distinct subterms.

pub mod basic;
pub mod bounds;
pub mod hook;
pub mod order;
pub mod packing;
pub mod pf;
pub mod plan;
pub mod plan_clique;
pub mod recover;
pub mod structural;
pub mod structural_eq;
pub mod table;
pub mod telescope;
pub mod transport;
pub mod wf;
