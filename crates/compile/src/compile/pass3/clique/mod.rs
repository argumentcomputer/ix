//! Pass 3's clique transport (M6R slice 3): a port of
//! `Ix/Compile/Clique/**` (without the proof file `FixPerm.lean`) and of
//! `Ix/Compile/Pass/Cliques.lean`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Clique/Basic.lean` | [`basic`] |
//! | `Clique/Packing.lean`, `PackingMatch.lean` | [`packing`] |
//! | `Clique/Telescope.lean`, `Whnf.lean` | [`telescope`] |
//! | `Clique/WF.lean`, `WFSchema.lean`, `WFMatcher.lean`, `WFConjugation.lean` | [`wf`] |
//! | `Clique/Structural.lean` | [`structural`] |
//! | `Clique/PartialFixpoint.lean`, `PFConjugation.lean` | [`pf`] |
//! | `Clique/Transport.lean`, `Plan.lean` | [`transport`] |
//! | `Clique/Recover.lean` | [`recover`] |
//! | `Canon/{Order,Classes,Clique}.lean` (the clique order) | [`order`] |
//! | `Pass/Cliques.lean` | [`hook`] |

// The port mirrors the Lean modules branch by branch (the same `if` chains,
// match arms, index loops, `Except`-returning helpers and owned arguments as
// the originals), so that each function can be read against its Lean
// original; these style lints would reshape it away from them.
#![allow(
  clippy::if_same_then_else,
  clippy::match_same_arms,
  clippy::needless_range_loop,
  clippy::unnecessary_wraps,
  clippy::needless_pass_by_value,
  clippy::collapsible_match
)]

pub mod basic;
pub mod hook;
pub mod order;
pub mod packing;
pub mod pf;
pub mod recover;
pub mod structural;
pub mod telescope;
pub mod transport;
pub mod wf;
