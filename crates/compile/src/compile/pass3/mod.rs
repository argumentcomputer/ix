//! Pass 3, the faithful rewrite, in the Rust compiler: its core, unwired.
//! The reference is the Lean compiler's `Ix.Compile.Image` (the image
//! generator) and `Ix.Compile.Pass`.
//!
//! Module map (Lean to Rust):
//!
//! | Lean | Rust |
//! |---|---|
//! | `Pass/Names.lean` | [`names`] |
//! | `Canon/Expr.lean`, `Image/Expr.lean` | [`expr`] |
//! | `Image/Develop.lean` | [`develop`] |
//! | `Image/Spec.lean` | [`spec`] |
//! | `Image/Build.lean` | [`build`] |
//! | `Pass/ImageView.lean` | [`view`] |
//! | `Pass/Translate.lean` | [`translate`] |
//! | `Pass/SideCar.lean` | [`sidecar`] |
//!
//! Nothing in the compile path calls these modules yet, except the
//! reserved-input refusal ([`names`]): the driver's hooks, which record the
//! changed blocks' components and rewrite the blocks that reference an image
//! head, come with the switch from the call-site surgery to Pass 3. The
//! modules are public, so the unit tests reach them. The optimisation passes
//! are not here.

pub mod build;
pub mod develop;
pub mod expr;
pub mod names;
pub mod sidecar;
pub mod spec;
pub mod translate;
pub mod view;
