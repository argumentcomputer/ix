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
//!
//! Nothing in the compile path calls these modules yet, except the
//! reserved-input refusal ([`names`]): the driver's hooks come with the
//! switch from the call-site surgery to Pass 3. The modules are public, so
//! the unit tests reach them.

pub mod expr;
pub mod names;
