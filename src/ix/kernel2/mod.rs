//! Kernel2: NbE type checker using Krivine machine semantics.
//!
//! This module implements a Normalization-by-Evaluation (NbE) kernel
//! with call-by-need thunks for O(1) beta reduction, replacing
//! the substitution-based approach in `kernel`.

pub mod check;
pub mod convert;
pub mod def_eq;
pub mod equiv;
pub mod error;
pub mod eval;
pub mod helpers;
pub mod infer;
pub mod level;
pub mod primitive;
pub mod quote;
pub mod tc;
pub mod types;
pub mod value;
pub mod whnf;

#[cfg(test)]
mod tests;
