//! Tests translated from lean-kernel-arena tutorial/Tutorial.lean.
//!
//! Each test builds a small `KEnv<Meta>` and checks that the zero kernel
//! correctly accepts or rejects specific constants.
//!
//! Organized by category:
//! - `basic`: definitions, levels, lets, forall checks
//! - `inductive`: good and bad inductive types
//! - `reduction`: recursor reduction, Peano arithmetic, Bool/Nat rec
//! - `defeq`: proof irrelevance, eta, equality

mod basic;
mod defeq;
mod inductive;
mod reduction;
