//! Native GF(2^128) constraints for recursive verification of Flock proofs.
//! Setup fixes the verifier graph before any child statement or proof is read.
//! Deferred claims remain explicit until a root verifier discharges them.

mod algebra;
mod backend;
mod blake3;
mod f128;
mod fold;
mod gates;
mod ligerito;
mod merged_pcs;
mod multipoint;
mod pair;
mod proof;
mod transcript;
mod tree;
mod wiring;

pub use pair::{GrammarPairRelation, NativePairCensus};
pub use proof::{CompiledGrammarPair, GrammarPairGeometry};
pub use tree::{
  CompiledGrammarNode, GrammarNodeGeometry, GrammarRootVerifier,
  GrammarTreeCompiler, MAX_GRAMMAR_TREE_BYTES, MAX_GRAMMAR_TREE_LEAVES,
};

use algebra::*;
use backend::{
  BitRef as Variable, BitRef as LinearCombination, NativeBuilder as R1csBuilder,
};
use f128::*;
use ligerito::*;
use merged_pcs::*;
use multipoint::*;
use transcript::*;
use wiring::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConstraintPhase {
  Statement,
  Transcript,
  Zerocheck,
  Lincheck,
  Wiring,
  Pcs,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum R1csError {
  InternalShape,
}
impl std::fmt::Display for R1csError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "invalid native Flock constraint shape")
  }
}
impl std::error::Error for R1csError {}
