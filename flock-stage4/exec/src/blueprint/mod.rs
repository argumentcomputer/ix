//! Proof-free verifier topology compilation. Each phase is reconstructed from
//! approved interpreter/protocol geometry, then compared with native replay.
//! These blueprints fix the complete root-conditional replay. Key generation
//! and terminal root closure are separate obligations, not implied by them.

mod algebra;
mod boolean;
mod folds;
mod hash;
mod inner;
mod pcs;
mod tape;
mod transcript;
mod wiring;

pub(crate) use boolean::{BooleanBlueprint, compile_boolean};
pub(crate) use folds::{FoldBlueprint, compile_folds};
pub(crate) use pcs::{PcsBlueprint, compile_pcs};
pub(crate) use transcript::{MainBlueprint, compile_transcript};
pub(crate) use wiring::compile_wiring;

use flock_prover::{circuit::builder::CircuitShape, pcs::PcsParams};
use ixby_flock::ixby::{
  exec::CompiledExec, io::PublicLayout,
  ixbf_decode::stream::batch::CompiledGrammarBatch,
};

/// Only approved, immutable setup owners implement this private interface.
/// Generalizing the topology compiler does not admit proof-supplied shapes.
pub(crate) trait VerifierSetup {
  fn verifier_shape(&self) -> &CircuitShape;
  fn pcs_params(&self) -> &PcsParams;
  fn public_template(&self) -> &PublicLayout;
  fn transcript_domain(&self) -> Vec<u8>;
  fn registry_digest(&self) -> [u8; 32];
  fn circuit_digest(&self) -> [u8; 32];
}

impl VerifierSetup for CompiledExec {
  fn verifier_shape(&self) -> &CircuitShape {
    self.verifier_shape()
  }
  fn pcs_params(&self) -> &PcsParams {
    self.pcs_params()
  }
  fn public_template(&self) -> &PublicLayout {
    self.public_template()
  }
  fn transcript_domain(&self) -> Vec<u8> {
    self.transcript_domain()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.identities().registry
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.identities().circuit
  }
}

impl VerifierSetup for CompiledGrammarBatch {
  fn verifier_shape(&self) -> &CircuitShape {
    self.verifier_shape()
  }
  fn pcs_params(&self) -> &PcsParams {
    self.pcs_params()
  }
  fn public_template(&self) -> &PublicLayout {
    self.public_template()
  }
  fn transcript_domain(&self) -> Vec<u8> {
    self.transcript_domain().to_vec()
  }
  fn registry_digest(&self) -> [u8; 32] {
    self.verifier_shape().registry.digest()
  }
  fn circuit_digest(&self) -> [u8; 32] {
    self.verifier_shape().circuit.digest()
  }
}
