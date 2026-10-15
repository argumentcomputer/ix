//! Compression stages for aggregated Ix certificates.
//!
//! The caller supplies the trusted aggregate key, expected outer claim and
//! proving parameters. No certificate, filesystem layout or development SRS
//! is built into these stages. Verifiers returned by local construction must
//! be authenticated before use elsewhere; a prover-supplied key is not trusted.
mod codec;
pub(in crate::pipeline) mod construct;
pub(in crate::pipeline) mod statement;
use statement::Statement;
mod fixed;
pub(in crate::pipeline) mod root;
mod setup;
#[cfg(test)]
mod tests;
pub(in crate::pipeline) mod verification;
mod wrap;
pub use verification::RecursiveVerifier;

pub use fixed::FixedRoot;
pub use root::prepare_root;
pub use setup::setup;
pub use wrap::{RecursiveProof, RecursiveStage, prepare_recursive};

use crate::fri::{self, VerifierKey};
use crate::kzg::{KzgConfig, Scalar, Srs, VerifierParams};
use multi_stark::plonkish::{Assignment, Circuit};
use multi_stark::prover::Proof;
use multi_stark::system::{System, SystemWitness};
#[cfg(test)]
use multi_stark::traits::Algebra;
use multi_stark::traits::Field;
use multi_stark::types::{GoldilocksBlake3Config, Val};
use p3_field::PrimeField64;
use std::sync::Arc;

use super::{
  Result,
  prover::{self, validate_config},
};

/// A checked circuit and its witness, ready for lowering and proving.
/// Keeping preparation separate lets callers inspect costs and choose an SRS
/// and partition height before allocating prover data.
pub struct Prepared<F: Field> {
  pub(in crate::pipeline) circuit: Circuit<F>,
  pub(in crate::pipeline) assignment: Assignment<F>,
}

impl<F: Field> Prepared<F> {
  pub fn circuit(&self) -> &Circuit<F> {
    &self.circuit
  }

  pub fn public_values(&self) -> &[F] {
    self.assignment.public_values()
  }
}

/// Trusted verifier for the first, FRI-compressed stage.
pub struct FriVerifier {
  pub(in crate::pipeline) key: VerifierKey,
  pub(in crate::pipeline) statement: Statement<Val>,
}

impl FriVerifier {
  pub fn verify(
    &self,
    proof: &Proof<GoldilocksBlake3Config>,
    expected: &[Val],
  ) -> Result<()> {
    let claims = self.statement.claims(expected)?;
    self
      .key
      .system()
      .verify_multiple_claims(
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        proof,
      )
      .map_err(|e| format!("FRI compression proof: {e:?}"))?;
    Ok(())
  }
}

impl Prepared<Val> {
  /// Prove the root-verifier circuit using caller-selected FRI parameters.
  pub fn prove_fri(
    self,
    config: GoldilocksBlake3Config,
    max_height: usize,
  ) -> Result<(FriVerifier, Proof<GoldilocksBlake3Config>)> {
    use multi_stark::config::StarkGenericConfig;
    fri::validate_parameters(
      multi_stark::types::CommitmentParameters {
        log_blowup: config.log_blowup(),
        cap_height: config.cap_height(),
      },
      config.fri_parameters(),
    )?;
    let compiled = construct::lower_fri(self.circuit, max_height)?;
    let statement = Statement::from_lowered(
      &compiled,
      self.assignment.public_values().len(),
    )?;
    let claims = statement.claims(self.assignment.public_values())?;
    let trace_span = tracing::info_span!("compression/trace").entered();
    let definitions = construct::fri_definitions(&compiled);
    validate_config(&config, &definitions)?;
    let traces = compiled.traces(&self.assignment)?;
    drop(trace_span);
    drop(compiled);
    drop(self.assignment);
    let (system, key) = tracing::info_span!("compression/setup")
      .in_scope(|| System::new(config, definitions));
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = tracing::info_span!("compression/prove").in_scope(|| {
      system.prove_multiple_claims(
        &key,
        &refs,
        SystemWitness::from_stage_1(traces, &system),
      )
    });
    tracing::info_span!("compression/verify")
      .in_scope(|| system.verify_multiple_claims(&refs, &proof))
      .map_err(|e| format!("new FRI proof: {e:?}"))?;
    Ok((FriVerifier { key: VerifierKey::new(system), statement }, proof))
  }
}

/// Prepare a FRI verifier over the BLS12-381 scalar field. The statement and
/// all activation anchors come from the trusted previous stage's verifier.
pub fn prepare_kzg(
  verifier: &FriVerifier,
  proof: &Proof<GoldilocksBlake3Config>,
  expected: &[Val],
  limits: fri::VerifierLimits,
) -> Result<Prepared<Scalar>> {
  verifier.verify(proof, expected)?;
  let claims = verifier.statement.claims(expected)?;
  let profile = construct::fri_profile(&verifier.key, &claims)?;
  if proof.active != profile.active || proof.log_degrees != profile.log_degrees
  {
    return Err("compressed proof profile differs from the key".into());
  }
  let plan = fri::VerifierPlan::validate(&verifier.key, profile, limits)?;
  let source =
    construct::FriConstruction::build(&plan, verifier.statement.schema())?
      .assign(&plan, proof, claims)?;
  let foreign = construct::translate(&source.circuit);
  drop(source.circuit);
  let assignment = construct::assign_foreign(
    &foreign.inputs,
    &foreign.circuit,
    &source.assignment,
  )?;
  Ok(Prepared { circuit: foreign.circuit, assignment })
}

/// Trusted verifier for a scalar-field compression stage. It retains only
/// verification parameters, never the SRS proving powers or fixed matrices.
pub struct KzgVerifier {
  system: System<KzgConfig>,
  params: VerifierParams,
  statement: Statement<Scalar>,
  codec: crate::kzg::compact::FixedProofCodec,
}

impl KzgVerifier {
  pub(in crate::pipeline) fn new(
    system: System<KzgConfig>,
    statement: Statement<Scalar>,
  ) -> Result<Self> {
    use multi_stark::config::ProofConfig;
    let params = system.config.pcs().verifier_params().clone();
    statement.validate()?;
    let commitment =
      system.preprocessed_commit.as_ref().ok_or("missing fixed commitment")?;
    if system.circuits.is_empty()
      || commitment.0.len() != system.circuits.len()
      || system
        .preprocessed_indices
        .iter()
        .copied()
        .ne((0..system.circuits.len()).map(Some))
    {
      return Err("invalid fixed commitment dimensions".into());
    }
    for (i, c) in system.circuits.iter().enumerate() {
      crate::circuit_metadata::validate_circuit(c, 1)?;
      if c.preprocessed.is_some()
        || c.preprocessed_width == 0
        || !c.preprocessed_height.is_power_of_two()
        || c.preprocessed_height > params.max_trace_len()
        || c.quotient_degree() > 2
        || commitment.0[i].len() != c.preprocessed_width
      {
        return Err("invalid KZG compression circuit metadata".into());
      }
    }
    let logs = system
      .circuits
      .iter()
      .map(|c| u8::try_from(c.preprocessed_height.ilog2()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let codec = crate::kzg::compact::FixedProofCodec::new(&system, &logs)?;
    Ok(Self { system, params, statement, codec })
  }

  /// Fixed-shape transport under this trusted key; encoding is not verification.
  pub fn encode_proof(&self, proof: &Proof<KzgConfig>) -> Result<Vec<u8>> {
    Ok(self.codec.encode(proof)?)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Scalar]) -> Result<()> {
    self.verify(&self.codec.decode(bytes)?, expected)
  }

  pub fn verify(
    &self,
    proof: &Proof<KzgConfig>,
    expected: &[Scalar],
  ) -> Result<()> {
    let claims = self.statement.claims(expected)?;
    self
      .system
      .verify_multiple_claims(
        &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        proof,
      )
      .map_err(|e| format!("KZG compression proof: {e:?}"))?;
    Ok(())
  }
}

impl Prepared<Scalar> {
  /// Parameters must have trusted provenance and pass Srs::validate before
  /// use. Partitioning is bounded by both max_height and the supplied SRS.
  pub fn prove_kzg(
    self,
    srs: Arc<Srs>,
    max_height: usize,
  ) -> Result<(KzgVerifier, Proof<KzgConfig>)> {
    if srs.max_len() < 2
      || !srs.max_len().is_power_of_two()
      || srs.public_setup.max_degree < srs.max_len() - 1
      || srs.public_setup.max_degree.checked_add(1).is_none()
    {
      return Err("invalid SRS shape".into());
    }
    if max_height < 2
      || !max_height.is_power_of_two()
      || max_height > srs.max_len()
    {
      return Err(
        "partition height must be a power of two within the SRS range".into(),
      );
    }
    let compiled =
      construct::lower_first(self.circuit, max_height, max_height)?;
    let height = construct::max_height(&compiled)?;
    if height > srs.max_len() {
      return Err("compression trace exceeds the SRS range".into());
    }
    let config = KzgConfig::with_max_trace_len(srs, height, 2)
      .with_streaming_lookups()
      .with_streaming_quotient();
    prove_lowered(
      construct::Lowered { compiled, assignment: self.assignment },
      config,
    )
  }
}

pub(in crate::pipeline) fn scalar_statement(expected: &[Val]) -> Vec<Scalar> {
  expected.iter().map(|v| Scalar::from_u64(v.as_canonical_u64())).collect()
}

fn prove_lowered(
  lowered: construct::Lowered,
  config: KzgConfig,
) -> Result<(KzgVerifier, Proof<KzgConfig>)> {
  use multi_stark::config::ProofConfig;
  let statement = Statement::from_lowered(
    &lowered.compiled,
    lowered.assignment.public_values().len(),
  )?;
  let claims = statement.claims(lowered.assignment.public_values())?;
  let params = config.pcs().verifier_params().clone();
  let transcript = config.transcript_kind();
  let committed = lowered.commit(config, None, 0)?;
  let prover::Proved { mut system, proof, .. } = committed.prove(&claims)?;
  system.config =
    KzgConfig::verifier_only(params, 2).with_transcript(transcript);
  Ok((KzgVerifier::new(system, statement)?, proof))
}
