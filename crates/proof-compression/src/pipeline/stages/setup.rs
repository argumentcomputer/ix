//! Verifier construction without a proof or witness.
use super::*;
#[cfg(test)]
use multi_stark::traits::TwoAdicField;

/// The FRI stage's verifier for `circuit`, with the commitments
/// `Prepared::prove_fri` derives, built without a witness.
pub(in crate::pipeline) fn fri(
  circuit: Circuit<Val>,
  config: GoldilocksBlake3Config,
  height: usize,
) -> Result<FriVerifier> {
  use multi_stark::config::StarkGenericConfig;
  fri::validate_parameters(
    multi_stark::types::CommitmentParameters {
      log_blowup: config.log_blowup(),
      cap_height: config.cap_height(),
    },
    config.fri_parameters(),
  )?;
  let public_count = circuit.public_values().len();
  let compiled = construct::lower_fri(circuit, height)?;
  let statement = Statement::from_lowered(&compiled, public_count)?;
  let definitions = construct::fri_definitions(&compiled);
  drop(compiled);
  validate_config(&config, &definitions)?;
  let (system, _) = System::new_without_preprocessed(config, definitions);
  Ok(FriVerifier { key: VerifierKey::new(system), statement })
}

#[cfg(test)]
pub(super) fn kzg(
  circuit: Circuit<Scalar>,
  srs: Arc<Srs>,
  height: usize,
) -> Result<KzgVerifier> {
  if height < 2 || !height.is_power_of_two() || height > srs.max_len() {
    return Err(
      "partition height must be a power of two within the SRS range".into(),
    );
  }
  if height.ilog2() as usize + 1 > Scalar::TWO_ADICITY {
    return Err("quotient domain exceeds scalar field two-adicity".into());
  }
  let public_count = circuit.public_values().len();
  let compiled = construct::lower_first(circuit, height, height)?;
  let height = construct::max_height(&compiled)?;
  if height > srs.max_len() {
    return Err("compression trace exceeds the SRS range".into());
  }
  let config = KzgConfig::with_max_trace_len(srs, height, 2)
    .with_streaming_lookups()
    .with_streaming_quotient();
  kzg_lowered(compiled, config, public_count)
}

#[cfg(test)]
fn kzg_lowered(
  compiled: multi_stark::plonkish::MultiStarkCircuit<Scalar>,
  config: KzgConfig,
  public_count: usize,
) -> Result<KzgVerifier> {
  use multi_stark::config::ProofConfig;
  let statement = Statement::from_lowered(&compiled, public_count)?;
  let params = config.pcs().verifier_params().clone();
  let transcript = config.transcript_kind();
  let mut system = prover::setup(config, &compiled)?;
  drop(compiled);
  system.config =
    KzgConfig::verifier_only(params, 2).with_transcript(transcript);
  KzgVerifier::new(system, statement)
}
