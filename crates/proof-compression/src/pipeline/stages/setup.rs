//! Deterministic verifier construction. No proof or witness is an input.
use super::*;
use aiur::vk_codec::AiurVerifyingKey;

/// Derive a complete fixed compression verifier from locally trusted inputs.
/// This performs circuit construction and preprocessing commitments, but no
/// proof generation. The supplied SRS must have been authenticated/validated.
pub fn setup(
  root_key: &AiurVerifyingKey,
  root: &FixedRoot,
  srs: Arc<Srs>,
  fri_config: GoldilocksBlake3Config,
  fri_height: usize,
  kzg_height: usize,
) -> Result<RecursiveVerifier> {
  let circuit = root.circuit(root_key, Default::default())?;
  let fri = fri(circuit, fri_config, fri_height)?;
  let circuit = foreign(&fri)?;
  let kzg = kzg(circuit, srs.clone(), kzg_height)?;
  wrap::setup_recursive(&kzg, srs, kzg_height)
}

pub(super) fn fri(
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
  validate_config(&config, &definitions)?;
  let (system, _) = System::new_without_preprocessed(config, definitions);
  Ok(FriVerifier { key: VerifierKey::new(system), statement })
}

pub(super) fn foreign(verifier: &FriVerifier) -> Result<Circuit<Scalar>> {
  let profile =
    construct::fri_profile(&verifier.key, &verifier.statement.template)?;
  let plan =
    fri::VerifierPlan::validate(&verifier.key, profile, Default::default())?;
  let built =
    construct::FriConstruction::build(&plan, verifier.statement.schema())?;
  Ok(construct::translate(&built.circuit).circuit)
}

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

pub(super) fn kzg_lowered(
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
