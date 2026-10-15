//! Deterministic verifier construction. No proof or witness is an input.
use super::*;
use crate::kzg::KzgCommitment;
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
  let compiled =
    circuit.lower_to_multi_stark_with_max_height(Val::ONE, height)?;
  let statement = Statement::from_lowered(&compiled, public_count)?;
  let definitions = compiled.circuit_inputs();
  validate_config(&config, &definitions)?;
  let (system, _) = System::new_without_preprocessed(config, definitions);
  Ok(FriVerifier { key: VerifierKey::new(system), statement })
}

pub(super) fn foreign(verifier: &FriVerifier) -> Result<Circuit<Scalar>> {
  let system = verifier.key.system();
  let profile = fri::ProofProfile {
    envelope: fri::Envelope::Ordinary,
    active: vec![true; system.circuits.len()],
    log_degrees: system
      .circuits
      .iter()
      .map(|c| {
        u8::try_from(c.preprocessed_height.ilog2()).expect("usize log fits u8")
      })
      .collect(),
    claim_lengths: verifier.statement.template.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: fri::DEFAULT_FIELD_RETRIES,
  };
  let plan =
    fri::VerifierPlan::validate(&verifier.key, profile, Default::default())?;
  let (circuit, _) = plan.build(verifier.schema(), Default::default())?;
  Ok(GoldilocksCircuit::new_preallocated(&circuit).circuit)
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
  let compiled = circuit
    .lower_to_multi_stark_sharded(Scalar::ONE, height)?
    .merge_table_traces(height)?;
  let statement = Statement::from_lowered(&compiled, public_count)?;
  let params = VerifierParams::from_srs(&srs);
  let config =
    KzgConfig::new(srs, 2).with_streaming_lookups().with_streaming_quotient();
  let count = compiled.num_circuits();
  let mut circuits = Vec::with_capacity(count);
  let mut fixed = KzgCommitment(vec![]);
  for i in 0..count {
    let definition = compiled
      .kzg_circuit_input(i, params.max_trace_len(), 2)?
      .ok_or("missing compression circuit")?;
    validate_config(&config, std::slice::from_ref(&definition))?;
    let (mut local, _) =
      System::new_without_preprocessed(config.clone(), [definition]);
    let commit =
      local.preprocessed_commit.take().ok_or("missing fixed commitment")?;
    fixed.0.extend(commit.0);
    circuits.push(local.circuits.remove(0));
  }
  Ok(KzgVerifier {
    system: System {
      config: KzgConfig::verifier_only(params.clone(), 2),
      circuits,
      preprocessed_commit: Some(fixed),
      preprocessed_indices: (0..count).map(Some).collect(),
    },
    params,
    statement,
  })
}
