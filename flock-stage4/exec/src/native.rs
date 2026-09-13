use crate::replay::{
  self, STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN,
  Stage4FlockInnerLigeritoWitnessV1, Stage4FlockMatrixAccumulatorWitnessV1,
  Stage4FlockMergedPcsFrontendWitnessV1,
  Stage4FlockMultipointTwistedAssistWitnessV1, Stage4FlockTranscriptWitnessV1,
  Stage4FlockVerifierCensusV1, Stage4FlockWiringWitnessV1,
  Stage4TranscriptOpV1,
};
use anyhow::{Result, ensure};
use flock_prover::{
  aggregate,
  challenger::FsChallenger,
  field::F128,
  matrix_fold::FoldGrinding,
  pcs::jagged::JaggedParams,
  transcript_record::RecordingChallenger,
  union::{UnionInstance, publics_digest},
  verifier,
};
use ix_stage4_trace::{ExecBindingV0, ExecCommitmentsV0, ExecPublicWordV0};
use ixby_flock::ixby::{
  exec::{CompiledExec, ExecStatementDigest},
  io::PublicWord,
};

/// Complete native replay diagnostic. Its private fields are tied to one
/// approved setup, but this is neither a Stage 4 key nor terminal acceptance:
/// every exported phase topology is checked against the proof-free replay
/// compiler, but the folded roots still need constraints in the final proof.
#[derive(Clone)]
pub struct ExecReplayWitness<'a> {
  setup: &'a CompiledExec,
  topology_digest: [u8; 32],
  commitments: ExecCommitmentsV0,
  binding: ExecBindingV0,
  public_values: Vec<[u8; 16]>,
  proof_bytes: usize,
  transcript: Stage4FlockTranscriptWitnessV1,
  wiring: Stage4FlockWiringWitnessV1,
  merged_pcs: Stage4FlockMergedPcsFrontendWitnessV1,
  multipoint_assist: Stage4FlockMultipointTwistedAssistWitnessV1,
  inner_ligerito: Stage4FlockInnerLigeritoWitnessV1,
  matrix_accumulator: Stage4FlockMatrixAccumulatorWitnessV1,
}

impl ExecReplayWitness<'_> {
  pub fn topology_digest(&self) -> [u8; 32] {
    self.topology_digest
  }
  pub fn setup(&self) -> &CompiledExec {
    self.setup
  }
  pub fn commitments(&self) -> ExecCommitmentsV0 {
    self.commitments
  }
  pub fn binding(&self) -> &ExecBindingV0 {
    &self.binding
  }
  pub fn public_values(&self) -> &[[u8; 16]] {
    &self.public_values
  }
  pub fn proof_bytes(&self) -> usize {
    self.proof_bytes
  }
  pub fn public_digest(&self) -> [u8; 32] {
    self.commitments.public_digest(self.binding.profile_digest)
  }
  pub fn transcript(&self) -> &Stage4FlockTranscriptWitnessV1 {
    &self.transcript
  }
  pub fn wiring(&self) -> &Stage4FlockWiringWitnessV1 {
    &self.wiring
  }
  pub fn merged_pcs(&self) -> &Stage4FlockMergedPcsFrontendWitnessV1 {
    &self.merged_pcs
  }
  pub fn multipoint_assist(
    &self,
  ) -> &Stage4FlockMultipointTwistedAssistWitnessV1 {
    &self.multipoint_assist
  }
  pub fn inner_ligerito(&self) -> &Stage4FlockInnerLigeritoWitnessV1 {
    &self.inner_ligerito
  }
  pub fn matrix_accumulator(&self) -> &Stage4FlockMatrixAccumulatorWitnessV1 {
    &self.matrix_accumulator
  }
  pub fn census(&self) -> Stage4FlockVerifierCensusV1 {
    replay::census_components(
      self.public_values.len(),
      self.proof_bytes,
      &self.transcript,
      &self.wiring,
      &self.merged_pcs,
      &self.multipoint_assist,
      &self.inner_ligerito,
      &self.matrix_accumulator,
    )
  }
}

/// The binding part of setup needs only approved interpreter geometry and
/// public positions. No image, input, output, execution, or proof is consulted.
pub fn compile_exec_binding(setup: &CompiledExec) -> Result<ExecBindingV0> {
  let identities = setup.identities();
  let binding = ExecBindingV0 {
    profile_digest: identities.profile,
    registry_digest: identities.registry,
    circuit_digest: identities.circuit,
    counts: setup
      .verifier_shape()
      .counts
      .iter()
      .map(|&count| u64::try_from(count))
      .collect::<Result<Vec<_>, _>>()?,
    public_template: setup
      .public_template()
      .words()
      .iter()
      .map(|word| {
        Ok(match *word {
          PublicWord::Fixed(value) => {
            ExecPublicWordV0::Fixed(encode_f128(value))
          },
          PublicWord::Output(0) => ExecPublicWordV0::StatementLow,
          PublicWord::Output(1) => ExecPublicWordV0::StatementHigh,
          _ => anyhow::bail!("unsupported Exec public-output position"),
        })
      })
      .collect::<Result<Vec<_>>>()?,
  };
  binding.validate(binding.public_template.len(), 5)?;
  Ok(binding)
}

/// Strict generic entry point. It does not receive or reconstruct native
/// Stage 2 transport, guest bytes, private input bytes, or a witness trace.
/// The host verifier is a witness-generation check, not a circuit constraint.
pub fn replay_exec<'a>(
  setup: &'a CompiledExec,
  commitments: ExecCommitmentsV0,
  proof_bytes: &[u8],
) -> Result<ExecReplayWitness<'a>> {
  crate::compile_exec_replay(setup)?.replay(commitments, proof_bytes)
}

pub(crate) fn replay_compiled<'a>(
  compiled: &crate::CompiledExecReplay<'a>,
  commitments: ExecCommitmentsV0,
  proof_bytes: &[u8],
) -> Result<ExecReplayWitness<'a>> {
  let setup = compiled.setup;
  let binding = compiled.binding.clone();
  let approved_wiring = &compiled.wiring;
  let approved_boolean = &compiled.boolean;
  let approved_pcs = &compiled.pcs;
  let approved_main = &compiled.main;
  let approved_folds = &compiled.folds;
  let expected =
    ExecStatementDigest(commitments.statement_digest(binding.profile_digest));
  let verified = setup.verify_for_replay(expected, proof_bytes)?;
  let shape = setup.verifier_shape();
  let params = setup.pcs_params();
  let domain = setup.transcript_domain();
  let public = verified.public_values();
  let proof = verified.proof();
  let commitment = verified.commitment();
  ensure!(
    proof.element.is_none(),
    "Exec replay supports the approved Boolean registry only"
  );
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let linchecks = setup.lincheck_circuits();
  let mut challenger =
    RecordingChallenger::new(FsChallenger::with_chained_blake3(&domain));
  let (_, deferred, sigma) = verifier::verify_ligerito_union_circuit_deferred(
    &union,
    &shape.circuit,
    public,
    &linchecks,
    commitment,
    proof,
    params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("generic Exec deferred replay: {error:?}")
  })?;
  let fixed_public = binding
    .public_template
    .iter()
    .map(|word| match word {
      ExecPublicWordV0::Fixed(value) => Some(*value),
      _ => None,
    })
    .collect();
  let wiring = replay::export_wiring_f128_algebra(
    &challenger,
    &shape.circuit,
    public,
    &proof.wiring,
    &sigma,
    fixed_public,
  )?;
  ensure!(
    wiring.trace() == approved_wiring,
    "Exec wiring differs from proof-free blueprint"
  );
  let boolean = proof
    .boolean
    .as_ref()
    .ok_or_else(|| anyhow::anyhow!("missing Exec Boolean PIOP"))?;
  let algebra = replay::export_boolean_piop_f128_algebra(
    &challenger,
    &union,
    boolean,
    params.zerocheck_grinding(),
    params.lincheck_grinding(),
  )?;
  ensure!(
    algebra.trace == approved_boolean.trace,
    "Exec Boolean PIOP differs from proof-free blueprint"
  );
  algebra.matrix_assertion.check_reported(&shape.registry).map_err(
    |error| {
      anyhow::anyhow!("generic Exec canonical matrix assertion: {error:?}")
    },
  )?;
  let frontend = replay::export_merged_pcs_frontend(
    &challenger,
    &union,
    commitment,
    &proof.pcs_open,
    wiring.trace(),
    &algebra,
  )?;
  ensure!(
    frontend == approved_pcs.frontend,
    "Exec merged PCS differs from proof-free blueprint"
  );
  let multipoint_assist = replay::export_multipoint_twisted_assist(
    &challenger,
    binding.circuit_digest,
    &union,
    &proof.pcs_open,
    wiring.trace(),
    &algebra,
    &frontend,
    &deferred.jagged,
  )?;
  ensure!(
    *multipoint_assist.trace() == approved_pcs.multipoint,
    "Exec multipoint assist differs from proof-free blueprint"
  );
  let inner_ligerito = replay::export_inner_ligerito(
    &challenger,
    commitment,
    &proof.pcs_open,
    &frontend,
  )?;
  let merged_pcs = Stage4FlockMergedPcsFrontendWitnessV1::new(frontend);
  ensure!(
    *inner_ligerito.trace() == approved_main.inner,
    "Exec inner Ligerito differs from proof-free blueprint"
  );

  // These diagnostic folds preserve all three unresolved root families.
  // Removing the native checks here cannot turn them into a compact proof.
  let matrices = shape
    .registry
    .boolean_types()
    .iter()
    .map(|ty| (&ty.a_0, &ty.b_0))
    .collect::<Vec<_>>();
  let assertions = std::slice::from_ref(&algebra.matrix_assertion);
  let mut structure = sigma;
  // The Boolean algebra recomputes these pin helpers from approved counts.
  structure.boolean_pins.clear();
  structure.element_constants = None;
  ensure!(
    structure.claims().len() == 3,
    "Exec Product-GKR structure claim count"
  );
  let sigma_keys = [(&shape.circuit, vec![&structure])];
  let dense_variables = params
    .m
    .checked_sub(7)
    .ok_or_else(|| anyhow::anyhow!("Exec PCS dimension below 7"))?;
  let jagged_params = JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    dense_variables,
  );
  let jagged_prover_keys =
    [(binding.circuit_digest, &jagged_params, vec![&deferred.jagged])];
  let jagged_verifier_keys = [(binding.circuit_digest, vec![&deferred.jagged])];
  let grinding = FoldGrinding::per_challenge_128();
  let mut fold_prover = FsChallenger::with_chained_blake3(
    STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN,
  );
  let (aggregate_proof, accumulator) =
    aggregate::prove_aggregate_classes_with_grinding(
      &shape.registry,
      &matrices,
      &linchecks,
      assertions,
      &[],
      &[],
      &sigma_keys,
      &jagged_prover_keys,
      &[],
      grinding,
      &mut fold_prover,
    )
    .map_err(|error| {
      anyhow::anyhow!("generic Exec accumulator prover: {error:?}")
    })?;
  ensure!(
    accumulator.discharge(&matrices),
    "Exec native matrix root discharge"
  );
  ensure!(
    accumulator.discharge_jagged(&[(binding.circuit_digest, &jagged_params)]),
    "Exec native jagged root discharge"
  );
  let mut fold_verifier =
    RecordingChallenger::new(FsChallenger::with_chained_blake3(
      STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN,
    ));
  let checked_accumulator = aggregate::verify_aggregate_classes_with_grinding(
    &shape.registry,
    assertions,
    &[],
    &sigma_keys,
    &jagged_verifier_keys,
    &[],
    &aggregate_proof,
    grinding,
    &mut fold_verifier,
  )
  .map_err(|error| {
    anyhow::anyhow!("generic Exec accumulator verifier: {error:?}")
  })?;
  ensure!(accumulator == checked_accumulator, "Exec accumulator differential");
  let matrix_accumulator = replay::export_stage4_matrix_accumulator(
    &fold_verifier,
    STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN,
    &shape.registry,
    &shape.circuit,
    &algebra.matrix_assertion,
    &structure,
    &deferred.jagged,
    &aggregate_proof,
    &accumulator,
    &algebra.trace.deferred_matrix_claims,
  )?;
  ensure!(
    matrix_accumulator.circuit_structure_root_claim().check(&shape.circuit),
    "Exec native structure root discharge"
  );
  ensure!(
    matrix_accumulator.jagged_root_claim().check(&jagged_params),
    "Exec native jagged terminal differential"
  );
  ensure!(
    *matrix_accumulator.trace() == approved_folds.matrices
      && *matrix_accumulator.circuit_structure_trace()
        == approved_folds.structure
      && *matrix_accumulator.jagged_trace() == approved_folds.jagged
      && matrix_accumulator.operations() == approved_folds.operations
      && matrix_accumulator.observed_values().len() as u64
        == approved_folds.observed_values
      && matrix_accumulator.challenges().len() as u64
        == approved_folds.challenges
      && matrix_accumulator
        .byte_payloads()
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>()
        == approved_folds.payload_lengths,
    "Exec leaf accumulator differs from proof-free blueprint"
  );
  ensure!(
    approved_folds.hash.matches(matrix_accumulator.chained_blake3()),
    "Exec accumulator hash topology differs from proof-free blueprint"
  );
  let transcript = Stage4FlockTranscriptWitnessV1::from_recording_with_algebra(
    &challenger,
    &domain,
    algebra.trace,
    &algebra.private_values,
  )?;
  check_prefix(&binding, &transcript, public)?;
  ensure!(
    transcript.operations() == approved_main.operations
      && transcript.observed_values().len() as u64
        == approved_main.observed_values
      && transcript.challenges().len() as u64 == approved_main.challenges
      && transcript.byte_payloads().iter().map(Vec::len).collect::<Vec<_>>()
        == approved_main.payload_lengths,
    "Exec main transcript differs from proof-free blueprint"
  );
  ensure!(
    approved_main.hash.matches(transcript.chained_blake3()),
    "Exec main hash topology differs from proof-free blueprint"
  );
  replay::validate_components(
    public.len(),
    binding.circuit_digest,
    &transcript,
    &wiring,
    &merged_pcs,
    &multipoint_assist,
    &inner_ligerito,
    &matrix_accumulator,
  )?;
  Ok(ExecReplayWitness {
    setup,
    topology_digest: compiled.identities().digest(),
    commitments,
    binding,
    public_values: public.iter().copied().map(encode_f128).collect(),
    proof_bytes: proof_bytes.len(),
    transcript,
    wiring,
    merged_pcs,
    multipoint_assist,
    inner_ligerito,
    matrix_accumulator,
  })
}

fn check_prefix(
  binding: &ExecBindingV0,
  tape: &Stage4FlockTranscriptWitnessV1,
  public: &[F128],
) -> Result<()> {
  binding.validate(public.len(), tape.byte_payloads().len())?;
  let counts = binding
    .counts
    .iter()
    .flat_map(|count| count.to_le_bytes())
    .collect::<Vec<_>>();
  let expected_prefix = [
    Stage4TranscriptOpV1::Label(b"flock-mixed-v1".to_vec()),
    Stage4TranscriptOpV1::ObserveBytes(32),
    Stage4TranscriptOpV1::ObserveBytes(u64::try_from(counts.len())?),
    Stage4TranscriptOpV1::ObserveBytes(u64::try_from(
      tape.byte_payloads()[2].len(),
    )?),
    Stage4TranscriptOpV1::Label(b"flock-circuit-stmt-v2".to_vec()),
    Stage4TranscriptOpV1::ObserveBytes(32),
    Stage4TranscriptOpV1::ObserveBytes(32),
  ];
  ensure!(
    tape.operations().starts_with(&expected_prefix),
    "Exec Flock statement prefix order"
  );
  let expected_public = publics_digest(public);
  for (index, expected) in [
    (0, binding.registry_digest.as_slice()),
    (1, counts.as_slice()),
    (3, binding.circuit_digest.as_slice()),
    (4, expected_public.as_slice()),
  ] {
    ensure!(
      tape.byte_payloads()[index] == expected,
      "Exec statement-prefix payload {index}"
    );
  }
  Ok(())
}

fn encode_f128(value: F128) -> [u8; 16] {
  let mut bytes = [0; 16];
  bytes[..8].copy_from_slice(&value.lo.to_le_bytes());
  bytes[8..].copy_from_slice(&value.hi.to_le_bytes());
  bytes
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
