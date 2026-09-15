//! Proof-free parser-batch verifier topology for native recursive composition.
//! This reuses the existing verifier algebra/transcript compiler without an
//! Exec commitment adapter. It is not an outer proof or a root certificate.
use crate::{
  blueprint::{self, BooleanBlueprint, MainBlueprint, PcsBlueprint},
  replay::{
    self, Stage4FlockInnerLigeritoWitnessV1,
    Stage4FlockMergedPcsFrontendWitnessV1,
    Stage4FlockMultipointTwistedAssistWitnessV1,
    Stage4FlockTranscriptWitnessV1, Stage4FlockWiringWitnessV1,
  },
};
use anyhow::{Result, ensure};
use flock_prover::{
  challenger::FsChallenger,
  circuit::SigmaAssertion,
  field::F128,
  lincheck::MatrixAssertion,
  matrix_fold::JaggedAssertion,
  transcript_record::RecordingChallenger,
  union::{UnionInstance, publics_digest},
  verifier,
};
use ix_stage4_trace::{
  ChainedBlake3TranscriptV1, F128AlgebraTraceV1, F128InnerLigeritoTraceV1,
  F128MergedPcsFrontendTraceV1, F128MultipointTwistedAssistTraceV1,
  F128WiringTraceV1,
};
use ixby_flock::ixby::{
  io::PublicWord,
  ixbf_decode::stream::batch::{CompiledGrammarBatch, GrammarBatchStatement},
};

/// Immutable topology borrowed from the exact fixed parser-batch setup. The
/// compiler never sees a source file, endpoint, proof or witness value.
pub struct CompiledGrammarBatchReplay<'a> {
  setup: &'a CompiledGrammarBatch,
  wiring: F128WiringTraceV1,
  boolean: BooleanBlueprint,
  pcs: PcsBlueprint,
  main: MainBlueprint,
  identity: [u8; 32],
}

pub fn compile_grammar_batch_replay(
  setup: &CompiledGrammarBatch,
) -> Result<CompiledGrammarBatchReplay<'_>> {
  let wiring = blueprint::compile_wiring(setup)?;
  let boolean = blueprint::compile_boolean(setup)?;
  let pcs = blueprint::compile_pcs(setup, &wiring, &boolean)?;
  let main = blueprint::compile_transcript(setup, &boolean, &pcs)?;
  let mut hash = blake3::Hasher::new();
  hash.update(b"IxBy/grammar-batch-replay/v0\0");
  hash.update(setup.transcript_domain());
  for digest in [
    setup.verifier_shape().registry.digest(),
    setup.verifier_shape().circuit.digest(),
    setup.public_template().digest(),
    wiring.topology_digest(),
    boolean.trace.topology_digest(),
    pcs.frontend.topology_digest(),
    pcs.multipoint.topology_digest(),
    main.inner.topology_digest(),
    main.hash.topology_digest(),
  ] {
    hash.update(&digest);
  }
  let identity = *hash.finalize().as_bytes();
  Ok(CompiledGrammarBatchReplay { setup, wiring, boolean, pcs, main, identity })
}

impl CompiledGrammarBatchReplay<'_> {
  pub fn setup(&self) -> &CompiledGrammarBatch {
    self.setup
  }
  pub fn identity(&self) -> [u8; 32] {
    self.identity
  }
  pub fn wiring(&self) -> &F128WiringTraceV1 {
    &self.wiring
  }
  pub fn boolean(&self) -> &F128AlgebraTraceV1 {
    &self.boolean.trace
  }
  pub fn merged_pcs(&self) -> &F128MergedPcsFrontendTraceV1 {
    &self.pcs.frontend
  }
  pub fn multipoint(&self) -> &F128MultipointTwistedAssistTraceV1 {
    &self.pcs.multipoint
  }
  pub fn inner(&self) -> &F128InnerLigeritoTraceV1 {
    &self.main.inner
  }
  pub fn transcript(&self) -> &ChainedBlake3TranscriptV1 {
    self.main.hash.setup_topology()
  }
  pub fn payload_lengths(&self) -> &[usize] {
    &self.main.payload_lengths
  }
  pub fn observed_values(&self) -> usize {
    usize::try_from(self.main.observed_values)
      .expect("compiled observation count fits usize")
  }
  pub fn challenges(&self) -> usize {
    usize::try_from(self.main.challenges)
      .expect("compiled challenge count fits usize")
  }

  /// Native verification and exact topology comparison are witness-generation
  /// checks. A parent must constrain all exported phases and every root claim.
  pub fn replay(
    &self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<GrammarBatchReplayWitness> {
    let verified = self.setup.verify_for_replay(expected, bytes)?;
    let shape = self.setup.verifier_shape();
    let params = self.setup.pcs_params();
    let domain = self.setup.transcript_domain();
    let public = verified.public_values();
    let proof = verified.proof();
    let commitment = verified.commitment();
    ensure!(
      proof.element.is_none(),
      "parser replay requires its Boolean class"
    );
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    let mut recording =
      RecordingChallenger::new(FsChallenger::with_chained_blake3(domain));
    let (_, deferred, sigma) =
      verifier::verify_ligerito_union_circuit_deferred(
        &union,
        &shape.circuit,
        public,
        &self.setup.lincheck_circuits(),
        commitment,
        proof,
        params,
        &mut recording,
      )
      .map_err(|e| anyhow::anyhow!("parser deferred replay: {e:?}"))?;
    let fixed_public = self
      .setup
      .public_template()
      .words()
      .iter()
      .map(|word| match word {
        PublicWord::Fixed(value) => Some(encode(*value)),
        PublicWord::Output(_) => None,
      })
      .collect();
    let wiring = replay::export_wiring_f128_algebra(
      &recording,
      &shape.circuit,
      public,
      &proof.wiring,
      &sigma,
      fixed_public,
    )?;
    ensure!(wiring.trace() == &self.wiring, "parser wiring topology");
    let boolean = proof
      .boolean
      .as_ref()
      .ok_or_else(|| anyhow::anyhow!("parser Boolean proof missing"))?;
    let algebra = replay::export_boolean_piop_f128_algebra(
      &recording,
      &union,
      boolean,
      params.zerocheck_grinding(),
      params.lincheck_grinding(),
    )?;
    ensure!(algebra.trace == self.boolean.trace, "parser Boolean topology");
    let frontend = replay::export_merged_pcs_frontend(
      &recording,
      &union,
      commitment,
      &proof.pcs_open,
      wiring.trace(),
      &algebra,
    )?;
    ensure!(frontend == self.pcs.frontend, "parser merged PCS topology");
    let multipoint = replay::export_multipoint_twisted_assist(
      &recording,
      shape.circuit.digest(),
      &union,
      &proof.pcs_open,
      wiring.trace(),
      &algebra,
      &frontend,
      &deferred.jagged,
    )?;
    ensure!(
      multipoint.trace() == &self.pcs.multipoint,
      "parser multipoint topology"
    );
    let inner = replay::export_inner_ligerito(
      &recording,
      commitment,
      &proof.pcs_open,
      &frontend,
    )?;
    ensure!(inner.trace() == &self.main.inner, "parser Ligerito topology");
    let transcript =
      Stage4FlockTranscriptWitnessV1::from_recording_with_algebra(
        &recording,
        domain,
        algebra.trace,
        &algebra.private_values,
      )?;
    ensure!(
      transcript.operations() == self.main.operations
        && transcript.observed_values().len() == self.observed_values()
        && transcript.challenges().len() == self.challenges()
        && transcript.byte_payloads().iter().map(Vec::len).collect::<Vec<_>>()
          == self.main.payload_lengths
        && self.main.hash.matches(transcript.chained_blake3()),
      "parser transcript topology"
    );
    let payloads = transcript.byte_payloads();
    let counts = shape
      .counts
      .iter()
      .flat_map(|&n| (n as u64).to_le_bytes())
      .collect::<Vec<_>>();
    ensure!(
      payloads[0] == shape.registry.digest()
        && payloads[1] == counts
        && payloads[3] == shape.circuit.digest()
        && payloads[4] == publics_digest(public),
      "parser transcript statement prefix"
    );
    Ok(GrammarBatchReplayWitness {
      identity: self.identity,
      public: public.iter().copied().map(encode).collect(),
      transcript,
      wiring,
      merged_pcs: Stage4FlockMergedPcsFrontendWitnessV1::new(frontend),
      multipoint,
      inner,
      matrices: algebra.matrix_assertion,
      structure: sigma,
      jagged: deferred.jagged,
    })
  }
}

/// Owned untrusted advice. Root assertions remain explicit and must either
/// be checked by a root verifier or constrained into a recursive accumulator.
pub struct GrammarBatchReplayWitness {
  identity: [u8; 32],
  public: Vec<[u8; 16]>,
  transcript: Stage4FlockTranscriptWitnessV1,
  wiring: Stage4FlockWiringWitnessV1,
  merged_pcs: Stage4FlockMergedPcsFrontendWitnessV1,
  multipoint: Stage4FlockMultipointTwistedAssistWitnessV1,
  inner: Stage4FlockInnerLigeritoWitnessV1,
  matrices: MatrixAssertion,
  structure: SigmaAssertion,
  jagged: JaggedAssertion,
}
impl GrammarBatchReplayWitness {
  pub fn identity(&self) -> [u8; 32] {
    self.identity
  }
  pub fn public_values(&self) -> &[[u8; 16]] {
    &self.public
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
  pub fn multipoint(&self) -> &Stage4FlockMultipointTwistedAssistWitnessV1 {
    &self.multipoint
  }
  pub fn inner(&self) -> &Stage4FlockInnerLigeritoWitnessV1 {
    &self.inner
  }
  pub fn matrices(&self) -> &MatrixAssertion {
    &self.matrices
  }
  pub fn structure(&self) -> &SigmaAssertion {
    &self.structure
  }
  pub fn jagged(&self) -> &JaggedAssertion {
    &self.jagged
  }
}

fn encode(value: F128) -> [u8; 16] {
  let mut bytes = [0; 16];
  bytes[..8].copy_from_slice(&value.lo.to_le_bytes());
  bytes[8..].copy_from_slice(&value.hi.to_le_bytes());
  bytes
}

#[cfg(test)]
mod tests {
  use super::*;
  use ixby_flock::ixby::ixbf_decode::GrammarKind;

  #[test]
  #[ignore = "requires two retained CSLib parser frames in IXBY_CSLIB_FRAME_DIR"]
  fn retained_cslib_pair_replay_has_proof_free_topology() {
    let setup = CompiledGrammarBatch::compile(GrammarKind::Program).unwrap();
    let replay = compile_grammar_batch_replay(&setup).unwrap();
    eprintln!(
      "parser replay: identity={} boolean={:?} wiring={:?} frontend={:?} multipoint={:?} inner={:?} transcript={:?}",
      blake3::Hash::from(replay.identity()),
      replay.boolean().census(),
      replay.wiring().census(),
      replay.merged_pcs().census(),
      replay.multipoint().census(),
      replay.inner().census(),
      replay.transcript().census(),
    );
    // Setup above has no access to the files, endpoints, or proof bytes.
    let directory = std::path::PathBuf::from(
      std::env::var_os("IXBY_CSLIB_FRAME_DIR").expect("IXBY_CSLIB_FRAME_DIR"),
    );
    let root = blake3::Hash::from_hex(
      "96ed4322c7e4db289b876848e885d02afd2958f829135d5108b565ce9d493c05",
    )
    .unwrap();
    let length = 1_016_587;
    let mut initial = [F128::ZERO; 30];
    initial[0] = F128::new(0, length);
    for index in 0..2 {
      let frame =
        std::fs::read(directory.join(format!("program-{index:06}.frame")))
          .unwrap();
      let size = u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize;
      assert_eq!(frame.len(), 4 + 30 * 16 + size);
      let end = std::array::from_fn(|i| {
        ixby_flock::hash::pack_bytes(&frame[4 + 16 * i..4 + 16 * (i + 1)])
      });
      let statement =
        GrammarBatchStatement::new(length, *root.as_bytes(), initial, end)
          .unwrap();
      let witness = replay.replay(&statement, &frame[4 + 30 * 16..]).unwrap();
      assert_eq!(witness.identity(), replay.identity());
      assert_eq!(
        witness.matrices().claims(&setup.verifier_shape().registry).len(),
        35
      );
      eprintln!(
        "parser replay frame {index}: verified, public_words={}, private_boolean={}, private_wiring={}, private_multipoint={}, private_inner={}, private_digests={}",
        witness.public_values().len(),
        witness.transcript().f128_private_values().len(),
        witness.wiring().private_values().len(),
        witness.multipoint().private_values().len(),
        witness.inner().private_values().len(),
        witness.inner().private_digests().len(),
      );
      initial = end;
    }
  }
}
