//! Fixed parser-batch verification and read-only recursive-verifier inputs.
//!
//! A verified native projection is witness material, not an outer proof. An
//! outer relation must constrain the complete child verifier independently.
use super::{StreamSlots, witness::BatchAdvice};
use crate::{
  hash::pack_bytes,
  ixby::{
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::{
      GrammarKind, NaturalCapacity,
      dispatch::{DispatchConfig, DispatchState},
      source::{SourceCapacity, SourceChunkProofWires},
    },
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder},
  field::F128,
  hash::HashKind,
  lincheck::{CscCircuit, LincheckCircuit},
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};

pub const BATCH_STEPS: usize = 32;
pub const BATCH_SOURCE_DEPTH: usize = 14;
pub const BATCH_PUBLIC_WORDS: usize = 63;
pub const BATCH_MAX_PROOF_BYTES: u64 = 8 * 1024 * 1024;
pub(super) const BATCH_NU: usize = 7;
const MAGIC: [u8; 8] = *b"IXFSTB00";

pub(super) fn domain(kind: GrammarKind) -> &'static [u8] {
  match kind {
    GrammarKind::Program => {
      b"ix:ixby:ixbf-stream-program:d14:steps32:nat4096:v2"
    },
    GrammarKind::Input => b"ix:ixby:ixbf-stream-input:d14:steps32:nat4096:v1",
    GrammarKind::Output => b"ix:ixby:ixbf-stream-output:d14:steps32:nat4096:v1",
  }
}

pub(super) fn config(kind: GrammarKind) -> DispatchConfig {
  DispatchConfig { kind, natural: NaturalCapacity::new(4096).unwrap() }
}

pub(super) struct Emission {
  pub slots: StreamSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}

pub(super) fn emit(b: &mut impl CircuitEmitter, kind: GrammarKind) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots =
    StreamSlots::declare(&mut b, BATCH_NU, config(kind), BATCH_SOURCE_DEPTH)
      .unwrap();
  let length = b.input();
  let root = std::array::from_fn(|_| b.input());
  let initial = DispatchState(std::array::from_fn(|_| b.input()));
  let first = b.input();
  let mut remaining = b.input();
  let proofs = std::array::from_fn(|_| SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..BATCH_SOURCE_DEPTH)
      .map(|_| std::array::from_fn(|_| b.input()))
      .collect(),
  });
  for word in [length].into_iter().chain(root).chain(initial.0) {
    b.publish(word);
  }
  let cache = slots.authenticate(&mut b, length, root, first, &proofs);
  let mut state = initial;
  for _ in 0..BATCH_STEPS {
    let step = slots.step(&mut b, &cache, state, remaining);
    state = step.event.state;
    remaining = step.remaining;
  }
  slots.finish_batch(&mut b, remaining);
  for word in state.0 {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  Emission { slots, inputs, public }
}

/// Exact externally expected source identity and complete parser endpoints.
/// Construction validates encoding widths; only a proof establishes a step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrammarBatchStatement([F128; BATCH_PUBLIC_WORDS]);

impl GrammarBatchStatement {
  pub fn new(
    length: u64,
    root: [u8; 32],
    initial: [F128; 30],
    final_state: [F128; 30],
  ) -> Result<Self> {
    let mut words = [F128::ZERO; BATCH_PUBLIC_WORDS];
    words[0] = F128::new(length, 0);
    words[1] = pack_bytes(root[..16].try_into().unwrap());
    words[2] = pack_bytes(root[16..].try_into().unwrap());
    words[3..33].copy_from_slice(&initial);
    words[33..].copy_from_slice(&final_state);
    Self::from_words(&words)
  }
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == BATCH_PUBLIC_WORDS, "parser batch public width");
    ensure!(
      words[0].hi == 0
        && SourceCapacity::new(BATCH_SOURCE_DEPTH, 0)?
          .admits_length(words[0].lo),
      "parser batch source length"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; BATCH_PUBLIC_WORDS] {
    &self.0
  }
  pub fn initial(&self) -> &[F128; 30] {
    self.0[3..33].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 30] {
    self.0[33..].try_into().unwrap()
  }
  pub fn source_identity(&self) -> &[F128; 3] {
    self.0[..3].try_into().unwrap()
  }

  /// Check whole-file endpoints after the batch or aggregate proof is verified.
  /// Transport context must come from the application's verified Program.
  /// This checks public-state predicates; it does not verify a proof itself.
  pub fn check_complete(
    &self,
    kind: GrammarKind,
    context: &[F128; 15],
  ) -> Result<()> {
    use crate::ixby::ixbf_decode::{
      dispatch::DISPATCH_CONTEXT_INDICES, grammar,
    };
    ensure!(
      kind != GrammarKind::Program || context.iter().all(|v| *v == F128::ZERO),
      "Program initial context"
    );
    let length = self.source_identity()[0].lo;
    let mut initial = [F128::ZERO; 30];
    initial[0] = F128::new(0, length);
    for (&index, &value) in DISPATCH_CONTEXT_INDICES.iter().zip(context) {
      initial[index] = value;
    }
    ensure!(
      self.initial() == &initial,
      "grammar file did not start at initialization"
    );
    let state = self.final_state();
    ensure!(
      state[0] == F128::new(length, length)
        && state[1].lo & 0xff == u64::from(grammar::Phase::Done as u8)
        && state[28..] == [F128::ZERO; 2],
      "grammar file did not finish at EOF"
    );
    for index in [
      grammar::FUNCTIONS_LEFT,
      grammar::BLOCKS_LEFT,
      grammar::CTORS_LEFT,
      grammar::ITEMS,
      grammar::PAYLOAD,
      grammar::PENDING,
    ] {
      ensure!(state[index] == F128::ZERO, "unfinished grammar obligation");
    }
    Ok(())
  }
}

#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
  kind: u8,
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}
fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(BATCH_MAX_PROOF_BYTES)
    .reject_trailing_bytes()
}

/// Immutable setup, compiled without source files, statements, proofs or traces.
pub struct CompiledGrammarBatch {
  kind: GrammarKind,
  shape: CircuitShape,
  emission: Emission,
  linchecks: Vec<CscCircuit>,
  params: PcsParams,
}

impl CompiledGrammarBatch {
  pub fn compile(kind: GrammarKind) -> Result<Self> {
    let mut b = ShapeBuilder::new(BATCH_NU);
    let emission = emit(&mut b, kind);
    let shape =
      b.finish().map_err(|e| anyhow::anyhow!("parser batch circuit: {e:?}"))?;
    ensure!(
      emission.inputs.private_words() == 311
        && emission.public.outputs() == BATCH_PUBLIC_WORDS
        && emission.slots.source().capacity().depth() == BATCH_SOURCE_DEPTH,
      "fixed parser batch input/source layout"
    );
    let union = UnionInstance::new(&shape.registry, shape.counts.clone());
    ensure!(
      union.dense_m() == 25 && !union.has_element(),
      "fixed parser batch PCS geometry"
    );
    let profile = LigeritoProfile::Fast128;
    let log_batch_size = embedded_initial_k_or_default(25, profile);
    let params = PcsParams {
      m: 25,
      profile,
      log_batch_size,
      log_inv_rate: profile.log_inv_rate(),
      num_lanes: union.commit_lanes(log_batch_size),
      merkle_hash: HashKind::Blake3,
    };
    let linchecks = shape
      .registry
      .boolean_types()
      .iter()
      .map(|ty| {
        CscCircuit::from_matrices(&ty.a_0, &ty.b_0).with_const_pin(ty.const_pin)
      })
      .collect();
    Ok(Self { kind, shape, emission, linchecks, params })
  }
  pub fn kind(&self) -> GrammarKind {
    self.kind
  }
  pub fn verifier_shape(&self) -> &CircuitShape {
    &self.shape
  }
  pub fn public_template(&self) -> &PublicLayout {
    &self.emission.public
  }
  pub fn pcs_params(&self) -> &PcsParams {
    &self.params
  }
  pub fn transcript_domain(&self) -> &'static [u8] {
    domain(self.kind)
  }
  pub fn lincheck_circuits(&self) -> Vec<&dyn LincheckCircuit> {
    self.linchecks.iter().map(|c| c as &dyn LincheckCircuit).collect()
  }
  /// Checks the complete native child proof. This does not check an entire
  /// file's Start/Done predicates or adjacency to any other batch.
  pub fn verify(
    &self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<()> {
    self.verify_for_replay(expected, bytes).map(|_| ())
  }
  pub fn verify_for_replay<'a>(
    &'a self,
    expected: &GrammarBatchStatement,
    bytes: &[u8],
  ) -> Result<VerifiedGrammarBatch<'a>> {
    ensure!(
      bytes.len() as u64 <= BATCH_MAX_PROOF_BYTES,
      "parser batch proof size"
    );
    let bundle: Bundle = codec().deserialize(bytes)?;
    ensure!(
      bundle.magic == MAGIC && bundle.kind == self.kind as u8,
      "parser batch proof kind/revision"
    );
    ensure!(
      codec().serialize(&bundle)? == bytes,
      "noncanonical parser batch proof"
    );
    let public = self.public_template().instantiate(expected.words())?;
    let union =
      UnionInstance::new(&self.shape.registry, self.shape.counts.clone());
    let mut challenger =
      FsChallenger::with_chained_blake3(self.transcript_domain());
    verifier::verify_ligerito_union_circuit(
      &union,
      &self.shape.circuit,
      &public,
      &self.lincheck_circuits(),
      &bundle.commitment,
      &bundle.proof,
      &self.params,
      &mut challenger,
    )
    .map_err(|e| anyhow::anyhow!("parser batch proof rejected: {e:?}"))?;
    Ok(VerifiedGrammarBatch {
      setup: self,
      expected: expected.clone(),
      public,
      bundle,
    })
  }

  /// A witness-side check for callers preparing a parser batch. Its result is
  /// not admission and is never used by verification.
  pub fn check_advice(&self, advice: &BatchAdvice) -> Result<()> {
    let input = self.emission.inputs.assign(&advice.private)?;
    let expected = self.public_template().instantiate(&advice.statement)?;
    let witness =
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        self.shape.run(&input, &[])
      }))
      .map_err(|_| anyhow::anyhow!("parser batch advice rejected"))?;
    ensure!(witness.public == expected, "parser batch advice statement");
    Ok(())
  }
}

/// Native replay projection tied to the exact compiled setup and expected
/// statement. An outer verifier must constrain every phase independently.
pub struct VerifiedGrammarBatch<'a> {
  setup: &'a CompiledGrammarBatch,
  expected: GrammarBatchStatement,
  public: Vec<F128>,
  bundle: Bundle,
}
impl VerifiedGrammarBatch<'_> {
  pub fn setup(&self) -> &CompiledGrammarBatch {
    self.setup
  }
  pub fn expected(&self) -> &GrammarBatchStatement {
    &self.expected
  }
  pub fn public_values(&self) -> &[F128] {
    &self.public
  }
  pub fn commitment(&self) -> &Commitment {
    &self.bundle.commitment
  }
  pub fn proof(&self) -> &R1csProofCircuitMerged {
    &self.bundle.proof
  }
}
