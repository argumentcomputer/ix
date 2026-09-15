//! Fixed generic batch setup; isolated verifiers never receive source bytes.
use super::super::{dispatch::*, source::*, *};
use super::{tests, *};
use crate::{
  equality::{
    F128EqualityGate, F128EqualityRow, build_f128_equality_r1cs,
    generate_f128_equality_witness_into,
  },
  hash::Blake3Gate,
  ixby::{
    io::{InputLayout, LayoutEmitter, PublicLayout},
    select::SelectWordsGate,
  },
  sizing::{CircuitEmitter, CountingEmitter},
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, CircuitWitness, GateType, ShapeBuilder, SlotId,
  },
  field::F128,
  hash::HashKind,
  lincheck::LincheckCircuit,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
  union::{SlotWitnessDest, UnionInstance},
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

#[path = "cslib_tests.rs"]
mod cslib_tests;

const NU: usize = 7;
const STEPS: usize = 32;
const DEPTH: usize = 14;
const OUTPUTS: usize = 63;
const MAGIC: [u8; 8] = *b"IXFSTB00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_STREAM_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::stream::proof_tests::batches_and_chains_verify_in_isolation_and_reject_substitutions";

fn domain(kind: GrammarKind) -> &'static [u8] {
  match kind {
    GrammarKind::Program => {
      b"ix:ixby:ixbf-stream-program:d14:steps32:nat4096:v0"
    },
    GrammarKind::Input => b"ix:ixby:ixbf-stream-input:d14:steps32:nat4096:v0",
    GrammarKind::Output => b"ix:ixby:ixbf-stream-output:d14:steps32:nat4096:v0",
  }
}
fn kind(tag: u8) -> Result<GrammarKind> {
  match tag {
    0 => Ok(GrammarKind::Program),
    1 => Ok(GrammarKind::Input),
    2 => Ok(GrammarKind::Output),
    _ => anyhow::bail!("unknown dispatch grammar"),
  }
}

pub(super) struct Emission {
  pub slots: StreamSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn config(kind: GrammarKind) -> DispatchConfig {
  DispatchConfig { kind, natural: NaturalCapacity::new(4096).unwrap() }
}
pub(super) fn emit(b: &mut impl CircuitEmitter, kind: GrammarKind) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = StreamSlots::declare(&mut b, NU, config(kind), DEPTH).unwrap();
  let length = b.input();
  let root = std::array::from_fn(|_| b.input());
  let initial = DispatchState(std::array::from_fn(|_| b.input()));
  let first = b.input();
  let mut remaining = b.input();
  let proofs = std::array::from_fn(|_| SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..DEPTH).map(|_| std::array::from_fn(|_| b.input())).collect(),
  });
  for word in [length].into_iter().chain(root).chain(initial.0) {
    b.publish(word);
  }
  let cache = slots.authenticate(&mut b, length, root, first, &proofs);
  let mut state = initial;
  for _ in 0..STEPS {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  CacheLength,
  CacheIndex,
  ReadCursor,
  EmptyReadLength,
  PausedState,
  RemainingSteps,
  SourceBuffer,
  PathSibling,
  CompressionCounter,
}
trait Driver: Send + Sync {
  fn slot(&self) -> SlotId;
  fn table(&self) -> &BlockR1cs;
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
    attack: Attack,
  ) -> UnionSlotProverInput<'a>;
}
type Generate<G> =
  fn(&G, &[<G as GateType>::Row], SlotWitnessDest<'_>) -> Vec<u8>;
struct TypedDriver<G: GateType> {
  slot: SlotId,
  gate: G,
  table: BlockR1cs,
  generate: Generate<G>,
  alter: fn(&G, &mut [G::Row], Attack),
}
impl<G> Driver for TypedDriver<G>
where
  G: GateType<Hint = ()> + Send + Sync + 'static,
  G::Row: Clone + Send + Sync + 'static,
{
  fn slot(&self) -> SlotId {
    self.slot
  }
  fn table(&self) -> &BlockR1cs {
    &self.table
  }
  fn prover<'a>(
    &'a self,
    witness: &'a CircuitWitness,
    attack: Attack,
  ) -> UnionSlotProverInput<'a> {
    let mut rows = witness.rows::<G>(self.slot).to_vec();
    (self.alter)(&self.gate, &mut rows, attack);
    UnionSlotProverInput::in_place(
      move |dst| (self.generate)(&self.gate, &rows, dst),
      self.table.csc_lincheck_circuit(),
    )
  }
}
fn untouched<G: GateType>(_: &G, _: &mut [G::Row], _: Attack) {}
fn values<G: GateType<Hint = ()>>(gate: &G, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  gate.eval(input, &(), &mut out);
  out
}
fn alter_stream(g: &StreamGate, rows: &mut [StreamRow], attack: Attack) {
  let op = match attack {
    Attack::CacheLength | Attack::CacheIndex => StreamOp::Cache,
    Attack::ReadCursor | Attack::EmptyReadLength => StreamOp::Read,
    Attack::PausedState | Attack::RemainingSteps => StreamOp::Prepare,
    _ => return,
  };
  if g.op() != op {
    return;
  }
  let row = match attack {
    Attack::EmptyReadLength => {
      rows.iter_mut().find(|r| r.0[1] == F128::ZERO).unwrap()
    },
    Attack::PausedState => {
      rows.iter_mut().find(|r| r.0[0] == F128::ZERO).unwrap()
    },
    _ => &mut rows[0],
  };
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::CacheLength => row.0[0].lo += 1024,
    Attack::CacheIndex => row.0[1].lo += 1,
    Attack::ReadCursor => row.0[0].lo += 1,
    Attack::EmptyReadLength => {
      row.0[0].hi += 1;
      row.0[2].lo += 1;
    },
    Attack::PausedState => row.0[15].hi ^= 1,
    Attack::RemainingSteps => row.0[0].lo += 1,
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), &row.0, &after);
  if attack == Attack::PausedState {
    assert_eq!(before, after);
  }
}
fn alter_window(
  g: &SourceWindowGate,
  rows: &mut [SourceWindowRow],
  attack: Attack,
) {
  if attack != Attack::SourceBuffer {
    return;
  }
  let row = rows
    .iter_mut()
    .find_map(|r| (r.test_inputs_mut()[1] == F128::ZERO).then_some(r))
    .unwrap();
  let input = row.test_inputs_mut();
  let before = values(g, input);
  input[2].lo ^= 1;
  let after = values(g, input);
  assert_eq!(
    before, after,
    "unused source bytes preserve the local read result"
  );
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), input, &after);
}
fn alter_path(g: &SourcePathGate, rows: &mut [SourcePathRow], attack: Attack) {
  if attack != Attack::PathSibling {
    return;
  }
  let input = rows[0].test_inputs_mut();
  let before = values(g, input);
  assert_eq!(before.last(), Some(&F128::ZERO));
  input[5].lo ^= 1;
  let after = values(g, input);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), input, &after);
}
fn compression(
  _: &Blake3Gate,
  rows: &[<Blake3Gate as GateType>::Row],
  mut dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  dst.elide_padding_writes = false;
  flock_blake3::generate_witness_batch_major_partial_into(rows, NU, dst)
}
fn equality(
  _: &F128EqualityGate,
  rows: &[F128EqualityRow],
  mut dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  dst.elide_padding_writes = false;
  generate_f128_equality_witness_into(rows, NU, dst)
}
fn alter_compression(
  _: &Blake3Gate,
  rows: &mut [<Blake3Gate as GateType>::Row],
  attack: Attack,
) {
  if attack == Attack::CompressionCounter {
    rows[0].2 += 1;
    let table = flock_blake3::build_block_r1cs(3);
    let bits = flock_blake3::generate_witness(&rows[..1], 3);
    assert!(table.satisfies(&bits));
  }
}

pub(super) struct Setup {
  pub shape: CircuitShape,
  pub emission: Emission,
  drivers: Vec<Box<dyn Driver>>,
}
pub(super) fn setup(kind: GrammarKind) -> Setup {
  let mut b = ShapeBuilder::new(NU);
  let emission = emit(&mut b, kind);
  let shape = b.finish().unwrap();
  let config = config(kind);
  let slots = emission.slots.dispatch();
  let mut drivers: Vec<Box<dyn Driver>> = Vec::new();
  macro_rules! driver {
    ($slot:expr, $gate:expr, $type:ty, $alter:expr) => {{
      let gate = $gate;
      let table = gate.r1cs();
      drivers.push(Box::new(TypedDriver {
        slot: $slot,
        gate,
        table,
        generate: <$type>::generate_witness_into,
        alter: $alter,
      }));
    }};
  }
  for op in DispatchOp::ALL {
    driver!(
      slots.control_slot(op),
      DispatchGate::new(NU, config, op).unwrap(),
      DispatchGate,
      untouched::<DispatchGate>
    );
  }
  for k in RecordKind::ALL {
    driver!(
      slots.record_slot(k),
      RecordDecodeGate::new(NU, k).unwrap(),
      RecordDecodeGate,
      untouched::<RecordDecodeGate>
    );
  }
  driver!(
    slots.header_slot(),
    HeaderDecodeGate::new(NU).unwrap(),
    HeaderDecodeGate,
    untouched::<HeaderDecodeGate>
  );
  driver!(
    slots.natural_slot(),
    NaturalDecodeGate::new(NU, config.natural).unwrap(),
    NaturalDecodeGate,
    untouched::<NaturalDecodeGate>
  );
  driver!(
    slots.natural_limit_slot(),
    NaturalLimitGate::new(NU, config.natural).unwrap(),
    NaturalLimitGate,
    untouched::<NaturalLimitGate>
  );
  driver!(
    slots.payload_slot(),
    PayloadCursorGate::new(NU).unwrap(),
    PayloadCursorGate,
    untouched::<PayloadCursorGate>
  );
  driver!(
    slots.utf8_slot(),
    Utf8ChunkGate::new(NU).unwrap(),
    Utf8ChunkGate,
    untouched::<Utf8ChunkGate>
  );
  driver!(
    slots.grammar_slot(),
    GrammarStepGate::new(NU, kind).unwrap(),
    GrammarStepGate,
    untouched::<GrammarStepGate>
  );
  let source = emission.slots.source();
  driver!(
    source.window_gate().0,
    source.window_gate().1.clone(),
    SourceWindowGate,
    alter_window
  );
  driver!(
    source.block_gate().0,
    source.block_gate().1.clone(),
    SourceBlockGate,
    untouched::<SourceBlockGate>
  );
  driver!(
    source.path_gate().0,
    source.path_gate().1.clone(),
    SourcePathGate,
    alter_path
  );
  driver!(
    source.select_gate().0,
    source.select_gate().1.clone(),
    SelectWordsGate,
    untouched::<SelectWordsGate>
  );
  for op in StreamOp::ALL {
    driver!(
      emission.slots.control_slot(op),
      StreamGate::new(NU, source.capacity(), op).unwrap(),
      StreamGate,
      alter_stream
    );
  }
  driver!(
    emission.slots.select_slot(),
    SelectWordsGate::new(NU, 31).unwrap(),
    SelectWordsGate,
    untouched::<SelectWordsGate>
  );
  let crate::blake3_backend::Blake3CompressionSlots::LegacyOptionF {
    slot, ..
  } = source.compression()
  else {
    panic!("legacy conformance setup")
  };
  drivers.push(Box::new(TypedDriver {
    slot: *slot,
    gate: Blake3Gate { nu: NU },
    table: flock_blake3::build_block_r1cs(NU),
    generate: compression,
    alter: alter_compression,
  }));
  drivers.push(Box::new(TypedDriver {
    slot: emission.slots.equality_slot(),
    gate: F128EqualityGate { nu: NU },
    table: build_f128_equality_r1cs(NU),
    generate: equality,
    alter: untouched::<F128EqualityGate>,
  }));
  drivers.sort_by_key(|d| shape.registry_slot(d.slot()));
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 35 + 3 * (64 + 2 * DEPTH));
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, drivers }
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert_eq!(m, 25, "explicit streaming batch PCS geometry");
  let profile = LigeritoProfile::Fast128;
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  PcsParams {
    m,
    profile,
    log_batch_size,
    log_inv_rate: profile.log_inv_rate(),
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: HashKind::Blake3,
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
    .with_limit(MAX_BYTES)
    .reject_trailing_bytes()
}
fn prove(
  kind: GrammarKind,
  s: &Setup,
  w: &CircuitWitness,
  expected: &[F128],
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(domain(kind));
  let slots = s.drivers.iter().map(|d| d.prover(w, attack)).collect();
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &s.shape.circuit,
    &s.emission.public.instantiate(expected).unwrap(),
    &params(&union),
    slots,
    Vec::new(),
    &mut challenger,
  );
  let bytes = codec()
    .serialize(&Bundle { magic: MAGIC, kind: kind as u8, commitment, proof })
    .unwrap();
  eprintln!(
    "stream batch proof {kind:?} {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify_with(
  s: &Setup,
  kind: GrammarKind,
  expected: &[F128],
  bytes: &[u8],
  domain: &[u8],
) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "stream batch proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.kind == kind as u8,
    "stream batch proof kind or revision"
  );
  ensure!(
    codec().serialize(&bundle)? == bytes,
    "noncanonical stream batch proof"
  );
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  let circuits: Vec<&dyn LincheckCircuit> = s
    .drivers
    .iter()
    .map(|d| d.table().csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect();
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &s.shape.circuit,
    &s.emission.public.instantiate(expected)?,
    &circuits,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|e| anyhow::anyhow!("stream batch proof rejected: {e:?}"))?;
  Ok(())
}

fn verify(
  kind: GrammarKind,
  expected: &[F128],
  bytes: &[u8],
  domain: &[u8],
) -> Result<()> {
  verify_with(&setup(kind), kind, expected, bytes, domain)
}

const CHAIN_MAGIC: &[u8; 8] = b"IXFSTC00";
const CHAIN_EXPECTED: usize = 18;
const MAX_BATCHES: usize = 4096;

fn read_words(input: &mut impl Read, count: usize) -> Result<Vec<F128>> {
  let mut bytes = vec![0; count * 16];
  input.read_exact(&mut bytes)?;
  Ok(
    bytes
      .as_chunks::<16>()
      .0
      .iter()
      .map(|w| crate::hash::pack_bytes(w))
      .collect(),
  )
}
fn write_words(output: &mut impl Write, words: &[F128]) -> std::io::Result<()> {
  for word in words {
    output.write_all(&word.lo.to_le_bytes())?;
    output.write_all(&word.hi.to_le_bytes())?;
  }
  Ok(())
}
fn chain_expected(bytes: &[u8], context: [F128; 15]) -> Vec<F128> {
  let mut expected = vec![F128::new(bytes.len() as u64, 0)];
  expected.extend(
    blake3::hash(bytes)
      .as_bytes()
      .as_chunks::<16>()
      .0
      .iter()
      .map(|w| crate::hash::pack_bytes(w)),
  );
  expected.extend(context);
  expected
}

/// Streams bounded proof frames. Only externally expected root/length/context
/// and proof bytes enter this verifier: no AST, file access or native evaluator.
fn verify_chain(
  kind: GrammarKind,
  expected: &[F128],
  input: &mut impl Read,
) -> Result<[F128; 30]> {
  ensure!(expected.len() == CHAIN_EXPECTED, "chain public width");
  let length = expected[0];
  ensure!(
    length.hi == 0 && SourceCapacity::new(DEPTH, 0)?.admits_length(length.lo),
    "chain source length"
  );
  ensure!(
    kind != GrammarKind::Program
      || expected[3..].iter().all(|w| *w == F128::ZERO),
    "Program initial context"
  );
  let mut magic = [0; 8];
  input.read_exact(&mut magic)?;
  ensure!(&magic == CHAIN_MAGIC, "parser chain domain/revision");
  let s = setup(kind);
  let mut state = [F128::ZERO; 30];
  state[0] = F128::new(0, length.lo);
  for (i, at) in DISPATCH_CONTEXT_INDICES.into_iter().enumerate() {
    state[at] = expected[3 + i];
  }
  let mut batches = 0;
  loop {
    let mut size = [0; 4];
    input.read_exact(&mut size)?;
    let size = u32::from_le_bytes(size) as usize;
    if size == 0 {
      break;
    }
    ensure!(
      batches < MAX_BATCHES && size as u64 <= MAX_BYTES,
      "parser chain resource limit"
    );
    let next: [F128; 30] = read_words(input, 30)?.try_into().unwrap();
    ensure!(next != state, "parser batch made no progress");
    let mut proof = vec![0; size];
    input.read_exact(&mut proof)?;
    let mut statement = expected[..3].to_vec();
    statement.extend(state);
    statement.extend(next);
    verify_with(&s, kind, &statement, &proof, domain(kind))?;
    state = next;
    batches += 1;
  }
  ensure!(
    batches > 0
      && state[0] == F128::new(length.lo, length.lo)
      && state[1].lo as u8 == 20
      && state[28..] == [F128::ZERO; 2],
    "parser chain did not finish"
  );
  for at in [
    grammar::FUNCTIONS_LEFT,
    grammar::BLOCKS_LEFT,
    grammar::CTORS_LEFT,
    grammar::ITEMS,
    grammar::PAYLOAD,
    grammar::PENDING,
  ] {
    ensure!(state[at] == F128::ZERO, "unfinished grammar obligation");
  }
  let mut trailing = [0];
  ensure!(input.read(&mut trailing)? == 0, "trailing parser chain bytes");
  Ok(state)
}
fn encode_chain(frames: &[([F128; 30], Vec<u8>)]) -> Vec<u8> {
  let mut out = CHAIN_MAGIC.to_vec();
  for (end, proof) in frames {
    out.extend(u32::try_from(proof.len()).unwrap().to_le_bytes());
    write_words(&mut out, end).unwrap();
    out.extend_from_slice(proof);
  }
  out.extend(0u32.to_le_bytes());
  out
}
fn isolated(
  mode: u8,
  kind: GrammarKind,
  expected: &[F128],
  proof: &[u8],
) -> (bool, String) {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut input = child.stdin.take().unwrap();
  let written = (|| -> std::io::Result<()> {
    input.write_all(&[mode, kind as u8])?;
    write_words(&mut input, expected)?;
    input.write_all(proof)
  })();
  drop(input);
  let out = child.wait_with_output().unwrap();
  let error = String::from_utf8_lossy(&out.stderr).into_owned();
  if out.status.success() {
    written.unwrap();
  } else {
    eprintln!("fresh stream verifier rejected: {error}");
  }
  (out.status.success(), error)
}
fn child() -> Result<()> {
  let mut input = std::io::stdin().lock();
  let mut tag = [0; 2];
  input.read_exact(&mut tag)?;
  let kind = kind(tag[1])?;
  match tag[0] {
    0 => {
      let expected = read_words(&mut input, OUTPUTS)?;
      let mut proof = Vec::new();
      input.take(MAX_BYTES + 1).read_to_end(&mut proof)?;
      verify(kind, &expected, &proof, domain(kind))
    },
    1 => {
      let expected = read_words(&mut input, CHAIN_EXPECTED)?;
      verify_chain(kind, &expected, &mut input).map(|_| ())
    },
    _ => anyhow::bail!("unknown parser verifier mode"),
  }
}

pub(super) fn witness(
  s: &Setup,
  advice: &witness::BatchAdvice,
) -> CircuitWitness {
  let w = s.shape.run(&s.emission.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(
    w.public,
    s.emission.public.instantiate(&advice.statement).unwrap()
  );
  let crate::blake3_backend::Blake3CompressionSlots::LegacyOptionF {
    slot, ..
  } = s.emission.slots.source().compression()
  else {
    unreachable!()
  };
  assert_eq!(
    w.rows::<Blake3Gate>(*slot).len(),
    3 * (16 + DEPTH),
    "three authentications per batch, independent of decoder steps"
  );
  w
}
fn prove_chain(
  s: &Setup,
  kind: GrammarKind,
  bytes: &[u8],
  context: [F128; 15],
) -> Vec<([F128; 30], Vec<u8>)> {
  let mut stream =
    witness::BatchWitness::new(config(kind), DEPTH, bytes, context).unwrap();
  let mut frames = Vec::new();
  while let Some(advice) = stream.next_batch(STEPS).unwrap() {
    let w = witness(s, &advice);
    let proof = prove(kind, s, &w, &advice.statement, Attack::None);
    frames.push((advice.final_state, proof));
  }
  let encoded = encode_chain(&frames);
  assert!(isolated(1, kind, &chain_expected(bytes, context), &encoded).0);
  eprintln!(
    "stream chain {kind:?}: source={} batches={} bytes={}",
    bytes.len(),
    frames.len(),
    encoded.len()
  );
  frames
}

#[test]
fn batch_setup_is_counted_and_independent_of_original_file_and_schedule() {
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let mut count = CountingEmitter::new();
    let emission = emit(&mut count, kind);
    let s = setup(kind);
    count.ensure_matches(&s.shape).unwrap();
    assert_eq!(emission.inputs, s.emission.inputs);
    assert_eq!(emission.public, s.emission.public);
    assert_eq!(count.required_nu(3).unwrap(), NU);
    let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
    eprintln!(
      "stream {kind:?}: tables={} M={} private={} public={} rows={:?}",
      s.shape.counts.len(),
      union.dense_m(),
      emission.inputs.private_words(),
      emission.public.outputs(),
      s.shape.counts
    );
    let identity = s.shape.circuit.digest();
    let p = tests::program(None, 1);
    let program_state = test_parse_program(&p, 1000).unwrap();
    let context = if kind == GrammarKind::Program {
      [F128::ZERO; 15]
    } else {
      DISPATCH_CONTEXT_INDICES.map(|i| program_state[i])
    };
    for scalar in [vec![0, 0], tests::string(2400), tests::bytes(6000)] {
      let bytes = if kind == GrammarKind::Program {
        tests::program(Some(&scalar), 1)
      } else {
        tests::transport(kind, &[scalar])
      };
      let mut stream =
        witness::BatchWitness::new(config(kind), DEPTH, &bytes, context)
          .unwrap();
      while let Some(advice) = stream.next_batch(STEPS).unwrap() {
        witness(&s, &advice);
      }
      assert_eq!(s.shape.circuit.digest(), identity);
      let expected = if kind == GrammarKind::Program {
        test_parse_program(&bytes, 1000).unwrap()
      } else {
        test_parse_transport(kind, &bytes, &program_state, 1000).unwrap()
      };
      assert_eq!(stream.state()[..28], expected);
    }
  }
}

#[test]
#[ignore = "real shared-source parser batch/chain proofs, isolated verification and recomputed wiring attacks"]
fn batches_and_chains_verify_in_isolation_and_reject_substitutions() {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let kind = GrammarKind::Program;
  let s = setup(kind);
  let bytes = tests::program(Some(&tests::bytes(6000)), 1);
  let mut stream =
    witness::BatchWitness::new(config(kind), DEPTH, &bytes, [F128::ZERO; 15])
      .unwrap();
  let advice = stream.next_batch(STEPS).unwrap().unwrap();
  assert!(stream.done());
  let w = witness(&s, &advice);
  let honest = prove(kind, &s, &w, &advice.statement, Attack::None);
  assert!(isolated(0, kind, &advice.statement, &honest).0);
  for attack in [
    Attack::CacheLength,
    Attack::CacheIndex,
    Attack::ReadCursor,
    Attack::EmptyReadLength,
    Attack::PausedState,
    Attack::RemainingSteps,
    Attack::SourceBuffer,
    Attack::PathSibling,
    Attack::CompressionCounter,
  ] {
    let proof = prove(kind, &s, &w, &advice.statement, attack);
    let (accepted, error) = isolated(0, kind, &advice.statement, &proof);
    assert!(!accepted && error.contains("Wiring"), "{attack:?}: {error}");
  }
  let source = tests::program(Some(&tests::string(2400)), 1);
  let frames = prove_chain(&s, kind, &source, [F128::ZERO; 15]);
  assert!(frames.len() >= 3);
  let expected = chain_expected(&source, [F128::ZERO; 15]);
  let rejects = |frames: &[([F128; 30], Vec<u8>)]| {
    assert!(!isolated(1, kind, &expected, &encode_chain(frames)).0);
  };
  rejects(&frames[1..]);
  rejects(&frames[..frames.len() - 1]);
  let mut swapped = frames.clone();
  swapped.swap(0, 1);
  rejects(&swapped);
  let mut replayed = frames.clone();
  replayed.insert(1, frames[0].clone());
  rejects(&replayed);
  for at in [0, 1, 14, 28, 29] {
    let mut changed = frames.clone();
    changed[0].0[at].lo ^= 1;
    rejects(&changed);
  }
  let mut trailing = encode_chain(&frames);
  trailing.push(0);
  assert!(!isolated(1, kind, &expected, &trailing).0);
  let mut incomplete = encode_chain(&frames);
  incomplete.truncate(incomplete.len() - 1);
  assert!(!isolated(1, kind, &expected, &incomplete).0);
  for at in [0, 1, 2, 17] {
    let mut changed = expected.clone();
    changed[at].lo ^= 1;
    assert!(!isolated(1, kind, &changed, &encode_chain(&frames)).0);
  }
  for at in [0, 1, 3, 17, 32, 33, 61, 62] {
    let mut wrong = advice.statement.clone();
    wrong[at].hi ^= 1;
    assert!(verify(kind, &wrong, &honest, domain(kind)).is_err());
  }
  assert!(
    verify(
      kind,
      &advice.statement,
      &honest,
      b"ix:ixby:ixbf-dispatch-program:bytes1024:steps32:nat4096:v0"
    )
    .is_err()
  );
  for at in [0, 7, 8, honest.len() - 1] {
    let mut wrong = honest.clone();
    wrong[at] ^= 1;
    assert!(verify(kind, &advice.statement, &wrong, domain(kind)).is_err());
  }
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(verify(kind, &advice.statement, &trailing, domain(kind)).is_err());
  assert!(
    verify(kind, &advice.statement[..OUTPUTS - 1], &honest, domain(kind))
      .is_err()
  );
  let p = tests::program(None, 2);
  let final_program = test_parse_program(&p, 32).unwrap();
  let context = DISPATCH_CONTEXT_INDICES.map(|i| final_program[i]);
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let s = setup(kind);
    for scalars in [vec![tests::string(2400)], vec![tests::bytes(6000)]] {
      let scalars = if kind == GrammarKind::Input {
        vec![scalars[0].clone(), tests::wide_nat()]
      } else {
        scalars
      };
      prove_chain(&s, kind, &tests::transport(kind, &scalars), context);
    }
  }
}
