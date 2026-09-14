//! Explicit small-file grammar-proof conformance class, not Exec admission.
//! One private 1 KiB buffer is hashed ONCE and reused by every source window.
//! No host AST, decoder schedule, Nat length, or acceptance bit is an input.
use super::super::{
  source::{SourceCapacity, SourceReadWires, SourceWindowGate},
  *,
};
use super::*;
use crate::{
  hash::Blake3Gate,
  ixby::{
    bounded_hash::{BoundedBlake3, tests as hash_tests},
    hash_control::{HashBlockGate, RootParamsGate},
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

const NU: usize = 7;
const STEPS: usize = 32;
const CAPACITY: usize = 1024;
const OUTPUTS: usize = 45;
const MAGIC: [u8; 8] = *b"IXFDSP00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_DISPATCH_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::dispatch::proof_tests::whole_grammar_proofs_verify_without_source_and_reject_recomputed_substitutions";

fn domain(kind: GrammarKind) -> &'static [u8] {
  match kind {
    GrammarKind::Program => {
      b"ix:ixby:ixbf-dispatch-program:bytes1024:steps32:nat4096:v0"
    },
    GrammarKind::Input => {
      b"ix:ixby:ixbf-dispatch-input:bytes1024:steps32:nat4096:v0"
    },
    GrammarKind::Output => {
      b"ix:ixby:ixbf-dispatch-output:bytes1024:steps32:nat4096:v0"
    },
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

struct Emission {
  slots: DispatchSlots,
  hash: BoundedBlake3,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter, kind: GrammarKind) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let config = model_tests::config(kind);
  let slots = DispatchSlots::declare(&mut b, NU, config).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, CAPACITY).unwrap();
  let window = b.slot(
    SourceWindowGate::new(
      NU,
      SourceCapacity::new(0, config.window_bytes()).unwrap(),
    )
    .unwrap(),
  );
  let zero = b.fixed_public_input(F128::ZERO);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let context: [_; 15] = std::array::from_fn(|_| b.input());
  let root = hash.hash(&mut b, length, &bytes);
  for word in root.into_iter().chain(context) {
    b.publish(word);
  }
  let mut state = slots.initialize(&mut b, length, context);
  for _ in 0..STEPS {
    state = slots
      .step(&mut b, state, |b, cursor, take| {
        let mut input = vec![cursor, take];
        input.extend_from_slice(&bytes);
        input.extend_from_slice(&bytes);
        let mut out = b.gate(window, &input);
        b.connect(out.pop().unwrap(), zero);
        SourceReadWires { file_length: out[0], words: out[4..].to_vec() }
      })
      .state;
  }
  for word in slots.finish(&mut b, state).0 {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  Emission { slots, hash, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  RequestState,
  SourceBuffer,
  MergeDecoder,
  FinishString,
  NaturalBytes,
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
fn alter_control(g: &DispatchGate, rows: &mut [DispatchRow], attack: Attack) {
  let op = match attack {
    Attack::RequestState => DispatchOp::Request,
    Attack::MergeDecoder => DispatchOp::Merge,
    Attack::FinishString => DispatchOp::Finish,
    Attack::NaturalBytes => DispatchOp::NaturalLookahead,
    _ => return,
  };
  if g.op() != op {
    return;
  }
  let row = match attack {
    Attack::FinishString => rows
      .iter_mut()
      .find(|r| r.0[61] == F128::new(15, 0) && r.0[59].lo > 0)
      .unwrap(),
    Attack::NaturalBytes => {
      rows.iter_mut().find(|r| r.0[0] == F128::ONE).unwrap()
    },
    _ => &mut rows[0],
  };
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::RequestState => row.0[27].lo ^= 1,
    Attack::MergeDecoder => row.0[16].lo ^= 1,
    Attack::FinishString => {
      row.0[58] = row.0[60];
      row.0[59] = F128::ZERO;
    },
    Attack::NaturalBytes => row.0[1].lo ^= 1,
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO));
  if matches!(attack, Attack::RequestState | Attack::MergeDecoder) {
    assert_eq!(before, after);
  } else {
    assert_ne!(before, after);
  }
}
fn alter_window(
  g: &SourceWindowGate,
  rows: &mut [source::SourceWindowRow],
  attack: Attack,
) {
  if attack != Attack::SourceBuffer {
    return;
  }
  let input = rows[1].test_inputs_mut();
  assert!(input[0].lo > 0);
  let before = values(g, input);
  assert_eq!(before.last(), Some(&F128::ZERO));
  input[2].lo ^= 1;
  assert_eq!(
    values(g, input),
    before,
    "source substitution outside this read preserves every local output"
  );
}
fn compression(
  _: &Blake3Gate,
  rows: &[<Blake3Gate as GateType>::Row],
  mut dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  dst.elide_padding_writes = false;
  flock_blake3::generate_witness_batch_major_partial_into(rows, NU, dst)
}
fn alter_compression(
  _: &Blake3Gate,
  rows: &mut [<Blake3Gate as GateType>::Row],
  attack: Attack,
) {
  if attack == Attack::CompressionCounter {
    rows[0].2 += 1;
  }
}

struct Setup {
  shape: CircuitShape,
  emission: Emission,
  drivers: Vec<Box<dyn Driver>>,
}
fn setup(kind: GrammarKind) -> Setup {
  let mut b = ShapeBuilder::new(NU);
  let emission = emit(&mut b, kind);
  let shape = b.finish().unwrap();
  let config = model_tests::config(kind);
  let slots = &emission.slots;
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
      alter_control
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
  driver!(
    emission.window,
    SourceWindowGate::new(
      NU,
      SourceCapacity::new(0, config.window_bytes()).unwrap()
    )
    .unwrap(),
    SourceWindowGate,
    alter_window
  );
  let hash = &emission.hash;
  driver!(
    hash.block_slot(),
    hash.block_gate().clone(),
    HashBlockGate,
    untouched::<HashBlockGate>
  );
  driver!(
    hash.select_slot(),
    hash.select_gate().clone(),
    SelectWordsGate,
    untouched::<SelectWordsGate>
  );
  driver!(
    hash.root_slot(),
    *hash.root_gate(),
    RootParamsGate,
    untouched::<RootParamsGate>
  );
  drivers.push(Box::new(TypedDriver {
    slot: hash.compression_slot(),
    gate: Blake3Gate { nu: NU },
    table: flock_blake3::build_block_r1cs(NU),
    generate: compression,
    alter: alter_compression,
  }));
  drivers.sort_by_key(|d| shape.registry_slot(d.slot()));
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 80);
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, drivers }
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m), "unchanged pinned PCS geometry");
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
    "dispatch proof {kind:?} {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify(
  kind: GrammarKind,
  expected: &[F128],
  bytes: &[u8],
  domain: &[u8],
) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "dispatch proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.kind == kind as u8,
    "dispatch proof kind or revision"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical dispatch proof");
  let s = setup(kind);
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
  .map_err(|e| anyhow::anyhow!("dispatch proof rejected: {e:?}"))?;
  Ok(())
}
fn isolated(kind: GrammarKind, expected: &[F128], proof: &[u8]) -> bool {
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
  input.write_all(&[kind as u8]).unwrap();
  for word in expected {
    input.write_all(&word.lo.to_le_bytes()).unwrap();
    input.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  input.write_all(proof).unwrap();
  drop(input);
  let out = child.wait_with_output().unwrap();
  if !out.status.success() {
    eprintln!(
      "fresh dispatch verifier rejected: {}",
      String::from_utf8_lossy(&out.stderr)
    );
  }
  out.status.success()
}
fn child() -> Result<()> {
  let mut input = Vec::new();
  std::io::stdin()
    .take(MAX_BYTES + 1 + 16 * OUTPUTS as u64 + 1)
    .read_to_end(&mut input)?;
  let prefix = 1 + 16 * OUTPUTS;
  ensure!(
    (prefix..=prefix + MAX_BYTES as usize).contains(&input.len()),
    "dispatch verifier input size"
  );
  let kind = kind(input[0])?;
  let expected: Vec<_> = input[1..prefix]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|w| crate::hash::pack_bytes(w))
    .collect();
  verify(kind, &expected, &input[prefix..], domain(kind))
}
fn witness(
  s: &Setup,
  bytes: &[u8],
  context: [F128; 15],
) -> (CircuitWitness, Vec<F128>) {
  let parsed = model_tests::Model::new(s.emission.slots.config(), false)
    .parse(bytes, context, STEPS)
    .unwrap();
  let mut private = hash_tests::private_input(CAPACITY, bytes);
  private.extend(context);
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(bytes).to_vec();
  expected.extend(context);
  expected.extend(parsed.state);
  assert_eq!(w.public, s.emission.public.instantiate(&expected).unwrap());
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    17,
    "one whole-buffer hash, not a hash per read"
  );
  for op in DispatchOp::ALL {
    assert_eq!(
      w.rows::<DispatchGate>(s.emission.slots.control_slot(op)).len(),
      if op == DispatchOp::Initialize { 1 } else { STEPS }
    );
  }
  assert_eq!(
    w.rows::<PayloadCursorGate>(s.emission.slots.payload_slot()).len(),
    2 * STEPS
  );
  assert_eq!(
    w.rows::<GrammarStepGate>(s.emission.slots.grammar_slot()).len(),
    STEPS + 1
  );
  (w, expected)
}

#[test]
fn whole_buffer_dispatch_is_data_independent_and_counted_before_witnessing() {
  for kind in [GrammarKind::Program, GrammarKind::Input, GrammarKind::Output] {
    let mut count = CountingEmitter::new();
    let emission = emit(&mut count, kind);
    let s = setup(kind);
    count.ensure_matches(&s.shape).unwrap();
    assert_eq!(emission.inputs, s.emission.inputs);
    assert_eq!(emission.public, s.emission.public);
    let p = model_tests::program(None, 1);
    let parsed =
      model_tests::Model::new(model_tests::config(GrammarKind::Program), false)
        .parse(&p, [F128::ZERO; 15], STEPS)
        .unwrap();
    let context = if kind == GrammarKind::Program {
      [F128::ZERO; 15]
    } else {
      model_tests::context(&parsed.state)
    };
    let identity = s.shape.circuit.digest();
    for scalar in
      [vec![0, 0], model_tests::strings(65), model_tests::strings(512)]
    {
      let bytes = if kind == GrammarKind::Program {
        model_tests::program(Some(&scalar), 1)
      } else {
        model_tests::transport(kind, &scalar)
      };
      witness(&s, &bytes, context);
      assert_eq!(s.shape.circuit.digest(), identity);
    }
  }
}

#[test]
fn whole_buffer_constraints_require_genuine_start_eof_context_and_step_capacity()
 {
  let s = setup(GrammarKind::Program);
  let program = model_tests::program(None, 1);
  let rejects = |bytes: &[u8], change: &dyn Fn(&mut Vec<F128>)| {
    let mut private = hash_tests::private_input(CAPACITY, bytes);
    private.extend([F128::ZERO; 15]);
    change(&mut private);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[])
      }))
      .is_err(),
      "actual fixed wiring must reject malformed private data"
    );
  };
  for end in [0, 12, program.len() - 1] {
    rejects(&program[..end], &|_| {});
  }
  let mut trailing = program.clone();
  trailing.push(0);
  rejects(&trailing, &|_| {});
  rejects(&program, &|private| private[65] = F128::ONE);
  rejects(&program, &|private| private[0].hi = 1);
  rejects(&program, &|private| private[0].lo = 1025);
  rejects(&model_tests::program(Some(&model_tests::strings(900)), 1), &|_| {});
  let bad_utf8 = model_tests::program(Some(&[1, 1, 255]), 1);
  rejects(&bad_utf8, &|_| {});
}

#[test]
#[ignore = "real source-bound whole-grammar proofs, isolated verification and locally recomputed wiring attacks"]
fn whole_grammar_proofs_verify_without_source_and_reject_recomputed_substitutions()
 {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let p = model_tests::program(None, 1);
  let parsed =
    model_tests::Model::new(model_tests::config(GrammarKind::Program), false)
      .parse(&p, [F128::ZERO; 15], STEPS)
      .unwrap();
  let context = model_tests::context(&parsed.state);
  let s = setup(GrammarKind::Program);
  let (w, expected) = witness(&s, &p, [F128::ZERO; 15]);
  let honest = prove(GrammarKind::Program, &s, &w, &expected, Attack::None);
  assert!(isolated(GrammarKind::Program, &expected, &honest));
  for attack in [
    Attack::RequestState,
    Attack::SourceBuffer,
    Attack::MergeDecoder,
    Attack::CompressionCounter,
  ] {
    let proof = prove(GrammarKind::Program, &s, &w, &expected, attack);
    assert!(!isolated(GrammarKind::Program, &expected, &proof));
  }
  let mut wide = vec![0];
  wide.extend(vec![255; 585]);
  wide.push(1);
  let mut bytes = vec![6];
  model_tests::nat(&mut bytes, 800);
  bytes.extend((0..800).map(|i| i as u8));
  for scalar in
    [wide, model_tests::strings(65), model_tests::strings(512), bytes]
  {
    let bytes = model_tests::program(Some(&scalar), 1);
    let (w, expected) = witness(&s, &bytes, [F128::ZERO; 15]);
    let proof = prove(GrammarKind::Program, &s, &w, &expected, Attack::None);
    assert!(isolated(GrammarKind::Program, &expected, &proof));
    if scalar[0] <= 1 && scalar.len() < 600 {
      let attack = if scalar[0] == 0 {
        Attack::NaturalBytes
      } else {
        Attack::FinishString
      };
      if scalar[0] == 0 || scalar.len() < 100 {
        let proof = prove(GrammarKind::Program, &s, &w, &expected, attack);
        assert!(!isolated(GrammarKind::Program, &expected, &proof));
      }
    }
  }
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let s = setup(kind);
    let bytes = model_tests::transport(kind, &model_tests::strings(35));
    let (w, expected) = witness(&s, &bytes, context);
    let proof = prove(kind, &s, &w, &expected, Attack::None);
    assert!(isolated(kind, &expected, &proof));
  }
  let branching = model_tests::branching_program();
  let (branch_witness, branch_expected) =
    witness(&s, &branching, [F128::ZERO; 15]);
  let proof = prove(
    GrammarKind::Program,
    &s,
    &branch_witness,
    &branch_expected,
    Attack::None,
  );
  assert!(isolated(GrammarKind::Program, &branch_expected, &proof));
  for at in [0, 2, 17, 17 + 27] {
    let mut wrong = expected.clone();
    wrong[at].lo ^= 1;
    assert!(
      verify(
        GrammarKind::Program,
        &wrong,
        &honest,
        domain(GrammarKind::Program)
      )
      .is_err()
    );
  }
  assert!(
    verify(GrammarKind::Program, &expected, &honest, b"wrong dispatch domain")
      .is_err()
  );
  for at in [0, 8] {
    let mut bad = honest.clone();
    bad[at] ^= 1;
    assert!(
      verify(
        GrammarKind::Program,
        &expected,
        &bad,
        domain(GrammarKind::Program)
      )
      .is_err()
    );
  }
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(
    verify(
      GrammarKind::Program,
      &expected,
      &trailing,
      domain(GrammarKind::Program)
    )
    .is_err()
  );
  assert!(
    verify(
      GrammarKind::Program,
      &expected[..44],
      &honest,
      domain(GrammarKind::Program)
    )
    .is_err()
  );
}
