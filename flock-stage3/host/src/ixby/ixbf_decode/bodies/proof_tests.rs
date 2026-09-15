//! Source-bound complete typed executable-body proofs with isolated verification.
use super::tests as body_tests;
use super::{
  super::{
    dispatch::*,
    references::{ReferenceGate, ReferenceOp},
    registry::{RegistryGate, RegistryOp},
    source::*,
    *,
  },
  *,
};
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
const BYTES: usize = 1024;
const OUTPUTS: usize = 105; // root2, grammar28, query13, typed results62
const MAGIC: [u8; 8] = *b"IXFBOD00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const DOMAIN: &[u8] =
  b"ix:ixby:ixbf-bodies:bytes1024:steps32:nat4096:c2:f2:b2:o3:v0";
const CHILD: &str = "IXBY_BODIES_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::bodies::proof_tests::source_bound_bodies_verify_in_isolation_and_reject_recomputed_substitutions";

fn capacity() -> RegistryCapacity {
  RegistryCapacity::new(2, 2, 2).unwrap()
}
fn natural() -> NaturalCapacity {
  NaturalCapacity::new(4096).unwrap()
}
fn body_capacity() -> BodyCapacity {
  BodyCapacity::new(capacity(), natural(), 3).unwrap()
}
fn window_gate() -> SourceWindowGate {
  SourceWindowGate::new(
    NU,
    SourceCapacity::new(
      0,
      DispatchConfig { kind: GrammarKind::Program, natural: natural() }
        .window_bytes(),
    )
    .unwrap(),
  )
  .unwrap()
}
struct Emission {
  slots: ProgramBodySlots,
  hash: BoundedBlake3,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = ProgramBodySlots::declare(&mut b, NU, body_capacity()).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let window = b.slot(window_gate());
  let zero = b.fixed_public_input(F128::ZERO);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  for word in hash.hash(&mut b, length, &bytes) {
    b.publish(word);
  }
  let mut state = slots.initialize(&mut b, length);
  for _ in 0..STEPS {
    state = slots.step(&mut b, state, |b, cursor, take| {
      let mut input = vec![cursor, take];
      input.extend_from_slice(&bytes);
      input.extend_from_slice(&bytes);
      let mut out = b.gate(window, &input);
      b.connect(out.pop().unwrap(), zero);
      SourceReadWires { file_length: out[0], words: out[4..].to_vec() }
    });
  }
  let checked = slots.finish(&mut b, state);
  for word in checked.references().registry().grammar().0 {
    b.publish(word);
  }
  let query: Vec<_> = (0..13).map(|_| b.input()).collect();
  for &word in &query {
    b.publish(word);
  }
  let results = [
    slots.function(&mut b, &checked, query[0], query[1]),
    slots.block(&mut b, &checked, query[2], query[3], query[4]),
    slots.operand(&mut b, &checked, query[5..9].try_into().unwrap()),
    slots.alternative(&mut b, &checked, query[9..13].try_into().unwrap()),
  ];
  for read in results {
    for word in read.fields {
      b.publish(word);
    }
  }
  let (inputs, public) = b.finish();
  Emission { slots, hash, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Operation,
  TailCallee,
  Owner,
  Natural,
  OperandOrder,
  Target,
  NextControl,
  ScalarCarry,
  CaptureCarry,
  FinishValue,
  FinishSpan,
  ReadAddress,
  ReadPayload,
  InactiveMetadata,
  SourceBuffer,
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
fn values<G: GateType<Hint = ()>>(g: &G, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(input, &(), &mut out);
  out
}
fn alter_body(g: &BodyGate, rows: &mut [BodyRow], attack: Attack) {
  let op = match attack {
    Attack::CaptureCarry => BodyOp::Capture,
    Attack::FinishValue | Attack::FinishSpan => BodyOp::Finish,
    Attack::ReadAddress => BodyOp::ReadBlock,
    Attack::ReadPayload => BodyOp::ReadOperand,
    Attack::None | Attack::SourceBuffer => return,
    _ => BodyOp::Step,
  };
  if g.op() != op {
    return;
  }
  let c = g.capacity();
  let s = c.state();
  let at = s + CONTROL_WORDS;
  let r = c.block_words();
  let row = rows
    .iter_mut()
    .find(|r| match attack {
      Attack::Operation => r.0[1].lo as u8 == grammar::Phase::Operation as u8,
      Attack::TailCallee => {
        r.0[1].lo as u8 == grammar::Phase::FunctionIndex as u8
      },
      Attack::Owner => {
        r.0[1].lo as u8 == grammar::Phase::Target as u8
          && r.0[grammar::FUNCTION_INDEX] == F128::new(2, 0)
      },
      Attack::Natural | Attack::NextControl | Attack::ScalarCarry => {
        r.0[1].lo as u8 == grammar::Phase::Natural as u8
      },
      Attack::OperandOrder => {
        r.0[1].lo as u8 == grammar::Phase::Operand as u8
          && r.0[at + OPERANDS] == F128::new(2, 0)
      },
      Attack::Target => r.0[1].lo as u8 == grammar::Phase::Target as u8,
      Attack::CaptureCarry => {
        r.0[2] == F128::ZERO && r.0[2 + c.block_words()] == F128::ONE
      },
      Attack::InactiveMetadata => r.0[TAG] == F128::new(17, 0),
      _ => true,
    })
    .unwrap_or_else(|| panic!("fixture exercises {op:?} {attack:?}"));
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::Operation => row.0[FIELDS + 2].lo ^= 1,
    Attack::TailCallee | Attack::Target => row.0[FIELDS].lo ^= 1,
    Attack::Owner => {
      row.0[grammar::FUNCTION_INDEX] = F128::ONE;
      row.0[s] = F128::ZERO;
    },
    Attack::Natural => row.0[NAT].lo ^= 1,
    Attack::NextControl => {
      row.0[NEXT_CONTROL] = F128::new(grammar::Phase::Natural as u64, 0)
    },
    Attack::ScalarCarry => row.0[s + 3].lo += 1,
    Attack::OperandOrder => {
      for i in 0..c.operand_words() {
        row.0.swap(
          at + HEADER_WORDS + i,
          at + HEADER_WORDS + c.operand_words() + i,
        );
      }
    },
    Attack::CaptureCarry => row.0[2 + r + LOCALS].lo ^= 1,
    Attack::FinishValue => {
      row.0[28
        + c.state_words()
        + c.registry.words()
        + HEADER_WORDS
        + O_MAGNITUDE]
        .lo ^= 1
    },
    Attack::FinishSpan => {
      row.0
        [28 + c.state_words() + c.registry.words() + HEADER_WORDS + O_SPAN]
        .lo += 1
    },
    Attack::ReadAddress => row.0[2].lo ^= 1,
    Attack::ReadPayload => {
      row.0[4
        + c.registry.functions() * FUNCTION_WORDS
        + HEADER_WORDS
        + O_MAGNITUDE]
        .lo ^= 1
    },
    Attack::InactiveMetadata => row.0[grammar::FUEL].lo ^= 1,
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO), "{attack:?}");
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), &row.0, &after);
  if attack == Attack::InactiveMetadata {
    assert_eq!(before, after);
  } else {
    assert_ne!(before, after, "{attack:?} recomputes outputs");
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
  let row = rows[1].test_inputs_mut();
  assert!(row[0].lo > 0);
  let before = values(g, row);
  assert_eq!(before.last(), Some(&F128::ZERO));
  row[2].lo ^= 1;
  assert_eq!(
    values(g, row),
    before,
    "unused source byte preserves all local outputs"
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

struct Setup {
  shape: CircuitShape,
  emission: Emission,
  drivers: Vec<Box<dyn Driver>>,
}
fn setup() -> Setup {
  let mut b = ShapeBuilder::new(NU);
  let emission = emit(&mut b);
  let shape = b.finish().unwrap();
  let dispatch = emission.slots.reference_slots().registry_slots().dispatch();
  let config = dispatch.config();
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
  for op in BodyOp::ALL {
    driver!(
      emission.slots.slot(op),
      BodyGate::new(NU, body_capacity(), op).unwrap(),
      BodyGate,
      alter_body
    );
  }
  for op in ReferenceOp::ALL {
    driver!(
      emission.slots.reference_slots().slot(op),
      ReferenceGate::new(NU, capacity(), op).unwrap(),
      ReferenceGate,
      untouched::<ReferenceGate>
    );
  }
  for op in RegistryOp::ALL {
    driver!(
      emission.slots.reference_slots().registry_slots().slot(op),
      RegistryGate::new(NU, capacity(), op).unwrap(),
      RegistryGate,
      untouched::<RegistryGate>
    );
  }
  for op in DispatchOp::ALL {
    driver!(
      dispatch.control_slot(op),
      DispatchGate::new(NU, config, op).unwrap(),
      DispatchGate,
      untouched::<DispatchGate>
    );
  }
  for kind in RecordKind::ALL {
    driver!(
      dispatch.record_slot(kind),
      RecordDecodeGate::new(NU, kind).unwrap(),
      RecordDecodeGate,
      untouched::<RecordDecodeGate>
    );
  }
  driver!(
    dispatch.header_slot(),
    HeaderDecodeGate::new(NU).unwrap(),
    HeaderDecodeGate,
    untouched::<HeaderDecodeGate>
  );
  driver!(
    dispatch.natural_slot(),
    NaturalDecodeGate::new(NU, config.natural).unwrap(),
    NaturalDecodeGate,
    untouched::<NaturalDecodeGate>
  );
  driver!(
    dispatch.natural_limit_slot(),
    NaturalLimitGate::new(NU, config.natural).unwrap(),
    NaturalLimitGate,
    untouched::<NaturalLimitGate>
  );
  driver!(
    dispatch.payload_slot(),
    PayloadCursorGate::new(NU).unwrap(),
    PayloadCursorGate,
    untouched::<PayloadCursorGate>
  );
  driver!(
    dispatch.utf8_slot(),
    Utf8ChunkGate::new(NU).unwrap(),
    Utf8ChunkGate,
    untouched::<Utf8ChunkGate>
  );
  driver!(
    dispatch.grammar_slot(),
    GrammarStepGate::new(NU, GrammarKind::Program).unwrap(),
    GrammarStepGate,
    untouched::<GrammarStepGate>
  );
  driver!(emission.window, window_gate(), SourceWindowGate, alter_window);
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
    alter: untouched::<Blake3Gate>,
  }));
  drivers.sort_by_key(|d| shape.registry_slot(d.slot()));
  assert_eq!(drivers.len(), 44);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 78);
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, drivers }
}
fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert_eq!(m, 26, "pinned bounded body PCS geometry");
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
  revision: u8,
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
  s: &Setup,
  w: &CircuitWitness,
  expected: &[F128],
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
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
    .serialize(&Bundle { magic: MAGIC, revision: 0, commitment, proof })
    .unwrap();
  eprintln!(
    "body proof {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify(expected: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "body proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(bundle.magic == MAGIC && bundle.revision == 0, "body proof envelope");
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical body proof");
  let s = setup();
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
  .map_err(|e| anyhow::anyhow!("body proof rejected: {e:?}"))?;
  Ok(())
}
fn isolated(
  expected: &[F128],
  proof: &[u8],
) -> std::result::Result<(), String> {
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
  for word in expected {
    input.write_all(&word.lo.to_le_bytes()).unwrap();
    input.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  input.write_all(proof).unwrap();
  drop(input);
  let out = child.wait_with_output().unwrap();
  if out.status.success() {
    Ok(())
  } else {
    Err(String::from_utf8_lossy(&out.stderr).into_owned())
  }
}
fn child() -> Result<()> {
  let prefix = 16 * OUTPUTS;
  let mut input = Vec::new();
  std::io::stdin()
    .take(MAX_BYTES + prefix as u64 + 1)
    .read_to_end(&mut input)?;
  ensure!(
    (prefix..=prefix + MAX_BYTES as usize).contains(&input.len()),
    "body verifier input size"
  );
  let expected: Vec<_> = input[..prefix]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|w| crate::hash::pack_bytes(w))
    .collect();
  verify(&expected, &input[prefix..], DOMAIN)
}

fn witness(
  s: &Setup,
  fixture: &fixtures::Fixture,
) -> (CircuitWitness, Vec<F128>) {
  let state = test_parse_program(&fixture.source.bytes, STEPS).unwrap();
  let query = fixture.queries(body_capacity());
  let mut private = hash_tests::private_input(BYTES, &fixture.source.bytes);
  private.extend(query);
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(&fixture.source.bytes).to_vec();
  expected.extend(state);
  expected.extend(query);
  expected.extend(fixture.results(body_capacity(), &query));
  assert_eq!(
    w.public,
    s.emission.public.instantiate(&expected).unwrap(),
    "{}",
    fixture.name
  );
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    17
  );
  (w, expected)
}
fn attacks(name: &str) -> &'static [Attack] {
  match name {
    "call" => &[Attack::Operation],
    "forward-tail" => &[Attack::TailCallee],
    "owned-target" => &[Attack::Owner],
    "branch" => &[Attack::Target],
    "ordered-mixed" => &[Attack::OperandOrder, Attack::ReadAddress],
    "zero" => &[
      Attack::Natural,
      Attack::NextControl,
      Attack::ScalarCarry,
      Attack::FinishValue,
      Attack::FinishSpan,
      Attack::ReadPayload,
    ],
    "return" => {
      &[Attack::CaptureCarry, Attack::InactiveMetadata, Attack::SourceBuffer]
    },
    _ => &[],
  }
}

#[test]
fn complete_body_shape_matches_native_records_for_every_instruction_operation_and_scalar()
 {
  use crate::sizing::CountedGate;
  let mut count = CountingEmitter::new();
  let emission = emit(&mut count);
  let s = setup();
  count.ensure_matches(&s.shape).unwrap();
  assert_eq!(emission.inputs, s.emission.inputs);
  assert_eq!(emission.public, s.emission.public);
  let identity = s.shape.circuit.digest();
  let gates: Vec<_> = BodyOp::ALL
    .into_iter()
    .map(|op| BodyGate::new(NU, body_capacity(), op).unwrap())
    .collect();
  let mut instructions = [false; 8];
  let mut operations = [false; 8];
  let mut primitives = [false; 45];
  let mut scalars = [false; 7];
  let fixtures = fixtures::corpus(body_capacity());
  for f in &fixtures {
    eprintln!("body differential {}", f.name);
    let (w, _) = witness(&s, f);
    for g in &gates {
      let rows = w.rows::<BodyGate>(s.emission.slots.slot(g.op()));
      assert_eq!(
        rows.len(),
        if matches!(g.op(), BodyOp::Step | BodyOp::Capture) {
          STEPS
        } else {
          1
        }
      );
      for row in rows {
        let out = body_tests::checked(g, &row.0);
        assert_eq!(out.last(), Some(&F128::ZERO));
        if g.op() == BodyOp::Finish {
          assert_eq!(&out[..out.len() - 1], f.bank, "{} complete bank", f.name);
        }
        if g.op() == BodyOp::Step {
          if row.0[TAG] == F128::new(5, 0) {
            instructions[row.0[FIELDS + 1].lo as usize] = true;
          }
          if row.0[TAG] == F128::new(12, 0) {
            operations[row.0[FIELDS].lo as usize] = true;
            if row.0[FIELDS] == F128::ONE {
              primitives[row.0[FIELDS + 1].lo as usize] = true;
            }
          }
          if row.0[TAG] == F128::new(11, 0) {
            scalars[row.0[FIELDS].lo as usize] = true;
          }
        }
      }
      for &attack in attacks(&f.name) {
        alter_body(g, &mut rows.to_vec(), attack);
      }
    }
    assert_eq!(s.shape.circuit.digest(), identity);
  }
  assert_eq!(instructions, [true; 8]);
  assert_eq!(operations, [true; 8]);
  assert_eq!(primitives, [true; 45]);
  assert_eq!(scalars, [true; 7]);
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  eprintln!(
    "body census: fixtures={} tables={} M={} private={} public={}",
    fixtures.len(),
    s.drivers.len(),
    union.dense_m(),
    s.emission.inputs.private_words(),
    OUTPUTS
  );
  for g in &gates {
    eprintln!(
      "body {:?}: input={} output={} useful={} k={}",
      g.op(),
      g.input_count(),
      g.output_count(),
      g.plan().useful_bits(),
      g.plan().k()
    );
  }
}

#[test]
fn complete_bodies_reject_invalid_references_and_physical_operand_overflow() {
  let s = setup();
  let mut programs: Vec<_> = references::test_invalid_programs()
    .into_iter()
    .map(|(name, spec)| (name, registry::fixtures::encode(&spec), false))
    .collect();
  let mut spec = fixtures::base();
  spec.functions[0].arity = 4;
  spec.functions[0].blocks[0] = (4, vec![3, 4, 2, 2, 2, 2]);
  programs.push(("four-operands", registry::fixtures::encode(&spec), true));
  spec = fixtures::base();
  spec.functions[0].blocks[0].1 = vec![4, 2, 3, 2, 2, 2];
  programs.push((
    "closure-plus-three",
    registry::fixtures::encode(&spec),
    true,
  ));
  for (name, fixture, native_valid) in programs {
    test_parse_program(&fixture.bytes, STEPS)
      .unwrap_or_else(|e| panic!("{name}: {e:#}"));
    assert_eq!(
      crate::ixby::ixbf::decode_program(
        &fixture.bytes,
        crate::ixby::ixbf::DecodeLimits::default()
      )
      .is_ok(),
      native_valid,
      "{name}"
    );
    let mut private = hash_tests::private_input(BYTES, &fixture.bytes);
    private.extend([F128::ZERO; 13]);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| s
        .shape
        .run(&s.emission.inputs.assign(&private).unwrap(), &[])))
      .is_err(),
      "circuit must reject {name}"
    );
  }
}

#[test]
#[ignore = "real complete body proofs, isolated verification and locally recomputed wiring attacks"]
fn source_bound_bodies_verify_in_isolation_and_reject_recomputed_substitutions()
{
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let s = setup();
  let mut first = None;
  for fixture in
    fixtures::corpus(body_capacity()).into_iter().filter(|f| f.prove)
  {
    let (w, expected) = witness(&s, &fixture);
    let proof = prove(&s, &w, &expected, Attack::None);
    isolated(&expected, &proof).unwrap();
    eprintln!("fresh body proof verified {}", fixture.name);
    if first.is_none() {
      first = Some((expected.clone(), proof));
    }
    for &attack in attacks(&fixture.name) {
      let proof = prove(&s, &w, &expected, attack);
      let failure = isolated(&expected, &proof).unwrap_err();
      assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
      eprintln!("fresh body verifier rejected {attack:?} at Wiring");
    }
  }
  let (expected, honest) = first.unwrap();
  for at in [
    0,
    1,
    2,
    2 + grammar::FUEL,
    2 + grammar::ENTRY_ARITY,
    30,
    34,
    38,
    42,
    43,
    47,
    48 + SPAN,
    62 + O_MAGNITUDE,
    OUTPUTS - 1,
  ] {
    let mut wrong = expected.clone();
    wrong[at].lo ^= 1;
    assert!(verify(&wrong, &honest, DOMAIN).is_err(), "expected word {at}");
  }
  assert!(
    verify(
      &expected,
      &honest,
      b"ix:ixby:ixbf-program-references:bytes1024:steps32:nat4096:c2:f2:b2:v0"
    )
    .is_err()
  );
  for at in [0, 8] {
    let mut wrong = honest.clone();
    wrong[at] ^= 1;
    assert!(verify(&expected, &wrong, DOMAIN).is_err());
  }
  let mut changed = honest.clone();
  *changed.last_mut().unwrap() ^= 1;
  assert!(verify(&expected, &changed, DOMAIN).is_err());
  let mut wrong = honest.clone();
  wrong[0..8].copy_from_slice(b"IXFREF00");
  assert!(verify(&expected, &wrong, DOMAIN).is_err());
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(verify(&expected, &trailing, DOMAIN).is_err());
  assert!(verify(&expected[..OUTPUTS - 1], &honest, DOMAIN).is_err());
  assert!(verify(&expected, &honest[..honest.len() - 1], DOMAIN).is_err());
}
