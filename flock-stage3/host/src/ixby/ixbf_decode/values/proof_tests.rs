//! Source-bound typed value forest proofs with isolated verification.
use super::{
  super::{
    dispatch::*,
    references::{ProgramReferenceSlots, ReferenceGate, ReferenceOp},
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
const OUTPUTS: usize = 208; // two digests, two grammars, summary, queries, typed reads
const MAGIC: [u8; 8] = *b"IXFVAL00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
fn domain(kind: GrammarKind) -> &'static [u8] {
  match kind {
    GrammarKind::Input => {
      b"ix:ixby:ixbf-values:input:bytes1024:steps32:nat4096:c2:f2:b2:n4:d4:v0"
    },
    GrammarKind::Output => {
      b"ix:ixby:ixbf-values:output:bytes1024:steps32:nat4096:c2:f2:b2:n4:d4:v0"
    },
    _ => panic!("transport setup kind"),
  }
}
const CHILD: &str = "IXBY_VALUES_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::values::proof_tests::source_bound_values_verify_in_isolation_and_reject_recomputed_substitutions";

fn capacity() -> RegistryCapacity {
  RegistryCapacity::new(2, 2, 2).unwrap()
}
fn natural() -> NaturalCapacity {
  NaturalCapacity::new(4096).unwrap()
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
fn config(kind: GrammarKind) -> ValueConfig {
  ValueConfig {
    kind,
    registry: capacity(),
    arena: ValueCapacity::new(4, 4, natural()).unwrap(),
  }
}
struct Emission {
  program: ProgramReferenceSlots,
  slots: ValueArenaSlots,
  hash: BoundedBlake3,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn source(
  b: &mut impl CircuitEmitter,
  window: SlotId,
  zero: flock_prover::circuit::builder::Wire,
  bytes: &[flock_prover::circuit::builder::Wire],
  cursor: flock_prover::circuit::builder::Wire,
  take: flock_prover::circuit::builder::Wire,
) -> SourceReadWires {
  let mut input = vec![cursor, take];
  input.extend(bytes);
  input.extend(bytes);
  let mut out = b.gate(window, &input);
  b.connect(out.pop().unwrap(), zero);
  SourceReadWires { file_length: out[0], words: out[4..].to_vec() }
}
fn emit(b: &mut impl CircuitEmitter, kind: GrammarKind) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let program =
    ProgramReferenceSlots::declare(&mut b, NU, natural(), capacity()).unwrap();
  let slots = ValueArenaSlots::declare(&mut b, NU, config(kind)).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let window = b.slot(window_gate());
  let zero = b.fixed_public_input(F128::ZERO);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  for w in hash.hash(&mut b, length, &bytes) {
    b.publish(w);
  }
  let mut state = program.initialize(&mut b, length);
  for _ in 0..STEPS {
    state = program.step(&mut b, state, |b, cursor, take| {
      source(b, window, zero, &bytes, cursor, take)
    });
  }
  let checked = program.finish(&mut b, state);
  for w in checked.registry().grammar().0 {
    b.publish(w);
  }
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  for w in hash.hash(&mut b, length, &bytes) {
    b.publish(w);
  }
  let mut state = slots.initialize(&mut b, length, &checked);
  for _ in 0..STEPS {
    state = slots.step(&mut b, state, |b, cursor, take| {
      source(b, window, zero, &bytes, cursor, take)
    });
  }
  let finished = slots.finish(&mut b, state);
  for w in finished.grammar().0 {
    b.publish(w);
  }
  for w in finished.summary() {
    b.publish(w);
  }
  let q: Vec<_> = (0..7)
    .map(|_| {
      let w = b.input();
      b.publish(w);
      w
    })
    .collect();
  let reads = [
    slots.node(&mut b, &finished, q[0], q[1]),
    slots.child(&mut b, &finished, q[2], q[3], q[4]),
    slots.root(&mut b, &finished, q[5], q[6]),
  ];
  for read in reads {
    b.publish(read.index);
    for w in read.record {
      b.publish(w);
    }
  }
  let (inputs, public) = b.finish();
  Emission { program, slots, hash, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  LinkIdentity,
  LinkBank,
  NodeMagnitude,
  NodeStart,
  NodeContext,
  CaptureCarry,
  FinishRecord,
  ReadAddress,
  ReadMetadata,
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
fn alter_value(g: &ValueGate, rows: &mut [ValueRow], attack: Attack) {
  let op = match attack {
    Attack::LinkIdentity | Attack::LinkBank => ValueOp::Link,
    Attack::NodeMagnitude | Attack::NodeStart | Attack::NodeContext => {
      ValueOp::Node
    },
    Attack::CaptureCarry => ValueOp::Capture,
    Attack::FinishRecord => ValueOp::Finish,
    Attack::ReadAddress | Attack::ReadMetadata => ValueOp::ReadNode,
    _ => return,
  };
  if g.op() != op {
    return;
  }
  let r = g.config.arena.record_words();
  let stride = g.config.arena.finished_record_words();
  let row = rows
    .iter_mut()
    .find(|row| match attack {
      Attack::LinkIdentity | Attack::LinkBank => {
        row.0[1] == F128::new(9, 0) && row.0[2] == F128::ONE
      },
      Attack::NodeMagnitude | Attack::NodeStart => {
        row.0[TAG] == F128::new(14, 0)
      },
      Attack::NodeContext => row.0[TAG] == F128::new(17, 0),
      Attack::CaptureCarry => row.0[0].lo >= 3,
      _ => true,
    })
    .expect("fixture exercises attacked value row");
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::LinkIdentity => {
      row.0[3].hi ^= 1u64 << 63;
      row.0[LINK_BANK + 7 + 1].hi ^= 1u64 << 63;
    },
    Attack::LinkBank => {
      let at = LINK_BANK
        + g.config.registry.constructors() * 7
        + g.config.registry.functions() * 5
        + 2;
      row.0[at].lo ^= 1;
    },
    Attack::NodeMagnitude => row.0[NAT].lo ^= 1,
    Attack::NodeStart => {
      row.0[NAT + g.config.arena.natural.magnitude_words() + 1].lo -= 1
    },
    Attack::NodeContext => row.0[grammar::ENTRY_ARITY].hi ^= 1,
    Attack::CaptureCarry => row.0[2 + r + 2 * r + MAGNITUDE].lo ^= 1,
    Attack::FinishRecord => row.0[33 + 2 * r + MAGNITUDE].lo ^= 1,
    Attack::ReadAddress => row.0[1] = F128::ZERO,
    Attack::ReadMetadata => {
      let selected = row.0[1].lo as usize;
      row.0[3 + selected * stride + r + 3].lo += 1;
    },
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO), "{attack:?}");
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), &row.0, &after);
  if matches!(
    attack,
    Attack::LinkIdentity | Attack::LinkBank | Attack::NodeContext
  ) {
    assert_eq!(before, after, "all local outputs preserved");
  } else {
    assert_ne!(before, after, "outputs are recomputed");
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
  kind: GrammarKind,
  drivers: Vec<Box<dyn Driver>>,
}
fn setup(kind: GrammarKind) -> Setup {
  let mut b = ShapeBuilder::new(NU);
  let emission = emit(&mut b, kind);
  let shape = b.finish().unwrap();
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
  for op in ValueOp::ALL {
    driver!(
      emission.slots.slot(op),
      ValueGate::new(NU, config(kind), op).unwrap(),
      ValueGate,
      alter_value
    );
  }
  for op in ReferenceOp::ALL {
    driver!(
      emission.program.slot(op),
      ReferenceGate::new(NU, capacity(), op).unwrap(),
      ReferenceGate,
      untouched::<ReferenceGate>
    );
  }
  for op in RegistryOp::ALL {
    driver!(
      emission.program.registry_slots().slot(op),
      RegistryGate::new(NU, capacity(), op).unwrap(),
      RegistryGate,
      untouched::<RegistryGate>
    );
  }
  for dispatch in
    [emission.program.registry_slots().dispatch(), emission.slots.dispatch()]
  {
    let config = dispatch.config();
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
      GrammarStepGate::new(NU, config.kind).unwrap(),
      GrammarStepGate,
      untouched::<GrammarStepGate>
    );
  }
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
  assert_eq!(drivers.len(), 69);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 137);
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, kind, drivers }
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
  let mut challenger = FsChallenger::with_chained_blake3(domain(s.kind));
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
    "value proof {attack:?}: M={} bytes={}",
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
    "value proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.revision == 0,
    "value proof envelope"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical value proof");
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
  .map_err(|e| anyhow::anyhow!("value proof rejected: {e:?}"))?;
  Ok(())
}
fn isolated(
  kind: GrammarKind,
  expected: &[F128],
  proof: &[u8],
) -> std::result::Result<(), String> {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, if kind == GrammarKind::Input { "input" } else { "output" })
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
    "value verifier input size"
  );
  let expected: Vec<_> = input[..prefix]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|w| crate::hash::pack_bytes(w))
    .collect();
  let kind = match std::env::var(CHILD)?.as_str() {
    "input" => GrammarKind::Input,
    "output" => GrammarKind::Output,
    _ => anyhow::bail!("approved transport setup"),
  };
  verify(kind, &expected, &input[prefix..], domain(kind))
}
fn witness(
  s: &Setup,
  fixture: &fixtures::Fixture,
) -> (CircuitWitness, Vec<F128>) {
  let program = test_parse_program(&fixture.program.bytes, STEPS).unwrap();
  let state =
    test_parse_transport(s.kind, &fixture.bytes, &program, STEPS).unwrap();
  let q = fixture.requests();
  let mut private = hash_tests::private_input(BYTES, &fixture.program.bytes);
  private.extend(hash_tests::private_input(BYTES, &fixture.bytes));
  private.extend(q);
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(&fixture.program.bytes).to_vec();
  expected.extend(program);
  expected.extend(hash_tests::expected(&fixture.bytes));
  expected.extend(state);
  expected.extend(fixture.summary);
  expected.extend(q);
  expected.extend(fixture.results(config(s.kind).arena, &q));
  assert_eq!(w.public, s.emission.public.instantiate(&expected).unwrap());
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    34
  );
  for op in ValueOp::ALL {
    assert_eq!(
      w.rows::<ValueGate>(s.emission.slots.slot(op)).len(),
      if matches!(op, ValueOp::Link | ValueOp::Node | ValueOp::Capture) {
        STEPS
      } else {
        1
      }
    );
  }
  (w, expected)
}

#[test]
fn complete_value_shapes_match_native_forests_scalars_and_independent_encodings()
 {
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let mut count = CountingEmitter::new();
    let emission = emit(&mut count, kind);
    let s = setup(kind);
    count.ensure_matches(&s.shape).unwrap();
    assert_eq!(emission.inputs, s.emission.inputs);
    assert_eq!(emission.public, s.emission.public);
    let identity = s.shape.circuit.digest();
    let mut scalar_tags = [false; 7];
    let mut value_tags = [false; 5];
    for (name, fixture) in fixtures::corpus(kind, config(kind).arena) {
      fixture.check_native(config(kind).arena);
      eprintln!("value witness {kind:?} {name}");
      let (w, _) = witness(&s, &fixture);
      for op in ValueOp::ALL {
        let g = ValueGate::new(NU, config(kind), op).unwrap();
        for row in w.rows::<ValueGate>(s.emission.slots.slot(op)) {
          let out = super::tests::checked(&g, &row.0);
          assert_eq!(out.last(), Some(&F128::ZERO));
          if op == ValueOp::Node && out[PACKET_RECORD + PRESENT] == F128::ONE {
            let tag = out[PACKET_RECORD + KIND].lo as usize;
            value_tags[tag] = true;
            if tag == 0 {
              scalar_tags[out[PACKET_RECORD + SCALAR].lo as usize] = true;
            }
          }
        }
      }
      assert_eq!(s.shape.circuit.digest(), identity);
    }
    assert_eq!(scalar_tags, [true; 7]);
    assert_eq!(value_tags, [true; 5]);
    let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
    eprintln!(
      "value census {kind:?}: tables={} M={} private={} public={}",
      s.drivers.len(),
      union.dense_m(),
      s.emission.inputs.private_words(),
      OUTPUTS
    );
  }
}

#[test]
fn complete_value_checks_reject_bad_references_and_enforce_physical_capacity() {
  use crate::ixby::ixbf;
  use fixtures::Value::*;
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let s = setup(kind);
    let a = config(kind).arena;
    let mut cases = Vec::new();
    let mut wrong = fixtures::encode(
      kind,
      a,
      &fixtures::spec(1),
      &[Constructor(0, vec![Erased])],
    );
    let start = wrong.records[0][SPAN].lo as usize;
    wrong.bytes[start + 1] ^= 1;
    cases.push(("undeclared-constructor", wrong, false, true));
    let mut spec = fixtures::spec(1);
    spec.constructors[1][4] = 3;
    cases.push((
      "constructor-child-count",
      fixtures::encode(kind, a, &spec, &[Constructor(1, vec![Erased, Erased])]),
      false,
      true,
    ));
    for (name, args) in [("saturated-pap", 1), ("oversaturated-pap", 2)] {
      cases.push((
        name,
        fixtures::encode(
          kind,
          a,
          &fixtures::spec(1),
          &[Pap(1, vec![Erased; args])],
        ),
        false,
        true,
      ));
    }
    let mut spec = fixtures::spec(1);
    spec.constructors[1][4] = 4;
    cases.push((
      "arena-node-capacity",
      fixtures::encode(kind, a, &spec, &[Constructor(1, vec![Erased; 4])]),
      true,
      true,
    ));
    let mut chain = Erased;
    for _ in 0..4 {
      chain = Constructor(0, vec![chain]);
    }
    cases.push((
      "arena-chain-capacity",
      fixtures::encode(kind, a, &fixtures::spec(1), &[chain]),
      true,
      true,
    ));
    if kind == GrammarKind::Input {
      cases.push((
        "program-entry-arity",
        fixtures::encode(kind, a, &fixtures::spec(2), &[Erased]),
        false,
        false,
      ));
    }
    for (name, f, native_ok, grammar_ok) in cases {
      let program =
        ixbf::decode_program(&f.program.bytes, ixbf::DecodeLimits::default())
          .unwrap();
      let native = if kind == GrammarKind::Input {
        ixbf::decode_input(&program, &f.bytes, ixbf::DecodeLimits::default())
          .is_ok()
      } else {
        ixbf::decode_output(&program, &f.bytes, ixbf::DecodeLimits::default())
          .is_ok()
      };
      assert_eq!(native, native_ok, "native {name}");
      let grammar = test_parse_program(&f.program.bytes, STEPS).unwrap();
      assert_eq!(
        test_parse_transport(kind, &f.bytes, &grammar, STEPS).is_ok(),
        grammar_ok,
        "grammar {name}"
      );
      let mut private = hash_tests::private_input(BYTES, &f.program.bytes);
      private.extend(hash_tests::private_input(BYTES, &f.bytes));
      private.extend([F128::ZERO; 7]);
      assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| s
          .shape
          .run(&s.emission.inputs.assign(&private).unwrap(), &[])))
        .is_err(),
        "circuit must reject {kind:?} {name}"
      );
    }
  }
}

#[test]
#[ignore = "real source-bound value proofs, isolated verification and recomputed wiring attacks"]
fn source_bound_values_verify_in_isolation_and_reject_recomputed_substitutions()
{
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let s = setup(kind);
    let mut first = None;
    for (name, fixture) in fixtures::corpus(kind, config(kind).arena) {
      let (w, expected) = witness(&s, &fixture);
      let proof = prove(&s, &w, &expected, Attack::None);
      isolated(kind, &expected, &proof).unwrap();
      eprintln!("fresh value proof verified {kind:?} {name}");
      if first.is_none() {
        first = Some((expected.clone(), proof));
      }
      let attacks: &[Attack] = if kind == GrammarKind::Input && name == "nested"
      {
        &[
          Attack::LinkIdentity,
          Attack::LinkBank,
          Attack::NodeMagnitude,
          Attack::NodeStart,
          Attack::NodeContext,
          Attack::CaptureCarry,
          Attack::FinishRecord,
          Attack::ReadAddress,
          Attack::ReadMetadata,
          Attack::SourceBuffer,
        ]
      } else {
        &[]
      };
      for &attack in attacks {
        let proof = prove(&s, &w, &expected, attack);
        let failure = isolated(kind, &expected, &proof).unwrap_err();
        assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
        eprintln!("fresh value verifier rejected {attack:?} at Wiring");
      }
    }
    let (expected, honest) = first.unwrap();
    for at in [
      0,
      1,
      2,
      2 + grammar::ENTRY_ARITY,
      30,
      31,
      32,
      32 + grammar::ENTRY_ARITY,
      60,
      61,
      62,
      63,
      64,
      70,
      OUTPUTS - 1,
    ] {
      let mut wrong = expected.clone();
      wrong[at].lo ^= 1;
      assert!(
        verify(kind, &wrong, &honest, domain(kind)).is_err(),
        "public word {at}"
      );
    }
    assert!(verify(kind,&expected,&honest,b"ix:ixby:ixbf-program-references:bytes1024:steps32:nat4096:c2:f2:b2:v0").is_err());
    let other = if kind == GrammarKind::Input {
      GrammarKind::Output
    } else {
      GrammarKind::Input
    };
    assert!(verify(other, &expected, &honest, domain(other)).is_err());
    for at in [0, 8, honest.len() - 1] {
      let mut wrong = honest.clone();
      wrong[at] ^= 1;
      assert!(verify(kind, &expected, &wrong, domain(kind)).is_err());
    }
    let mut wrong = honest.clone();
    wrong[..8].copy_from_slice(b"IXFREF00");
    assert!(verify(kind, &expected, &wrong, domain(kind)).is_err());
    let mut trailing = honest.clone();
    trailing.push(0);
    assert!(verify(kind, &expected, &trailing, domain(kind)).is_err());
    assert!(
      verify(kind, &expected[..OUTPUTS - 1], &honest, domain(kind)).is_err()
    );
    assert!(
      verify(kind, &expected, &honest[..honest.len() - 1], domain(kind))
        .is_err()
    );
  }
}
