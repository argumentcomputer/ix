//! Source-bound instruction/reference proofs with isolated verification.
use super::{
  super::{
    dispatch::*,
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
const OUTPUTS: usize = 30; // root[2], complete final grammar[28]
const MAGIC: [u8; 8] = *b"IXFREF00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const DOMAIN: &[u8] =
  b"ix:ixby:ixbf-program-references:bytes1024:steps32:nat4096:c2:f2:b2:v0";
const CHILD: &str = "IXBY_REFERENCES_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::references::proof_tests::source_bound_references_verify_in_isolation_and_reject_recomputed_substitutions";

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
struct Emission {
  slots: ProgramReferenceSlots,
  hash: BoundedBlake3,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots =
    ProgramReferenceSlots::declare(&mut b, NU, natural(), capacity()).unwrap();
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
  for word in checked.registry().grammar().0 {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  Emission { slots, hash, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  DecodedCall,
  TailCallee,
  Owner,
  FrameMetadata,
  ConstructorArity,
  CalleeArity,
  AlternativeCarry,
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
fn alter_reference(
  g: &ReferenceGate,
  rows: &mut [ReferenceRow],
  attack: Attack,
) {
  let op = match attack {
    Attack::DecodedCall
    | Attack::TailCallee
    | Attack::Owner
    | Attack::AlternativeCarry
    | Attack::InactiveMetadata => ReferenceOp::Request,
    Attack::FrameMetadata | Attack::ConstructorArity | Attack::CalleeArity => {
      ReferenceOp::Check
    },
    _ => return,
  };
  if g.op() != op {
    return;
  }
  let row = rows
    .iter_mut()
    .find(|r| match attack {
      Attack::DecodedCall => {
        r.0[1].lo as u8 == grammar::Phase::Operation as u8
          && r.0[FIELDS] == F128::new(5, 0)
      },
      Attack::TailCallee => {
        r.0[1].lo as u8 == grammar::Phase::OperandCount as u8
          && r.0[STATE] == F128::new(2, 0)
      },
      Attack::Owner => {
        r.0[1].lo as u8 == grammar::Phase::Target as u8
          && r.0[grammar::FUNCTION_INDEX] == F128::new(2, 0)
      },
      Attack::AlternativeCarry => {
        r.0[1].lo as u8 == grammar::Phase::Alternative as u8
          && r.0[STATE + 2] == F128::ONE
      },
      Attack::InactiveMetadata => r.0[TAG] == F128::new(17, 0),
      Attack::FrameMetadata => r.0[BLOCK_ENABLE] == F128::ONE,
      Attack::ConstructorArity => r.0[CONSTRUCT] == F128::ONE,
      Attack::CalleeArity => {
        r.0[FUNCTION_ENABLE] == F128::ONE && r.0[PARTIAL] == F128::ZERO
      },
      _ => false,
    })
    .expect("fixture exercises the attacked reference");
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::DecodedCall => row.0[FIELDS + 2].lo ^= 1,
    Attack::TailCallee => row.0[STATE + 1].lo ^= 1,
    Attack::Owner => row.0[grammar::FUNCTION_INDEX] = F128::ONE,
    Attack::AlternativeCarry => row.0[STATE + 2] = F128::ZERO,
    Attack::InactiveMetadata => row.0[grammar::FUEL].lo ^= 1,
    Attack::FrameMetadata => {
      row.0[LOCALS].lo += 1;
      row.0[BLOCK].lo += 1;
    },
    Attack::ConstructorArity => {
      row.0[ARGUMENTS].lo += 1;
      row.0[CTOR + 4].lo += 1;
    },
    Attack::CalleeArity => {
      row.0[ARGUMENTS].lo += 1;
      row.0[FUNCTION].lo += 1;
    },
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), &row.0, &after);
  if op == ReferenceOp::Check || attack == Attack::InactiveMetadata {
    assert_eq!(before, after, "all local outputs preserved");
  } else {
    assert_ne!(before, after, "new outputs are recomputed");
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
  let dispatch = emission.slots.registry_slots().dispatch();
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
  for op in ReferenceOp::ALL {
    driver!(
      emission.slots.slot(op),
      ReferenceGate::new(NU, capacity(), op).unwrap(),
      ReferenceGate,
      alter_reference
    );
  }
  for op in RegistryOp::ALL {
    driver!(
      emission.slots.registry_slots().slot(op),
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
  assert_eq!(drivers.len(), 37);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 65);
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
    "reference proof {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify(expected: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "reference proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.revision == 0,
    "reference proof envelope"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical reference proof");
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
  .map_err(|e| anyhow::anyhow!("reference proof rejected: {e:?}"))?;
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
    "reference verifier input size"
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
  let state = test_parse_program(&fixture.bytes, STEPS).unwrap();
  let private = hash_tests::private_input(BYTES, &fixture.bytes);
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(&fixture.bytes).to_vec();
  expected.extend(state);
  assert_eq!(w.public, s.emission.public.instantiate(&expected).unwrap());
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    17
  );
  for op in ReferenceOp::ALL {
    assert_eq!(w.rows::<ReferenceGate>(s.emission.slots.slot(op)).len(), STEPS);
  }
  for op in RegistryOp::ALL {
    assert_eq!(
      w.rows::<RegistryGate>(s.emission.slots.registry_slots().slot(op)).len(),
      if op == RegistryOp::Finish { 1 } else { STEPS }
    );
  }
  (w, expected)
}

#[test]
fn complete_reference_shape_is_source_independent_and_covers_all_instruction_forms()
 {
  let mut count = CountingEmitter::new();
  let emission = emit(&mut count);
  let s = setup();
  count.ensure_matches(&s.shape).unwrap();
  assert_eq!(emission.inputs, s.emission.inputs);
  assert_eq!(emission.public, s.emission.public);
  let identity = s.shape.circuit.digest();
  let mut instructions = [false; 8];
  let mut operations = [false; 8];
  for (name, spec) in fixtures::corpus() {
    let fixture = fixtures::encode(&spec);
    let artifact = crate::ixby::ixbf::decode_program(
      &fixture.bytes,
      crate::ixby::ixbf::DecodeLimits::default(),
    )
    .unwrap_or_else(|e| panic!("{name}: {e:#}"));
    assert_eq!(artifact.encode(), fixture.bytes);
    let (w, _) = witness(&s, &fixture);
    for r in
      w.rows::<ReferenceGate>(s.emission.slots.slot(ReferenceOp::Request))
    {
      if r.0[TAG] == F128::new(5, 0) {
        instructions[r.0[FIELDS + 1].lo as usize] = true;
      }
      if r.0[TAG] == F128::new(12, 0) {
        operations[r.0[FIELDS].lo as usize] = true;
      }
    }
    assert_eq!(s.shape.circuit.digest(), identity);
  }
  assert_eq!(instructions, [true; 8]);
  assert_eq!(operations, [true; 8]);
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  eprintln!(
    "reference census: tables={} M={} private={} public={}",
    s.drivers.len(),
    union.dense_m(),
    s.emission.inputs.private_words(),
    OUTPUTS
  );
}

#[test]
fn complete_reference_checks_reject_grammar_valid_bad_arities_frames_and_duplicate_alternatives()
 {
  let s = setup();
  registry::proof_tests::assert_registered(
    &fixtures::invalid()
      .iter()
      .map(|(_, spec)| fixtures::encode(spec))
      .collect::<Vec<_>>(),
  );
  for (name, spec) in fixtures::invalid() {
    let fixture = fixtures::encode(&spec);
    test_parse_program(&fixture.bytes, STEPS)
      .unwrap_or_else(|e| panic!("{name}: {e:#}"));
    assert!(
      crate::ixby::ixbf::decode_program(
        &fixture.bytes,
        crate::ixby::ixbf::DecodeLimits::default()
      )
      .is_err(),
      "native validator must reject {name}"
    );
    let private = hash_tests::private_input(BYTES, &fixture.bytes);
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
#[ignore = "real source-bound reference proofs, isolated verification and recomputed wiring attacks"]
fn source_bound_references_verify_in_isolation_and_reject_recomputed_substitutions()
 {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let s = setup();
  let mut first = None;
  for (name, spec) in fixtures::corpus() {
    let fixture = fixtures::encode(&spec);
    let (w, expected) = witness(&s, &fixture);
    let proof = prove(&s, &w, &expected, Attack::None);
    isolated(&expected, &proof).unwrap();
    eprintln!("fresh reference proof verified {name}");
    if first.is_none() {
      first = Some((expected.clone(), proof));
    }
    let attacks: &[Attack] = match name {
      "call" => {
        &[Attack::DecodedCall, Attack::FrameMetadata, Attack::CalleeArity]
      },
      "construct" => &[Attack::ConstructorArity],
      "forward-tail" => &[Attack::TailCallee],
      "owned-target" => &[Attack::Owner],
      "alternatives" => &[Attack::AlternativeCarry],
      "return" => &[Attack::InactiveMetadata, Attack::SourceBuffer],
      _ => &[],
    };
    for &attack in attacks {
      let proof = prove(&s, &w, &expected, attack);
      let failure = isolated(&expected, &proof).unwrap_err();
      assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
      eprintln!("fresh reference verifier rejected {attack:?} at Wiring");
    }
  }
  let (expected, honest) = first.unwrap();
  for at in [0, 1, 2, 2 + grammar::FUEL, 2 + grammar::ENTRY_ARITY] {
    let mut wrong = expected.clone();
    wrong[at].lo ^= 1;
    assert!(verify(&wrong, &honest, DOMAIN).is_err());
  }
  assert!(
    verify(
      &expected,
      &honest,
      b"ix:ixby:ixbf-program-registry:bytes1024:steps32:nat4096:c2:f2:b2:v0"
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
  wrong[0..8].copy_from_slice(b"IXFREG00");
  assert!(verify(&expected, &wrong, DOMAIN).is_err());
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(verify(&expected, &trailing, DOMAIN).is_err());
  assert!(verify(&expected[..OUTPUTS - 1], &honest, DOMAIN).is_err());
  assert!(verify(&expected, &honest[..honest.len() - 1], DOMAIN).is_err());
}
