//! Source-bound declaration/header proof class. This is not Exec admission.
//! Byte authentication and fixed dispatch precede all immutable registry reads.
use super::{
  super::{dispatch::*, source::*, *},
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
const OUTPUTS: usize = 55; // root[2], complete final grammar[28], queries[7], reads[18]
const MAGIC: [u8; 8] = *b"IXFREG00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const DOMAIN: &[u8] =
  b"ix:ixby:ixbf-program-registry:bytes1024:steps32:nat4096:c2:f2:b2:v0";
const CHILD: &str = "IXBY_REGISTRY_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::registry::proof_tests::source_bound_registries_verify_in_isolation_and_reject_recomputed_substitutions";

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
  slots: ProgramRegistrySlots,
  hash: BoundedBlake3,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots =
    ProgramRegistrySlots::declare(&mut b, NU, natural(), capacity()).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let window = b.slot(window_gate());
  let zero = b.fixed_public_input(F128::ZERO);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let queries: [_; 7] = std::array::from_fn(|_| b.input());
  for word in hash.hash(&mut b, length, &bytes) {
    b.publish(word);
  }
  let mut state = slots.initialize(&mut b, length);
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
      .0;
  }
  let registry = slots.finish(&mut b, state);
  for word in registry.grammar().0.into_iter().chain(queries) {
    b.publish(word);
  }
  let reads = [
    slots.constructor(&mut b, &registry, queries[0], queries[1]),
    slots.function(&mut b, &registry, queries[2], queries[3]),
    slots.block(&mut b, &registry, queries[4], queries[5], queries[6]),
  ];
  for read in reads {
    for word in read.fields.into_iter().chain([read.header_range]) {
      b.publish(word);
    }
  }
  let (inputs, public) = b.finish();
  Emission { slots, hash, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  CaptureFields,
  CaptureAddress,
  CaptureCarry,
  FinishState,
  ReadBank,
  ReadRequest,
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
fn alter_registry(g: &RegistryGate, rows: &mut [RegistryRow], attack: Attack) {
  let op = match attack {
    Attack::CaptureFields | Attack::CaptureAddress | Attack::CaptureCarry => {
      RegistryOp::Capture
    },
    Attack::FinishState => RegistryOp::Finish,
    Attack::ReadBank => RegistryOp::Function,
    Attack::ReadRequest => RegistryOp::Block,
    _ => return,
  };
  if g.op() != op {
    return;
  }
  let row = match attack {
    Attack::CaptureFields | Attack::CaptureAddress => {
      rows.iter_mut().find(|r| r.0[TAG] == F128::new(3, 0)).unwrap()
    },
    Attack::CaptureCarry => {
      rows.iter_mut().rev().find(|r| r.0[TAG] == F128::new(17, 0)).unwrap()
    },
    _ => &mut rows[0],
  };
  let before = values(g, &row.0);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::CaptureFields => row.0[FIELDS + 4].lo ^= 1,
    Attack::CaptureAddress => {
      assert_eq!(row.0[grammar::CTORS_LEFT], F128::new(2, 0));
      row.0[grammar::CTORS_LEFT] = F128::ONE;
      let fields = row.0[FIELDS..FIELDS + 5].to_vec();
      row.0[CAPTURE_BANK] = F128::ONE;
      row.0[CAPTURE_BANK + 1..CAPTURE_BANK + 6].copy_from_slice(&fields);
      row.0[CAPTURE_BANK + 1].lo ^= 64;
      row.0[CAPTURE_BANK + 6] = F128::new(row.0[0].lo - 1, row.0[0].lo);
    },
    Attack::CaptureCarry => row.0[CAPTURE_BANK + 5].lo ^= 1,
    Attack::FinishState => row.0[grammar::FUEL].lo ^= 1,
    Attack::ReadBank => row.0[READ_BANK + 1].lo ^= 1,
    Attack::ReadRequest => row.0[1].lo ^= 1,
    _ => unreachable!(),
  }
  let after = values(g, &row.0);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), &row.0, &after);
  if matches!(attack, Attack::FinishState | Attack::ReadBank) {
    assert_eq!(before, after, "all local outputs are preserved");
  } else {
    assert_ne!(before, after, "outputs are recomputed, not overwritten");
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
  let dispatch = emission.slots.dispatch();
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
  for op in RegistryOp::ALL {
    driver!(
      emission.slots.slot(op),
      RegistryGate::new(NU, capacity(), op).unwrap(),
      RegistryGate,
      alter_registry
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
  assert_eq!(drivers.len(), 35);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 72);
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
    "registry proof {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify(expected: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "registry proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.revision == 0,
    "registry proof envelope"
  );
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical registry proof");
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
  .map_err(|e| anyhow::anyhow!("registry proof rejected: {e:?}"))?;
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
    "registry verifier input size"
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
  queries: [F128; 7],
) -> (CircuitWitness, Vec<F128>) {
  let state = test_parse_program(&fixture.bytes, STEPS).unwrap();
  let mut private = hash_tests::private_input(BYTES, &fixture.bytes);
  private.extend(queries);
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(&fixture.bytes).to_vec();
  expected.extend(state);
  expected.extend(queries);
  expected.extend(fixture.results(&queries));
  assert_eq!(w.public, s.emission.public.instantiate(&expected).unwrap());
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    17
  );
  for op in RegistryOp::ALL {
    assert_eq!(
      w.rows::<RegistryGate>(s.emission.slots.slot(op)).len(),
      if op == RegistryOp::Capture { STEPS } else { 1 }
    );
  }
  let captures =
    w.rows::<RegistryGate>(s.emission.slots.slot(RegistryOp::Capture));
  let count = captures
    .iter()
    .filter(|r| r.0[COMMITTED] == F128::ONE && (3..=5).contains(&r.0[TAG].lo))
    .count();
  assert_eq!(count, fixture.headers.len());
  (w, expected)
}

#[test]
fn complete_registry_shape_is_proof_free_and_independent_of_image_and_read_requests()
 {
  let mut count = CountingEmitter::new();
  let emission = emit(&mut count);
  let s = setup();
  count.ensure_matches(&s.shape).unwrap();
  assert_eq!(emission.inputs, s.emission.inputs);
  assert_eq!(emission.public, s.emission.public);
  let identity = s.shape.circuit.digest();
  for spec in fixtures::corpus() {
    let fixture = fixtures::encode(&spec);
    let artifact = crate::ixby::ixbf::decode_program(
      &fixture.bytes,
      crate::ixby::ixbf::DecodeLimits::default(),
    )
    .unwrap();
    assert_eq!(artifact.encode(), fixture.bytes);
    assert_eq!(artifact.constructors().len(), spec.constructors.len());
    assert_eq!(artifact.functions().len(), spec.functions.len());
    for last in [false, true] {
      witness(&s, &fixture, fixture.requests(last));
    }
    assert_eq!(s.shape.circuit.digest(), identity);
  }
}

/// Reference negatives must pass the preceding source/grammar/header relation.
/// This runs the unchanged registry setup with all public lookups disabled.
pub(in crate::ixby::ixbf_decode) fn assert_registered(
  fixtures: &[fixtures::Fixture],
) {
  let s = setup();
  for fixture in fixtures {
    witness(&s, fixture, [F128::ZERO; 7]);
  }
}

#[test]
fn complete_registry_rejects_grammar_valid_duplicate_missing_owner_and_bad_entry_records()
 {
  let s = setup();
  let rejects = |spec: fixtures::Spec, native_accepts: bool| {
    let fixture = fixtures::encode(&spec);
    // These are complete canonical grammars: rejection must come from the
    // new registration/completion constraints, not the old grammar alone.
    test_parse_program(&fixture.bytes, STEPS).unwrap();
    assert_eq!(
      crate::ixby::ixbf::decode_program(
        &fixture.bytes,
        crate::ixby::ixbf::DecodeLimits::default(),
      )
      .is_ok(),
      native_accepts,
      "semantic rejection versus an explicit physical capacity"
    );
    let mut private = hash_tests::private_input(BYTES, &fixture.bytes);
    private.extend(fixture.requests(false));
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[])
      }))
      .is_err()
    );
  };
  let mut duplicate = fixtures::multi();
  duplicate.constructors[1][..4]
    .copy_from_slice(&fixtures::multi().constructors[0][..4]);
  rejects(duplicate, false); // second field count differs, identity does not
  let mut bad_entry = fixtures::multi();
  bad_entry.functions[0].blocks[1].0 = 1;
  rejects(bad_entry, false);
  let mut extra_constructor = fixtures::multi();
  extra_constructor.constructors.push([0, 1, 2, 3, 0]);
  rejects(extra_constructor, true);
  let mut extra_function = fixtures::base();
  extra_function.functions.resize(3, extra_function.functions[0].clone());
  rejects(extra_function, true);
  let mut extra_block = fixtures::base();
  extra_block.functions[0].blocks.resize(3, (0, vec![1, 2]));
  rejects(extra_block, true);

  let fixture = fixtures::encode(&fixtures::base());
  for (at, value) in [
    (0, F128::ONE),
    (1, F128::ONE),
    (3, F128::ONE),
    (5, F128::ONE),
    (6, F128::new(0, 1)),
  ] {
    let mut query = fixture.requests(false);
    query[at] = value;
    let mut private = hash_tests::private_input(BYTES, &fixture.bytes);
    private.extend(query);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[])
      }))
      .is_err()
    );
  }
}

#[test]
#[ignore = "real source-bound registry proofs, isolated verification and recomputed wiring attacks"]
fn source_bound_registries_verify_in_isolation_and_reject_recomputed_substitutions()
 {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let s = setup();
  let fixture = fixtures::encode(&fixtures::multi());
  let (w, expected) = witness(&s, &fixture, fixture.requests(true));
  let honest = prove(&s, &w, &expected, Attack::None);
  isolated(&expected, &honest).unwrap();
  for attack in [
    Attack::CaptureFields,
    Attack::CaptureAddress,
    Attack::CaptureCarry,
    Attack::FinishState,
    Attack::ReadBank,
    Attack::ReadRequest,
    Attack::SourceBuffer,
  ] {
    let proof = prove(&s, &w, &expected, attack);
    let failure = isolated(&expected, &proof).unwrap_err();
    assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
    eprintln!("fresh registry verifier rejected {attack:?} at Wiring");
  }
  for (i, spec) in
    fixtures::corpus().into_iter().enumerate().filter(|(i, _)| *i != 2)
  {
    let fixture = fixtures::encode(&spec);
    let (w, expected) = witness(&s, &fixture, fixture.requests(i % 2 != 0));
    let proof = prove(&s, &w, &expected, Attack::None);
    isolated(&expected, &proof).unwrap();
  }
  for at in [0, 2 + grammar::FUEL, 30, 31, 35, 37, 42, 54] {
    let mut wrong = expected.clone();
    wrong[at].lo ^= 1;
    assert!(verify(&wrong, &honest, DOMAIN).is_err());
  }
  assert!(
    verify(
      &expected,
      &honest,
      b"ix:ixby:ixbf-dispatch-program:bytes1024:steps32:nat4096:v0"
    )
    .is_err()
  );
  for at in [0, 8] {
    let mut wrong = honest.clone();
    wrong[at] ^= 1;
    assert!(verify(&expected, &wrong, DOMAIN).is_err());
  }
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(verify(&expected, &trailing, DOMAIN).is_err());
  assert!(verify(&expected[..OUTPUTS - 1], &honest, DOMAIN).is_err());
  assert!(verify(&expected, &honest[..honest.len() - 1], DOMAIN).is_err());
}
