//! Source-bound complete typed executable-code proofs with isolated verification.
use super::tests as code_tests;
use super::{
  super::{
    bodies::{BodyCapacity, BodyGate, BodyOp, ProgramBodySlots},
    dispatch::*,
    references::{ReferenceGate, ReferenceOp},
    registry::{RegistryCapacity, RegistryGate, RegistryOp},
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

const NU: usize = 9;
const STEPS: usize = 32;
const BYTES: usize = 1024;
const OUTPUTS: usize = 123; // original2, code2, query15, typed results104
const MAGIC: [u8; 8] = *b"IXFCOD00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const DOMAIN: &[u8] =
  b"ix:ixby:ixbf-code:bytes1024:steps32:nat4096:c2:f2:b2:o3:v0";
const CHILD: &str = "IXBY_CODE_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::code::proof_tests::source_bound_code_verify_in_isolation_and_reject_recomputed_substitutions";

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
  commit: CodeCommitSlots,
  access: CodeAccessSlots,
  window: SlotId,
  inputs: InputLayout,
  public: PublicLayout,
}
fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let slots = ProgramBodySlots::declare(&mut b, NU, body_capacity()).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let window = b.slot(window_gate());
  let commit =
    CodeCommitSlots::declare(&mut b, body_capacity(), &hash).unwrap();
  let layout = CodeLayout::from_bodies(body_capacity());
  let access =
    CodeAccessSlots::declare(&mut b, NU, layout, hash.compression()).unwrap();
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::ONE);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let original = hash.hash(&mut b, length, &bytes);
  for word in original {
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
  let code = commit.seal(&mut b, &checked, original);
  for word in code.digest() {
    b.publish(word);
  }
  let query: [_; 15] = std::array::from_fn(|_| b.input());
  for &word in &query {
    b.publish(word);
  }
  let requests: Vec<_> = fixtures::KINDS
    .into_iter()
    .zip(fixtures::query_wires(&query, one, zero))
    .map(|(kind, q)| access.request(&mut b, kind, q))
    .collect();
  let chunks: Vec<_> = [0, 4, 5, 6]
    .into_iter()
    .map(|i| {
      requests[i].chunk_indices().map(|index| {
        let proof = fixtures::proof_wires(&mut b, layout.depth());
        access.authenticate(&mut b, &code, index, &proof)
      })
    })
    .collect();
  for (i, request) in requests.iter().enumerate() {
    let pair = &chunks[if i < 4 { 0 } else { i - 3 }];
    let read = access.read(&mut b, &code, request, [&pair[0], &pair[1]]);
    for word in read.fields {
      b.publish(word);
    }
  }
  let (inputs, public) = b.finish();
  Emission { slots, hash, commit, access, window, inputs, public }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  ReadFunctionAddress,
  ReadPayload,
  UnusedChunkByte,
  SourceLength,
  PathSibling,
  SealSchema,
  SealOriginalDigest,
  SealPayload,
  CompressionCounter,
  CompressionEnd,
  CompressionRoot,
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
fn alter_code(g: &CodeGate, rows: &mut [CodeRow], attack: Attack) {
  let target = match attack {
    Attack::ReadFunctionAddress => (CodeKind::Function, CodeOp::Request),
    Attack::ReadPayload => (CodeKind::Operand, CodeOp::Record),
    _ => return,
  };
  if (g.kind(), g.op()) != target {
    return;
  }
  let row = &mut rows[0].0;
  let before = code_tests::checked(g, row);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::ReadFunctionAddress => {
      assert_eq!(row[1], F128::ONE);
      row[1] = F128::ZERO;
    },
    Attack::ReadPayload => row[1 + 7].lo ^= 1,
    _ => unreachable!(),
  }
  let after = code_tests::checked(g, row);
  assert_eq!(after.last(), Some(&F128::ZERO));
  assert_ne!(before, after);
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), row, &after);
}
fn alter_window(
  g: &SourceWindowGate,
  rows: &mut [SourceWindowRow],
  attack: Attack,
) {
  if attack != Attack::UnusedChunkByte {
    return;
  }
  let row = rows[0].test_inputs_mut();
  assert_eq!(row[0].lo, 96); // Program manifest starts after the schema.
  let before = values(g, row);
  row[2].lo ^= 1; // Authenticated schema byte outside this read's window.
  let after = values(g, row);
  assert_eq!(before, after);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), row, &after);
}
fn alter_block(
  g: &SourceBlockGate,
  rows: &mut [SourceBlockRow],
  attack: Attack,
) {
  if attack != Attack::SourceLength {
    return;
  }
  let row = rows[0].test_inputs_mut();
  let before = values(g, row);
  row[0].lo += 1; // Still a full non-final chunk: local outputs stay equal.
  let after = values(g, row);
  assert_eq!(before, after);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), row, &after);
}
fn alter_path(g: &SourcePathGate, rows: &mut [SourcePathRow], attack: Attack) {
  if attack != Attack::PathSibling {
    return;
  }
  let row = rows[0].test_inputs_mut();
  let before = values(g, row);
  row[5].lo ^= 1;
  let after = values(g, row);
  assert_ne!(before, after);
  assert_eq!(after.last(), Some(&F128::ZERO));
  scalar_payload_tests::checked(g.plan(), &g.r1cs(), row, &after);
}
fn alter_compression(
  _: &Blake3Gate,
  rows: &mut [flock_blake3::Compression],
  attack: Attack,
) {
  // Original hash = 17 rows; code hash = 154 leaves + 9 parents + ROOT.
  // First authenticated chunk starts at row 181, then 16 blocks + 4 levels.
  let at = match attack {
    Attack::SealSchema => 17,
    Attack::SealOriginalDigest => 17 + 6 / 4,
    Attack::SealPayload => 17 + 81 / 4,
    Attack::CompressionCounter => 181,
    Attack::CompressionEnd => 181 + 15,
    Attack::CompressionRoot => 181 + 19,
    _ => return,
  };
  let row = &mut rows[at];
  let output = |r: &flock_blake3::Compression| {
    flock_blake3::blake3_compress(&r.0, &r.1, r.2, r.3, r.4)
  };
  let before = output(row);
  match attack {
    Attack::SealSchema => row.1[0] ^= 1,
    Attack::SealOriginalDigest => row.1[4 * (6 % 4)] ^= 1,
    Attack::SealPayload => row.1[4] ^= 1, // Image word 81 is block word 1.
    Attack::CompressionCounter => row.2 ^= 1,
    Attack::CompressionEnd => {
      assert_eq!(row.4, crate::hash::CHUNK_END);
      row.4 ^= crate::hash::CHUNK_END;
    },
    Attack::CompressionRoot => {
      assert_eq!(row.4, crate::hash::PARENT | crate::hash::ROOT);
      row.4 ^= crate::hash::ROOT;
    },
    _ => unreachable!(),
  }
  assert_ne!(before, output(row));
  assert!(
    flock_blake3::build_block_r1cs(3)
      .satisfies(&flock_blake3::generate_witness(&[*row], 3))
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
      untouched::<BodyGate>
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
  driver!(
    emission.window,
    window_gate(),
    SourceWindowGate,
    untouched::<SourceWindowGate>
  );
  let code_hash = emission.commit.hash();
  driver!(
    code_hash.block_slot(),
    code_hash.block_gate().clone(),
    HashBlockGate,
    untouched::<HashBlockGate>
  );
  let source = emission.access.source_slots();
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
    alter_block
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
  for kind in CodeKind::ALL {
    for op in [CodeOp::Request, CodeOp::Record] {
      driver!(
        emission.access.slot(kind, op),
        CodeGate::new(NU, CodeLayout::from_bodies(body_capacity()), kind, op)
          .unwrap(),
        CodeGate,
        alter_code
      );
    }
  }
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
  assert_eq!(drivers.len(), 61);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 656);
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, drivers }
}
fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert_eq!(m, 26, "bounded code PCS geometry");
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
    "code proof {attack:?}: M={} bytes={}",
    union.dense_m(),
    bytes.len()
  );
  bytes
}
fn verify(expected: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    expected.len() == OUTPUTS && bytes.len() as u64 <= MAX_BYTES,
    "code proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(bundle.magic == MAGIC && bundle.revision == 0, "code proof envelope");
  ensure!(codec().serialize(&bundle)? == bytes, "noncanonical code proof");
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
  .map_err(|e| anyhow::anyhow!("code proof rejected: {e:?}"))?;
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
    "code verifier input size"
  );
  let expected: Vec<_> = input[..prefix]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|w| crate::hash::pack_bytes(w))
    .collect();
  verify(&expected, &input[prefix..], DOMAIN)
}

fn witness(s: &Setup, f: &fixtures::Fixture) -> (CircuitWitness, Vec<F128>) {
  let layout = CodeLayout::from_bodies(body_capacity());
  let mut private = hash_tests::private_input(BYTES, &f.original);
  private.extend(f.query);
  private.extend(f.proofs(layout));
  let w = s.shape.run(&s.emission.inputs.assign(&private).unwrap(), &[]);
  let mut expected = hash_tests::expected(&f.original).to_vec();
  expected.extend(hash_tests::expected(&f.image));
  expected.extend(f.query);
  expected.extend(&f.results);
  assert_eq!(
    w.public,
    s.emission.public.instantiate(&expected).unwrap(),
    "{}",
    f.name
  );
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    341
  );
  assert_eq!(
    w.rows::<SourceWindowGate>(
      s.emission.access.source_slots().window_gate().0
    )
    .len(),
    7
  );
  (w, expected)
}
fn attacks(name: &str) -> &'static [Attack] {
  match name {
    "owned-target" => &[Attack::ReadFunctionAddress],
    "zero" => &[Attack::ReadPayload, Attack::SealPayload],
    "return" => &[
      Attack::UnusedChunkByte,
      Attack::SourceLength,
      Attack::PathSibling,
      Attack::SealSchema,
      Attack::SealOriginalDigest,
      Attack::CompressionCounter,
      Attack::CompressionEnd,
      Attack::CompressionRoot,
    ],
    _ => &[],
  }
}

#[test]
fn complete_code_shape_matches_native_images_and_reuses_authenticated_chunks() {
  use crate::sizing::CountedGate;
  let mut count = CountingEmitter::new();
  let emission = emit(&mut count);
  let s = setup();
  count.ensure_matches(&s.shape).unwrap();
  assert_eq!(emission.inputs, s.emission.inputs);
  assert_eq!(emission.public, s.emission.public);
  let identity = s.shape.circuit.digest();
  let layout = CodeLayout::from_bodies(body_capacity());
  let gates: Vec<_> = CodeKind::ALL
    .into_iter()
    .flat_map(|kind| {
      [CodeOp::Request, CodeOp::Record]
        .map(|op| CodeGate::new(NU, layout, kind, op).unwrap())
    })
    .collect();
  let fixtures = fixtures::corpus(body_capacity());
  for tag in ["string", "bytes"] {
    let a =
      fixtures.iter().find(|f| f.name == format!("payload-{tag}-a")).unwrap();
    let b =
      fixtures.iter().find(|f| f.name == format!("payload-{tag}-b")).unwrap();
    assert_eq!(a.original.len(), b.original.len());
    assert_eq!(&a.image[..96], &b.image[..96]);
    assert_eq!(&a.image[128..], &b.image[128..]);
    assert_ne!(&a.image[96..128], &b.image[96..128]);
    assert_ne!(hash_tests::expected(&a.image), hash_tests::expected(&b.image));
  }
  let mut straddles = false;
  let mut final_chunk = false;
  for f in &fixtures {
    eprintln!("code differential {}", f.name);
    let (w, _) = witness(&s, f);
    for (i, &kind) in fixtures::KINDS.iter().enumerate() {
      let ordinal = if i == 3 { 1 } else { 0 };
      let g = CodeGate::new(NU, layout, kind, CodeOp::Record).unwrap();
      let row = &w
        .rows::<CodeGate>(s.emission.access.slot(kind, CodeOp::Record))
        [ordinal];
      let out = code_tests::checked(&g, &row.0);
      assert_eq!(&out[..out.len() - 1], f.records[i]);
      let at = fixtures::offset(layout, kind, &f.requests[i]);
      straddles |= f.requests[i][0] == F128::ONE
        && at / 1024 != (at + 16 * layout.record_words(kind) as u64 - 1) / 1024;
      final_chunk |= f.requests[i][0] == F128::ONE
        && (at / 1024 + 1).min((layout.bytes() - 1) / 1024)
          == (layout.bytes() - 1) / 1024;
    }
    for g in &gates {
      let rows = w.rows::<CodeGate>(s.emission.access.slot(g.kind(), g.op()));
      assert_eq!(
        rows.len(),
        if g.kind() == CodeKind::Function { 2 } else { 1 }
      );
      for row in rows {
        assert_eq!(code_tests::checked(g, &row.0).last(), Some(&F128::ZERO));
      }
      for &attack in attacks(&f.name) {
        alter_code(g, &mut rows.to_vec(), attack);
      }
    }
    let source = s.emission.access.source_slots();
    for &attack in attacks(&f.name) {
      alter_window(
        &source.window_gate().1,
        &mut w.rows::<SourceWindowGate>(source.window_gate().0).to_vec(),
        attack,
      );
      alter_block(
        &source.block_gate().1,
        &mut w.rows::<SourceBlockGate>(source.block_gate().0).to_vec(),
        attack,
      );
      alter_path(
        &source.path_gate().1,
        &mut w.rows::<SourcePathGate>(source.path_gate().0).to_vec(),
        attack,
      );
      alter_compression(
        &Blake3Gate { nu: NU },
        &mut w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).to_vec(),
        attack,
      );
    }
    assert_eq!(s.shape.circuit.digest(), identity);
  }
  assert!(straddles, "corpus exercises two-chunk records");
  assert!(final_chunk, "corpus authenticates the partial final chunk");
  let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
  let _ = params(&union);
  eprintln!(
    "code census fixtures={} tables={} M={} private={} public={} bytes={} depth={} compression=341",
    fixtures.len(),
    s.drivers.len(),
    union.dense_m(),
    s.emission.inputs.private_words(),
    OUTPUTS,
    layout.bytes(),
    layout.depth()
  );
  for g in &gates {
    eprintln!(
      "code {:?} {:?}: input={} output={} useful={} k={}",
      g.kind(),
      g.op(),
      g.input_count(),
      g.output_count(),
      g.plan().useful_bits(),
      g.plan().k()
    );
  }
}

#[test]
#[ignore = "real source-bound typed code proofs, isolated verification and locally recomputed substitutions"]
fn source_bound_code_verify_in_isolation_and_reject_recomputed_substitutions() {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let s = setup();
  let mut first = None;
  for f in fixtures::corpus(body_capacity()).into_iter().filter(|f| f.prove) {
    let (w, expected) = witness(&s, &f);
    let proof = prove(&s, &w, &expected, Attack::None);
    isolated(&expected, &proof).unwrap();
    eprintln!("fresh code proof verified {}", f.name);
    if first.is_none() {
      first = Some((expected.clone(), proof));
    }
    for &attack in attacks(&f.name) {
      let proof = prove(&s, &w, &expected, attack);
      let failure = isolated(&expected, &proof).unwrap_err();
      assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
      eprintln!("fresh code verifier rejected {attack:?} at Wiring");
    }
  }
  let (expected, honest) = first.unwrap();
  // Both digests, every query group, manifest, each typed result class.
  for at in [
    0,
    1,
    2,
    3,
    4,
    6,
    9,
    13,
    17,
    19,
    21,
    19 + 2 + grammar::FUEL,
    49,
    56,
    61,
    66,
    80 + 7,
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
      b"ix:ixby:ixbf-bodies:bytes1024:steps32:nat4096:c2:f2:b2:o3:v0"
    )
    .is_err()
  );
  for at in [0, 8, honest.len() - 1] {
    let mut wrong = honest.clone();
    wrong[at] ^= 1;
    assert!(verify(&expected, &wrong, DOMAIN).is_err());
  }
  let mut wrong = honest.clone();
  wrong[..8].copy_from_slice(b"IXFBOD00");
  assert!(verify(&expected, &wrong, DOMAIN).is_err());
  let mut trailing = honest.clone();
  trailing.push(0);
  assert!(verify(&expected, &trailing, DOMAIN).is_err());
  assert!(verify(&expected[..OUTPUTS - 1], &honest, DOMAIN).is_err());
  assert!(verify(&expected, &honest[..honest.len() - 1], DOMAIN).is_err());
}
