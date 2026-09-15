//! Source-bound typed value access proofs with isolated verification.
use super::super::{
  ValueArenaSlots, ValueCapacity, ValueConfig, ValueGate, ValueOp,
};
use super::{
  super::super::{
    bodies::{BodyCapacity, BodyGate, BodyOp, ProgramBodySlots},
    code::{CodeCommitSlots, CodeLayout},
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
const OUTPUTS: usize = 189; // four digests, seven queries, manifest and three node reads
const MAGIC: [u8; 8] = *b"IXFVAC00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
fn domain(kind: GrammarKind) -> &'static [u8] {
  match kind {
    GrammarKind::Input => {
      b"ix:ixby:ixbf-value-access:input:bytes1024:steps32:nat4096:c2:f2:b2:o3:n4:d4:v0"
    },
    GrammarKind::Output => {
      b"ix:ixby:ixbf-value-access:output:bytes1024:steps32:nat4096:c2:f2:b2:o3:n4:d4:v0"
    },
    _ => panic!("transport setup kind"),
  }
}
const CHILD: &str = "IXBY_VALUE_ACCESS_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::values::access::proof_tests::source_bound_value_access_verify_in_isolation_and_reject_recomputed_substitutions";

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
fn body_capacity() -> BodyCapacity {
  BodyCapacity::new(capacity(), natural(), 3).unwrap()
}
struct Emission {
  program: ProgramBodySlots,
  code_commit: CodeCommitSlots,
  commit: ValueCommitSlots,
  access: ValueAccessSlots,
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
  let program = ProgramBodySlots::declare(&mut b, NU, body_capacity()).unwrap();
  let slots = ValueArenaSlots::declare(&mut b, NU, config(kind)).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let window = b.slot(window_gate());
  let code_commit =
    CodeCommitSlots::declare(&mut b, body_capacity(), &hash).unwrap();
  let commit = ValueCommitSlots::declare(&mut b, config(kind), &hash).unwrap();
  let layout = ValueLayout::from_arena(config(kind));
  let access =
    ValueAccessSlots::declare(&mut b, NU, layout, hash.compression()).unwrap();
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::ONE);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let original = hash.hash(&mut b, length, &bytes);
  for w in original {
    b.publish(w);
  }
  let mut state = program.initialize(&mut b, length);
  for _ in 0..STEPS {
    state = program.step(&mut b, state, |b, cursor, take| {
      source(b, window, zero, &bytes, cursor, take)
    });
  }
  let checked = program.finish(&mut b, state);
  let code = code_commit.seal(&mut b, &checked, original);
  for w in code.digest() {
    b.publish(w);
  }
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let original = hash.hash(&mut b, length, &bytes);
  for w in original {
    b.publish(w);
  }
  let mut state = slots.initialize(&mut b, length, checked.references());
  for _ in 0..STEPS {
    state = slots.step(&mut b, state, |b, cursor, take| {
      source(b, window, zero, &bytes, cursor, take)
    });
  }
  let finished = slots.finish(&mut b, state);
  let values = commit.seal(&mut b, &finished, &code, original);
  for w in values.digest() {
    b.publish(w);
  }
  let query: [_; 7] = std::array::from_fn(|_| b.input());
  for &w in &query {
    b.publish(w);
  }
  let hints = [b.input(), b.input()];
  let requests: Vec<_> = ValueKind::ALL
    .into_iter()
    .zip(fixtures::query_wires(&query, hints, one, zero))
    .map(|(kind, q)| access.request(&mut b, kind, q))
    .collect();
  let chunks: Vec<_> = requests[..3]
    .iter()
    .map(|request| {
      request.chunk_indices().map(|index| {
        let proof = fixtures::proof_wires(&mut b, layout.depth());
        access.authenticate(&mut b, &values, index, &proof)
      })
    })
    .collect();
  for (i, request) in requests.iter().enumerate() {
    let pair = &chunks[if i == 3 { 0 } else { i }];
    let read = access.read(&mut b, &values, request, [&pair[0], &pair[1]]);
    b.publish(read.index);
    for w in read.record {
      b.publish(w);
    }
  }
  let (inputs, public) = b.finish();
  Emission {
    program,
    slots,
    hash,
    code_commit,
    commit,
    access,
    window,
    inputs,
    public,
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  RequestParent,
  RequestOrdinal,
  RequestLocator,
  ReadIndex,
  ReadParent,
  ReadOrdinal,
  ReadPayload,
  RootOrdinal,
  UnusedChunkByte,
  SourceLength,
  PathSibling,
  SealKind,
  SealCode,
  SealSource,
  SealSummary,
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
fn alter_access(
  g: &ValueAccessGate,
  rows: &mut [ValueAccessRow],
  attack: Attack,
) {
  let target = match attack {
    Attack::RequestParent | Attack::RequestOrdinal | Attack::RequestLocator => {
      (ValueKind::Child, ValueAccessOp::Request)
    },
    Attack::ReadIndex | Attack::ReadPayload => {
      (ValueKind::Node, ValueAccessOp::Record)
    },
    Attack::ReadParent | Attack::ReadOrdinal => {
      (ValueKind::Child, ValueAccessOp::Record)
    },
    Attack::RootOrdinal => (ValueKind::Root, ValueAccessOp::Record),
    _ => return,
  };
  if (g.kind(), g.op()) != target {
    return;
  }
  let row = &mut rows[0].0;
  let before = super::tests::checked(g, row);
  assert_eq!(before.last(), Some(&F128::ZERO));
  match attack {
    Attack::RequestParent => row[1] = F128::ONE,
    Attack::RequestOrdinal => row[2] = F128::ONE,
    Attack::RequestLocator => row[3].lo += 1,
    Attack::ReadIndex => {
      assert_eq!(row[1].lo, 3);
      row[1] = F128::ZERO;
    },
    Attack::ReadParent => {
      row[1].lo += 1;
      row[4 + g.layout().tree_start()].lo += 1;
    },
    Attack::ReadOrdinal | Attack::RootOrdinal => {
      row[2].lo += 1;
      row[4 + g.layout().tree_start() + 1].lo += 1;
    },
    Attack::ReadPayload => row[4 + 8].lo ^= 1,
    _ => unreachable!(),
  }
  let after = super::tests::checked(g, row);
  assert_eq!(after.last(), Some(&F128::ZERO));
  if matches!(attack, Attack::RequestParent | Attack::RequestOrdinal) {
    assert_eq!(before, after);
  } else {
    assert_ne!(before, after);
  }
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
  assert_eq!(row[0].lo, 80);
  let before = values(g, row);
  row[2].lo ^= 1;
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
  row[0].lo += 1;
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
  // Original program 17, code seal 164, transport 17, value seal 59 rows.
  let word = match attack {
    Attack::SealKind => Some(1),
    Attack::SealCode => Some(5),
    Attack::SealSource => Some(7),
    Attack::SealSummary => Some(37),
    Attack::SealPayload => Some(40 + 8),
    _ => None,
  };
  let at = if let Some(word) = word {
    198 + word / 4
  } else {
    match attack {
      Attack::CompressionCounter => 257,
      Attack::CompressionEnd => 257 + 15,
      Attack::CompressionRoot => 257 + 17,
      _ => return,
    }
  };
  let row = &mut rows[at];
  let output = |r: &flock_blake3::Compression| {
    flock_blake3::blake3_compress(&r.0, &r.1, r.2, r.3, r.4)
  };
  let before = output(row);
  if let Some(word) = word {
    row.1[4 * (word % 4)] ^= 1;
  } else {
    match attack {
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
  for op in BodyOp::ALL {
    driver!(
      emission.program.slot(op),
      BodyGate::new(NU, body_capacity(), op).unwrap(),
      BodyGate,
      untouched::<BodyGate>
    );
  }
  for op in ValueOp::ALL {
    driver!(
      emission.slots.slot(op),
      ValueGate::new(NU, config(kind), op).unwrap(),
      ValueGate,
      untouched::<ValueGate>
    );
  }
  for op in ReferenceOp::ALL {
    driver!(
      emission.program.reference_slots().slot(op),
      ReferenceGate::new(NU, capacity(), op).unwrap(),
      ReferenceGate,
      untouched::<ReferenceGate>
    );
  }
  for op in RegistryOp::ALL {
    driver!(
      emission.program.reference_slots().registry_slots().slot(op),
      RegistryGate::new(NU, capacity(), op).unwrap(),
      RegistryGate,
      untouched::<RegistryGate>
    );
  }
  for dispatch in [
    emission.program.reference_slots().registry_slots().dispatch(),
    emission.slots.dispatch(),
  ] {
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
  driver!(
    emission.window,
    window_gate(),
    SourceWindowGate,
    untouched::<SourceWindowGate>
  );
  for hash in [emission.code_commit.hash(), emission.commit.hash()] {
    driver!(
      hash.block_slot(),
      hash.block_gate().clone(),
      HashBlockGate,
      untouched::<HashBlockGate>
    );
  }
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
  let kind_transport = kind;
  for kind in ValueKind::ALL {
    for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
      driver!(
        emission.access.slot(kind, op),
        ValueAccessGate::new(
          NU,
          ValueLayout::from_arena(config(kind_transport)),
          kind,
          op
        )
        .unwrap(),
        ValueAccessGate,
        alter_access
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
  assert_eq!(drivers.len(), 90);
  for (index, d) in drivers.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot()), index);
  }
  assert_eq!(emission.inputs.private_words(), 547);
  assert_eq!(emission.public.outputs(), OUTPUTS);
  Setup { shape, emission, kind, drivers }
}
fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert_eq!(m, 27, "value access PCS geometry");
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
    "value access proof {attack:?}: M={} bytes={}",
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
    "value access proof/public size"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && bundle.revision == 0,
    "value access proof envelope"
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
  .map_err(|e| anyhow::anyhow!("value access proof rejected: {e:?}"))?;
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
    "value access verifier input size"
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

fn private(f: &fixtures::Fixture, layout: ValueLayout) -> Vec<F128> {
  let mut private = hash_tests::private_input(BYTES, &f.forest.program.bytes);
  private.extend(hash_tests::private_input(BYTES, &f.forest.bytes));
  private.extend(f.query);
  private.extend(f.hints);
  private.extend(f.proofs(layout));
  private
}
fn witness(s: &Setup, f: &fixtures::Fixture) -> (CircuitWitness, Vec<F128>) {
  let layout = ValueLayout::from_arena(config(s.kind));
  let w =
    s.shape.run(&s.emission.inputs.assign(&private(f, layout)).unwrap(), &[]);
  let mut expected = hash_tests::expected(&f.forest.program.bytes).to_vec();
  expected.extend(hash_tests::expected(&f.code_image));
  expected.extend(hash_tests::expected(&f.forest.bytes));
  expected.extend(hash_tests::expected(&f.image));
  expected.extend(f.query);
  expected.extend(f.records.iter().flatten());
  assert_eq!(
    w.public,
    s.emission.public.instantiate(&expected).unwrap(),
    "{}",
    f.name
  );
  assert_eq!(
    w.rows::<Blake3Gate>(s.emission.hash.compression_slot()).len(),
    365
  );
  for op in ValueOp::ALL {
    let n = match op {
      ValueOp::Link | ValueOp::Node | ValueOp::Capture => STEPS,
      ValueOp::Finish => 1,
      _ => 0,
    };
    assert_eq!(w.rows::<ValueGate>(s.emission.slots.slot(op)).len(), n);
  }
  (w, expected)
}
fn attacks(kind: GrammarKind, name: &str) -> &'static [Attack] {
  if kind != GrammarKind::Input {
    return &[];
  }
  match name {
    "nested" => &[
      Attack::RequestParent,
      Attack::RequestOrdinal,
      Attack::RequestLocator,
      Attack::ReadIndex,
      Attack::ReadParent,
      Attack::ReadOrdinal,
      Attack::RootOrdinal,
    ],
    "zero" => &[Attack::ReadPayload, Attack::SealPayload],
    "erased" => &[
      Attack::UnusedChunkByte,
      Attack::SourceLength,
      Attack::PathSibling,
      Attack::SealKind,
      Attack::SealCode,
      Attack::SealSource,
      Attack::SealSummary,
      Attack::CompressionCounter,
      Attack::CompressionEnd,
      Attack::CompressionRoot,
    ],
    _ => &[],
  }
}
#[test]
fn complete_value_access_matches_native_images_and_reuses_manifest_root_chunks()
{
  use crate::sizing::CountedGate;
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let mut count = CountingEmitter::new();
    let emission = emit(&mut count, kind);
    let s = setup(kind);
    count.ensure_matches(&s.shape).unwrap();
    assert_eq!(emission.inputs, s.emission.inputs);
    assert_eq!(emission.public, s.emission.public);
    let identity = s.shape.circuit.digest();
    let layout = ValueLayout::from_arena(config(kind));
    assert_eq!(
      (layout.words(), layout.bytes(), layout.depth()),
      (220, 3520, 2)
    );
    assert_eq!(CodeLayout::from_bodies(body_capacity()).bytes(), 9856);
    let fixtures = fixtures::corpus(config(kind), body_capacity());
    for tag in ["string", "bytes"] {
      let a =
        fixtures.iter().find(|f| f.name == format!("payload-{tag}-a")).unwrap();
      let b =
        fixtures.iter().find(|f| f.name == format!("payload-{tag}-b")).unwrap();
      assert_eq!(a.forest.records, b.forest.records);
      assert_eq!(a.code_image, b.code_image);
      assert_eq!(&a.image[..7 * 16], &b.image[..7 * 16]);
      assert_eq!(&a.image[9 * 16..], &b.image[9 * 16..]);
      assert_ne!(
        hash_tests::expected(&a.image),
        hash_tests::expected(&b.image)
      );
    }
    let a = fixtures.iter().find(|f| f.name == "code-a").unwrap();
    let b = fixtures.iter().find(|f| f.name == "code-b").unwrap();
    assert_eq!(a.forest.bytes, b.forest.bytes);
    assert_eq!(&a.image[..5 * 16], &b.image[..5 * 16]);
    assert_eq!(&a.image[7 * 16..], &b.image[7 * 16..]);
    assert_ne!(hash_tests::expected(&a.image), hash_tests::expected(&b.image));
    let mut straddles = false;
    let mut tail = false;
    for f in &fixtures {
      eprintln!("value access differential {kind:?} {}", f.name);
      let (w, _) = witness(&s, f);
      for (i, read_kind) in ValueKind::ALL.into_iter().enumerate() {
        for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
          let g = ValueAccessGate::new(NU, layout, read_kind, op).unwrap();
          let rows =
            w.rows::<ValueAccessGate>(s.emission.access.slot(read_kind, op));
          assert_eq!(rows.len(), 1);
          let out = super::tests::checked(&g, &rows[0].0);
          assert_eq!(out.last(), Some(&F128::ZERO));
          if op == ValueAccessOp::Record {
            assert_eq!(&out[..out.len() - 1], f.records[i]);
          }
          for &attack in attacks(kind, &f.name) {
            alter_access(&g, &mut rows.to_vec(), attack);
          }
        }
        let at = fixtures::offset(layout, read_kind, &f.requests[i]);
        straddles |= f.requests[i][0] == F128::ONE
          && at / 1024
            != (at + 16 * layout.record_words(read_kind) as u64 - 1) / 1024;
        tail |= f.requests[i][0] == F128::ONE
          && at + 16 * layout.record_words(read_kind) as u64 == layout.bytes();
      }
      let source = s.emission.access.source_slots();
      assert_eq!(w.rows::<SourceBlockGate>(source.block_gate().0).len(), 96);
      assert_eq!(w.rows::<SourcePathGate>(source.path_gate().0).len(), 12);
      assert_eq!(w.rows::<SourceWindowGate>(source.window_gate().0).len(), 4);
      for &attack in attacks(kind, &f.name) {
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
          &mut w
            .rows::<Blake3Gate>(s.emission.hash.compression_slot())
            .to_vec(),
          attack,
        );
      }
      assert_eq!(s.shape.circuit.digest(), identity);
    }
    assert!(straddles && tail);
    let union = UnionInstance::new(&s.shape.registry, s.shape.counts.clone());
    let _ = params(&union);
    eprintln!(
      "value access census {kind:?}: fixtures={} tables={} M={} private={} public={} bytes={} depth={} compression=365",
      fixtures.len(),
      s.drivers.len(),
      union.dense_m(),
      s.emission.inputs.private_words(),
      OUTPUTS,
      layout.bytes(),
      layout.depth()
    );
    for read_kind in ValueKind::ALL {
      for op in [ValueAccessOp::Request, ValueAccessOp::Record] {
        let g = ValueAccessGate::new(NU, layout, read_kind, op).unwrap();
        eprintln!(
          "value access {read_kind:?} {op:?}: input={} output={} useful={} k={}",
          g.input_count(),
          g.output_count(),
          g.plan().useful_bits(),
          g.plan().k()
        );
      }
    }
  }
}
#[test]
#[ignore = "real authenticated typed value proofs, isolated verification and locally recomputed substitutions"]
fn source_bound_value_access_verify_in_isolation_and_reject_recomputed_substitutions()
 {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  for kind in [GrammarKind::Input, GrammarKind::Output] {
    let s = setup(kind);
    let mut first = None;
    for f in fixtures::corpus(config(kind), body_capacity()) {
      let (w, expected) = witness(&s, &f);
      let proof = prove(&s, &w, &expected, Attack::None);
      isolated(kind, &expected, &proof).unwrap();
      eprintln!("fresh value access proof verified {kind:?} {}", f.name);
      if first.is_none() {
        first = Some((expected.clone(), proof));
      }
      for &attack in attacks(kind, &f.name) {
        let proof = prove(&s, &w, &expected, attack);
        let failure = isolated(kind, &expected, &proof).unwrap_err();
        assert!(failure.contains("Wiring"), "{attack:?}: {failure}");
        eprintln!("fresh value access verifier rejected {attack:?} at Wiring");
      }
    }
    let (expected, honest) = first.unwrap();
    for at in [
      0,
      1,
      2,
      3,
      4,
      5,
      6,
      7,
      8,
      10,
      13,
      15,
      16,
      18,
      21,
      48,
      51,
      60,
      97,
      143,
      OUTPUTS - 1,
    ] {
      let mut wrong = expected.clone();
      wrong[at].lo ^= 1;
      assert!(
        verify(kind, &wrong, &honest, domain(kind)).is_err(),
        "expected word {at}"
      );
    }
    let other = if kind == GrammarKind::Input {
      GrammarKind::Output
    } else {
      GrammarKind::Input
    };
    assert!(verify(other, &expected, &honest, domain(other)).is_err());
    assert!(verify(kind, &expected, &honest, b"ix:ixby:ixbf-values:input:bytes1024:steps32:nat4096:c2:f2:b2:n4:d4:v0").is_err());
    for at in [0, 8, honest.len() - 1] {
      let mut wrong = honest.clone();
      wrong[at] ^= 1;
      assert!(verify(kind, &expected, &wrong, domain(kind)).is_err());
    }
    for magic in [b"IXFVAL00", b"IXFCOD00"] {
      let mut wrong = honest.clone();
      wrong[..8].copy_from_slice(magic);
      assert!(verify(kind, &expected, &wrong, domain(kind)).is_err());
    }
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

#[test]
fn value_sealing_connects_the_actual_code_registry_and_transport_context() {
  use super::super::super::registry::fixtures as program;
  use super::super::fixtures as forest;
  use crate::ixby::ixbf;
  let kind = GrammarKind::Input;
  let mut builder = ShapeBuilder::new(NU);
  let mut b = LayoutEmitter::new(&mut builder);
  let programs =
    ProgramBodySlots::declare(&mut b, NU, body_capacity()).unwrap();
  let values = ValueArenaSlots::declare(&mut b, NU, config(kind)).unwrap();
  let hash = BoundedBlake3::declare(&mut b, NU, BYTES).unwrap();
  let code_commit =
    CodeCommitSlots::declare(&mut b, body_capacity(), &hash).unwrap();
  let commit = ValueCommitSlots::declare(&mut b, config(kind), &hash).unwrap();
  let window = b.slot(window_gate());
  let zero = b.fixed_public_input(F128::ZERO);
  let mut bodies = Vec::new();
  for _ in 0..2 {
    let length = b.input();
    let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
    let root = hash.hash(&mut b, length, &bytes);
    let mut state = programs.initialize(&mut b, length);
    for _ in 0..STEPS {
      state = programs.step(&mut b, state, |b, cursor, take| {
        source(b, window, zero, &bytes, cursor, take)
      });
    }
    bodies.push((programs.finish(&mut b, state), root));
  }
  let code = code_commit.seal(&mut b, &bodies[0].0, bodies[0].1);
  let length = b.input();
  let bytes: Vec<_> = (0..64).map(|_| b.input()).collect();
  let root = hash.hash(&mut b, length, &bytes);
  let mut state = values.initialize(&mut b, length, bodies[1].0.references());
  for _ in 0..STEPS {
    state = values.step(&mut b, state, |b, cursor, take| {
      source(b, window, zero, &bytes, cursor, take)
    });
  }
  let arena = values.finish(&mut b, state);
  for word in commit.seal(&mut b, &arena, &code, root).digest() {
    b.publish(word);
  }
  let (inputs, _) = b.finish();
  let shape = builder.finish().unwrap();
  let f = forest::corpus(kind, config(kind).arena)
    .into_iter()
    .find(|(name, _)| *name == "nested")
    .unwrap()
    .1;
  let run = |code: &[u8], registry: &[u8]| {
    let mut private = hash_tests::private_input(BYTES, code);
    private.extend(hash_tests::private_input(BYTES, registry));
    private.extend(hash_tests::private_input(BYTES, &f.bytes));
    shape.run(&inputs.assign(&private).unwrap(), &[])
  };
  run(&f.program.bytes, &f.program.bytes);
  for variant in 0..4 {
    let mut spec = forest::spec(1);
    match variant {
      0 => spec.constructors[0][0] ^= 1,
      1 => spec.constructors.swap(0, 1),
      2 => {
        spec.functions[0].arity = 4;
        spec.functions[0].blocks[0].0 = 4;
      },
      3 => spec.wide_limits = true,
      _ => unreachable!(),
    }
    let other = program::encode(&spec);
    let native =
      ixbf::decode_program(&other.bytes, ixbf::DecodeLimits::default())
        .unwrap();
    ixbf::decode_input(&native, &f.bytes, ixbf::DecodeLimits::default())
      .unwrap();
    // Each alternate program admits this transport when it also supplies code.
    run(&other.bytes, &other.bytes);
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(
        &f.program.bytes,
        &other.bytes
      )))
      .is_err(),
      "cross-program value seal {variant}"
    );
  }
}
