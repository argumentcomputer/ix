use super::*;
use crate::{
  extension::{self, GoldilocksLaneRepackGate},
  goldilocks::{self, CanonicalGoldilocksQuadGate, GoldilocksAddPairGate},
  hash::{Blake3Gate, pack_bytes},
  ixby::{
    auth_memory::{MemoryGate, multi::MultiGate},
    decode::PrimitiveSet,
    execution_order::{OrderGate, OrderKind},
    memory_log::{AuditGate, SwitchGate},
    paged_code::CodeGate,
    paged_frame::FrameGate,
    paged_nat::Nat128Gate,
    paged_primitive::PrimitiveRouteGate,
    primitive::{PrimitiveFinishGate, PrimitivePrepareGate},
    select::SelectWordsGate,
    wide_fuel::Fuel64StepGate,
  },
  multiplication::{self, GoldilocksMulPairGate},
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, CircuitWitness, GateType, ShapeBuilder, SlotId,
  },
  hash::HashKind,
  lincheck::LincheckCircuit,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionElementSlotInput, UnionSlotProverInput},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
  union::{SlotWitnessDest, UnionInstance},
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
  sync::Arc,
};

fn domain(class: BatchClass) -> &'static [u8] {
  match class {
    BatchClass::Small => b"IxBy/Flock/paged-execution:small:v2",
    BatchClass::Objects => b"IxBy/Flock/paged-execution:objects:v1",
    BatchClass::Compact => b"IxBy/Flock/paged-execution:compact:v1",
    BatchClass::Bytes => b"IxBy/Flock/paged-execution:bytes:v0",
    BatchClass::SharedCompact => {
      b"IxBy/Flock/paged-execution:shared-compact:v0"
    },
  }
}
const MAGIC: [u8; 8] = *b"IXFPGX00";
const MAX_BYTES: u64 = 16 * 1024 * 1024;
const OUTPUTS: usize = 57;
const TEST: &str = "ixby::paged_exec::proof_tests::instruction_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows";
const OBJECT_TEST: &str = "ixby::paged_exec::proof_tests::object_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows";
const BYTE_TEST: &str = "ixby::paged_exec::proof_tests::byte_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows";
const HASH_TEST: &str = "ixby::paged_exec::proof_tests::chunk_tree_hash_proves_fresh_and_rejects_recomputed_hash_rows";
const CHILD: &str = "IXBY_PAGED_EXEC_VERIFY_CHILD";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Fetch,
  Operand,
  Numeric,
  Call,
  Return,
  Fuel,
  OrderClock,
  MemoryClock,
  Field,
  HeapReservation,
  Closure,
  Splice,
  Alternative,
  StoreIndex,
  ApplyDeclaration,
  BytePointer,
  ByteAllocation,
  ByteConversion,
  ByteCopy,
  ByteEquality,
  ByteLimit,
  HashCounter,
  HashRoot,
  HashMask,
  HashCv,
}
#[derive(Serialize, Deserialize)]
struct Bundle {
  magic: [u8; 8],
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
type Generator = Box<dyn for<'d> FnOnce(SlotWitnessDest<'d>) -> Vec<u8> + Send>;
type Factory = Box<dyn Fn(&CircuitWitness, Attack) -> Generator + Send + Sync>;
struct Driver {
  slot: SlotId,
  table: BlockR1cs,
  make: Factory,
}
impl Driver {
  fn new<G, F>(slot: SlotId, gate: G, table: BlockR1cs, fill: F) -> Self
  where
    G: GateType + Send + Sync + 'static,
    G::Row: Clone + Send + 'static,
    F: for<'d> Fn(&G, &[G::Row], Attack, SlotWitnessDest<'d>) -> Vec<u8>
      + Send
      + Sync
      + 'static,
  {
    let fill = Arc::new(fill);
    let gate = Arc::new(gate);
    let make = Box::new(move |witness: &CircuitWitness, attack| {
      let rows = witness.rows::<G>(slot).to_vec();
      let gate = gate.clone();
      let fill = fill.clone();
      Box::new(move |dst: SlotWitnessDest<'_>| fill(&gate, &rows, attack, dst))
        as Generator
    });
    Self { slot, table, make }
  }
  fn prover<'a>(
    &'a self,
    witness: &CircuitWitness,
    attack: Attack,
  ) -> UnionSlotProverInput<'a> {
    let generate = (self.make)(witness, attack);
    UnionSlotProverInput::in_place(
      move |mut dst| {
        dst.elide_padding_writes = false;
        generate(dst)
      },
      self.table.csc_lincheck_circuit(),
    )
  }
}
fn micro_fill(
  gate: &MicroGate,
  rows: &[MicroRow],
  attack: Attack,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  let mut rows = rows.to_vec();
  let target = match (attack, gate.kind()) {
    (Attack::Fetch, MicroKind::Fetch) => {
      Some((1 + STATE_WORDS, F128::new(0, 1 << 16)))
    },
    (Attack::Operand, MicroKind::ResolveFinish)
    | (Attack::Numeric, MicroKind::NumericAction)
    | (Attack::Return, MicroKind::ControlAction) => {
      Some((2 + STATE_WORDS, F128::ONE))
    },
    (Attack::Call, MicroKind::CallAction) => {
      Some((1 + STATE_WORDS, F128::new(1 << 8, 0)))
    },
    (Attack::Fuel, MicroKind::Complete) => {
      Some((1 + STATE_WORDS + 5, F128::new(1, 1)))
    },
    (Attack::Field, MicroKind::Object(ObjectKind::StoreCopy)) => {
      Some((2 + STATE_WORDS, F128::ONE))
    },
    (Attack::HeapReservation, MicroKind::Object(ObjectKind::Construct)) => {
      Some((1 + HEAP_COUNT, F128::ONE))
    },
    (Attack::Closure, MicroKind::Object(ObjectKind::Closure)) => {
      Some((1 + HEADER, F128::new(0, 2)))
    },
    (Attack::Splice, MicroKind::Object(ObjectKind::ApplyStart)) => {
      Some((1 + 3, F128::ONE))
    },
    (Attack::Alternative, MicroKind::Object(ObjectKind::CaseAction)) => {
      Some((3 + STATE_WORDS, F128::new(1 << 8, 0)))
    },
    (Attack::StoreIndex, MicroKind::Object(ObjectKind::StoreCopy)) => {
      Some((1 + CONTROL, F128::new(1 << 8, 0)))
    },
    (Attack::ApplyDeclaration, MicroKind::Object(ObjectKind::ApplyStart)) => {
      Some((1 + STATE_WORDS, F128::ONE))
    },
    (Attack::BytePointer, MicroKind::Byte(ByteKind::Window)) => {
      Some((1 + STATE_WORDS, F128::ONE))
    },
    (Attack::ByteAllocation, MicroKind::Byte(ByteKind::Start)) => {
      Some((1 + BYTE_COUNT, F128::ONE))
    },
    (Attack::ByteConversion, MicroKind::Byte(ByteKind::ReadFinish))
    | (Attack::ByteCopy, MicroKind::Byte(ByteKind::AppendFinish))
    | (Attack::ByteEquality, MicroKind::Byte(ByteKind::EqFinish)) => {
      Some((1 + STATE_WORDS, F128::ONE))
    },
    (Attack::ByteLimit, MicroKind::Byte(ByteKind::Start)) => {
      Some((1 + STATE_WORDS + 6, F128::new(0, 1)))
    },
    (Attack::HashMask, MicroKind::Byte(ByteKind::HashMergeRequest)) => {
      Some((1 + bytes::MERGE_MASK, F128::new(2, 0)))
    },
    (Attack::HashCv, MicroKind::Byte(ByteKind::HashFinish)) => {
      Some((1 + bytes::CV, F128::ONE))
    },
    _ => None,
  };
  if let Some((at, delta)) = target {
    let row = rows
      .iter_mut()
      .find(|r| {
        r.0[0] == F128::ONE
          && (attack != Attack::HashCv
            || r.0[1 + bytes::POSITION].lo % 1024 != 0)
      })
      .unwrap();
    row.0[at] += delta;
    let local = MicroGate::new(3, gate.kind()).unwrap();
    let mut bits = vec![false; local.plan().k()];
    local
      .plan()
      .fill_row(&mut bits, |bits| crate::ixby::bits::fill_words(&row.0, bits));
    assert_eq!(
      crate::ixby::bits::read_words(
        &bits,
        gate.input_count(),
        gate.output_count()
      )
      .last(),
      Some(&F128::ZERO)
    );
    let r1cs = local.r1cs();
    bits.resize(r1cs.n(), false);
    assert!(r1cs.satisfies(&bits));
  }
  gate.generate_witness_into(&rows, dst)
}
fn order_driver(
  slot: SlotId,
  gate: &OrderGate,
  kind: OrderKind,
  attack_kind: Attack,
) -> Driver {
  Driver::new(slot, gate.clone(), gate.r1cs(), move |g, rows, attack, dst| {
    let mut rows = rows.to_vec();
    if attack != Attack::None && attack == attack_kind {
      let row = rows.iter_mut().find(|r| r.0[0] == F128::ONE).unwrap();
      row.0[1] += F128::ONE;
      let mut out = Vec::new();
      g.eval(&row.0, &(), &mut out);
      assert_eq!(out.last(), Some(&F128::ZERO));
      let local = OrderGate::new(3, kind).unwrap();
      let r1cs = local.r1cs();
      let plan = local.plan();
      let mut bits = vec![false; plan.k()];
      plan.fill_row(&mut bits, |bits| {
        crate::ixby::bits::fill_words(&row.0, bits)
      });
      bits.resize(r1cs.n(), false);
      assert!(r1cs.satisfies(&bits));
    }
    g.generate_witness_into(&rows, dst)
  })
}
fn drivers(emission: &BatchEmission, shape: &CircuitShape) -> Vec<Driver> {
  let nu = emission.class.nu();
  let mut result = Vec::new();
  for (slot, gate) in emission.execution.gates() {
    result.push(Driver::new(slot, gate.clone(), gate.r1cs(), micro_fill));
  }
  for (slot, gate) in emission.execution.code.gates() {
    result.push(Driver::new(
      slot,
      gate.clone(),
      gate.r1cs(),
      |g: &CodeGate, r, _, d| g.generate_witness_into(r, d),
    ));
  }
  let (slot, gate) = emission.execution.frame.frame_gate();
  result.push(Driver::new(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &FrameGate, r, _, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.frame.fuel_gate();
  result.push(Driver::new(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &Fuel64StepGate, r, _, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.numeric.route_gate();
  result.push(Driver::new(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &PrimitiveRouteGate, r, _, d| g.generate_witness_into(r, d),
  ));
  let (slot, gate) = emission.execution.numeric.nat.gate();
  result.push(Driver::new(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &Nat128Gate, r, _, d| g.generate_witness_into(r, d),
  ));
  let scalar = &emission.execution.numeric.scalar;
  let gate = PrimitivePrepareGate::new(
    nu,
    2,
    PrimitiveSet::crypto().crypto_scalar_subset(),
  )
  .unwrap();
  result.push(Driver::new(
    scalar.prepare,
    gate.clone(),
    gate.r1cs(),
    |g: &PrimitivePrepareGate, r, _, d| g.generate_witness_into(r, d),
  ));
  result.push(Driver::new(
    scalar.finish,
    scalar.finish_gate.clone(),
    scalar.finish_gate.r1cs(),
    |g: &PrimitiveFinishGate, r, _, d| g.generate_witness_into(r, d),
  ));
  let gate = SelectWordsGate::new(nu, 2).unwrap();
  result.push(Driver::new(
    emission.execution.numeric.select_slot(),
    gate.clone(),
    gate.r1cs(),
    |g: &SelectWordsGate, r, _, d| g.generate_witness_into(r, d),
  ));
  let a = &scalar.arithmetic;
  result.push(Driver::new(
    a.add,
    GoldilocksAddPairGate { nu },
    goldilocks::build_goldilocks_add_r1cs(nu),
    move |_: &GoldilocksAddPairGate, r, _, d| {
      goldilocks::generate_goldilocks_add_witness_into(r, nu, d)
    },
  ));
  result.push(Driver::new(
    a.mul,
    GoldilocksMulPairGate { nu },
    multiplication::build_goldilocks_mul_r1cs(nu),
    move |_: &GoldilocksMulPairGate, r, _, d| {
      multiplication::generate_goldilocks_mul_witness_into(r, nu, d)
    },
  ));
  result.push(Driver::new(
    a.canonical,
    CanonicalGoldilocksQuadGate { nu },
    goldilocks::build_canonical_quad_r1cs(nu),
    move |_: &CanonicalGoldilocksQuadGate, r, _, d| {
      goldilocks::generate_canonical_quad_witness_into(r, nu, d)
    },
  ));
  result.push(Driver::new(
    a.repack,
    GoldilocksLaneRepackGate { nu },
    extension::build_lane_repack_r1cs(nu),
    move |_: &GoldilocksLaneRepackGate, r, _, d| {
      extension::generate_lane_repack_witness_into(r, nu, d)
    },
  ));
  let (slot, gate) = emission.order.prepare_gate();
  result.push(order_driver(
    slot,
    gate,
    OrderKind::Prepare(STATE_WORDS),
    Attack::OrderClock,
  ));
  let (slot, gate) = emission.order.audit_gate();
  result.push(order_driver(
    slot,
    gate,
    OrderKind::Audit(STATE_WORDS),
    Attack::None,
  ));
  let (slot, gate) = emission.memory.prepare_gate();
  result.push(order_driver(slot, gate, OrderKind::Access, Attack::MemoryClock));
  let log = emission.memory.log();
  for (slot, gate) in log.memory().gates() {
    result.push(Driver::new(
      slot,
      gate.clone(),
      gate.r1cs(),
      |g: &MemoryGate, r, _, d| g.generate_witness_into(r, d),
    ));
  }
  if let Some(tree) = &emission.tree {
    for (slot, gate) in tree.gates() {
      result.push(Driver::new(
        slot,
        gate.clone(),
        gate.r1cs(),
        |g: &MultiGate, r, _, d| g.generate_witness_into(r, d),
      ));
    }
  }
  let (slot, gate) = log.audit_gate();
  result.push(Driver::new(
    slot,
    gate.clone(),
    gate.r1cs(),
    |g: &AuditGate, r, _, d| g.generate_witness_into(r, d),
  ));
  for (slot, table) in log.memory().compression().tables() {
    result.push(Driver::new(
      slot,
      Blake3Gate { nu },
      table,
      move |_: &Blake3Gate, r, attack, d| {
        let mut rows = r.to_vec();
        if attack == Attack::HashCounter {
          let row = rows
            .iter_mut()
            .find(|r| {
              r.2 == 1
                && r.3 == 1
                && r.4 == crate::hash::CHUNK_START | crate::hash::CHUNK_END
            })
            .unwrap();
          row.2 ^= 1;
        } else if attack == Attack::HashRoot {
          let row = rows
            .iter_mut()
            .find(|r| {
              r.3 == 64 && r.4 == crate::hash::PARENT | crate::hash::ROOT
            })
            .unwrap();
          row.4 ^= crate::hash::ROOT;
        }
        flock_blake3::generate_witness_batch_major_partial_into(&rows, nu, d)
      },
    ));
  }
  result.sort_by_key(|d| shape.registry_slot(d.slot));
  for (i, d) in result.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot), i);
  }
  assert_eq!(
    result.len() + 2 + usize::from(emission.tree.is_some()),
    shape.counts.len()
  );
  result
}
fn setup(class: BatchClass) -> (BatchEmission, CircuitShape, Vec<Driver>) {
  let mut b = ShapeBuilder::new(class.nu());
  let emission = emit_batch(&mut b, class).unwrap();
  let shape = b.finish().unwrap();
  let drivers = drivers(&emission, &shape);
  (emission, shape, drivers)
}
fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m));
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
fn prove(
  emission: &BatchEmission,
  shape: &CircuitShape,
  drivers: &[Driver],
  witness: &CircuitWitness,
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let boolean = drivers.iter().map(|d| d.prover(witness, attack)).collect();
  let mut switches = vec![
    emission.order.permutation().gate(),
    emission.memory.log().permutation().gate(),
  ];
  if let Some(tree) = &emission.tree {
    switches.push(tree.permutation().gate());
  }
  switches.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  let nu = emission.class.nu();
  let element = switches
    .into_iter()
    .map(|(slot, gate)| {
      let rows = witness.rows::<SwitchGate>(slot).to_vec();
      UnionElementSlotInput::new(move |dst| gate.fill_witness(&rows, nu, dst))
    })
    .collect();
  let mut challenger =
    FsChallenger::with_chained_blake3(domain(emission.class));
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params(&union),
    boolean,
    element,
    &mut challenger,
  );
  codec().serialize(&Bundle { magic: MAGIC, commitment, proof }).unwrap()
}
fn verify(
  emission: &BatchEmission,
  shape: &CircuitShape,
  drivers: &[Driver],
  expected: &[F128],
  proof: &[u8],
) -> Result<()> {
  let public = emission.public.instantiate(expected)?;
  ensure!(proof.len() as u64 <= MAX_BYTES, "paged execution proof size");
  let bundle: Bundle = codec().deserialize(proof)?;
  ensure!(
    bundle.magic == MAGIC && codec().serialize(&bundle)? == proof,
    "paged execution envelope"
  );
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let circuits = drivers
    .iter()
    .map(|d| d.table.csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect::<Vec<_>>();
  let mut challenger =
    FsChallenger::with_chained_blake3(domain(emission.class));
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &public,
    &circuits,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|e| anyhow::anyhow!("paged execution proof rejected: {e:?}"))?;
  Ok(())
}
fn isolated(test: &str, expected: &[F128], proof: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", test, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for word in expected {
    stdin.write_all(&word.lo.to_le_bytes()).unwrap();
    stdin.write_all(&word.hi.to_le_bytes()).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  if !output.status.success() {
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
  }
  output.status.success()
}
#[test]
#[ignore = "real mixed instruction/state-order/fuel/memory proof and independently verified malicious-row rejections"]
fn instruction_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows() {
  proof_test(
    BatchClass::Small,
    TEST,
    tests::fixture,
    &[
      Attack::Fetch,
      Attack::Operand,
      Attack::Numeric,
      Attack::Call,
      Attack::Return,
      Attack::Fuel,
      Attack::OrderClock,
      Attack::MemoryClock,
    ],
  );
}
#[test]
#[ignore = "real object/application instruction proof, fresh receiver and recomputed malformed heap/splice/alternative rows"]
fn object_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows() {
  proof_test(
    BatchClass::Objects,
    OBJECT_TEST,
    object_tests::fixture,
    &[
      Attack::Field,
      Attack::HeapReservation,
      Attack::Closure,
      Attack::Splice,
      Attack::Alternative,
      Attack::StoreIndex,
      Attack::ApplyDeclaration,
      Attack::OrderClock,
      Attack::MemoryClock,
    ],
  );
}
#[test]
#[ignore = "real byte instruction proof, isolated verification and recomputed range/limit/value substitutions"]
fn byte_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows() {
  proof_test(
    BatchClass::Bytes,
    BYTE_TEST,
    byte_tests::fixture,
    &[
      Attack::BytePointer,
      Attack::ByteAllocation,
      Attack::ByteConversion,
      Attack::ByteCopy,
      Attack::ByteEquality,
      Attack::ByteLimit,
    ],
  );
}
#[test]
#[ignore = "real unaligned multi-chunk BLAKE3 execution proof, isolated verification and recomputed compression/merge substitutions"]
fn chunk_tree_hash_proves_fresh_and_rejects_recomputed_hash_rows() {
  proof_test(
    BatchClass::Bytes,
    HASH_TEST,
    byte_tests::hash_fixture,
    &[
      Attack::BytePointer,
      Attack::HashCounter,
      Attack::HashRoot,
      Attack::HashMask,
      Attack::HashCv,
    ],
  );
}
fn proof_test(
  class: BatchClass,
  test: &str,
  fixture: fn() -> (BatchAdvice, Vec<RowAdvice>),
  attacks: &[Attack],
) {
  let setup_start = std::time::Instant::now();
  let (emission, shape, drivers) = setup(class);
  let setup_elapsed = setup_start.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(MAX_BYTES + OUTPUTS as u64 * 16 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(
      (OUTPUTS * 16..=MAX_BYTES as usize + OUTPUTS * 16).contains(&bytes.len())
    );
    let expected = bytes[..OUTPUTS * 16]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|w| pack_bytes(w))
      .collect::<Vec<_>>();
    verify(&emission, &shape, &drivers, &expected, &bytes[OUTPUTS * 16..])
      .unwrap();
    return;
  }
  let (advice, _) = fixture();
  let witness =
    shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(advice.expected.len(), OUTPUTS);
  assert_eq!(
    witness.public,
    emission.public.instantiate(&advice.expected).unwrap()
  );
  let start = std::time::Instant::now();
  let geometry = UnionInstance::new(&shape.registry, shape.counts.clone());
  eprintln!(
    "paged execution geometry: M={}, dense={} words",
    geometry.dense_m(),
    geometry.dense_words()
  );
  let proof = prove(&emission, &shape, &drivers, &witness, Attack::None);
  let prove_elapsed = start.elapsed();
  verify(&emission, &shape, &drivers, &advice.expected, &proof).unwrap();
  assert!(isolated(test, &advice.expected, &proof));
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  eprintln!(
    "paged execution proof: {} bytes, setup {setup_elapsed:?}, prove {prove_elapsed:?}, M={}, dense={} words",
    proof.len(),
    union.dense_m(),
    union.dense_words()
  );
  for at in 0..advice.expected.len() {
    let mut bad = advice.expected.clone();
    bad[at] += F128::ONE;
    assert!(
      verify(&emission, &shape, &drivers, &bad, &proof).is_err(),
      "accepted public word {at}"
    );
  }
  let mut bad_limit = advice.expected.clone();
  bad_limit[2].hi ^= 1;
  assert!(verify(&emission, &shape, &drivers, &bad_limit, &proof).is_err());
  assert!(
    verify(
      &emission,
      &shape,
      &drivers,
      &advice.expected,
      &proof[..proof.len() - 1]
    )
    .is_err()
  );
  let mut extended = proof.clone();
  extended.push(0);
  assert!(
    verify(&emission, &shape, &drivers, &advice.expected, &extended).is_err()
  );
  for &attack in attacks {
    let bad = prove(&emission, &shape, &drivers, &witness, attack);
    let error =
      verify(&emission, &shape, &drivers, &advice.expected, &bad).unwrap_err();
    eprintln!("recomputed {attack:?} rejected: {error}");
    assert!(format!("{error}").contains("Wiring"));
  }
}

pub(super) fn original_proof_test(
  class: BatchClass,
  test: &str,
  fixture: fn() -> (BatchAdvice, Vec<RowAdvice>),
) {
  proof_test(class, test, fixture, &[Attack::OrderClock, Attack::MemoryClock]);
}
