use super::*;
use crate::{
  extension::{self, GoldilocksLaneRepackGate},
  goldilocks::{self, CanonicalGoldilocksQuadGate, GoldilocksAddPairGate},
  hash::{Blake3Gate, pack_bytes},
  ixby::{
    auth_memory::MemoryGate,
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

const DOMAIN: &[u8] = b"IxBy/Flock/paged-execution:small:v0";
const MAGIC: [u8; 8] = *b"IXFPGX00";
const MAX_BYTES: u64 = 16 * 1024 * 1024;
const OUTPUTS: usize = 57;
const TEST: &str = "ixby::paged_exec::proof_tests::instruction_batch_proves_fresh_and_rejects_locally_valid_recomputed_rows";
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
    _ => None,
  };
  if let Some((at, delta)) = target {
    let row = rows.iter_mut().find(|r| r.0[0] == F128::ONE).unwrap();
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
      move |_: &Blake3Gate, r, _, d| {
        flock_blake3::generate_witness_batch_major_partial_into(r, nu, d)
      },
    ));
  }
  result.sort_by_key(|d| shape.registry_slot(d.slot));
  for (i, d) in result.iter().enumerate() {
    assert_eq!(shape.registry_slot(d.slot), i);
  }
  assert_eq!(result.len() + 2, shape.counts.len());
  result
}
fn setup() -> (BatchEmission, CircuitShape, Vec<Driver>) {
  let mut b = ShapeBuilder::new(BatchClass::Small.nu());
  let emission = emit_batch(&mut b, BatchClass::Small).unwrap();
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
  switches.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  let nu = emission.class.nu();
  let element = switches
    .into_iter()
    .map(|(slot, gate)| {
      let rows = witness.rows::<SwitchGate>(slot).to_vec();
      UnionElementSlotInput::new(move |dst| gate.fill_witness(&rows, nu, dst))
    })
    .collect();
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
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
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
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
fn isolated(expected: &[F128], proof: &[u8]) -> bool {
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
  let setup_start = std::time::Instant::now();
  let (emission, shape, drivers) = setup();
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
  let (advice, _) = tests::fixture();
  let witness =
    shape.run(&emission.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(advice.expected.len(), OUTPUTS);
  assert_eq!(
    witness.public,
    emission.public.instantiate(&advice.expected).unwrap()
  );
  let start = std::time::Instant::now();
  let proof = prove(&emission, &shape, &drivers, &witness, Attack::None);
  let prove_elapsed = start.elapsed();
  verify(&emission, &shape, &drivers, &advice.expected, &proof).unwrap();
  assert!(isolated(&advice.expected, &proof));
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
  for attack in [
    Attack::Fetch,
    Attack::Operand,
    Attack::Numeric,
    Attack::Call,
    Attack::Return,
    Attack::Fuel,
    Attack::OrderClock,
    Attack::MemoryClock,
  ] {
    let bad = prove(&emission, &shape, &drivers, &witness, attack);
    let error =
      verify(&emission, &shape, &drivers, &advice.expected, &bad).unwrap_err();
    eprintln!("recomputed {attack:?} rejected: {error}");
    assert!(format!("{error}").contains("Wiring"));
  }
}
