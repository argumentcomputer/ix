use super::{tests::*, *};
use crate::{
  hash::{Blake3Gate, pack_bytes},
  ixby::auth_memory::{MemoryDepth, MemoryGate},
  sizing::CountedGate,
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
  prover::{self, UnionElementSlotInput, UnionSlotProverInput},
  r1cs::BlockR1cs,
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
  time::Instant,
};

const MAGIC: [u8; 8] = *b"IXFLOG00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const TEST: &str = "ixby::memory_log::proof_tests::memory_log_proofs_verify_in_isolation_and_reject_recomputed_accesses";
const CHILD: &str = "IXBY_LOG_VERIFY_CHILD";
#[derive(Clone, Copy)]
struct Class {
  nu: usize,
  depth: usize,
  accesses: usize,
  cells: usize,
  domain: &'static [u8],
}
const CONFORMANCE: Class = Class {
  nu: 8,
  depth: 16,
  accesses: ACCESSES,
  cells: CELLS,
  domain: b"IxBy/Flock/memory-log:depth16:accesses10:cells4:v0",
};
const BENCHMARK: Class = Class {
  nu: 12,
  depth: 40,
  accesses: 512,
  cells: 32,
  domain: b"IxBy/Flock/memory-log:depth40:accesses512:cells32:v0",
};
const BENCH_TEST: &str =
  "ixby::memory_log::proof_tests::batched_memory_benchmark";
impl Class {
  fn outputs(self) -> usize {
    4 + 4 * self.accesses
  }
  fn setup(self) -> (LogEmission, CircuitShape) {
    let mut b = ShapeBuilder::new(self.nu);
    let emission = log_emit_counts(
      &mut b,
      self.nu,
      MemoryDepth::new(self.depth).unwrap(),
      self.accesses,
      self.cells,
    );
    (emission, b.finish().unwrap())
  }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Route,
  Record,
  ReadValue,
  ReadTime,
  Boundary,
  Cell,
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
enum Driver {
  Memory(SlotId, MemoryGate, BlockR1cs),
  Audit(SlotId, AuditGate, BlockR1cs),
  Blake(SlotId, BlockR1cs),
}
impl Driver {
  fn slot(&self) -> SlotId {
    match self {
      Self::Memory(slot, ..)
      | Self::Audit(slot, ..)
      | Self::Blake(slot, ..) => *slot,
    }
  }
  fn table(&self) -> &BlockR1cs {
    match self {
      Self::Memory(_, _, table)
      | Self::Audit(_, _, table)
      | Self::Blake(_, table) => table,
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &CircuitWitness,
    attack: Attack,
    nu: usize,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Memory(slot, gate, table) => {
        let rows = witness.rows::<MemoryGate>(*slot).to_vec();
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Audit(slot, gate, table) => {
        let mut rows = witness.rows::<AuditGate>(*slot).to_vec();
        if matches!(attack, Attack::ReadValue | Attack::ReadTime) {
          let row =
            rows.iter_mut().find(|r| r.0[7] == F128::new(READ, 0)).unwrap();
          if attack == Attack::ReadValue {
            row.0[3] += F128::ONE;
            row.0[8] += F128::ONE;
          } else {
            row.0[6].lo += 1;
          }
          assert_eq!(checked_audit(gate, &row.0), F128::ZERO);
        } else if attack == Attack::Boundary {
          rows[0].0[5].lo += 1;
          assert_eq!(checked_audit(gate, &rows[0].0), F128::ZERO);
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Blake(slot, table) => {
        let mut rows = witness.rows::<Blake3Gate>(*slot).to_vec();
        if attack == Attack::Cell {
          rows[0].1[8] ^= 1;
        }
        UnionSlotProverInput::in_place(
          move |mut dst| {
            dst.elide_padding_writes = false;
            flock_blake3::generate_witness_batch_major_partial_into(
              &rows, nu, dst,
            )
          },
          table.csc_lincheck_circuit(),
        )
      },
    }
  }
}
fn drivers(emission: &LogEmission, shape: &CircuitShape) -> Vec<Driver> {
  let mut drivers = emission
    .slots
    .memory()
    .gates()
    .into_iter()
    .map(|(slot, gate)| Driver::Memory(slot, gate.clone(), gate.r1cs()))
    .collect::<Vec<_>>();
  let (slot, gate) = emission.slots.audit_gate();
  drivers.push(Driver::Audit(slot, gate.clone(), gate.r1cs()));
  drivers.extend(
    emission
      .slots
      .memory()
      .compression()
      .tables()
      .into_iter()
      .map(|(slot, table)| Driver::Blake(slot, table)),
  );
  drivers.sort_by_key(|driver| shape.registry_slot(driver.slot()));
  drivers
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
  class: Class,
  emission: &LogEmission,
  shape: &CircuitShape,
  drivers: &[Driver],
  witness: &CircuitWitness,
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let boolean = drivers
    .iter()
    .map(|driver| driver.prover(witness, attack, class.nu))
    .collect();
  let (slot, gate) = emission.slots.permutation().gate();
  let mut rows = witness.rows::<SwitchGate>(slot).to_vec();
  if matches!(attack, Attack::Route | Attack::Record) {
    // Row zero constructs typed accesses. Row one is the first actual
    // permutation stage. Recompute every output and auxiliary product.
    let mut input = rows[1].0[..gate.input_count()].to_vec();
    let at = if attack == Attack::Route { 0 } else { 4 };
    input[at] += F128::ONE;
    rows[1] = gate.eval(&input, &(), &mut Vec::new());
    let mut z = vec![F128::ONE; gate.element_table().width() << class.nu];
    gate.fill_witness(&rows, class.nu, &mut z);
    assert!(gate.element_table().satisfies(&z, class.nu, rows.len()));
  }
  let element = UnionElementSlotInput::new(move |dst| {
    gate.fill_witness(&rows, class.nu, dst)
  });
  let mut challenger = FsChallenger::with_chained_blake3(class.domain);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params(&union),
    boolean,
    vec![element],
    &mut challenger,
  );
  codec().serialize(&Bundle { magic: MAGIC, commitment, proof }).unwrap()
}
fn verify(class: Class, expected: &[F128], bytes: &[u8]) -> Result<()> {
  let started = Instant::now();
  let (emission, shape) = class.setup();
  let public = emission.public.instantiate(expected)?;
  ensure!(bytes.len() as u64 <= MAX_BYTES, "memory log proof size");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
    "memory log proof envelope"
  );
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let drivers = drivers(&emission, &shape);
  let circuits = drivers
    .iter()
    .map(|d| d.table().csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect::<Vec<_>>();
  let setup_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let mut challenger = FsChallenger::with_chained_blake3(class.domain);
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
  .map_err(|error| anyhow::anyhow!("memory log proof rejected: {error:?}"))?;
  if class.accesses == BENCHMARK.accesses {
    eprintln!(
      "{{\"event\":\"verified\",\"setup_seconds\":{setup_seconds},\"verification_seconds\":{}}}",
      started.elapsed().as_secs_f64()
    );
  }
  Ok(())
}
fn isolated(class: Class, expected: &[F128], proof: &[u8]) -> bool {
  let test =
    if class.accesses == BENCHMARK.accesses { BENCH_TEST } else { TEST };
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
  if !output.status.success() || class.accesses == BENCHMARK.accesses {
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
  }
  output.status.success()
}

fn child(class: Class) -> bool {
  if std::env::var_os(CHILD).is_none() {
    return false;
  }
  let public_bytes = class.outputs() * 16;
  let mut bytes = Vec::new();
  std::io::stdin()
    .take(MAX_BYTES + public_bytes as u64 + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(
    (public_bytes..=MAX_BYTES as usize + public_bytes).contains(&bytes.len())
  );
  let expected = bytes[..public_bytes]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| pack_bytes(word))
    .collect::<Vec<_>>();
  verify(class, &expected, &bytes[public_bytes..]).unwrap();
  true
}

#[test]
#[ignore = "real authenticated memory log proofs with exact whole-record routing and malicious row substitutions"]
fn memory_log_proofs_verify_in_isolation_and_reject_recomputed_accesses() {
  let class = CONFORMANCE;
  if child(class) {
    return;
  }
  let depth = MemoryDepth::new(class.depth).unwrap();
  let (emission, shape) = class.setup();
  let drivers = drivers(&emission, &shape);
  for salt in [0, 0x0123456789abcdef, u64::MAX] {
    let (private, expected) = log_fixture(depth, salt);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
    let proof =
      prove(class, &emission, &shape, &drivers, &witness, Attack::None);
    assert!(isolated(class, &expected, &proof));
    eprintln!("memory log accesses10/cells4/depth16: {} bytes", proof.len());
    if salt == 0 {
      for at in 0..expected.len() {
        let mut changed = expected.clone();
        changed[at] += F128::ONE;
        assert!(verify(class, &changed, &proof).is_err());
      }
      for attack in [
        Attack::Route,
        Attack::Record,
        Attack::ReadValue,
        Attack::ReadTime,
        Attack::Boundary,
        Attack::Cell,
      ] {
        let forged =
          prove(class, &emission, &shape, &drivers, &witness, attack);
        assert!(!isolated(class, &expected, &forged), "accepted {attack:?}");
        eprintln!("recomputed memory log attack {attack:?} rejected");
      }
      let mut trailing = proof.clone();
      trailing.push(0);
      assert!(verify(class, &expected, &trailing).is_err());
      assert!(verify(class, &expected, &proof[..proof.len() - 1]).is_err());
    }
  }
}

fn benchmark_fixture(class: Class) -> (Vec<F128>, Vec<F128>) {
  use crate::ixby::auth_memory::SparseMemory;
  let initial = || {
    let mut memory = SparseMemory::new(MemoryDepth::new(class.depth).unwrap());
    for address in 0..class.cells as u64 {
      memory
        .replace(address, [F128::new(address, 1), F128::new(2, address)])
        .unwrap();
    }
    memory
  };
  let mut execution = initial();
  let mut private = execution.root().to_vec();
  let mut expected = private.clone();
  let mut records = Vec::new();
  for i in 0..class.accesses {
    let address = (i * 11 % class.cells) as u64;
    let write = i % 3 == 0;
    let value = if write {
      let value =
        [F128::new(i as u64, address), F128::new(address, !(i as u64))];
      execution.replace(address, value).unwrap();
      value
    } else {
      execution.open(address).unwrap().value
    };
    let fields = [
      F128::new(address, 0),
      F128::new(u64::from(write), 0),
      value[0],
      value[1],
    ];
    private.extend(fields);
    expected.extend(fields);
    records.push([
      fields[0],
      F128::new(i as u64 + 1, 0),
      F128::new(if write { WRITE } else { READ }, 0),
      value[0],
      value[1],
    ]);
  }
  let mut boundary = initial();
  for address in (0..class.cells as u64).rev() {
    let value = execution.open(address).unwrap().value;
    let old = boundary.replace(address, value).unwrap();
    private.extend(old.words());
    private.extend(value);
    records.push([
      F128::new(address, 0),
      F128::ZERO,
      F128::new(SEED, 0),
      old.value[0],
      old.value[1],
    ]);
    records.push([
      F128::new(address, 0),
      F128::new(u64::MAX, 0),
      F128::new(SEAL, 0),
      value[0],
      value[1],
    ]);
  }
  assert_eq!(execution.root(), boundary.root());
  expected.extend(execution.root());
  let plan = MemoryLogSlots::plan(class.accesses, class.cells).unwrap();
  records.resize(
    plan.lanes(),
    [F128::ZERO, F128::ZERO, F128::new(PAD, 0), F128::ZERO, F128::ZERO],
  );
  let mut order = (0..plan.lanes()).collect::<Vec<_>>();
  order.sort_by_key(|&i| {
    (records[i][2].lo == PAD, records[i][0].lo, records[i][1].lo)
  });
  let mut destination = vec![0; plan.lanes()];
  for (output, input) in order.into_iter().enumerate() {
    destination[input] = output;
  }
  private.extend(plan.route(&destination).unwrap());
  (private, expected)
}

#[test]
#[ignore = "measured 512-access memory batch; run with an explicit process memory cap"]
fn batched_memory_benchmark() {
  let class = BENCHMARK;
  if child(class) {
    return;
  }
  let started = Instant::now();
  let (emission, shape) = class.setup();
  let drivers = drivers(&emission, &shape);
  let setup_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let (private, expected) = benchmark_fixture(class);
  let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
  assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  let witness_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let proof = prove(class, &emission, &shape, &drivers, &witness, Attack::None);
  let proving_seconds = started.elapsed().as_secs_f64();
  assert!(isolated(class, &expected, &proof));
  eprintln!(
    "{{\"event\":\"proved\",\"accesses\":{},\"cells\":{},\"depth\":{},\"setup_seconds\":{setup_seconds},\"witness_seconds\":{witness_seconds},\"proving_seconds\":{proving_seconds},\"proof_bytes\":{}}}",
    class.accesses,
    class.cells,
    class.depth,
    proof.len()
  );
}
