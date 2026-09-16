use super::{
  super::{MemoryDepth, MultiUpdate, SparseMemory},
  tests::{Emission, checked, fixture, setup},
  *,
};
use crate::{
  hash::{Blake3Gate, pack_bytes},
  ixby::memory_log::SwitchGate,
  sizing::CountedGate,
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, CircuitWitness, GateType, SlotId},
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

const MAGIC: [u8; 8] = *b"IXFMTV00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_MULTI_MEMORY_VERIFY_CHILD";
#[derive(Clone, Copy)]
struct Class {
  nu: usize,
  leaves: usize,
  parents: usize,
  domain: &'static [u8],
  test: &'static str,
}
const SMALL: Class = Class {
  nu: 9,
  leaves: 3,
  parents: 48,
  domain: b"IxBy/Flock/shared-memory:depth40:leaves3:parents48:v0",
  test: "ixby::auth_memory::multi::proof_tests::shared_memory_tree_proves_fresh_and_rejects_recomputed_claims",
};
const BENCHMARK: Class = Class {
  nu: 10,
  leaves: 96,
  parents: 192,
  domain: b"IxBy/Flock/shared-memory:depth40:leaves96:parents192:v0",
  test: "ixby::auth_memory::multi::proof_tests::shared_memory_tree_benchmark_proves_actual_clustered_updates",
};
impl Class {
  fn capacity(self) -> MultiCapacity {
    MultiCapacity::new(self.leaves, self.parents).unwrap()
  }
  fn outputs(self) -> usize {
    4 + 5 * self.leaves
  }
  fn setup(self) -> (Emission, CircuitShape, Vec<Driver>) {
    let (e, shape) =
      setup(self.nu, MemoryDepth::new(40).unwrap(), self.capacity());
    let mut drivers = e
      .slots
      .gates()
      .map(|(s, g)| Driver::Multi(s, g.clone(), g.r1cs()))
      .collect::<Vec<_>>();
    drivers.extend(
      e.slots
        .compression()
        .tables()
        .into_iter()
        .map(|(s, t)| Driver::Blake(s, t)),
    );
    drivers.sort_by_key(|d| shape.registry_slot(d.slot()));
    for (i, d) in drivers.iter().enumerate() {
      assert_eq!(shape.registry_slot(d.slot()), i);
    }
    assert_eq!(drivers.len() + 1, shape.counts.len());
    (e, shape, drivers)
  }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Leaf,
  ParentPosition,
  ParentLevel,
  Child,
  ParentHash,
  Frontier,
  Equality,
  Route,
  Cell,
  Flags,
  Activation,
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
  Multi(SlotId, MultiGate, BlockR1cs),
  Blake(SlotId, BlockR1cs),
}
impl Driver {
  fn slot(&self) -> SlotId {
    match self {
      Self::Multi(s, ..) | Self::Blake(s, ..) => *s,
    }
  }
  fn table(&self) -> &BlockR1cs {
    match self {
      Self::Multi(_, _, t) | Self::Blake(_, t) => t,
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &CircuitWitness,
    attack: Attack,
    nu: usize,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Multi(slot, gate, table) => {
        let mut rows = witness.rows::<MultiGate>(*slot).to_vec();
        let mut changed = false;
        match (gate.kind(), attack) {
          (MultiKind::Leaf, Attack::Leaf) => {
            rows[0].0[0] += F128::ONE;
            changed = true;
          },
          (MultiKind::Parent, Attack::ParentPosition) => {
            rows[0].0[1].hi ^= 1;
            changed = true;
          },
          (MultiKind::Parent, Attack::ParentLevel) => {
            rows[0].0[1].lo += 1;
            changed = true;
          },
          (MultiKind::Parent, Attack::Child) => {
            rows[0].0[2] += F128::ONE;
            changed = true;
          },
          (MultiKind::Parent, Attack::ParentHash) => {
            rows[0].0[10] += F128::ONE;
            changed = true;
          },
          (MultiKind::Frontier, Attack::Frontier) => {
            rows[0].0[2] += F128::ONE;
            changed = true;
          },
          (MultiKind::Equal, Attack::Equality) => {
            rows[0].0[2] += F128::ONE;
            rows[0].0[8] += F128::ONE;
            changed = true;
          },
          (MultiKind::Parent, Attack::Activation) => {
            let row = rows.iter_mut().find(|r| r.0[0] == F128::ZERO).unwrap();
            row.0[0] = F128::ONE;
            row.0[1] = F128::new(1, 0);
            assert_eq!(checked(gate, &row.0).last(), Some(&F128::ZERO));
          },
          _ => {},
        }
        if changed {
          assert_eq!(checked(gate, &rows[0].0).last(), Some(&F128::ZERO));
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
        if attack == Attack::Flags {
          rows
            .iter_mut()
            .find(|r| r.4 == crate::hash::PARENT | crate::hash::ROOT)
            .unwrap()
            .4 ^= crate::hash::ROOT;
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
  e: &Emission,
  shape: &CircuitShape,
  drivers: &[Driver],
  witness: &CircuitWitness,
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let boolean =
    drivers.iter().map(|d| d.prover(witness, attack, class.nu)).collect();
  let (slot, gate) = e.slots.permutation().gate();
  let mut rows = witness.rows::<SwitchGate>(slot).to_vec();
  if attack == Attack::Route {
    let mut input = rows[0].0[..gate.input_count()].to_vec();
    input[0] += F128::ONE;
    rows[0] = gate.eval(&input, &(), &mut Vec::new());
    let mut z = vec![F128::ZERO; gate.element_table().width() << class.nu];
    gate.fill_witness(&rows, class.nu, &mut z);
    assert!(gate.element_table().satisfies(&z, class.nu, rows.len()));
  }
  let element = UnionElementSlotInput::new(move |dst| {
    gate.fill_witness(&rows, class.nu, dst)
  });
  let mut ch = FsChallenger::with_chained_blake3(class.domain);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params(&union),
    boolean,
    vec![element],
    &mut ch,
  );
  codec().serialize(&Bundle { magic: MAGIC, commitment, proof }).unwrap()
}
fn verify(
  class: Class,
  e: &Emission,
  shape: &CircuitShape,
  drivers: &[Driver],
  expected: &[F128],
  bytes: &[u8],
) -> Result<()> {
  ensure!(bytes.len() as u64 <= MAX_BYTES, "shared memory proof size");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == MAGIC && codec().serialize(&bundle)? == bytes,
    "shared memory envelope"
  );
  let public = e.public.instantiate(expected)?;
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let circuits = drivers
    .iter()
    .map(|d| d.table().csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect::<Vec<_>>();
  let mut ch = FsChallenger::with_chained_blake3(class.domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &public,
    &circuits,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut ch,
  )
  .map_err(|e| anyhow::anyhow!("shared memory proof rejected: {e:?}"))
  .map(|_| ())
}
fn isolated(class: Class, expected: &[F128], proof: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args([
      "--ignored",
      "--exact",
      class.test,
      "--test-threads=1",
      "--nocapture",
    ])
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
    eprintln!(
      "fresh receiver failed: {} {}",
      String::from_utf8_lossy(&output.stdout),
      String::from_utf8_lossy(&output.stderr)
    );
  }
  output.status.success()
}
fn benchmark_fixture() -> MultiUpdate {
  let depth = MemoryDepth::new(40).unwrap();
  let mut memory = SparseMemory::from_cells(
    depth,
    (0..192u64).flat_map(|i| {
      [
        ((8 << 36) + i, [F128::new(i, !i), F128::new(!i, i)]),
        ((4 << 36) + i, [F128::new(!i, i), F128::new(i, !i)]),
      ]
    }),
  )
  .unwrap();
  memory
    .replace_many((0..96u64).map(|i| {
      let address = if i < 64 { (8 << 36) + i } else { (4 << 36) + i - 64 };
      (
        address,
        if i & 3 == 0 {
          [F128::ZERO; 2]
        } else {
          [F128::new(i + 7, i + 11), F128::new(i + 13, i + 17)]
        },
      )
    }))
    .unwrap()
}
fn run(class: Class, fixture: fn() -> MultiUpdate, attacks: &[Attack]) {
  let started = Instant::now();
  let (e, shape, drivers) = class.setup();
  let setup_time = started.elapsed();
  if std::env::var_os(CHILD).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(MAX_BYTES + class.outputs() as u64 * 16 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    let end = class.outputs() * 16;
    assert!((end..=end + MAX_BYTES as usize).contains(&bytes.len()));
    let expected = bytes[..end]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|b| pack_bytes(b))
      .collect::<Vec<_>>();
    verify(class, &e, &shape, &drivers, &expected, &bytes[end..]).unwrap();
    return;
  }
  let update = fixture();
  let advice = MultiAdvice::new(class.capacity(), &update).unwrap();
  let witness = shape.run(&e.inputs.assign(&advice.private).unwrap(), &[]);
  assert_eq!(witness.public, e.public.instantiate(&advice.expected).unwrap());
  let started = Instant::now();
  let proof = prove(class, &e, &shape, &drivers, &witness, Attack::None);
  let prove_time = started.elapsed();
  verify(class, &e, &shape, &drivers, &advice.expected, &proof).unwrap();
  assert!(isolated(class, &advice.expected, &proof));
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  eprintln!(
    "shared memory: leaves={} parents={}/{} frontier={} compressions={} proof={} setup={setup_time:?} prove={prove_time:?} M={} dense={} words",
    class.leaves,
    update.parents.len(),
    class.parents,
    update.frontier.len(),
    class.capacity().compressions(),
    proof.len(),
    union.dense_m(),
    union.dense_words()
  );
  for at in 0..advice.expected.len() {
    let mut bad = advice.expected.clone();
    bad[at] += F128::ONE;
    assert!(
      verify(class, &e, &shape, &drivers, &bad, &proof).is_err(),
      "accepted expected word {at}"
    );
  }
  assert!(
    verify(
      class,
      &e,
      &shape,
      &drivers,
      &advice.expected,
      &proof[..proof.len() - 1]
    )
    .is_err()
  );
  let mut extra = proof.clone();
  extra.push(0);
  assert!(
    verify(class, &e, &shape, &drivers, &advice.expected, &extra).is_err()
  );
  for &attack in attacks {
    let bad = prove(class, &e, &shape, &drivers, &witness, attack);
    let error =
      verify(class, &e, &shape, &drivers, &advice.expected, &bad).unwrap_err();
    eprintln!("recomputed {attack:?} rejected: {error}");
    assert!(format!("{error}").contains("Wiring"));
  }
}
#[test]
#[ignore = "real shared-path memory proof with isolated verification and locally valid recomputed attacks"]
fn shared_memory_tree_proves_fresh_and_rejects_recomputed_claims() {
  run(
    SMALL,
    || fixture(MemoryDepth::new(40).unwrap()),
    &[
      Attack::Leaf,
      Attack::ParentPosition,
      Attack::ParentLevel,
      Attack::Child,
      Attack::ParentHash,
      Attack::Frontier,
      Attack::Equality,
      Attack::Route,
      Attack::Cell,
      Attack::Flags,
      Attack::Activation,
    ],
  );
}
#[test]
#[ignore = "actual 96-cell depth-40 memory multiproof benchmark with a fresh receiver"]
fn shared_memory_tree_benchmark_proves_actual_clustered_updates() {
  run(BENCHMARK, benchmark_fixture, &[]);
}
