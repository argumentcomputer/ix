//! Real memory proofs. Execution control is a separate caller of these rows.
use super::{
  tests::{arena_fixture, arena_setup, fixture, setup},
  *,
};
use crate::hash::Blake3Gate;
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, CircuitWitness},
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
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const NU: usize = 8;
const DEPTH: usize = 16;
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_MEMORY_VERIFY_CHILD";
#[derive(Clone, Copy)]
enum Relation {
  Memory,
  Arena,
}
impl Relation {
  fn magic(self) -> [u8; 8] {
    match self {
      Self::Memory => *b"IXFMEM00",
      Self::Arena => *b"IXFARN00",
    }
  }
  fn domain(self) -> &'static [u8] {
    match self {
      Self::Memory => b"IxBy/Flock/memory:depth16:writes3:reads1:v0",
      Self::Arena => b"IxBy/Flock/arena:depth16:allocations3:reads1:v0",
    }
  }
  fn outputs(self) -> usize {
    match self {
      Self::Memory => 16,
      Self::Arena => 18,
    }
  }
  fn test(self) -> &'static str {
    match self {
      Self::Memory => {
        "ixby::auth_memory::proof_tests::mutable_memory_proofs_verify_in_isolation_and_reject_recomputed_accesses"
      },
      Self::Arena => {
        "ixby::auth_memory::proof_tests::immutable_arena_proof_binds_allocated_prefix_and_zero_old_cells"
      },
    }
  }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Address,
  PathAddress,
  Level,
  Sibling,
  Cell,
  Counter,
  ParentFlags,
  Allocation,
  ReadPrefix,
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
  Memory { slot: SlotId, gate: MemoryGate, table: BlockR1cs },
  Blake { slot: SlotId, table: BlockR1cs },
}
impl Driver {
  fn slot(&self) -> SlotId {
    match self {
      Self::Memory { slot, .. } | Self::Blake { slot, .. } => *slot,
    }
  }
  fn table(&self) -> &BlockR1cs {
    match self {
      Self::Memory { table, .. } | Self::Blake { table, .. } => table,
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &CircuitWitness,
    attack: Attack,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Memory { slot, gate, table } => {
        let mut rows = witness.rows::<MemoryGate>(*slot).to_vec();
        let change = match (gate.kind(), attack) {
          (MemoryGateKind::Address, Attack::Address)
          | (MemoryGateKind::Path, Attack::PathAddress) => Some(0),
          (MemoryGateKind::Path, Attack::Level) => Some(1),
          (MemoryGateKind::Path, Attack::Sibling) => Some(4),
          _ => None,
        };
        if let Some(word) = change {
          rows[0].0[word] += F128::ONE;
          assert_eq!(
            tests::checked(gate, &rows[0].0).last(),
            Some(&F128::ZERO)
          );
        }
        if gate.kind() == MemoryGateKind::Index {
          let at = match attack {
            Attack::Allocation => {
              // Recompute a valid allocation at zero while the real carried
              // counter and memory address are one.
              rows[1].0[0] = F128::ZERO;
              rows[1].0[1] = F128::ZERO;
              Some(1)
            },
            Attack::ReadPrefix => {
              // A locally valid read at three under a forged count of four;
              // the actual initialized prefix has only three cells.
              rows[3].0[0] = F128::new(3, 0);
              rows[3].0[1] = F128::new(4, 0);
              Some(3)
            },
            _ => None,
          };
          if let Some(at) = at {
            assert_eq!(tests::checked(gate, &rows[at].0)[1], F128::ZERO);
          }
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Blake { slot, table } => {
        let mut rows = witness.rows::<Blake3Gate>(*slot).to_vec();
        match attack {
          Attack::Cell => rows[0].1[8] ^= 1,
          Attack::Counter => rows[0].2 ^= 1,
          Attack::ParentFlags => rows[1].4 ^= ROOT,
          _ => {},
        }
        UnionSlotProverInput::in_place(
          move |mut dst| {
            dst.elide_padding_writes = false;
            flock_blake3::generate_witness_batch_major_partial_into(
              &rows, NU, dst,
            )
          },
          table.csc_lincheck_circuit(),
        )
      },
    }
  }
}
fn drivers(slots: &MemoryAccessSlots, shape: &CircuitShape) -> Vec<Driver> {
  let mut drivers = slots
    .gates()
    .into_iter()
    .map(|(slot, gate)| Driver::Memory {
      slot,
      gate: gate.clone(),
      table: gate.r1cs(),
    })
    .collect::<Vec<_>>();
  drivers.extend(
    slots
      .compression()
      .tables()
      .into_iter()
      .map(|(slot, table)| Driver::Blake { slot, table }),
  );
  drivers.sort_by_key(|driver| shape.registry_slot(driver.slot()));
  drivers
}
fn arena_drivers(
  slots: &ImmutableArenaSlots,
  shape: &CircuitShape,
) -> Vec<Driver> {
  let mut drivers = drivers(slots.memory(), shape);
  let (slot, gate) = slots.index_gate();
  drivers.push(Driver::Memory { slot, gate: gate.clone(), table: gate.r1cs() });
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
  relation: Relation,
  shape: &CircuitShape,
  drivers: &[Driver],
  witness: &CircuitWitness,
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let inputs =
    drivers.iter().map(|driver| driver.prover(witness, attack)).collect();
  let mut ch = FsChallenger::with_chained_blake3(relation.domain());
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params(&union),
    inputs,
    vec![],
    &mut ch,
  );
  codec()
    .serialize(&Bundle { magic: relation.magic(), commitment, proof })
    .unwrap()
}
fn verify(relation: Relation, expected: &[F128], bytes: &[u8]) -> Result<()> {
  let depth = MemoryDepth::new(DEPTH)?;
  let (shape, public, drivers) = match relation {
    Relation::Memory => {
      let (emission, shape) = setup(NU, depth);
      let public = emission.public.instantiate(expected)?;
      let drivers = drivers(&emission.slots, &shape);
      (shape, public, drivers)
    },
    Relation::Arena => {
      let (emission, shape) = arena_setup(NU, depth);
      let public = emission.public.instantiate(expected)?;
      let drivers = arena_drivers(&emission.slots, &shape);
      (shape, public, drivers)
    },
  };
  ensure!(bytes.len() as u64 <= MAX_BYTES, "memory proof size");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    bundle.magic == relation.magic() && codec().serialize(&bundle)? == bytes,
    "memory proof envelope"
  );
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let circuits = drivers
    .iter()
    .map(|d| d.table().csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect::<Vec<_>>();
  let mut ch = FsChallenger::with_chained_blake3(relation.domain());
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
  .map_err(|error| anyhow::anyhow!("memory proof rejected: {error:?}"))?;
  Ok(())
}
fn isolated(relation: Relation, expected: &[F128], proof: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args([
      "--ignored",
      "--exact",
      relation.test(),
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
    eprintln!("{}", String::from_utf8_lossy(&output.stderr));
  }
  output.status.success()
}

fn child(relation: Relation) -> bool {
  if std::env::var_os(CHILD).is_none() {
    return false;
  }
  let public_bytes = relation.outputs() * 16;
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
    .map(|w| pack_bytes(w))
    .collect::<Vec<_>>();
  verify(relation, &expected, &bytes[public_bytes..]).unwrap();
  true
}

#[test]
#[ignore = "real memory read/write proofs and recomputed row substitutions"]
fn mutable_memory_proofs_verify_in_isolation_and_reject_recomputed_accesses() {
  let relation = Relation::Memory;
  if child(relation) {
    return;
  }
  let (emission, shape) = setup(NU, MemoryDepth::new(DEPTH).unwrap());
  let drivers = drivers(&emission.slots, &shape);
  for salt in [0, 0x0123456789abcdef, u64::MAX] {
    let (private, expected) = fixture(MemoryDepth::new(DEPTH).unwrap(), salt);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
    let proof = prove(relation, &shape, &drivers, &witness, Attack::None);
    assert!(isolated(relation, &expected, &proof));
    eprintln!("memory writes3/reads1/depth16: {} bytes", proof.len());
    if salt == 0 {
      for position in 0..expected.len() {
        let mut changed = expected.clone();
        changed[position] += F128::ONE;
        assert!(verify(relation, &changed, &proof).is_err());
      }
      for attack in [
        Attack::Address,
        Attack::PathAddress,
        Attack::Level,
        Attack::Sibling,
        Attack::Cell,
        Attack::Counter,
        Attack::ParentFlags,
      ] {
        let forged = prove(relation, &shape, &drivers, &witness, attack);
        assert!(!isolated(relation, &expected, &forged), "accepted {attack:?}");
        eprintln!("recomputed memory attack {attack:?} rejected");
      }
      let mut trailing = proof.clone();
      trailing.push(0);
      assert!(verify(relation, &expected, &trailing).is_err());
      assert!(verify(relation, &expected, &proof[..proof.len() - 1]).is_err());
      let mut altered = proof.clone();
      altered[0] ^= 1;
      assert!(verify(relation, &expected, &altered).is_err());
    }
  }
}

#[test]
#[ignore = "real immutable allocation proof and recomputed allocation/read substitutions"]
fn immutable_arena_proof_binds_allocated_prefix_and_zero_old_cells() {
  let relation = Relation::Arena;
  if child(relation) {
    return;
  }
  let depth = MemoryDepth::new(DEPTH).unwrap();
  let (emission, shape) = arena_setup(NU, depth);
  let drivers = arena_drivers(&emission.slots, &shape);
  let (private, expected) = arena_fixture(depth);
  assert_eq!(expected.len(), relation.outputs());
  let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
  assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  let proof = prove(relation, &shape, &drivers, &witness, Attack::None);
  assert!(isolated(relation, &expected, &proof));
  eprintln!(
    "immutable arena allocations3/reads1/depth16: {} bytes",
    proof.len()
  );
  for position in 0..expected.len() {
    let mut changed = expected.clone();
    changed[position] += F128::ONE;
    assert!(verify(relation, &changed, &proof).is_err());
  }
  for attack in
    [Attack::Allocation, Attack::ReadPrefix, Attack::Cell, Attack::Address]
  {
    let forged = prove(relation, &shape, &drivers, &witness, attack);
    assert!(!isolated(relation, &expected, &forged), "accepted {attack:?}");
    eprintln!("recomputed arena attack {attack:?} rejected");
  }
  let mut trailing = proof.clone();
  trailing.push(0);
  assert!(verify(relation, &expected, &trailing).is_err());
  assert!(verify(relation, &expected, &proof[..proof.len() - 1]).is_err());
}
