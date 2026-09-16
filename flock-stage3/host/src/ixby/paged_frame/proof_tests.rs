use super::{batch_tests::*, *};
use crate::{
  hash::{Blake3Gate, pack_bytes},
  ixby::{
    auth_memory::MemoryGate,
    memory_log::{AuditGate, SwitchGate},
    wide_fuel::Fuel64StepGate,
  },
};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, CircuitWitness, GateType, SlotId},
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
};

const DOMAIN: &[u8] = b"IxBy/Flock/paged-frame:depth40:steps6:cells8:v0";
const MAGIC: [u8; 8] = *b"IXFFRM00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const TEST: &str = "ixby::paged_frame::proof_tests::frame_memory_proof_verifies_fresh_and_rejects_recomputed_steps";
const CHILD: &str = "IXBY_FRAME_VERIFY_CHILD";
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Attack {
  None,
  Target,
  Depth,
  CopyValue,
  SavedCaller,
  Fuel,
}
enum Driver {
  Frame(SlotId, FrameGate, BlockR1cs),
  Fuel(SlotId, Fuel64StepGate, BlockR1cs),
  Memory(SlotId, MemoryGate, BlockR1cs),
  Audit(SlotId, AuditGate, BlockR1cs),
  Blake(SlotId, BlockR1cs),
}
impl Driver {
  fn slot(&self) -> SlotId {
    match self {
      Self::Frame(s, ..)
      | Self::Fuel(s, ..)
      | Self::Memory(s, ..)
      | Self::Audit(s, ..)
      | Self::Blake(s, ..) => *s,
    }
  }
  fn table(&self) -> &BlockR1cs {
    match self {
      Self::Frame(_, _, t)
      | Self::Fuel(_, _, t)
      | Self::Memory(_, _, t)
      | Self::Audit(_, _, t)
      | Self::Blake(_, t) => t,
    }
  }
  fn prover<'a>(
    &'a self,
    witness: &CircuitWitness,
    attack: Attack,
  ) -> UnionSlotProverInput<'a> {
    match self {
      Self::Frame(slot, gate, table) => {
        let mut rows = witness.rows::<FrameGate>(*slot).to_vec();
        let changed = match attack {
          Attack::Target => {
            rows[0].0[5].lo ^= 1 << 8;
            Some(0)
          },
          Attack::Depth => {
            rows[2].0[0].lo ^= 1 << 48;
            Some(2)
          },
          Attack::CopyValue => {
            rows[2].0[11] += F128::ONE;
            Some(2)
          },
          Attack::SavedCaller => {
            rows[5].0[10].lo ^= 1 << 24;
            Some(5)
          },
          _ => None,
        };
        if let Some(index) = changed {
          let mut bits = vec![false; gate.plan().k()];
          gate.plan().fill_row(&mut bits, |bits| {
            crate::ixby::bits::fill_words(&rows[index].0, bits)
          });
          assert_eq!(
            crate::ixby::bits::read_words(&bits, 13, 19)[18],
            F128::ZERO
          );
          let table = gate.r1cs();
          bits.resize(table.n(), false);
          assert!(table.satisfies(&bits));
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Fuel(slot, gate, table) => {
        let mut rows = witness.rows::<Fuel64StepGate>(*slot).to_vec();
        if attack == Attack::Fuel {
          let mut output = Vec::new();
          rows[0] = gate.eval(
            &[F128::new(BUDGET, 0), F128::new(2, 0), F128::new(BUDGET, 0)],
            &(),
            &mut output,
          );
          assert_eq!(output[1], F128::ZERO);
        }
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Memory(slot, gate, table) => {
        let rows = witness.rows::<MemoryGate>(*slot).to_vec();
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Audit(slot, gate, table) => {
        let rows = witness.rows::<AuditGate>(*slot).to_vec();
        UnionSlotProverInput::in_place(
          move |dst| gate.generate_witness_into(&rows, dst),
          table.csc_lincheck_circuit(),
        )
      },
      Self::Blake(slot, table) => {
        let rows = witness.rows::<Blake3Gate>(*slot).to_vec();
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
fn drivers(emission: &Emission, shape: &CircuitShape) -> Vec<Driver> {
  let (slot, gate) = emission.frame.frame_gate();
  let mut drivers = vec![Driver::Frame(slot, gate.clone(), gate.r1cs())];
  let (slot, gate) = emission.frame.fuel_gate();
  drivers.push(Driver::Fuel(slot, gate.clone(), gate.r1cs()));
  drivers.extend(
    emission
      .memory
      .memory()
      .gates()
      .into_iter()
      .map(|(slot, gate)| Driver::Memory(slot, gate.clone(), gate.r1cs())),
  );
  let (slot, gate) = emission.memory.audit_gate();
  drivers.push(Driver::Audit(slot, gate.clone(), gate.r1cs()));
  drivers.extend(
    emission
      .memory
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
  emission: &Emission,
  shape: &CircuitShape,
  drivers: &[Driver],
  witness: &CircuitWitness,
  attack: Attack,
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let boolean = drivers.iter().map(|d| d.prover(witness, attack)).collect();
  let (slot, gate) = emission.memory.permutation().gate();
  let rows = witness.rows::<SwitchGate>(slot).to_vec();
  let element =
    UnionElementSlotInput::new(move |dst| gate.fill_witness(&rows, NU, dst));
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
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
fn verify(
  emission: &Emission,
  shape: &CircuitShape,
  drivers: &[Driver],
  expected: &[F128],
  proof: &[u8],
) -> Result<()> {
  let public = emission.public.instantiate(expected)?;
  ensure!(proof.len() as u64 <= MAX_BYTES, "frame proof size");
  let bundle: Bundle = codec().deserialize(proof)?;
  ensure!(
    bundle.magic == MAGIC && codec().serialize(&bundle)? == proof,
    "frame proof envelope"
  );
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let circuits = drivers
    .iter()
    .map(|d| d.table().csc_lincheck_circuit() as &dyn LincheckCircuit)
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
  .map_err(|error| anyhow::anyhow!("frame proof rejected: {error:?}"))?;
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
#[ignore = "real mixed frame/fuel/memory proof with fresh verification and recomputed malicious frame rows"]
fn frame_memory_proof_verifies_fresh_and_rejects_recomputed_steps() {
  let (emission, shape) = setup();
  let drivers = drivers(&emission, &shape);
  if std::env::var_os(CHILD).is_some() {
    let public_bytes = OUTPUTS * 16;
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
    verify(&emission, &shape, &drivers, &expected, &bytes[public_bytes..])
      .unwrap();
    return;
  }
  for salt in [0, u64::MAX] {
    let (private, expected) = fixture(salt);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
    let proof = prove(&emission, &shape, &drivers, &witness, Attack::None);
    assert!(isolated(&expected, &proof));
    eprintln!(
      "frame/memory six steps, four logical transitions, 18 accesses: {} bytes",
      proof.len()
    );
    if salt == 0 {
      for at in 0..expected.len() {
        let mut changed = expected.clone();
        changed[at] += F128::ONE;
        assert!(verify(&emission, &shape, &drivers, &changed, &proof).is_err());
      }
      for attack in [
        Attack::Target,
        Attack::Depth,
        Attack::CopyValue,
        Attack::SavedCaller,
        Attack::Fuel,
      ] {
        let forged = prove(&emission, &shape, &drivers, &witness, attack);
        assert!(!isolated(&expected, &forged), "accepted {attack:?}");
        eprintln!("recomputed frame attack {attack:?} rejected");
      }
      let mut trailing = proof.clone();
      trailing.push(0);
      assert!(
        verify(&emission, &shape, &drivers, &expected, &trailing).is_err()
      );
      assert!(
        verify(
          &emission,
          &shape,
          &drivers,
          &expected,
          &proof[..proof.len() - 1]
        )
        .is_err()
      );
    }
  }
}
