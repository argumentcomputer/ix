//! Real isolated-verifier conformance for the global ledger only. Control
//! words are private test inputs, NOT authenticated execution states. This is
//! not an Exec proof or a proof of the Init run.

use super::*;
use anyhow::{Context, Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder},
  hash::HashKind,
  pcs::{
    Commitment, PcsParams,
    ligerito::{LigeritoProfile, embedded_initial_k_or_default},
  },
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const NU: usize = 10;
const STEPS: usize = 6;
const DOMAIN: &[u8] = b"ix:ixby:wide-fuel-conformance:v0";
const MAGIC: [u8; 8] = *b"IXFUEL00";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD: &str = "IXBY_WIDE_FUEL_VERIFY_CHILD";
const TEST: &str = "ixby::wide_fuel::proof_tests::wide_ledgers_verify_in_fresh_process_and_reject_rebased_rows";

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

fn setup() -> (Fuel64StepGate, CircuitShape, SlotId) {
  let gate = Fuel64StepGate::new(NU).unwrap();
  let mut builder = ShapeBuilder::new(NU);
  let slot = Fuel64StepSlot::declare(&mut builder, gate.clone());
  let budget = builder.public_input();
  let mut fuel = builder.public_input();
  for _ in 0..STEPS {
    let control = builder.input();
    fuel = slot.step(&mut builder, fuel, control, budget);
  }
  builder.publish(fuel);
  (gate, builder.finish().unwrap(), slot.slot())
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

fn prove_rows(
  gate: &Fuel64StepGate,
  shape: &CircuitShape,
  rows: &[Fuel64StepRow],
  expected: &[F128; 4],
) -> Vec<u8> {
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    expected,
    &params(&union),
    vec![UnionSlotProverInput::in_place(
      |dst| gate.generate_witness_into(rows, dst),
      gate.r1cs().csc_lincheck_circuit(),
    )],
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { magic: MAGIC, commitment, proof }).unwrap()
}

fn verify(expected: &[F128; 4], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(expected[0] == F128::ZERO, "fixed wide-fuel validity pin");
  ensure!(bytes.len() as u64 <= MAX_BYTES, "wide-fuel proof byte budget");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(bundle.magic == MAGIC, "wrong wide-fuel proof domain");
  ensure!(
    codec().serialize(&bundle)? == bytes,
    "non-canonical wide-fuel proof"
  );
  let (gate, shape, _) = setup();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    expected,
    &[gate.r1cs().csc_lincheck_circuit()],
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|error| anyhow::anyhow!("wide-fuel proof rejected: {error:?}"))?;
  Ok(())
}

fn isolated(expected: &[F128; 4], proof: &[u8]) -> bool {
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
  let output = child.wait_with_output().unwrap();
  if !output.status.success() {
    eprintln!(
      "fresh wide-fuel verifier rejected: {}",
      String::from_utf8_lossy(&output.stderr)
    );
  }
  output.status.success()
}

fn child() -> Result<()> {
  let mut input = Vec::new();
  std::io::stdin().take(MAX_BYTES + 65).read_to_end(&mut input)?;
  ensure!(
    (64..=MAX_BYTES as usize + 64).contains(&input.len()),
    "wide-fuel verifier input length"
  );
  let expected: Vec<_> = input[..64]
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| {
      F128::new(
        u64::from_le_bytes(word[..8].try_into().unwrap()),
        u64::from_le_bytes(word[8..].try_into().unwrap()),
      )
    })
    .collect();
  verify(
    expected.as_slice().try_into().context("wide-fuel endpoint count")?,
    &input[64..],
    DOMAIN,
  )
}

#[test]
#[ignore = "real wide-fuel component proofs, isolated verification and recomputed cross-row forgery"]
fn wide_ledgers_verify_in_fresh_process_and_reject_rebased_rows() {
  if std::env::var_os(CHILD).is_some() {
    child().unwrap();
    return;
  }
  let (gate, shape, slot) = setup();
  assert_eq!(shape.registry_slot(slot), 0);
  for (budget, consumed, active) in [
    (16_000_000_000, u64::from(u32::MAX) - 2, 5),
    (16_000_000_000, 5_372_353_187, 3),
    (u64::MAX, u64::MAX - 1, 1),
  ] {
    let start = Fuel64 { remaining: budget - consumed, consumed }.word();
    let finish = Fuel64 {
      remaining: budget - consumed - active,
      consumed: consumed + active,
    }
    .word();
    let expected = [F128::ZERO, F128::new(budget, 0), start, finish];
    let mut input = expected[..3].to_vec();
    input.extend((0..STEPS).map(|step| {
      F128::new(if (step as u64) < active { (step % 2) as u64 } else { 2 }, 0)
    }));
    let witness = shape.run(&input, &[]);
    assert_eq!(witness.public, expected);
    let rows = witness.rows::<Fuel64StepGate>(slot);
    let proof = prove_rows(&gate, &shape, rows, &expected);
    assert!(isolated(&expected, &proof));
    eprintln!(
      "wide-fuel component: {} bytes; budget={budget}; consumed={consumed}; active={active}",
      proof.len()
    );
    for word in 1..4 {
      for high in [false, true] {
        let mut changed = expected;
        if high {
          changed[word].hi ^= 1 << 32;
        } else {
          changed[word].lo ^= 1 << 32;
        }
        assert!(verify(&changed, &proof, DOMAIN).is_err());
      }
    }
    let mut trailing = proof.clone();
    trailing.push(0);
    assert!(verify(&expected, &trailing, DOMAIN).is_err());
    assert!(verify(&expected, &proof[..proof.len() - 1], DOMAIN).is_err());
    let mut changed = proof.clone();
    changed[0] ^= 1;
    assert!(verify(&expected, &changed, DOMAIN).is_err());
    assert!(
      verify(&expected, &proof, b"ix:ixby:bank-read-conformance:v0").is_err()
    );
    if active == 5 {
      // Preserve the row's exact budget equation and recompute every derived
      // value, but rebase its starting counter away from the previous row.
      // Only global wiring—not a stale local residual—can reject this proof.
      let mut forged = rows.to_vec();
      forged[2].0[0].lo -= 1;
      forged[2].0[0].hi += 1;
      assert_eq!(evaluate(&forged[2])[1], F128::ZERO);
      let forged_proof = prove_rows(&gate, &shape, &forged, &expected);
      assert!(!isolated(&expected, &forged_proof));
    }
  }
}
