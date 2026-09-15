//! Real pinned-parameter compression-component proofs, NOT Exec or FFLONK.
//! Fresh verification uses only fixed setup, four expected output words and
//! proof bytes. It never obtains private CV/message/parameters or gate rows.

use super::{
  tests::{expected, setup},
  *,
};
use crate::{hash::pack_bytes, ixby::io::InputLayout};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::CircuitShape,
  hash::HashKind,
  lincheck::LincheckCircuit,
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

// The small tables' padded total width is 2^13. nu=9 admits baseline m22
// security configuration; nu=7 would not. No reduced-query fallback.
const NU: usize = 9;
const DOMAIN: &[u8] = b"ix:ixby:packed-blake3-compression-conformance:v0";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD_ENV: &str = "IXBY_PACKED_BLAKE3_VERIFY_CHILD";
const TEST: &str = "packed_blake3::proof_tests::private_compressions_verify_in_fresh_process_and_reject_broken_wiring";

#[derive(Serialize, Deserialize)]
struct Bundle {
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

fn tables(slots: &PackedBlake3, shape: &CircuitShape) -> Vec<BlockR1cs> {
  let mut tables: Vec<_> = slots
    .gates()
    .iter()
    .map(|(gate, slot)| (shape.registry_slot(*slot), gate.r1cs()))
    .collect();
  tables.sort_by_key(|(index, _)| *index);
  assert_eq!(tables.len(), shape.counts.len());
  for (expected, (index, _)) in tables.iter().enumerate() {
    assert_eq!(expected, *index);
  }
  tables.into_iter().map(|(_, table)| table).collect()
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert_eq!(m, 22);
  assert_eq!(union.m_total(), 22);
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
  slots: &PackedBlake3,
  layout: &InputLayout,
  shape: &CircuitShape,
  private: &[F128; 7],
  corrupt_wiring: bool,
) -> Vec<u8> {
  let witness = shape.run(&layout.assign(private).unwrap(), &[]);
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let tables = tables(slots, shape);
  let mut rows: Vec<_> = slots
    .gates()
    .iter()
    .map(|(gate, slot)| {
      (gate, *slot, witness.rows::<PackedWordGate>(*slot).to_vec())
    })
    .collect();
  if corrupt_wiring {
    let (_, _, rows) = rows
      .iter_mut()
      .find(|(gate, _, _)| gate.kind == PackedGateKind::Add)
      .unwrap();
    // The driver recomputes a VALID local sum/carry row from this altered
    // input. Rejection must come from the proof's fixed global wiring.
    rows[0].0[1].lo ^= 1;
  }
  rows.sort_by_key(|(_, slot, _)| shape.registry_slot(*slot));
  let drivers = rows
    .iter()
    .enumerate()
    .map(|(index, (gate, _, rows))| {
      UnionSlotProverInput::in_place(
        |dst| gate.generate_witness_into(rows, dst),
        tables[index].csc_lincheck_circuit(),
      )
    })
    .collect();
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params(&union),
    drivers,
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { commitment, proof }).unwrap()
}

fn verify(expected: &[F128; 4], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(
    bytes.len() as u64 <= MAX_BYTES,
    "packed compression proof byte admission"
  );
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(codec().serialize(&bundle)? == bytes, "canonical compression proof");
  let (slots, _, public, shape) = setup(NU);
  let public = public.instantiate(expected)?;
  let tables = tables(&slots, &shape);
  let linchecks: Vec<&dyn LincheckCircuit> = tables
    .iter()
    .map(|table| table.csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params(&union),
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("packed BLAKE3 proof rejected: {error:?}")
  })?;
  Ok(())
}

fn isolated_verify(expected: &[F128; 4], bytes: &[u8]) -> bool {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD_ENV, "1")
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
  stdin.write_all(bytes).unwrap();
  drop(stdin);
  let result = child.wait_with_output().unwrap();
  if !result.status.success() {
    eprintln!(
      "isolated packed compression verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "real pinned m22 packed BLAKE3 proofs, fresh output-only verification, and wiring negative"]
fn private_compressions_verify_in_fresh_process_and_reject_broken_wiring() {
  if std::env::var_os(CHILD_ENV).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin().take(MAX_BYTES + 65).read_to_end(&mut bytes).unwrap();
    assert!((64..=MAX_BYTES as usize + 64).contains(&bytes.len()));
    let expected =
      std::array::from_fn(|i| pack_bytes(&bytes[i * 16..(i + 1) * 16]));
    verify(&expected, &bytes[64..], DOMAIN).unwrap();
    return;
  }
  let (slots, input, public, shape) = setup(NU);
  let identity = shape.circuit.digest();
  let cases = [
    [F128::ZERO; 7],
    std::array::from_fn(|i| {
      F128::new(u64::MAX - i as u64, 0xd134_2543_de82_ef95 ^ i as u64)
    }),
  ];
  for private in cases {
    let output = expected(&private);
    let bytes = prove(&slots, &input, &shape, &private, false);
    eprintln!(
      "packed BLAKE3 compression component: {} proof-bundle bytes, 64 expected-output bytes",
      bytes.len()
    );
    assert!(isolated_verify(&output, &bytes));
    assert_eq!(setup(NU).3.circuit.digest(), identity);
    assert_eq!(public.outputs(), 4);
    for i in 0..4 {
      let mut wrong = output;
      wrong[i].hi ^= 1 << 63;
      assert!(verify(&wrong, &bytes, DOMAIN).is_err());
    }
    let mut wrong = bytes.clone();
    wrong[0] ^= 1;
    assert!(verify(&output, &wrong, DOMAIN).is_err());
    wrong = bytes.clone();
    let end = wrong.len() - 1;
    wrong[end] ^= 1;
    assert!(verify(&output, &wrong, DOMAIN).is_err());
    assert!(verify(&output, &bytes[..bytes.len() - 1], DOMAIN).is_err());
    wrong = bytes.clone();
    wrong.push(0);
    assert!(verify(&output, &wrong, DOMAIN).is_err());
    assert!(verify(&output, &bytes, b"wrong-compression-domain").is_err());
  }
  let bad = prove(&slots, &input, &shape, &cases[1], true);
  assert!(!isolated_verify(&expected(&cases[1]), &bad));
}
