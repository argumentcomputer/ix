//! Real hash-component conformance, not an Exec proof. No private message,
//! length, native hash invocation, or gate evaluation is used by `verify`.

use super::{
  bounded_hash::{
    BoundedBlake3,
    tests::{expected, private_input, setup},
  },
  hash_control::{HashBlockGate, RootParamsGate},
  io::InputLayout,
  select::SelectWordsGate,
};
use crate::hash::Blake3Gate;
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::CircuitShape,
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
  union::UnionInstance,
  verifier,
};
use serde::{Deserialize, Serialize};

const NU: usize = 8;
const CAPACITY: usize = 3073;
const DOMAIN: &[u8] = b"ix:ixby:bounded-blake3-conformance:v0";
const MAX_PROOF_BYTES: u64 = 8 * 1024 * 1024;

#[derive(Serialize, Deserialize)]
struct Bundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_PROOF_BYTES)
    .reject_trailing_bytes()
}

fn tables(hash: &BoundedBlake3, shape: &CircuitShape) -> Vec<BlockR1cs> {
  let mut tables = vec![
    (hash.compression_slot(), flock_blake3::build_block_r1cs(NU)),
    (hash.block_slot(), hash.block_gate().r1cs()),
    (hash.select_slot(), hash.select_gate().r1cs()),
    (hash.root_slot(), hash.root_gate().r1cs()),
  ];
  tables.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  tables.into_iter().map(|(_, table)| table).collect()
}

fn params(union: &UnionInstance<'_>) -> PcsParams {
  let m = union.dense_m();
  assert!((22..=35).contains(&m), "pinned baseline PCS geometry");
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
  hash: &BoundedBlake3,
  layout: &InputLayout,
  shape: &CircuitShape,
  message: &[u8],
  corrupt_compression_wiring: bool,
) -> Vec<u8> {
  let witness =
    shape.run(&layout.assign(&private_input(CAPACITY, message)).unwrap(), &[]);
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let tables = tables(hash, shape);
  let mut compression_rows =
    witness.rows::<Blake3Gate>(hash.compression_slot()).to_vec();
  if corrupt_compression_wiring {
    // Recompute an entirely valid compression row from a different CV. This
    // passes that table's equations, but violates the fixed IV/input wiring.
    compression_rows[0].0[0] ^= 1;
  }
  let block_rows = witness.rows::<HashBlockGate>(hash.block_slot());
  let select_rows = witness.rows::<SelectWordsGate>(hash.select_slot());
  let root_rows = witness.rows::<RootParamsGate>(hash.root_slot());
  let mut slots = vec![
    (
      hash.compression_slot(),
      UnionSlotProverInput::in_place(
        |mut dst| {
          dst.elide_padding_writes = false;
          flock_blake3::generate_witness_batch_major_partial_into(
            &compression_rows,
            NU,
            dst,
          )
        },
        tables[shape.registry_slot(hash.compression_slot())]
          .csc_lincheck_circuit(),
      ),
    ),
    (
      hash.block_slot(),
      UnionSlotProverInput::in_place(
        |dst| hash.block_gate().generate_witness_into(block_rows, dst),
        tables[shape.registry_slot(hash.block_slot())].csc_lincheck_circuit(),
      ),
    ),
    (
      hash.select_slot(),
      UnionSlotProverInput::in_place(
        |dst| hash.select_gate().generate_witness_into(select_rows, dst),
        tables[shape.registry_slot(hash.select_slot())].csc_lincheck_circuit(),
      ),
    ),
    (
      hash.root_slot(),
      UnionSlotProverInput::in_place(
        |dst| hash.root_gate().generate_witness_into(root_rows, dst),
        tables[shape.registry_slot(hash.root_slot())].csc_lincheck_circuit(),
      ),
    ),
  ];
  slots.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params,
    slots.into_iter().map(|(_, input)| input).collect(),
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { commitment, proof }).unwrap()
}

fn verify(expected: &[F128; 2], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(bytes.len() as u64 <= MAX_PROOF_BYTES, "hash proof byte admission");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    codec().serialize(&bundle)? == bytes,
    "canonical hash proof encoding"
  );
  let (hash, _, public, shape) = setup(NU, CAPACITY);
  let public = public.instantiate(expected)?;
  let tables = tables(&hash, &shape);
  let linchecks: Vec<&dyn LincheckCircuit> = tables
    .iter()
    .map(|table| table.csc_lincheck_circuit() as &dyn LincheckCircuit)
    .collect();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| anyhow::anyhow!("bounded hash proof rejected: {error:?}"))?;
  Ok(())
}

#[test]
#[ignore = "real fixed-capacity private-message BLAKE3 proofs and corrupted-wiring rejection"]
fn changed_private_lengths_share_setup_and_verify_from_expected_digest_only() {
  let (hash, inputs, public, shape) = setup(NU, CAPACITY);
  let identity = shape.circuit.digest();
  for length in [3073, 0, 1024, 1025, 2049] {
    let message: Vec<_> =
      (0..length).map(|i| (i * 17 + i / 128 + 11) as u8).collect();
    let digest = expected(&message);
    let bytes = prove(&hash, &inputs, &shape, &message, false);
    eprintln!(
      "Flock bounded BLAKE3 conformance: {} bytes; length {length}; capacity {CAPACITY}",
      bytes.len()
    );
    verify(&digest, &bytes, DOMAIN).unwrap();
    assert_eq!(setup(NU, CAPACITY).3.circuit.digest(), identity);
    for word in 0..2 {
      let mut wrong = digest;
      wrong[word].hi ^= 1 << 63;
      assert!(verify(&wrong, &bytes, DOMAIN).is_err());
    }
    assert_eq!(public.outputs(), 2);
    let mut wrong = bytes.clone();
    wrong[0] ^= 1;
    assert!(verify(&digest, &wrong, DOMAIN).is_err());
    wrong = bytes.clone();
    wrong.push(0);
    assert!(verify(&digest, &wrong, DOMAIN).is_err());
    assert!(verify(&digest, &bytes[..bytes.len() - 1], DOMAIN).is_err());
    assert!(
      verify(&digest, &bytes, b"ix:ixby:bank-read-conformance:v0").is_err()
    );
  }
  let message = b"locally valid compression, invalid global wiring";
  let bad = prove(&hash, &inputs, &shape, message, true);
  assert!(verify(&expected(message), &bad, DOMAIN).is_err());
}
