//! Byte-binding conformance only: all four commitments and S are constrained,
//! but canonical decoding/execution are deliberately not claimed here. Fresh
//! child verification receives ONLY the expected S digest and the Flock bundle.

use super::{
  commitment::{
    ByteCommitmentSlots, CommitmentCapacities,
    tests::{
      GOLDEN_INPUT, GOLDEN_OUTPUT, GOLDEN_PROFILE, GOLDEN_PROGRAM, advice,
      emit, native,
    },
  },
  hash_control::{HashBlockGate, RootParamsGate},
  io::{InputLayout, PublicLayout},
  length::CheckedLengthAddGate,
  select::SelectWordsGate,
};
use crate::hash::{Blake3Gate, pack_bytes};
use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder},
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
use std::{
  io::{Read, Write},
  process::{Command, Stdio},
};

const NU: usize = 8;
const CAPACITIES: CommitmentCapacities =
  CommitmentCapacities { program: 130, input: 1100, output: 67 };
const DOMAIN: &[u8] = b"ix:ixby:byte-commitment-conformance:v0";
const MAX_BYTES: u64 = 8 * 1024 * 1024;
const CHILD_ENV: &str = "IXBY_FLOCK_COMMITMENT_VERIFY_CHILD";
const TEST: &str = "ixby::commitment_proof_tests::all_commitments_bind_private_bytes_with_fresh_digest_only_verification";

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

fn setup(
  profile: &[u8],
  capacities: CommitmentCapacities,
) -> (ByteCommitmentSlots, InputLayout, PublicLayout, CircuitShape) {
  let mut builder = ShapeBuilder::new(NU);
  let (slots, inputs, public) = emit(&mut builder, profile, capacities, false);
  (slots, inputs, public, builder.finish().unwrap())
}

fn tables(slots: &ByteCommitmentSlots, shape: &CircuitShape) -> Vec<BlockR1cs> {
  let common = &slots.hashes()[0];
  let mut tables = vec![
    (common.compression_slot(), flock_blake3::build_block_r1cs(NU)),
    (common.select_slot(), common.select_gate().r1cs()),
    (common.root_slot(), common.root_gate().r1cs()),
    (slots.length_slot().slot(), slots.length_gate().r1cs()),
  ];
  tables.extend(
    slots
      .hashes()
      .iter()
      .map(|hash| (hash.block_slot(), hash.block_gate().r1cs())),
  );
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
  slots: &ByteCommitmentSlots,
  shape: &CircuitShape,
  inputs: &[F128],
  public: &[F128],
) -> Vec<u8> {
  let witness = shape.run(inputs, &[]);
  assert_eq!(witness.public, public);
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let tables = tables(slots, shape);
  let common = &slots.hashes()[0];
  let compression_rows = witness.rows::<Blake3Gate>(common.compression_slot());
  let select_rows = witness.rows::<SelectWordsGate>(common.select_slot());
  let root_rows = witness.rows::<RootParamsGate>(common.root_slot());
  let length_rows =
    witness.rows::<CheckedLengthAddGate>(slots.length_slot().slot());
  let mut drivers = vec![
    (
      common.compression_slot(),
      UnionSlotProverInput::in_place(
        |mut dst| {
          dst.elide_padding_writes = false;
          flock_blake3::generate_witness_batch_major_partial_into(
            compression_rows,
            NU,
            dst,
          )
        },
        tables[shape.registry_slot(common.compression_slot())]
          .csc_lincheck_circuit(),
      ),
    ),
    (
      common.select_slot(),
      UnionSlotProverInput::in_place(
        |dst| common.select_gate().generate_witness_into(select_rows, dst),
        tables[shape.registry_slot(common.select_slot())]
          .csc_lincheck_circuit(),
      ),
    ),
    (
      common.root_slot(),
      UnionSlotProverInput::in_place(
        |dst| common.root_gate().generate_witness_into(root_rows, dst),
        tables[shape.registry_slot(common.root_slot())].csc_lincheck_circuit(),
      ),
    ),
    (
      slots.length_slot().slot(),
      UnionSlotProverInput::in_place(
        |dst| slots.length_gate().generate_witness_into(length_rows, dst),
        tables[shape.registry_slot(slots.length_slot().slot())]
          .csc_lincheck_circuit(),
      ),
    ),
  ];
  for hash in slots.hashes() {
    let rows = witness.rows::<HashBlockGate>(hash.block_slot());
    drivers.push((
      hash.block_slot(),
      UnionSlotProverInput::in_place(
        move |dst| hash.block_gate().generate_witness_into(rows, dst),
        tables[shape.registry_slot(hash.block_slot())].csc_lincheck_circuit(),
      ),
    ));
  }
  drivers.sort_by_key(|(slot, _)| shape.registry_slot(*slot));
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    public,
    &params,
    drivers.into_iter().map(|(_, driver)| driver).collect(),
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { commitment, proof }).unwrap()
}

fn verify(
  expected: &[F128; 2],
  bytes: &[u8],
  profile: &[u8],
  capacities: CommitmentCapacities,
  domain: &[u8],
) -> Result<()> {
  ensure!(bytes.len() as u64 <= MAX_BYTES, "commitment proof byte admission");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(
    codec().serialize(&bundle)? == bytes,
    "canonical commitment proof encoding"
  );
  let (slots, _, public, shape) = setup(profile, capacities);
  ensure!(public.outputs() == 2, "final statement digest only");
  let public = public.instantiate(expected)?;
  let tables = tables(&slots, &shape);
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
  .map_err(|error| {
    anyhow::anyhow!("byte commitment proof rejected: {error:?}")
  })?;
  Ok(())
}

fn isolated_verify(expected: &[F128; 2], bytes: &[u8]) -> bool {
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
      "isolated commitment verifier rejected: {}",
      String::from_utf8_lossy(&result.stderr)
    );
  }
  result.status.success()
}

#[test]
#[ignore = "real full byte-commitment chain with isolated digest-only verification"]
fn all_commitments_bind_private_bytes_with_fresh_digest_only_verification() {
  if std::env::var_os(CHILD_ENV).is_some() {
    let mut bytes = Vec::new();
    std::io::stdin().take(MAX_BYTES + 33).read_to_end(&mut bytes).unwrap();
    assert!((32..=MAX_BYTES as usize + 32).contains(&bytes.len()));
    let expected = [pack_bytes(&bytes[..16]), pack_bytes(&bytes[16..32])];
    // This branch does not construct or receive private buffers, evaluate a
    // gate, hash an artifact, execute IxBy, or invoke the prover.
    verify(&expected, &bytes[32..], GOLDEN_PROFILE, CAPACITIES, DOMAIN)
      .unwrap();
    return;
  }
  let (slots, layout, public, shape) = setup(GOLDEN_PROFILE, CAPACITIES);
  let identity = shape.circuit.digest();
  let cases = [
    (GOLDEN_PROGRAM.to_vec(), GOLDEN_INPUT.to_vec(), GOLDEN_OUTPUT.to_vec()),
    (Vec::new(), Vec::new(), Vec::new()),
    (vec![17; 130], vec![29; 1100], vec![41; 67]),
  ];
  for (program, input, output) in cases {
    let expected = native(GOLDEN_PROFILE, &program, &input, &output)[4];
    let advice = [
      advice(CAPACITIES.program, &program),
      advice(CAPACITIES.input, &input),
      advice(CAPACITIES.output, &output),
    ]
    .concat();
    let bytes = prove(
      &slots,
      &shape,
      &layout.assign(&advice).unwrap(),
      &public.instantiate(&expected).unwrap(),
    );
    eprintln!(
      "Flock full byte-commitment conformance: {} bytes; private byte lengths {}, {}, {}",
      bytes.len(),
      program.len(),
      input.len(),
      output.len()
    );
    assert!(isolated_verify(&expected, &bytes));
    assert_eq!(shape.circuit.digest(), identity);
    for word in 0..2 {
      let mut wrong = expected;
      wrong[word].lo ^= 1;
      assert!(
        verify(&wrong, &bytes, GOLDEN_PROFILE, CAPACITIES, DOMAIN).is_err()
      );
    }
    let mut wrong = bytes.clone();
    wrong[0] ^= 1;
    assert!(
      verify(&expected, &wrong, GOLDEN_PROFILE, CAPACITIES, DOMAIN).is_err()
    );
    wrong = bytes.clone();
    wrong.push(0);
    assert!(
      verify(&expected, &wrong, GOLDEN_PROFILE, CAPACITIES, DOMAIN).is_err()
    );
    assert!(
      verify(
        &expected,
        &bytes[..bytes.len() - 1],
        GOLDEN_PROFILE,
        CAPACITIES,
        DOMAIN
      )
      .is_err()
    );
    assert!(
      verify(
        &expected,
        &bytes,
        GOLDEN_PROFILE,
        CAPACITIES,
        b"ix:ixby:bounded-blake3-conformance:v0"
      )
      .is_err()
    );
  }
  let expected =
    native(GOLDEN_PROFILE, GOLDEN_PROGRAM, GOLDEN_INPUT, GOLDEN_OUTPUT)[4];
  let advice = [
    advice(CAPACITIES.program, GOLDEN_PROGRAM),
    advice(CAPACITIES.input, GOLDEN_INPUT),
    advice(CAPACITIES.output, GOLDEN_OUTPUT),
  ]
  .concat();
  let bytes = prove(
    &slots,
    &shape,
    &layout.assign(&advice).unwrap(),
    &public.instantiate(&expected).unwrap(),
  );
  let mut wrong = expected;
  wrong[1].hi ^= 1;
  assert!(!isolated_verify(&wrong, &bytes));
  let mut changed_profile = GOLDEN_PROFILE.to_vec();
  changed_profile[12] ^= 1;
  assert!(
    verify(&expected, &bytes, &changed_profile, CAPACITIES, DOMAIN).is_err()
  );
  assert!(
    verify(
      &expected,
      &bytes,
      GOLDEN_PROFILE,
      CommitmentCapacities { program: 129, ..CAPACITIES },
      DOMAIN
    )
    .is_err()
  );
}
