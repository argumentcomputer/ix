//! Opt-in gate conformance, not an execution proof. Verification rebuilds
//! only the fixed setup and consumes externally expected public words; it
//! never runs the gate evaluator or accepts a prover public-vector dump.

use anyhow::{Result, ensure};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder, SlotId},
  field::F128,
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

use super::{BankReadGate, BankReadSlot, control};

const NU: usize = 10;
const CAPACITY: usize = 4;
const DOMAIN: &[u8] = b"ix:ixby:bank-read-conformance:v0";
const MAX_PROOF_BYTES: u64 = 8 * 1024 * 1024;

#[derive(Serialize, Deserialize)]
struct Bundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

fn setup() -> (BankReadGate, CircuitShape, SlotId) {
  let gate = BankReadGate::new(NU, CAPACITY).unwrap();
  let mut builder = ShapeBuilder::new(NU);
  let slot = BankReadSlot::declare(&mut builder, gate.clone());
  let control = builder.public_input();
  let cells: Vec<_> = (0..CAPACITY).map(|_| builder.public_input()).collect();
  let selected = slot.read(&mut builder, control, &cells);
  builder.publish(selected);
  (gate, builder.finish().unwrap(), slot.slot())
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

fn codec() -> impl Options {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_little_endian()
    .with_limit(MAX_PROOF_BYTES)
    .reject_trailing_bytes()
}

fn prove(
  gate: &BankReadGate,
  shape: &CircuitShape,
  slot: SlotId,
  public: &[F128],
) -> Vec<u8> {
  let witness = shape.run(&public[..CAPACITY + 2], &[]);
  assert_eq!(witness.public, public);
  let rows = witness.rows::<BankReadGate>(slot);
  assert_eq!(shape.registry_slot(slot), 0);
  let r1cs = gate.r1cs();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(DOMAIN);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    public,
    &params,
    vec![UnionSlotProverInput::in_place(
      |dst| gate.generate_witness_into(rows, dst),
      r1cs.csc_lincheck_circuit(),
    )],
    Vec::new(),
    &mut challenger,
  );
  codec().serialize(&Bundle { commitment, proof }).unwrap()
}

fn verify(public: &[F128], bytes: &[u8], domain: &[u8]) -> Result<()> {
  ensure!(public.len() == CAPACITY + 3, "public template width");
  ensure!(public[0] == F128::ZERO, "verifier-owned validity pin");
  ensure!(bytes.len() as u64 <= MAX_PROOF_BYTES, "proof byte admission");
  let bundle: Bundle = codec().deserialize(bytes)?;
  ensure!(codec().serialize(&bundle)? == bytes, "canonical proof encoding");
  let (gate, shape, _) = setup();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let r1cs = gate.r1cs();
  let params = params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    public,
    &[r1cs.csc_lincheck_circuit()],
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| anyhow::anyhow!("bank access proof rejected: {error:?}"))?;
  Ok(())
}

#[test]
#[ignore = "real fixed-capacity Flock bank-access conformance proofs"]
fn different_accesses_share_setup_and_verify_without_native_execution() {
  let (gate, shape, slot) = setup();
  let digest = shape.circuit.digest();
  let a = F128::new(11, 101);
  let b = F128::new(12, 102);
  let c = F128::new(13, 103);
  let d = F128::new(14, 104);
  let cases = [
    [F128::ZERO, control(3, 4, true), a, b, c, d, d],
    [F128::ZERO, control(0, 1, true), c, F128::ZERO, F128::ZERO, F128::ZERO, c],
    [F128::ZERO; CAPACITY + 3],
  ];
  for public in cases {
    let bytes = prove(&gate, &shape, slot, &public);
    eprintln!(
      "Flock bank-access conformance: {} bytes; fixed capacity {CAPACITY}",
      bytes.len()
    );
    verify(&public, &bytes, DOMAIN).unwrap();
    assert_eq!(setup().1.circuit.digest(), digest);
    assert!(verify(&public[..public.len() - 1], &bytes, DOMAIN).is_err());
    for index in 0..public.len() {
      let mut wrong = public;
      wrong[index].lo ^= 1;
      assert!(verify(&wrong, &bytes, DOMAIN).is_err());
    }
    let mut changed = bytes.clone();
    changed[0] ^= 1;
    assert!(verify(&public, &changed, DOMAIN).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(verify(&public, &trailing, DOMAIN).is_err());
    assert!(verify(&public, &bytes[..bytes.len() - 1], DOMAIN).is_err());
    assert!(
      verify(
        &public,
        &bytes,
        b"ix:flock-stage3:goldilocks-arithmetic-conformance:v1"
      )
      .is_err()
    );
  }
}
