//! The Aiur packed-SHPLONK verifier on systems whose circuits share a
//! committed fixed matrix (`System::new_shared`, multi-stark fork
//! `formal-aiur/shared-fixed`): honest proofs give the native deferred pair
//! and the native final transcript, and forged shared-slot openings or slot
//! lists are rejected.
//!
//! The system has two circuits reading one fixed column at the current and
//! next row (slot 0, opened once), a circuit with its own fixed column of
//! another height (slot 1) and a selector without fixed columns that pulls
//! the claim.

use aiur::{
  Execution, artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1, kzg_advice as wire,
    kzg_packed_advice::{self as packed_wire, Proof},
  },
  kzg::{
    Scalar, Srs,
    curve::G1Affine,
    packed_shplonk::{PackedShplonkConfig, capture_verification},
  },
};
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  system::{CircuitInputs, System, SystemWitness},
};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::{Arc, OnceLock};

const ENTRY: &str = "KzgPackedVerifier::verify_deferred";
const FOLD_ENTRY: &str = "KzgPackedTest::fold";

fn f(value: u64) -> Scalar {
  Bn254.from_u64(value)
}

fn plan() -> &'static TracePlan<'static, Bn254> {
  static PLAN: OnceLock<TracePlan<'static, Bn254>> = OnceLock::new();
  PLAN.get_or_init(|| {
    let path = std::env::var_os("IX_AIUR_KZG_PACKED_ARTIFACT").map_or_else(
      || {
        std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
          .join("../aiur/tests/fixtures/kzg-packed-shplonk.ixa")
      },
      std::path::PathBuf::from,
    );
    let package = WidePackage::decode(&std::fs::read(path).unwrap()).unwrap();
    let trace = package.trace.expect("compiler trace");
    let mut program = package.program.check_with(Bn254).unwrap();
    program.track_depth(&trace).unwrap();
    TracePlan::new(Arc::new(program), trace).unwrap()
  })
}

struct Native {
  system: System<PackedShplonkConfig>,
  srs: Arc<Srs>,
  proof: Proof,
  claims: Vec<Vec<Scalar>>,
}

/// `main0 = fixed0` and `fixed0' = main0 + 1` on every transition.
fn reader(
  preprocessed: Option<RowMajorMatrix<Scalar>>,
) -> CircuitInputs<Scalar> {
  CircuitInputs {
    main_width: 1,
    preprocessed,
    constraints: vec![
      Expr::main(0) - Expr::preprocessed(0),
      Expr::IsTransition
        * (Expr::preprocessed_next(0) - Expr::main(0) - Expr::constant(f(1))),
    ],
    ..Default::default()
  }
}

fn native() -> &'static Native {
  static NATIVE: OnceLock<Native> = OnceLock::new();
  NATIVE.get_or_init(|| {
    let shared = RowMajorMatrix::new_col((1..=8).map(f).collect());
    let own = RowMajorMatrix::new_col([3, 5, 7, 9].map(f).to_vec());
    let squares = CircuitInputs {
      main_width: 1,
      preprocessed: Some(own),
      constraints: vec![
        Expr::main(0) - Expr::preprocessed(0) * Expr::preprocessed(0),
      ],
      ..Default::default()
    };
    let selector = CircuitInputs {
      main_width: 2,
      constraints: vec![
        Expr::main(0) * (Expr::main(0) - Expr::constant(f(1))),
        Expr::main(1) - Expr::constant(f(7)),
      ],
      lookups: vec![Lookup::pull(Expr::main(0), vec![Expr::constant(f(42))])],
      ..Default::default()
    };
    let srs =
      Arc::new(Srs::unsafe_dev_setup(1 << 6, b"aiur-packed-shared-fixed"));
    let (system, key) = System::new_shared(
      PackedShplonkConfig::new(srs.clone(), 8),
      [reader(Some(shared.clone())), reader(None), squares, selector],
      &[None, Some(0), None, None],
      false,
    );
    assert_eq!(system.preprocessed_slots(), 2);
    let claims = vec![vec![f(42)]];
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let traces = vec![
      shared.clone(),
      shared,
      RowMajorMatrix::new_col([9, 25, 49, 81].map(f).to_vec()),
      RowMajorMatrix::new([1, 7, 0, 7, 0, 7, 0, 7].map(f).to_vec(), 2),
    ];
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(traces, &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    assert_eq!(
      proof.preprocessed_opened_values.as_ref().map(Vec::len),
      Some(2)
    );
    Native { system, srs, proof, claims }
  })
}

fn execute_entry(
  key: &[u8],
  claims: &[Vec<Scalar>],
  proof: &Proof,
  entry: &str,
  arguments: impl FnOnce(&[u8], &[u8]) -> Vec<Scalar>,
) -> Result<Execution<Bn254>, String> {
  let claims = wire::claims_bytes(claims)?;
  let proof = packed_wire::proof_bytes(proof)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  wire::Inputs::new(key.to_vec(), claims.clone(), proof, vec![])?
    .register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan().program(), &mut maps)?;
  let public = arguments(key, &claims);
  plan()
    .program()
    .prepare_hint_channels(&[], &hints)
    .map_err(|e| e.clone())?
    .with_map_overrides(&maps)
    .map_err(|e| e.clone())?
    .execute(entry, public)
    .map_err(|e| e.to_string())
}

fn execute_key(key: &[u8], proof: &Proof) -> Result<Execution<Bn254>, String> {
  execute_entry(key, &native().claims, proof, ENTRY, |key, claims| {
    wire::digest_words(blake3::hash(key).as_bytes())
      .into_iter()
      .chain(wire::digest_words(blake3::hash(claims).as_bytes()))
      .collect()
  })
}

fn key() -> Vec<u8> {
  packed_wire::key_bytes(&native().system).unwrap()
}

fn pairing_holds(pair: [G1Affine; 2]) -> bool {
  let srs = &native().srs;
  ark_bn254::Bn254::multi_pairing(pair, [srs.g2, srs.tau_g2]).0
    == <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
}

/// Rejected natively, and by the Aiur verifier under `key`; returns whether
/// the Aiur execution failed (rather than giving a pair that fails the
/// pairing check).
fn rejected_with(key: &[u8], proof: &Proof) -> bool {
  let native = native();
  let refs: Vec<_> = native.claims.iter().map(Vec::as_slice).collect();
  assert!(native.system.verify_multiple_claims(&refs, proof).is_err());
  match execute_key(key, proof) {
    Err(_) => true,
    Ok(record) => {
      let pair = wire::decode_accumulator(&record.output).unwrap();
      assert!(!pairing_holds(pair), "Aiur accumulator accepted a forgery");
      false
    },
  }
}

#[test]
fn shared_key_lists_each_circuit_slot() {
  let key = key();
  // Tag 2, then four slots plus one: shared slot 0, own slot 1, none.
  let tail: Vec<u8> =
    [4u32, 1, 1, 2, 0].iter().flat_map(|v| v.to_le_bytes()).collect();
  assert!(key.ends_with(&tail));
  // The two readers are one circuit listed with copy count two.
  let compact =
    packed_wire::key_bytes_with_copies(&native().system, &[2, 1, 1]).unwrap();
  assert!(compact.len() < key.len() && compact.ends_with(&tail));
}

#[test]
fn honest_shared_slot_proof_gives_the_native_pair() {
  let native = native();
  for key in [
    key(),
    packed_wire::key_bytes_with_copies(&native.system, &[2, 1, 1]).unwrap(),
  ] {
    let record = execute_key(&key, &native.proof).unwrap();
    let pair = wire::decode_accumulator(&record.output).unwrap();
    // B is fixed by the proof and the pairing is injective in A.
    let w2 = native.proof.opening_proof.opening.w2;
    assert_eq!(pair[1].into_group(), -w2.into_group());
    assert!(pairing_holds(pair));
  }
}

/// The fold weight is squeezed from the final transcript: equal weights mean
/// the Aiur transcript absorbed the native verifier's bytes, including the
/// slot list.
#[test]
fn shared_slot_transcript_matches_the_native_verifier() {
  let native = native();
  let refs: Vec<_> = native.claims.iter().map(Vec::as_slice).collect();
  let verified = capture_verification(|| {
    native.system.verify_multiple_claims(&refs, &native.proof)
  })
  .unwrap();
  let policy = *blake3::hash(b"shared policy").as_bytes();
  let statement = *blake3::hash(b"shared statement").as_bytes();
  let key_digest = *blake3::hash(b"shared key").as_bytes();
  let previous =
    [native.srs.g1[1], (-native.srs.g1[0].into_group()).into_affine()];
  let weight = wire::transcript_fold_challenge(
    &verified.transcript.0,
    &policy,
    &statement,
    3,
    &key_digest,
    &previous,
    &verified.pair,
  )
  .unwrap();
  let record =
    execute_entry(&key(), &native.claims, &native.proof, FOLD_ENTRY, |_, _| {
      wire::digest_words(&policy)
        .into_iter()
        .chain(wire::digest_words(&statement))
        .chain([f(3)])
        .chain(wire::digest_words(&key_digest))
        .chain(wire::accumulator_words(&previous).unwrap())
        .collect()
    })
    .unwrap();
  assert_eq!(record.output[0], weight);
  let folded =
    [0, 1].map(|i| (verified.pair[i] + previous[i] * weight.0).into_affine());
  assert_eq!(wire::decode_accumulator(&record.output[1..]).unwrap(), folded);
}

#[test]
fn forged_shared_slot_openings_are_rejected() {
  let one = ark_bn254::Fr::from(1u8);
  let key = key();
  // A changed shared value breaks both readers' identities.
  let mut proof = native().proof.clone();
  proof.preprocessed_opened_values.as_mut().unwrap()[0][0][0].0 += one;
  assert!(rejected_with(&key, &proof));
  // Shifting the shared rows and both readers' main values keeps every AIR
  // identity: only the opening of the one committed matrix rejects.
  let mut proof = native().proof.clone();
  for row in &mut proof.preprocessed_opened_values.as_mut().unwrap()[0] {
    row[0].0 += one;
  }
  for circuit in 0..2 {
    proof.stage_1_opened_values[circuit][0][0].0 += one;
  }
  assert!(!rejected_with(&key, &proof));
  // A second opened matrix for the shared slot.
  let mut proof = native().proof.clone();
  let fixed = proof.preprocessed_opened_values.as_mut().unwrap();
  fixed.insert(1, fixed[0].clone());
  assert!(rejected_with(&key, &proof));
}

#[test]
fn altered_slot_lists_are_rejected() {
  let honest = key();
  let at = honest.len() - 16;
  let mut keys = vec![];
  // The reader claims its own slot, a later slot, no slot; a circuit without
  // fixed columns claims a slot.
  for slots in [[1u32, 2, 3, 0], [1, 2, 2, 0], [1, 0, 2, 0], [1, 1, 2, 1]] {
    let mut key = honest.clone();
    key[at..].copy_from_slice(
      &slots.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<_>>(),
    );
    keys.push(key);
  }
  // The unshared grammar for the same commitment.
  let mut key = honest[..at - 4].to_vec();
  let tag = key.len() - packed_wire_commitment_len(&honest) - 1;
  key[tag] = 1;
  keys.push(key);
  for key in keys {
    assert!(execute_key(&key, &native().proof).is_err());
  }
}

/// Length of the fixed commitment blob (with its u32 prefix) in a shared key.
fn packed_wire_commitment_len(key: &[u8]) -> usize {
  let commitment =
    native().system.preprocessed_commit.as_ref().unwrap().to_bytes().unwrap();
  let blob = 4 + commitment.len();
  assert_eq!(
    &key[key.len() - 20 - commitment.len()..key.len() - 20],
    &commitment[..]
  );
  blob
}
