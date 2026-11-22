//! The Aiur packed-SHPLONK verifier (`KzgPackedVerifier::verify_deferred`)
//! on natively produced packed proofs: it accepts honest proofs with the
//! native deferred pair, and every altered evaluation, commitment or witness
//! is rejected both natively and by the Aiur execution (an execution failure
//! or an output pair that fails the pairing check).
//!
//! The forgery system has two equal-height circuits, one reading the next
//! row and one not, so their shared main pack opens the second circuit's
//! columns at `ζω` through extra evaluations.

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
  foreign::KzgCircuitExt,
  kzg::{
    Scalar, Srs,
    curve::G1Affine,
    packed_shplonk::{PackedShplonkConfig, capture_verification},
  },
};
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  plonkish::CircuitBuilder,
  system::{CircuitInputs, System, SystemWitness},
};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::{Arc, OnceLock};

const ENTRY: &str = "KzgPackedVerifier::verify_deferred";

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
  /// Key copy counts: consecutive system circuits listed once in the key.
  copies: Vec<usize>,
}

fn prove(
  inputs: Vec<CircuitInputs<Scalar>>,
  traces: Vec<RowMajorMatrix<Scalar>>,
  claims: Vec<Vec<Scalar>>,
  cap: usize,
) -> Native {
  prove_classified(inputs, traces, claims, cap, None)
}

fn prove_classified(
  inputs: Vec<CircuitInputs<Scalar>>,
  traces: Vec<RowMajorMatrix<Scalar>>,
  claims: Vec<Vec<Scalar>>,
  cap: usize,
  main_next_rows: Option<Vec<bool>>,
) -> Native {
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let srs = Arc::new(Srs::unsafe_dev_setup(cap, b"aiur-packed-tests"));
  let (system, key) =
    System::new(PackedShplonkConfig::new(srs.clone(), 8), inputs);
  if let Some(classes) = main_next_rows {
    system.config.set_main_next_rows(classes);
  }
  let proof = system.prove_multiple_claims(
    &key,
    &refs,
    SystemWitness::from_stage_1(traces, &system),
  );
  system.verify_multiple_claims(&refs, &proof).unwrap();
  let copies = vec![1; system.circuits.len()];
  Native { system, srs, proof, claims, copies }
}

/// A counter (next-row transition) and a selector circuit pulling the claim
/// once, both of height four.
fn native() -> &'static Native {
  static NATIVE: OnceLock<Native> = OnceLock::new();
  NATIVE.get_or_init(|| counter_and_selector(None))
}

fn counter_and_selector(main_next_rows: Option<Vec<bool>>) -> Native {
  {
    let f = |value| Bn254.from_u64(value);
    let (counter, selector) = counter_and_selector_inputs();
    prove_classified(
      vec![counter, selector],
      vec![
        RowMajorMatrix::new_col((0..4).map(f).collect()),
        RowMajorMatrix::new([1, 7, 0, 7, 0, 7, 0, 7].map(f).to_vec(), 2),
      ],
      vec![vec![f(42)]],
      1 << 6,
      main_next_rows,
    )
  }
}

fn counter_and_selector_inputs()
-> (CircuitInputs<Scalar>, CircuitInputs<Scalar>) {
  {
    let f = |value| Bn254.from_u64(value);
    let counter = CircuitInputs {
      main_width: 1,
      constraints: vec![
        Expr::IsFirstRow * Expr::main(0),
        Expr::IsTransition
          * (Expr::main_next(0) - Expr::main(0) - Expr::constant(f(1))),
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
    (counter, selector)
  }
}

/// The selector's rows split across two copies of its circuit. The key lists
/// it once with copy count two; the Aiur verifier expands it as the native
/// system does, and a key whose copies cover the wrong circuits is rejected.
#[test]
fn honest_packed_proof_with_circuit_copies_is_accepted() {
  let f = |value| Bn254.from_u64(value);
  let (counter, selector) = counter_and_selector_inputs();
  let mut native = prove(
    vec![counter, selector.clone(), selector],
    vec![
      RowMajorMatrix::new_col((0..4).map(f).collect()),
      RowMajorMatrix::new([1, 7, 0, 7].map(f).to_vec(), 2),
      RowMajorMatrix::new([0, 7, 0, 7].map(f).to_vec(), 2),
    ],
    vec![vec![f(42)]],
    1 << 6,
  );
  native.copies = vec![1, 2];
  let compact =
    packed_wire::key_bytes_with_copies(&native.system, &native.copies).unwrap();
  assert!(
    compact.len() < packed_wire::key_bytes(&native.system).unwrap().len()
  );
  assert_native_pair(&native);
  native.copies = vec![2, 1];
  match execute_with(&native, &native.proof) {
    Err(_) => {},
    Ok(record) => {
      let pair = wire::decode_accumulator(&record.output).unwrap();
      assert!(!pairing_holds_for(&native, pair));
    },
  }
  native.copies = vec![1, 1];
  assert!(
    packed_wire::key_bytes_with_copies(&native.system, &native.copies).is_err()
  );
}

fn execute_with(
  native: &Native,
  proof: &Proof,
) -> Result<Execution<Bn254>, String> {
  execute_entry(native, &native.claims, proof, ENTRY, |key, claims| {
    wire::digest_words(blake3::hash(key).as_bytes())
      .into_iter()
      .chain(wire::digest_words(blake3::hash(claims).as_bytes()))
      .collect()
  })
}

fn execute_entry(
  native: &Native,
  claims: &[Vec<Scalar>],
  proof: &Proof,
  entry: &str,
  arguments: impl FnOnce(&[u8], &[u8]) -> Vec<Scalar>,
) -> Result<Execution<Bn254>, String> {
  let key = packed_wire::key_bytes_with_copies(&native.system, &native.copies)?;
  let claims = wire::claims_bytes(claims)?;
  let proof = packed_wire::proof_bytes(proof)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  wire::Inputs::new(key.clone(), claims.clone(), proof, vec![])?
    .register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan().program(), &mut maps)?;
  let public = arguments(&key, &claims);
  plan()
    .program()
    .prepare_hint_channels(&[], &hints)
    .map_err(|e| e.clone())?
    .with_map_overrides(&maps)
    .map_err(|e| e.clone())?
    .execute(entry, public)
    .map_err(|e| e.to_string())
}

fn execute(proof: &Proof) -> Result<Execution<Bn254>, String> {
  execute_with(native(), proof)
}

fn pairing_holds_for(native: &Native, pair: [G1Affine; 2]) -> bool {
  let srs = &native.srs;
  ark_bn254::Bn254::multi_pairing(pair, [srs.g2, srs.tau_g2]).0
    == <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
}

fn pairing_holds(pair: [G1Affine; 2]) -> bool {
  pairing_holds_for(native(), pair)
}

fn natively_accepted(proof: &Proof) -> bool {
  let native = native();
  let refs: Vec<_> = native.claims.iter().map(Vec::as_slice).collect();
  native.system.verify_multiple_claims(&refs, proof).is_ok()
}

/// Rejected by both verifiers; returns whether the Aiur execution itself
/// failed (rather than producing a pair that fails the pairing check).
fn assert_rejected(proof: &Proof) -> bool {
  assert!(!natively_accepted(proof), "native verifier accepted a forgery");
  match execute(proof) {
    Err(_) => true,
    Ok(record) => {
      let pair = wire::decode_accumulator(&record.output).unwrap();
      assert!(!pairing_holds(pair), "Aiur accumulator accepted a forgery");
      false
    },
  }
}

fn shifted(point: G1Affine) -> G1Affine {
  (point.into_group() + G1Affine::generator()).into_affine()
}

fn assert_native_pair(native: &Native) {
  let record = execute_with(native, &native.proof).unwrap();
  let pair = wire::decode_accumulator(&record.output).unwrap();
  // B is fixed by the proof and the pairing is injective in A, so equality
  // with the native operands follows from these two checks.
  let w2 = native.proof.opening_proof.opening.w2;
  assert_eq!(pair[1].into_group(), -w2.into_group());
  assert!(pairing_holds_for(native, pair));
}

#[test]
fn honest_packed_proof_with_extra_evaluations_is_accepted() {
  assert_eq!(native().proof.opening_proof.extra_values.len(), 2);
  assert_native_pair(native());
}

/// Declared next-row classes put the selector's current-row-only columns in
/// their own pack: no extra values, and the Aiur plan follows the classes.
#[test]
fn honest_packed_proof_with_next_row_classes_is_accepted() {
  let native = counter_and_selector(Some(vec![true, false]));
  assert!(native.proof.opening_proof.extra_values.is_empty());
  assert_eq!(native.proof.commitments.stage_1_trace.packs.len(), 2);
  assert_native_pair(&native);
}

/// The 30-lookup statement of `aiur_verifier_comparison`: sharded circuits,
/// fixed tables and several heights.
#[test]
fn honest_packed_proof_of_lowered_statement_is_accepted() {
  let mut b = CircuitBuilder::<Scalar>::new();
  let table =
    b.fixed_table("small", vec![vec![Bn254.one()], vec![Bn254.from_u64(2)]]);
  let x = b.input("x");
  for _ in 0..30 {
    b.lookup(table, &[x]);
  }
  let square = b.mul(x, x);
  b.expose_public(square);
  let circuit = b.finish();
  let mut witness = circuit.witness();
  witness.set(x, Bn254.from_u64(2)).unwrap();
  let assignment = witness.generate().unwrap();
  let lowered =
    circuit.lower_to_multi_stark_sharded(Bn254.from_u64(93), 32).unwrap();
  let claims = lowered.claims(assignment.public_values()).unwrap();
  for cap in [1 << 5, 1 << 10] {
    let native = prove(
      lowered.kzg_circuit_inputs(32, 2).unwrap(),
      lowered.traces(&assignment).unwrap(),
      claims.clone(),
      cap,
    );
    assert_native_pair(&native);
  }
}

#[test]
fn altered_extra_evaluation_fails_the_shplonk_check() {
  let mut proof = native().proof.clone();
  proof.opening_proof.extra_values[0].0 += ark_bn254::Fr::from(1u8);
  // Extra values feed no AIR constraint: only the opening check rejects.
  assert!(!assert_rejected(&proof));
}

#[test]
fn appended_or_dropped_extra_evaluations_are_rejected() {
  let mut proof = native().proof.clone();
  proof.opening_proof.extra_values.push(Bn254.one());
  assert!(assert_rejected(&proof));
  let mut proof = native().proof.clone();
  proof.opening_proof.extra_values.pop();
  assert!(assert_rejected(&proof));
}

#[test]
fn altered_trace_and_quotient_evaluations_are_rejected() {
  let mut proof = native().proof.clone();
  proof.stage_1_opened_values[0][0][0].0 += ark_bn254::Fr::from(1u8);
  assert_rejected(&proof);
  let mut proof = native().proof.clone();
  proof.stage_2_opened_values[0][1][0].0 += ark_bn254::Fr::from(1u8);
  assert_rejected(&proof);
  let mut proof = native().proof.clone();
  proof.quotient_opened_values[0][0][0].0 += ark_bn254::Fr::from(1u8);
  assert_rejected(&proof);
}

#[test]
fn altered_commitments_and_witnesses_are_rejected() {
  let mut proof = native().proof.clone();
  let pack = &mut proof.commitments.stage_1_trace.packs[0];
  *pack = shifted(*pack);
  assert_rejected(&proof);
  let mut proof = native().proof.clone();
  let pack = &mut proof.commitments.stage_2_trace.packs[0];
  *pack = shifted(*pack);
  assert_rejected(&proof);
  let mut proof = native().proof.clone();
  proof.opening_proof.opening.w1 = shifted(proof.opening_proof.opening.w1);
  assert_rejected(&proof);
  let mut proof = native().proof.clone();
  proof.opening_proof.opening.w2 = shifted(proof.opening_proof.opening.w2);
  assert_rejected(&proof);
}

#[test]
fn dropped_pack_commitment_is_rejected() {
  let mut proof = native().proof.clone();
  proof.commitments.stage_2_trace.packs.pop();
  assert!(assert_rejected(&proof));
}

const FOLD_ENTRY: &str = "KzgPackedTest::fold";

/// Public data the CompressBN fold binds besides the predecessor transcript.
#[derive(Clone, Copy)]
struct Bindings {
  policy: [u8; 32],
  statement: [u8; 32],
  stage: u32,
  key: [u8; 32],
  previous: [G1Affine; 2],
}

/// A previous accumulator `([τ]₁, −[1]₁)` that satisfies the pairing check.
fn bindings() -> Bindings {
  let srs = &native().srs;
  Bindings {
    policy: *blake3::hash(b"fold policy").as_bytes(),
    statement: *blake3::hash(b"fold statement").as_bytes(),
    stage: 3,
    key: *blake3::hash(b"fold key").as_bytes(),
    previous: [srs.g1[1], (-srs.g1[0].into_group()).into_affine()],
  }
}

/// The Aiur fold weight and folded pair over `proof` and `claims`.
fn aiur_fold(
  claims: &[Vec<Scalar>],
  proof: &Proof,
  bindings: Bindings,
) -> Result<(Scalar, [G1Affine; 2]), String> {
  let record = execute_entry(native(), claims, proof, FOLD_ENTRY, |_, _| {
    wire::digest_words(&bindings.policy)
      .into_iter()
      .chain(wire::digest_words(&bindings.statement))
      .chain([Bn254.from_u64(u64::from(bindings.stage))])
      .chain(wire::digest_words(&bindings.key))
      .chain(wire::accumulator_words(&bindings.previous).unwrap())
      .collect()
  })?;
  assert_eq!(record.output.len(), 5);
  Ok((record.output[0], wire::decode_accumulator(&record.output[1..])?))
}

/// The native reference: the weight squeezed from the native verifier's
/// final transcript, and the folded native deferred pair.
fn native_fold(bindings: Bindings) -> (Scalar, [G1Affine; 2]) {
  let native = native();
  let refs: Vec<_> = native.claims.iter().map(Vec::as_slice).collect();
  let verified = capture_verification(|| {
    native.system.verify_multiple_claims(&refs, &native.proof)
  })
  .unwrap();
  let weight = wire::transcript_fold_challenge(
    &verified.transcript.0,
    &bindings.policy,
    &bindings.statement,
    bindings.stage,
    &bindings.key,
    &bindings.previous,
    &verified.pair,
  )
  .unwrap();
  let folded = [0, 1].map(|i| {
    (verified.pair[i] + bindings.previous[i] * weight.0).into_affine()
  });
  (weight, folded)
}

#[test]
fn fold_weight_is_squeezed_from_the_final_verifier_transcript() {
  let honest = bindings();
  let (weight, folded) = native_fold(honest);
  assert_eq!(
    aiur_fold(&native().claims, &native().proof, honest).unwrap(),
    (weight, folded)
  );
  assert!(pairing_holds(honest.previous) && pairing_holds(folded));
  let mut changes = vec![];
  let mut b = honest;
  b.policy[0] ^= 1;
  changes.push(b);
  let mut b = honest;
  b.statement[31] ^= 1;
  changes.push(b);
  let mut b = honest;
  b.stage += 1;
  changes.push(b);
  let mut b = honest;
  b.key[7] ^= 1;
  changes.push(b);
  let mut b = honest;
  b.previous.swap(0, 1);
  changes.push(b);
  for changed in changes {
    let (other, _) =
      aiur_fold(&native().claims, &native().proof, changed).unwrap();
    assert_ne!(other, weight);
    assert_eq!(other, native_fold(changed).0);
  }
  // A carried pair that fails the pairing check is not cancelled by the fold.
  let mut invalid = honest;
  invalid.previous[0] = shifted(invalid.previous[0]);
  let (_, folded) =
    aiur_fold(&native().claims, &native().proof, invalid).unwrap();
  assert!(!pairing_holds(folded));
}

/// Every proof component is absorbed before the fold weight is squeezed:
/// altering any of them after the fact either fails the Aiur execution or
/// changes the weight. Components that enter only the deferred SHPLONK pair
/// (the opening witnesses and extra values) execute and must move the weight.
#[test]
fn altering_any_proof_component_rejects_or_changes_the_fold_weight() {
  let honest = bindings();
  let (weight, _) = native_fold(honest);
  let one = ark_bn254::Fr::from(1u8);
  let mut mutated: Vec<(&str, Proof)> = vec![];
  let base = || native().proof.clone();
  let mut p = base();
  p.commitments.stage_1_trace.packs[0] =
    shifted(p.commitments.stage_1_trace.packs[0]);
  mutated.push(("main commitment", p));
  let mut p = base();
  p.commitments.stage_2_trace.packs[0] =
    shifted(p.commitments.stage_2_trace.packs[0]);
  mutated.push(("lookup commitment", p));
  let mut p = base();
  p.commitments.quotient_chunks.packs[0] =
    shifted(p.commitments.quotient_chunks.packs[0]);
  mutated.push(("quotient commitment", p));
  let mut p = base();
  p.intermediate_accumulators[0].0 += one;
  mutated.push(("lookup accumulator", p));
  let mut p = base();
  p.stage_1_opened_values[0][0][0].0 += one;
  mutated.push(("main evaluation", p));
  let mut p = base();
  p.stage_2_opened_values[0][1][0].0 += one;
  mutated.push(("lookup evaluation", p));
  let mut p = base();
  p.quotient_opened_values[0][0][0].0 += one;
  mutated.push(("quotient evaluation", p));
  let deferred = mutated.len();
  let mut p = base();
  p.opening_proof.extra_values[0].0 += one;
  mutated.push(("extra evaluation", p));
  let mut p = base();
  p.opening_proof.opening.w1 = shifted(p.opening_proof.opening.w1);
  mutated.push(("opening witness W1", p));
  let mut p = base();
  p.opening_proof.opening.w2 = shifted(p.opening_proof.opening.w2);
  mutated.push(("opening witness W2", p));
  for (index, (name, proof)) in mutated.iter().enumerate() {
    match aiur_fold(&native().claims, proof, honest) {
      Err(_) => {
        assert!(index < deferred, "{name}: deferred component rejected")
      },
      Ok((other, _)) => {
        assert_ne!(other, weight, "{name}: unchanged fold weight")
      },
    }
  }
  let mut claims = native().claims.clone();
  claims[0][0] += Bn254.one();
  if let Ok((other, _)) = aiur_fold(&claims, &native().proof, honest) {
    assert_ne!(other, weight, "claims: unchanged fold weight");
  }
}
