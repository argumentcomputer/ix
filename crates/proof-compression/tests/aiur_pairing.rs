use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  trace::TracePlan,
};
use ark_bn254::{Bn254 as Engine, Fq, Fq2, Fq6, Fq12, G1Affine, G2Affine};
use ark_ec::{
  AffineRepr, CurveGroup,
  pairing::{MillerLoopOutput, Pairing},
};
use ark_ff::{CyclotomicMultSubgroup, Field, One, PrimeField, Zero};
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, g1, pairing},
  kzg::Scalar,
};
use std::{path::PathBuf, sync::Arc};

fn package() -> WidePackage {
  let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("../aiur/tests/fixtures/bn254-pairing.ixa");
  WidePackage::decode(&std::fs::read(path).unwrap()).unwrap()
}
fn plan() -> TracePlan<'static, Bn254> {
  let package = package();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}
fn channels() -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  fq::register(&mut channels).unwrap();
  g1::register(&mut channels).unwrap();
  pairing::register(&mut channels).unwrap();
  channels
}
fn fp12(seed: u8) -> Fq12 {
  let values: Vec<_> = (0..12u8)
    .map(|index| {
      Fq::from_le_bytes_mod_order(blake3::hash(&[seed, index]).as_bytes())
    })
    .collect();
  Fq12::new(
    Fq6::new(
      Fq2::new(values[0], values[1]),
      Fq2::new(values[2], values[3]),
      Fq2::new(values[4], values[5]),
    ),
    Fq6::new(
      Fq2::new(values[6], values[7]),
      Fq2::new(values[8], values[9]),
      Fq2::new(values[10], values[11]),
    ),
  )
}

#[test]
fn prepared_tables_match_native_miller_loop_and_authenticated_generator() {
  let q = G2Affine::generator();
  let anchors = [q, q];
  let rows = pairing::fixed_lines(anchors).unwrap();
  assert_eq!(rows.len(), 87);
  let package = package();
  let table = package
    .program
    .tables
    .iter()
    .find(|table| table.name == "BN254Pairing::line_outputs")
    .unwrap();
  let expected: Vec<Vec<_>> = rows
    .iter()
    .map(|row| row.iter().map(|&value| Bn254.to_word(value)).collect())
    .collect();
  assert_eq!(table.rows, expected);
  let p = (G1Affine::generator() * ark_bn254::Fr::from(7u8)).into_affine();
  for points in
    [[p, -p], [p, p], [p, G1Affine::identity()], [G1Affine::identity(); 2]]
  {
    assert_eq!(
      pairing::evaluate_fixed_lines(&rows, points).unwrap(),
      Engine::multi_miller_loop(points, anchors).0
    );
  }
  for anchors in [
    [G2Affine::identity(); 2],
    [q, G2Affine::identity()],
    [G2Affine::identity(), q],
  ] {
    assert!(pairing::fixed_lines(anchors).is_err());
  }
  let malformed = G2Affine::new_unchecked(Fq2::one(), Fq2::one());
  assert!(pairing::fixed_lines([q, malformed]).is_err());
}

#[test]
fn constrained_tower_matches_arkworks() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let a = fp12(17);
  let b = fp12(93);
  for (
    name,
    encode_a,
    encode_b,
    expected_mul,
    expected_square,
    expected_inverse,
  ) in [
    (
      "fp2",
      pairing::encode_fp2(a.c0.c0).to_vec(),
      pairing::encode_fp2(b.c0.c0).to_vec(),
      pairing::encode_fp2(a.c0.c0 * b.c0.c0).to_vec(),
      pairing::encode_fp2(a.c0.c0.square()).to_vec(),
      pairing::encode_fp2(a.c0.c0.inverse().unwrap()).to_vec(),
    ),
    (
      "fp6",
      pairing::encode_fp6(a.c0).to_vec(),
      pairing::encode_fp6(b.c0).to_vec(),
      pairing::encode_fp6(a.c0 * b.c0).to_vec(),
      pairing::encode_fp6(a.c0.square()).to_vec(),
      pairing::encode_fp6(a.c0.inverse().unwrap()).to_vec(),
    ),
    (
      "fp12",
      pairing::encode_fp12(a).to_vec(),
      pairing::encode_fp12(b).to_vec(),
      pairing::encode_fp12(a * b).to_vec(),
      pairing::encode_fp12(a.square()).to_vec(),
      pairing::encode_fp12(a.inverse().unwrap()).to_vec(),
    ),
  ] {
    let args: Vec<_> = encode_a.iter().chain(&encode_b).copied().collect();
    assert_eq!(
      executor
        .execute(&format!("PairingTest::{name}_mul"), args)
        .unwrap()
        .output,
      expected_mul,
      "{name} multiplication"
    );
    assert_eq!(
      executor
        .execute(&format!("PairingTest::{name}_square"), encode_a.clone())
        .unwrap()
        .output,
      expected_square,
      "{name} square"
    );
    assert_eq!(
      executor
        .execute(&format!("PairingTest::{name}_inverse"), encode_a)
        .unwrap()
        .output,
      expected_inverse,
      "{name} inverse"
    );
  }
  for power in 1..=3 {
    let mut expected = a;
    expected.frobenius_map_in_place(power);
    assert_eq!(
      executor
        .execute(
          &format!("PairingTest::fp12_frobenius{power}"),
          pairing::encode_fp12(a).to_vec()
        )
        .unwrap()
        .output,
      pairing::encode_fp12(expected)
    );
    let mut expected = a.c0;
    expected.frobenius_map_in_place(power);
    assert_eq!(
      executor
        .execute(
          &format!("PairingTest::fp6_frobenius{power}"),
          pairing::encode_fp6(a.c0).to_vec()
        )
        .unwrap()
        .output,
      pairing::encode_fp6(expected)
    );
  }
  let mut conjugate = a;
  conjugate.conjugate_in_place();
  let first = conjugate * a.inverse().unwrap();
  let mut easy = first;
  easy.frobenius_map_in_place(2);
  easy *= first;
  assert_eq!(
    executor
      .execute("PairingTest::easy_final", pairing::encode_fp12(a).to_vec())
      .unwrap()
      .output,
    pairing::encode_fp12(easy)
  );
  assert_eq!(
    executor
      .execute(
        "PairingTest::cyclotomic_square",
        pairing::encode_fp12(a).to_vec()
      )
      .unwrap()
      .output,
    pairing::encode_fp12(easy.square())
  );
  let mut power = easy.cyclotomic_exp([4965661367192848881u64]);
  power.conjugate_in_place();
  assert_eq!(
    executor
      .execute("PairingTest::exp_neg_x", pairing::encode_fp12(a).to_vec())
      .unwrap()
      .output,
    pairing::encode_fp12(power)
  );
  let expected = Engine::final_exponentiation(MillerLoopOutput(a)).unwrap().0;
  assert_eq!(
    executor
      .execute(
        "PairingTest::final_exponentiation",
        pairing::encode_fp12(a).to_vec()
      )
      .unwrap()
      .output,
    pairing::encode_fp12(expected)
  );
  assert!(
    executor
      .execute("PairingTest::fp12_inverse", vec![Bn254.zero(); 48])
      .is_err()
  );
}

#[test]
fn constrained_pairing_checks_cancellation_and_infinity() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let p = G1Affine::generator();
  let q = G2Affine::generator();
  for points in
    [[p, -p], [p, p], [p, G1Affine::identity()], [G1Affine::identity(); 2]]
  {
    let args: Vec<_> = points.into_iter().flat_map(g1::encode).collect();
    let miller = executor.execute("PairingTest::miller", args.clone()).unwrap();
    assert_eq!(
      miller.output,
      pairing::encode_fp12(Engine::multi_miller_loop(points, [q, q]).0)
    );
    let expected = Engine::multi_pairing(points, [q, q]).is_zero();
    assert_eq!(executor.execute("PairingTest::check", args).is_ok(), expected);
  }
  let mut malformed: Vec<_> =
    g1::encode(p).into_iter().chain(g1::encode(-p)).collect();
  malformed[4] += Bn254.one();
  assert!(executor.execute("PairingTest::check", malformed).is_err());
}

#[test]
fn constrained_pairing_binds_released_ignition_tau_anchor() {
  let parameters =
    ix_proof_compression::pipeline::ignition_parameters().unwrap();
  let (powers, anchors) = pairing::verifier_anchors(&parameters);
  let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("../aiur/tests/fixtures/bn254-pairing-ignition.ixa");
  let package = WidePackage::decode(&std::fs::read(path).unwrap()).unwrap();
  let rows = pairing::fixed_lines(anchors).unwrap();
  let expected: Vec<Vec<_>> = rows
    .iter()
    .map(|row| row.iter().map(|&value| Bn254.to_word(value)).collect())
    .collect();
  assert_eq!(
    package
      .program
      .tables
      .iter()
      .find(|table| table.name == "BN254Pairing::line_outputs")
      .unwrap()
      .rows,
    expected
  );
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  let plan = TracePlan::new(Arc::new(program), trace).unwrap();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let points = [powers[1], -powers[0]];
  assert!(Engine::multi_pairing(points, anchors).is_zero());
  assert_eq!(
    pairing::evaluate_fixed_lines(&rows, points).unwrap(),
    Engine::multi_miller_loop(points, anchors).0
  );
  let args = points.into_iter().flat_map(g1::encode).collect();
  executor.execute("PairingTest::check", args).unwrap();
  let changed = [(powers[1] + powers[0]).into_affine(), -powers[0]];
  assert!(!Engine::multi_pairing(changed, anchors).is_zero());
  assert!(
    executor
      .execute(
        "PairingTest::check",
        changed.into_iter().flat_map(g1::encode).collect()
      )
      .is_err()
  );
}
