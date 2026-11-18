use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_bn254::G1Affine;
use ark_ec::{AffineRepr, CurveGroup};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::Accumulator,
    fq, g1,
    kzg::{Compiler, VerifyingKey},
    kzg_advice as wire,
  },
  kzg::{KzgConfig, Scalar, Srs},
};
use multi_stark::{
  config::ProofConfig,
  expr::Expr,
  lookup::{Lookup, logup_max_degree, stage2_width},
  system::{CircuitInputs, System, SystemWitness, extension_params},
};
use p3_matrix::dense::RowMajorMatrix;
use std::sync::Arc;

fn verifier_plan() -> TracePlan<'static, Bn254> {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/kzg-source.ixa"
  ))
  .unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}

#[test]
fn compiler_batches_lookups_without_increasing_any_quotient_domain() {
  let plan = verifier_plan();
  let compiler = Compiler::new(&plan).unwrap();
  let params = extension_params::<KzgConfig>();
  let mut improved = false;
  for input in compiler.inputs() {
    let graph = input.compile_graph(&params).unwrap();
    let quotient = |group| {
      let degree =
        graph.max_constraint_degree.max(logup_max_degree(&graph, group));
      (degree.max(2) - 1).next_power_of_two()
    };
    assert_eq!(quotient(1), quotient(input.lookup_group_size));
    let old = stage2_width(input.lookups.len(), 1, params.degree);
    let new =
      stage2_width(input.lookups.len(), input.lookup_group_size, params.degree);
    assert!(new <= old);
    improved |= new < old;
  }
  assert!(improved);
}

#[test]
fn grouped_lookup_key_and_proof_roundtrip_through_the_aiur_verifier() {
  let one = Bn254.one();
  let x = Expr::<Scalar>::main(0);
  let mut lookups = Vec::new();
  for index in 0..10 {
    let argument = if matches!(index, 4 | 5) {
      x.clone() * x.clone()
    } else {
      Expr::constant(one)
    };
    let multiplicity = match index {
      0 => Expr::main(1),
      9 => Expr::constant(Bn254.zero()),
      _ => Expr::constant(one),
    };
    lookups.push(if matches!(index, 2 | 4 | 6 | 8) {
      Lookup::push(multiplicity, vec![argument])
    } else {
      Lookup::pull(multiplicity, vec![argument])
    });
  }
  let input = CircuitInputs {
    main_width: 2,
    constraints: vec![
      x.clone() * x.clone() * x.clone() - x,
      Expr::IsFirstRow * (Expr::main(1) - Expr::constant(one)),
      Expr::IsTransition * Expr::main_next(1),
    ],
    lookups,
    lookup_group_size: 5,
    ..Default::default()
  };
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(16, b"aiur-lookup-group-roundtrip")),
    2,
  );
  let (system, prover) = System::new(config, [input]);
  let claim = vec![one];
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(
      vec![
        one,
        one,
        Bn254.zero(),
        Bn254.zero(),
        -one,
        Bn254.zero(),
        one,
        Bn254.zero(),
      ],
      2,
    )],
    &system,
  );
  let proof = system.prove(&prover, &claim, witness);
  system.verify(&claim, &proof).unwrap();

  let key = VerifyingKey::from_system(&system).unwrap();
  let key_bytes = key.to_bytes().unwrap();
  let restored =
    VerifyingKey::from_bytes(&key_bytes, blake3::hash(&key_bytes).as_bytes())
      .unwrap();
  assert_eq!(restored.to_bytes().unwrap(), key_bytes);
  assert_eq!(restored.system().circuits[0].lookup_group_size, 5);
  let proof_bytes = key.encode_proof(&proof).unwrap();
  restored.verify_bytes(&claim, &proof_bytes).unwrap();
  assert!(restored.verify_bytes(&[Bn254.from_u64(2)], &proof_bytes).is_err());
  let proof = restored.decode_proof(&proof_bytes).unwrap();
  let key_wire = wire::key_bytes(&restored).unwrap();
  let claims_wire = wire::claims_bytes(std::slice::from_ref(&claim)).unwrap();
  let args: Vec<_> = wire::digest_words(blake3::hash(&key_wire).as_bytes())
    .into_iter()
    .chain(wire::digest_words(blake3::hash(&claims_wire).as_bytes()))
    .collect();
  let plan = verifier_plan();
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps).unwrap();
  let mut forged = proof.clone();
  forged.opening_proof.0[0] =
    (forged.opening_proof.0[0] + G1Affine::generator()).into_affine();
  for (candidate, valid) in [(proof, true), (forged, false)] {
    assert_eq!(restored.verify(&claim, &candidate).is_ok(), valid);
    let source = wire::Inputs::new(
      key_wire.clone(),
      claims_wire.clone(),
      wire::proof_bytes(&candidate).unwrap(),
      vec![],
    )
    .unwrap();
    let mut hints = HintChannels::new();
    aiur::library::u32::register(&mut hints, Bn254).unwrap();
    aiur::library::u64::register(&mut hints, Bn254).unwrap();
    fq::register(&mut hints).unwrap();
    g1::register(&mut hints).unwrap();
    wire::register(&mut hints).unwrap();
    source.register(&mut hints).unwrap();
    let record = plan
      .program()
      .prepare_hint_channels(&[], &hints)
      .unwrap()
      .with_map_overrides(&maps)
      .unwrap()
      .execute("KzgVerifier::verify_deferred", args.clone())
      .unwrap();
    assert_eq!(
      Accumulator::from_words(&record.output)
        .unwrap()
        .check_pairing(restored.system().config.pcs().verifier_params())
        .is_ok(),
      valid,
    );
  }
}
