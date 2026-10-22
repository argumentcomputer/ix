//! Small real proofs for testing recursive statement bindings. These systems
//! intentionally accept arbitrary digest arguments; they are not IxVM keys.
use multi_stark::{
  batch::ShardInput,
  expr::Expr,
  lookup::Lookup,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val},
};
use std::{error::Error, path::Path};

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  let args: Vec<u64> = serde_json::from_slice(&std::fs::read(
    cli.get(1).ok_or("expected digest arguments JSON")?,
  )?)?;
  if ![8, 16].contains(&args.len()) || args.iter().any(|&x| x >= Val::ORDER_U64)
  {
    return Err("expected eight or sixteen canonical field elements".into());
  }
  let out = Path::new(cli.get(2).ok_or("missing output directory")?);
  std::fs::create_dir_all(out)?;
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 4,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let one = Expr::constant(Val::ONE);
  let mut lookup = vec![one.clone(), Expr::constant(Val::ZERO)];
  lookup.extend((0..args.len()).map(|i| Expr::main(i as u32)));
  let inputs = vec![CircuitInputs {
    main_width: args.len(),
    constraints: vec![],
    lookups: vec![Lookup::pull(one, lookup)],
    ..Default::default()
  }];
  let (system, pk) = System::new(GoldilocksBlake3Config::new(cp, fp), inputs);
  let args: Vec<_> = args.into_iter().map(Val::from_u64).collect();
  let mut claim = vec![Val::ONE, Val::ZERO];
  claim.extend(&args);
  let claims = vec![claim];
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(args.clone(), args.len())],
    &system,
  );
  let proof = system.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness }],
    vec![],
  );
  system
    .verify_batch(&proof)
    .map_err(|e| format!("fixture verification failed: {e:?}"))?;
  std::fs::write(out.join("key.bin"), stark_key::to_bytes(&system, cp, fp))?;
  std::fs::write(out.join("proof.bin"), proof.to_bytes()?)?;
  std::fs::write(
    out.join("claims.bin"),
    stark_verifier::claims_bytes(&claims),
  )?;
  for hi in [0, 1] {
    let preamble = stark_key::range::preamble_bytes(&proof)?;
    let residual = stark_key::range::range_residual(&proof, 0, hi);
    std::fs::write(out.join("preamble.bin"), &preamble)?;
    std::fs::write(
      out.join(format!("range-{hi}.bin")),
      stark_key::range::proofs_slice_bytes(&proof, 0, hi)?,
    )?;
    std::fs::write(
      out.join(format!("statement-{hi}.bin")),
      stark_key::range::range_statement(
        blake3::hash(&preamble).as_bytes(),
        0,
        hi,
        residual,
      ),
    )?;
  }
  Ok(())
}
