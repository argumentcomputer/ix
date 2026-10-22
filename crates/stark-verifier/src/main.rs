use aiur::{
  field::FieldBackend,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::{
  batch::{Retention, ShardInput},
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val},
};
use std::{error::Error, path::Path, time::Instant};

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
  trace: TraceArtifact,
}

fn fixture(dir: &Path) -> Result<(), Box<dyn Error>> {
  std::fs::create_dir_all(dir)?;
  let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
  let fp = FriParameters {
    log_final_poly_len: 0,
    max_log_arity: 1,
    num_queries: 16,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };
  let x = Expr::main(0);
  let y = Expr::main(1);
  let one = Expr::constant(Val::ONE);
  let inputs = vec![CircuitInputs {
    main_width: 2,
    constraints: vec![x.clone() * x.clone() - y.clone()],
    lookups: vec![Lookup::pull(
      one.clone(),
      vec![one, Expr::constant(Val::ZERO), x, y],
    )],
    ..Default::default()
  }];
  let (system, pk) = System::new(GoldilocksBlake3Config::new(cp, fp), inputs);
  let claims =
    vec![vec![Val::ONE, Val::ZERO, Val::from_u64(3), Val::from_u64(9)]];
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(vec![Val::from_u64(3), Val::from_u64(9)], 2)],
    &system,
  );
  let proof = system.prove_batch(
    &pk,
    vec![ShardInput { claims: claims.clone(), witness }],
    vec![],
  );
  system
    .verify_batch(&proof)
    .map_err(|e| format!("fixture failed native verification: {e:?}"))?;
  let key = stark_key::to_bytes(&system, cp, fp);
  let claims = stark_verifier::claims_bytes(&claims);
  let proof = proof.to_bytes()?;
  std::fs::write(dir.join("key.bin"), &key)?;
  std::fs::write(dir.join("claims.bin"), &claims)?;
  std::fs::write(dir.join("proof.bin"), &proof)?;
  serde_json::to_writer(
    std::fs::File::create(dir.join("input.json"))?,
    &stark_verifier::invocation(&key, &claims, &proof),
  )?;
  println!("created natively verified recursion fixture in {}", dir.display());
  Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  let mode = cli.get(1).ok_or("usage: stark-verifier fixture DIR | key PACKAGE DIR | execute|test|prove|verify PACKAGE INPUT [OUTPUT] [SHARD_ROWS] [RETENTION]")?;
  if mode == "fixture" {
    return fixture(Path::new(cli.get(2).ok_or("missing directory")?));
  }
  if !["execute", "test", "prove", "verify", "key", "cases"]
    .contains(&mode.as_str())
  {
    return Err("unknown mode".into());
  }
  let package: Package = aiur::decode_artifact(&std::fs::read(
    cli.get(2).ok_or("missing package")?,
  )?)?;
  let program = package.program.check_field::<Val>()?;
  if mode == "cases" {
    #[derive(serde::Deserialize)]
    struct Case {
      label: String,
      accept: bool,
      invocation: stark_verifier::Invocation,
    }
    let cases: Vec<Case> = serde_json::from_slice(&std::fs::read(
      cli.get(3).ok_or("missing cases")?,
    )?)?;
    for case in cases {
      let args = program.field().decode(&case.invocation.args)?;
      let result = stark_verifier::prepare(&program, &case.invocation.streams)?
        .execute(&case.invocation.entry, args);
      if result.is_ok() != case.accept {
        return Err(
          format!("{}: unexpected result {:?}", case.label, result.err())
            .into(),
        );
      }
      println!(
        "{}: {}",
        case.label,
        if case.accept { "accepted" } else { "rejected" }
      );
    }
    return Ok(());
  }
  if mode == "key" {
    let out = Path::new(cli.get(3).ok_or("missing output directory")?);
    std::fs::create_dir_all(out)?;
    let plan = TracePlan::new(&program, package.trace)?;
    let backend = Backend::for_batch(&plan, Parameters::default())?;
    let entry = &program.program().entries[0].name;
    let claim = backend.claim(entry, &[Val::ZERO; 16], &[])?;
    use multi_stark::p3_field::PrimeField64;
    let key = backend.verifying_key_bytes()?;
    std::fs::write(out.join("key.bin"), &key)?;
    serde_json::to_writer(
      std::fs::File::create(out.join("identity.json"))?,
      &serde_json::json!({
      "function_index":claim[1].as_canonical_u64(), "call_channel":claim[0].as_canonical_u64(),
      "key_digest":blake3::hash(&key).to_hex().to_string()}),
    )?;
    return Ok(());
  }
  let invocation: stark_verifier::Invocation = serde_json::from_slice(
    &std::fs::read(cli.get(3).ok_or("missing invocation")?)?,
  )?;
  if !["MultiStark::verify_multi_stark_proof", "MultiStark::ix_aggr"]
    .contains(&invocation.entry.as_str())
    || invocation.args.len() != 16
  {
    return Err(
      "expected a recursive entrypoint with sixteen public digest words".into(),
    );
  }
  let args = program.field().decode(&invocation.args)?;
  if mode == "verify" {
    use aiur::trace::stark::BatchProof;
    let plan = TracePlan::new(&program, package.trace)?;
    let backend = Backend::for_batch(&plan, Parameters::default())?;
    let bytes = std::fs::read(cli.get(4).ok_or("missing proof")?)?;
    let proof = BatchProof::from_bytes(&bytes)?;
    if proof.to_bytes()? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    backend.verify_batch(&invocation.entry, &args, &[], &proof)?;
    println!("verified recursive proof");
    return Ok(());
  }
  let hints = stark_verifier::prepare(&program, &invocation.streams)?;
  let start = Instant::now();
  let record = hints.execute(&invocation.entry, args.clone())?;
  if !record.output.is_empty() {
    return Err("verifier returned a non-unit value".into());
  }
  eprintln!(
    "recursive bytecode verified in {:.3}s ({} queries, {} instructions)",
    start.elapsed().as_secs_f64(),
    record.queries.len(),
    record.instructions
  );
  if mode == "execute" {
    return Ok(());
  }
  if mode == "test" {
    for i in [0, 8] {
      let mut wrong = args.clone();
      wrong[i] += Val::ONE;
      if hints.execute(&invocation.entry, wrong).is_ok() {
        return Err("accepted wrong public digest".into());
      }
    }
    for channel in [0, 1, 2] {
      let mut wrong = invocation.streams.clone();
      let stream = wrong.0.iter_mut().find(|s| s.channel == channel).unwrap();
      // Truncation tests full consumption / bounds without inducing giant
      // adversarial count allocations in the honest interpreter.
      stream.values.pop();
      if stark_verifier::prepare(&program, &wrong)?
        .execute(&invocation.entry, args.clone())
        .is_ok()
      {
        return Err(format!("accepted truncated stream {channel}").into());
      }
    }
    let mut wrong = invocation.streams.clone();
    let stream = wrong.0.iter_mut().find(|s| s.channel == 0).unwrap();
    let bytes: Vec<_> =
      stream.values.iter().map(|&v| u8::try_from(v).unwrap()).collect();
    let mut proof = aiur::trace::stark::BatchProof::from_bytes(&bytes)?;
    proof.proofs[0].stage_1_opened_values[0][0][0] +=
      multi_stark::types::ExtVal::ONE;
    stream.values = proof.to_bytes()?.into_iter().map(u64::from).collect();
    if stark_verifier::prepare(&program, &wrong)?
      .execute(&invocation.entry, args.clone())
      .is_ok()
    {
      return Err("accepted a corrupted opening".into());
    }
    println!(
      "honest proof accepted; wrong public digests, truncated streams and corrupted opening rejected"
    );
    return Ok(());
  }
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::for_batch(&plan, Parameters::default())?;
  let witness = backend.generate_stage_1(&record, &invocation.entry, &args)?;
  drop(record);
  drop(hints);
  let rows = cli.get(5).map(|s| s.parse()).transpose()?.unwrap_or(1 << 16);
  let retention = match cli.get(6).map(String::as_str).unwrap_or("regenerate") {
    "retain" => Retention::Retain,
    "regenerate" => Retention::Regenerate,
    _ => return Err("expected retention retain or regenerate".into()),
  };
  let proof = backend.prove_batch_stage_1(
    &invocation.entry,
    &args,
    &[],
    witness,
    rows,
    retention,
  )?;
  let out = Path::new(cli.get(4).ok_or("missing output directory")?);
  std::fs::create_dir_all(out)?;
  let key = backend.verifying_key_bytes()?;
  let claims = stark_verifier::claims_bytes(&[backend.claim(
    &invocation.entry,
    &args,
    &[],
  )?]);
  let bytes = proof.to_bytes()?;
  std::fs::write(out.join("proof.bin"), &bytes)?;
  std::fs::write(out.join("key.bin"), &key)?;
  std::fs::write(out.join("claims.bin"), &claims)?;
  serde_json::to_writer(
    std::fs::File::create(out.join("public.json"))?,
    &aiur::library::io::Invocation {
      entry: invocation.entry,
      args: invocation.args,
      streams: Default::default(),
    },
  )?;
  serde_json::to_writer(
    std::fs::File::create(out.join("input.json"))?,
    &stark_verifier::invocation(&key, &claims, &bytes),
  )?;
  println!(
    "outer proof verified: {} bytes, {} shards",
    bytes.len(),
    proof.proofs.len()
  );
  Ok(())
}
