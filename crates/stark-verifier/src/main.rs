use aiur::{
  field::FieldBackend,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, Parameters, planning::Options},
  },
};
use multi_stark::{
  batch::ShardInput,
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
  if mode == "ranges" || mode == "inspect" {
    return ranges(&cli);
  }
  if !["execute", "plan", "test", "prove", "verify", "key", "cases"]
    .contains(&mode.as_str())
  {
    return Err("unknown mode".into());
  }
  let package: Package = aiur::decode_artifact(&std::fs::read(
    cli.get(2).ok_or("missing package")?,
  )?)?;
  let program = package.program.check_field::<Val>()?;
  let artifact_resident = aiur::trace::stark::planning::resident_memory();
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
  let options = Options::read(cli.get(7), cli.get(5), cli.get(6))?;
  let before_setup = aiur::trace::stark::planning::resident_memory();
  let trace_plan = if mode == "execute" || mode == "test" {
    None
  } else {
    Some(TracePlan::new(&program, package.trace)?)
  };
  let backend = trace_plan
    .as_ref()
    .map(|plan| {
      Backend::for_batch_on_device(plan, Parameters::default(), options.device)
    })
    .transpose()?;
  if let Some(backend) = &backend {
    let static_resident = artifact_resident.saturating_add(
      aiur::trace::stark::planning::resident_memory()
        .saturating_sub(before_setup),
    );
    let fixed = backend.plan_fixed(&options, static_resident)?;
    if !fixed.fits {
      let out = Path::new(cli.get(4).ok_or("missing output directory")?);
      std::fs::create_dir_all(out)?;
      let report = serde_json::json!({"plan":fixed, "can_split":false, "verified":false,
        "error":"budget is below the estimated artifact and fixed-table floor"});
      std::fs::write(
        out.join("report.json"),
        serde_json::to_vec_pretty(&report)?,
      )?;
      println!("{report}");
      if mode == "plan" {
        return Ok(());
      }
      std::process::exit(75);
    }
  }
  let hints = stark_verifier::prepare(&program, &invocation.streams)?;
  let start = Instant::now();
  let record = hints.execute(&invocation.entry, args.clone())?;
  let execute = start.elapsed().as_secs_f64();
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
  drop(invocation.streams);
  let backend = backend.ok_or("missing proving backend")?;
  let out = Path::new(cli.get(4).ok_or("missing output directory")?);
  std::fs::create_dir_all(out)?;
  let batch = backend.plan_batch(&record, &options)?;
  let mut report = serde_json::json!({"plan":batch, "execution_seconds":execute,
    "queries":record.queries.len(), "instructions":record.instructions, "verified":false});
  std::fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  if mode == "plan" {
    println!("{}", report);
    return Ok(());
  }
  if !batch.fits {
    eprintln!(
      "recursive proving estimate exceeds budget; see {}",
      out.join("report.json").display()
    );
    std::process::exit(75);
  }
  let start = Instant::now();
  let witness = backend.generate_stage_1(&record, &invocation.entry, &args)?;
  if witness.iter().map(|m| m.values.len() as u64).sum::<u64>()
    != batch.stage1_cells
  {
    return Err("generated trace differs from the resource plan".into());
  }
  let trace = start.elapsed().as_secs_f64();
  drop(record);
  drop(hints);
  let start = Instant::now();
  let proof = backend.prove_batch_stage_1(
    &invocation.entry,
    &args,
    &[],
    witness,
    batch.max_rows,
    batch.retention(),
  )?;
  let proving = start.elapsed().as_secs_f64();
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
  report["verified"] = true.into();
  report["trace_seconds"] = trace.into();
  report["proving_seconds"] = proving.into();
  report["proof_bytes"] = bytes.len().into();
  report["shards"] = proof.proofs.len().into();
  std::fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
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

/// Produce range advice, never a verification result. The controller verifies
/// the source proof before calling this; the Aiur range circuit checks it again.
fn ranges(cli: &[String]) -> Result<(), Box<dyn Error>> {
  use aiur::trace::stark::BatchProof;
  use stark_key::range::{
    preamble_bytes, proofs_slice_bytes, range_residual, range_statement,
  };
  let bytes = std::fs::read(cli.get(2).ok_or("missing proof")?)?;
  let proof = BatchProof::from_bytes(&bytes)?;
  if proof.to_bytes()? != bytes || proof.proofs.is_empty() {
    return Err("noncanonical, empty or trailing proof bytes".into());
  }
  if cli[1] == "inspect" {
    println!("{}", serde_json::json!({"shards":proof.proofs.len()}));
    return Ok(());
  }
  let out = Path::new(cli.get(3).ok_or("missing output directory")?);
  let size: usize = cli.get(4).ok_or("missing range size")?.parse()?;
  if size == 0 {
    return Err("range size must be positive".into());
  }
  std::fs::create_dir_all(out)?;
  let preamble = preamble_bytes(&proof)?;
  let digest = blake3::hash(&preamble);
  std::fs::write(out.join("preamble.bin"), preamble)?;
  let mut specs = Vec::new();
  let mut layer = Vec::new();
  for lo in (0..proof.proofs.len()).step_by(size) {
    let hi = lo.saturating_add(size).min(proof.proofs.len());
    let id = specs.len();
    std::fs::write(
      out.join(format!("{id}.proofs")),
      proofs_slice_bytes(&proof, lo, hi)?,
    )?;
    layer.push((id, lo, hi));
    specs.push(serde_json::json!({"lo":lo, "hi":hi, "children":[]}));
  }
  while layer.len() > 1 {
    let mut next = Vec::new();
    for pair in layer.chunks(2) {
      let [(left, lo, _), (right, _, hi)] = pair else {
        next.push(pair[0]);
        continue;
      };
      let id = specs.len();
      next.push((id, *lo, *hi));
      specs
        .push(serde_json::json!({"lo":lo, "hi":hi, "children":[left,right]}));
    }
    layer = next;
  }
  for (id, spec) in specs.iter().enumerate() {
    let lo = spec["lo"].as_u64().unwrap() as usize;
    let hi = spec["hi"].as_u64().unwrap() as usize;
    if proof.proofs[lo..hi]
      .iter()
      .any(|p| p.intermediate_accumulators.is_empty())
    {
      return Err("range contains a shard without accumulators".into());
    }
    std::fs::write(
      out.join(format!("{id}.statement")),
      range_statement(
        digest.as_bytes(),
        lo,
        hi,
        range_residual(&proof, lo, hi),
      ),
    )?;
  }
  std::fs::write(out.join("ranges.json"), serde_json::to_vec_pretty(&specs)?)?;
  Ok(())
}
