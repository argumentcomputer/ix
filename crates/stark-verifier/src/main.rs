use aiur::{
  artifact::Package,
  field::FieldBackend,
  trace::{
    TracePlan,
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
  types::{GoldilocksBlake3Config, Val},
};
use std::{
  error::Error,
  io::{BufWriter, Write},
  path::Path,
  time::Instant,
};

/// Serialize through a buffer. Recursive invocations encode every proof byte
/// as a JSON number; unbuffered, each token was a separate write syscall.
fn write_json(
  path: &Path,
  value: &impl serde::Serialize,
) -> Result<(), Box<dyn Error>> {
  let mut file = BufWriter::new(std::fs::File::create(path)?);
  serde_json::to_writer(&mut file, value)?;
  file.flush()?;
  Ok(())
}

/// A small proof under the production parameters, so the recursive verifier
/// is tested on the query proof of work and the full query count.
fn fixture(dir: &Path) -> Result<(), Box<dyn Error>> {
  std::fs::create_dir_all(dir)?;
  let (cp, fp) = (Parameters::DEFAULT.commitment(), Parameters::DEFAULT.fri());
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
  write_json(
    &dir.join("input.json"),
    &stark_verifier::invocation(&key, &claims, &proof),
  )?;
  println!("created natively verified recursion fixture in {}", dir.display());
  Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  let mode = cli.get(1).ok_or("usage: stark-verifier fixture DIR | key PACKAGE DIR | statistics KEY PROOF | execute|test|prove|verify PACKAGE INPUT [OUTPUT] [SHARD_ROWS] [RETENTION]")?;
  if mode == "fixture" {
    return fixture(Path::new(cli.get(2).ok_or("missing directory")?));
  }
  if mode == "ranges" || mode == "inspect" {
    return ranges(&cli);
  }
  if mode == "statistics" {
    return statistics(&cli);
  }
  if !["execute", "plan", "test", "prove", "verify", "key", "cases"]
    .contains(&mode.as_str())
  {
    return Err("unknown mode".into());
  }
  let path = cli.get(2).ok_or("missing package")?;
  let (package, artifact) = Package::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {artifact}");
  let (program, trace) = package.traced()?;
  let program = program.check_field::<Val>()?;
  let artifact_resident = aiur::trace::stark::planning::resident_memory();
  if mode == "cases" {
    #[derive(serde::Deserialize)]
    struct Case {
      label: String,
      accept: bool,
      /// For a rejection: text the execution error must contain.
      #[serde(default)]
      rejects_with: Option<String>,
      invocation: stark_verifier::Invocation,
    }
    let cases: Vec<Case> = serde_json::from_slice(&std::fs::read(
      cli.get(3).ok_or("missing cases")?,
    )?)?;
    // Every case runs, so that one report names every unexpected verdict.
    let mut failed = Vec::new();
    for case in cases {
      let args = program.field().decode(&case.invocation.args)?;
      let result = stark_verifier::prepare(&program, &case.invocation.streams)?
        .execute(&case.invocation.entry, args);
      let error = result.err().map(|e| e.to_string());
      let expected = match (&error, &case.rejects_with) {
        (None, _) => case.accept,
        (Some(e), Some(reason)) => !case.accept && e.contains(reason.as_str()),
        (Some(_), None) => !case.accept,
      };
      let verdict =
        error.map_or("accepted".to_owned(), |e| format!("rejected: {e}"));
      if expected {
        println!("{}: {verdict}", case.label);
      } else {
        println!("FAILED {}: {verdict}", case.label);
        failed.push(case.label);
      }
    }
    if !failed.is_empty() {
      return Err(
        format!("{} unexpected verdicts: {}", failed.len(), failed.join("; "))
          .into(),
      );
    }
    return Ok(());
  }
  if mode == "key" {
    let out = Path::new(cli.get(3).ok_or("missing output directory")?);
    std::fs::create_dir_all(out)?;
    let plan = TracePlan::new(&program, trace)?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let entry = &program.program().entries[0].name;
    let claim = backend.claim(entry, &[Val::ZERO; 16], &[])?;
    use multi_stark::p3_field::PrimeField64;
    let key = backend.verifying_key_bytes()?;
    std::fs::write(out.join("key.bin"), &key)?;
    write_json(
      &out.join("identity.json"),
      &serde_json::json!({
      "function_index":claim[1].as_canonical_u64(), "call_channel":claim[0].as_canonical_u64(),
      "key_digest":blake3::hash(&key).to_hex().to_string(),
      "artifact_digest":artifact.to_string()}),
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
    let plan = TracePlan::new(&program, trace)?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let bytes = std::fs::read(cli.get(4).ok_or("missing proof")?)?;
    let proof = BatchProof::from_bytes(&bytes)?;
    if proof.to_bytes()? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    backend.verify_batch(&invocation.entry, &args, &[], &proof)?;
    println!("verified recursive proof (artifact {artifact})");
    return Ok(());
  }
  let options = Options::read(cli.get(7), cli.get(5), cli.get(6))?;
  let before_setup = aiur::trace::stark::planning::resident_memory();
  let trace_plan = if mode == "execute" || mode == "test" {
    None
  } else {
    Some(TracePlan::new(&program, trace)?)
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
  let mut report = serde_json::json!({"plan":batch, "artifact_digest":artifact.to_string(), "execution_seconds":execute,
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
  let witness = backend.prepare_stage_1(&record, &invocation.entry, &args)?;
  if witness.cells() != batch.stage1_cells {
    return Err("generated trace differs from the resource plan".into());
  }
  let trace = start.elapsed().as_secs_f64();
  drop(record);
  drop(hints);
  let start = Instant::now();
  let proof = backend.prove_stage_one(
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
  write_json(
    &out.join("public.json"),
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
  write_json(
    &out.join("input.json"),
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

/// Instance statistics of a proof under its key, as JSON for
/// `lake exe fri-security`: the key's parameters and, for every active circuit
/// of every shard, its trace height and the widths, constraints and lookups
/// the soundness bounds need. Shards are separate FRI instances, so listing
/// each one's circuits also charges the union bound over shards.
fn statistics(cli: &[String]) -> Result<(), Box<dyn Error>> {
  use aiur::trace::stark::{BatchProof, VerifyingKey};
  // Reports on any key, including weak ones, and trusts none.
  let key = VerifyingKey::from_bytes_below_floor(&std::fs::read(
    cli.get(2).ok_or("usage: stark-verifier statistics KEY PROOF")?,
  )?)?;
  let bytes = std::fs::read(cli.get(3).ok_or("missing proof")?)?;
  let proof = BatchProof::from_bytes(&bytes)?;
  if proof.to_bytes()? != bytes {
    return Err("noncanonical or trailing proof bytes".into());
  }
  let (cp, fp) = (key.commitment_parameters(), key.fri_parameters());
  let mut circuits = vec![];
  for header in &proof.preamble.headers {
    let mut heights = header.log_degrees.iter();
    for (circuit, &active) in key.system().circuits.iter().zip(&header.active) {
      if !active {
        continue;
      }
      let log = heights.next().ok_or("missing trace height")?;
      circuits.push(serde_json::json!({
        "main": circuit.main_width, "pre": circuit.preprocessed_width,
        "height": 1u64 << log, "lookups": circuit.num_lookups,
        "stage2": circuit.stage_2_width, "group": circuit.lookup_group_size,
        "max_degree": circuit.max_constraint_degree,
        "zeros": circuit.graph.zeros.len(),
        "max_lookup_width": circuit.graph.lookups.iter()
          .map(|l| l.args.len()).max().unwrap_or(0),
      }));
    }
  }
  println!(
    "{}",
    serde_json::json!({
      "log_blowup": cp.log_blowup, "cap": cp.cap_height,
      "num_queries": fp.num_queries, "commit_pow": fp.commit_proof_of_work_bits,
      "query_pow": fp.query_proof_of_work_bits, "max_log_arity": fp.max_log_arity,
      "shards": proof.proofs.len(), "proof_bytes": bytes.len(),
      "circuits": circuits,
    })
  );
  Ok(())
}
