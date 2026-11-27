//! Production claim driver. The trusted artifact is separate from witness and
//! proof inputs. No legacy executor or generated kernels are linked here.
use aiur::{
  artifact::{Package, load_cases},
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TracePlan,
    stark::{Backend, BatchProof, Parameters, VerifyingKey, planning::Options},
  },
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use std::{error::Error, time::Instant};

const MAGIC: &[u8] = b"IXAIUR2\0";
/// Set to `1` to execute with every assertion checked (circuit-verdict mode).
const CIRCUIT_VERDICT: &str = "IX_AIUR_CIRCUIT_VERDICT";

fn main() -> Result<(), Box<dyn Error>> {
  let raw_cli: Vec<_> = std::env::args().collect();
  if raw_cli.get(1).is_some_and(|s| s == "resources") {
    println!(
      "{}",
      serde_json::json!({"budget_bytes":aiur::trace::stark::planning::default_budget(),
      "cores":std::thread::available_parallelism().map_or(1, usize::from)})
    );
    return Ok(());
  }
  let (cli, verify_pin_mode) = parse_verify_cli(&raw_cli)?;
  if cli.len() < 4 {
    return Err("usage: ixvm-proof execute|plan|prove|verify ARTIFACT INPUT.ixi [PROOF] [SHARD_ROWS] [RETENTION] [OPTIONS.json] [--keys PATH | --artifact-digest HEX | --allow-unpinned]".into());
  }
  let mode = cli[1].as_str();
  if !["execute", "plan", "prove", "verify", "test", "key", "tiles"]
    .contains(&mode)
  {
    return Err("unknown mode".into());
  }
  ixvm::register_compiled_trace();
  let (mut package, artifact) = Package::load(cli[2].as_ref())?;
  eprintln!("artifact {}: blake3 {artifact}", cli[2]);
  let verify_pin = if mode == "verify" {
    let pin = resolve_verify_pin(&verify_pin_mode)?;
    check_artifact_digest(&artifact.to_string(), pin.as_ref())?;
    if pin.is_none() {
      eprintln!(
        "warning: verifying proof against unpinned artifact {artifact} (--allow-unpinned)"
      );
    }
    pin
  } else {
    None
  };
  // Circuit-verdict mode: execution also checks the assertions only the
  // circuit enforces (`runtime_check: false`), so that a run fails exactly
  // where the circuit has no trace for the same witness. The artifact, its
  // digest and its circuits are unchanged; only the execution copy differs.
  if std::env::var_os(CIRCUIT_VERDICT).is_some_and(|v| v == "1") {
    let enabled = package.program.enforce_deferred_assertions();
    let line = format!(
      "circuit verdict: {enabled} deferred assertions enforced in execution"
    );
    if mode == "test" {
      println!("{line}");
    } else {
      eprintln!("{line}");
    }
  }
  let mut program = package.program.check_field::<Val>()?;
  if let Some(trace) = &package.trace {
    program.track_depth(trace)?;
  }
  let artifact_resident = aiur::trace::stark::planning::resident_memory();
  if mode == "key" {
    let plan = TracePlan::new(
      &program,
      package.trace.ok_or("artifact has no circuits")?,
    )?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let key = backend.verifying_key_bytes()?;
    let claim = backend.claim(
      "IxVM::verify_claim",
      &program.field().decode(&[0; 8])?,
      &[],
    )?;
    let dir = std::path::Path::new(&cli[3]);
    std::fs::create_dir_all(dir)?;
    std::fs::write(dir.join("key.bin"), &key)?;
    serde_json::to_writer(
      std::fs::File::create(dir.join("identity.json"))?,
      &serde_json::json!({"function_index":claim[1].as_canonical_u64(),
        "call_channel":claim[0].as_canonical_u64(), "key_digest":blake3::hash(&key).to_hex().to_string(),
        "artifact_digest":artifact.to_string()}),
    )?;
    return Ok(());
  }
  if mode == "test" {
    // Every case runs, so that one report names every unexpected verdict.
    let cases = load_cases(cli[3].as_ref())?;
    let stats_path =
      match &cli[4..] {
        [] => None,
        [flag, path] if flag == "--stats-out" => Some(path),
        _ => return Err(
          "usage: ixvm-proof test ARTIFACT CASES.ixt [--stats-out STATS.json]"
            .into(),
        ),
      };
    let plan = if stats_path.is_some() {
      Some(TracePlan::new(
        &program,
        package.trace.ok_or("statistics require an artifact with circuits")?,
      )?)
    } else {
      None
    };
    let backend = plan
      .as_ref()
      .map(|plan| Backend::for_statistics(plan, Parameters::default()))
      .transpose()?;
    let mut statistics = serde_json::Map::new();
    // Measurement aid (not a gate): with IXVM_FUNCTION_STATS set,
    // `--stats-out S` also writes `S.functions.json`, the memo rows and cache
    // hits of every function an accepted case called. A circuit's rows are the
    // sum of its member functions' rows. Circuit statistics are unchanged.
    let function_stats = std::env::var_os("IXVM_FUNCTION_STATS").is_some();
    let collect_function_stats = function_stats && stats_path.is_some();
    let mut functions = serde_json::Map::new();
    let mut failed = Vec::new();
    struct CaseOutcome {
      label: String,
      stats: Option<serde_json::Value>,
      functions: Option<serde_json::Value>,
      expected: bool,
      line: String,
    }
    let run_case =
      |case: &aiur::artifact::Case| -> Result<CaseOutcome, String> {
        let args = program.field().decode(&case.invocation.args)?;
        let start = Instant::now();
        let result = ixvm::prepare_streams(&program, &case.invocation.streams)?
          .execute(&case.invocation.entry, args);
        let seconds = start.elapsed().as_secs_f64();
        let stats = match (&backend, &result) {
          (Some(backend), Ok(record)) => Some(
            serde_json::to_value(backend.execution_statistics(record))
              .map_err(|e| e.to_string())?,
          ),
          _ => None,
        };
        let functions = if collect_function_stats {
          result.as_ref().ok().map(|record| {
          let mut rows: std::collections::BTreeMap<usize, (u64, u64)> =
            std::collections::BTreeMap::new();
          for (key, output) in record.queries.iter() {
            let entry = rows.entry(key.function).or_default();
            entry.0 += 1;
            entry.1 += output.multiplicity.saturating_sub(1);
          }
          let list: Vec<_> = rows
            .into_iter()
            .map(|(f, (r, h))| {
              serde_json::json!({"name": program.callable_name(f).unwrap_or("?"),
                "rows": r, "cache_hits": h})
            })
            .collect();
          serde_json::Value::Array(list)
        })
        } else {
          None
        };
        let reached = match (&result, &case.exercises) {
          (Ok(record), Some(name)) => record.queries.keys().any(|query| {
            program.callable_name(query.function) == Some(name.as_str())
          }),
          _ => true,
        };
        let error = result.as_ref().err().map(ToString::to_string);
        drop(result);
        // A witness that lacks data the program asks for stops execution before
        // the logic under test: that is not a verdict unless the case names it.
        let expected = match (&error, case.accept, &case.rejects_with) {
          (None, accept, _) => accept && reached,
          (Some(_), true, _) => false,
          (Some(e), false, Some(reason)) => e.contains(reason.as_str()),
          (Some(e), false, None) => !e.contains("missing hint"),
        };
        let verdict = match &error {
          None => "accepted".to_owned(),
          Some(e) => format!("rejected: {e}"),
        };
        let line = if expected {
          format!("{}: {verdict} ({seconds:.3}s)", case.label)
        } else {
          let wanted = match (case.accept, &case.rejects_with) {
            (true, _) if !reached => format!(
              "an acceptance calling {}",
              case.exercises.as_deref().unwrap_or_default()
            ),
            (true, _) => "acceptance".to_owned(),
            (false, Some(reason)) => {
              format!("a rejection containing {reason:?}")
            },
            (false, None) => "a rejection by the program".to_owned(),
          };
          format!("FAILED {}: {verdict}; expected {wanted}", case.label)
        };
        Ok(CaseOutcome {
          label: case.label.clone(),
          stats,
          functions,
          expected,
          line,
        })
      };
    #[cfg(feature = "parallel")]
    let outcomes: Vec<Result<CaseOutcome, String>> = {
      use rayon::prelude::*;
      cases.par_iter().map(run_case).collect()
    };
    #[cfg(not(feature = "parallel"))]
    let outcomes: Vec<Result<CaseOutcome, String>> =
      cases.iter().map(run_case).collect();
    for outcome in outcomes {
      let outcome = outcome?;
      if let Some(stats) = outcome.stats
        && statistics.insert(outcome.label.clone(), stats).is_some()
      {
        return Err(format!("duplicate case label: {}", outcome.label).into());
      }
      if let Some(list) = outcome.functions {
        functions.insert(outcome.label.clone(), list);
      }
      println!("{}", outcome.line);
      if !outcome.expected {
        failed.push(outcome.label);
      }
    }
    if let Some(path) = stats_path {
      serde_json::to_writer(std::fs::File::create(path)?, &statistics)?;
      if function_stats {
        serde_json::to_writer(
          std::fs::File::create(format!("{path}.functions.json"))?,
          &functions,
        )?;
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
  let input = Invocation::load(cli[3].as_ref())?;
  let args = program.field().decode(&input.args)?;
  // A production claim has precisely eight public digest words and no result.
  if input.entry != "IxVM::verify_claim" || args.len() != 8 {
    return Err("expected IxVM::verify_claim and eight digest words".into());
  }
  if mode == "execute" {
    let start = Instant::now();
    let result = ixvm::prepare_streams(&program, &input.streams)?
      .execute(&input.entry, args)?;
    if !result.output.is_empty() {
      return Err("claim verifier returned a value".into());
    }
    let seconds = start.elapsed().as_secs_f64();
    if let Some(path) = cli.get(4) {
      let plan = TracePlan::new(
        &program,
        package.trace.ok_or("statistics require an artifact with circuits")?,
      )?;
      let backend = Backend::for_statistics(&plan, Parameters::default())?;
      let report = serde_json::json!({"execution_statistics": backend.execution_statistics(&result), "execution_seconds": seconds});
      serde_json::to_writer(
        std::fs::File::create(format!("{path}.report.json"))?,
        &report,
      )?;
    }
    println!(
      "executed claim in {:.3}s ({} queries, {} instructions; runtime_check: false assertions skipped)",
      seconds,
      result.queries.len(),
      result.instructions
    );
    return Ok(());
  }
  let path = cli.get(4).ok_or("missing proof path")?;
  let options = Options::read(cli.get(7), cli.get(5), cli.get(6))?;
  let before_setup = aiur::trace::stark::planning::resident_memory();
  let plan =
    TracePlan::new(&program, package.trace.ok_or("artifact has no circuits")?)?;
  let backend = match mode {
    "verify" => Backend::for_batch_verification(&plan, Parameters::default())?,
    "plan" => {
      Backend::for_planning(&plan, Parameters::default(), options.device)?
    },
    _ => Backend::for_batch_on_device(
      &plan,
      Parameters::default(),
      options.device,
    )?,
  };
  if mode == "verify" {
    if let Some(expected_key) =
      verify_pin.as_ref().and_then(|pin| pin.key_digest.as_deref())
    {
      let key = backend.verifying_key_bytes()?;
      let derived = blake3::hash(&key).to_hex().to_string();
      check_key_digest(&derived, expected_key)?;
    }
    let bytes = std::fs::read(path)?;
    let bytes = bytes.strip_prefix(MAGIC).ok_or("not a formal Aiur proof")?;
    let proof = BatchProof::from_bytes(bytes)?;
    if proof.to_bytes()? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    backend.verify_batch(&input.entry, &args, &[], &proof)?;
    println!(
      "verified formal Aiur proof ({} trace shards, artifact {artifact})",
      proof.proofs.len()
    );
    return Ok(());
  }
  let static_resident = artifact_resident.saturating_add(
    aiur::trace::stark::planning::resident_memory()
      .saturating_sub(before_setup),
  );
  let fixed = backend.plan_fixed(&options, static_resident)?;
  if !fixed.fits {
    let report = serde_json::json!({"plan":fixed, "can_split":false, "verified":false,
      "error":"budget is below the estimated artifact and fixed-table floor"});
    std::fs::write(
      format!("{path}.report.json"),
      serde_json::to_vec_pretty(&report)?,
    )?;
    println!("{report}");
    if mode == "plan" {
      return Ok(());
    }
    std::process::exit(75);
  }
  let hints = ixvm::prepare_streams(&program, &input.streams)?;
  drop(input.streams);
  let start = Instant::now();
  let record = hints.execute(&input.entry, args.clone())?;
  let execute = start.elapsed().as_secs_f64();
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  if mode == "tiles" {
    #[cfg(feature = "compiled-trace")]
    {
      let (hosts, tiles, timings) = backend.check_device_tiles(&record)?;
      let report =
        serde_json::json!({"host":hosts, "tiles":tiles, "device":timings});
      std::fs::write(path, serde_json::to_vec_pretty(&report)?)?;
      println!("{report}");
      if tiles.iter().any(|t| t.mismatches != 0 || t.noncanonical != 0) {
        return Err("device tiles differ from host population".into());
      }
      return Ok(());
    }
    #[cfg(not(feature = "compiled-trace"))]
    return Err("tiles requires the compiled-trace feature".into());
  }
  let batch = backend.plan_batch(&record, &options)?;
  let mut report = serde_json::json!({"plan":batch, "artifact_digest":artifact.to_string(), "execution_seconds":execute,
    "storage":record.storage_usage(),
    "queries":record.queries.len(), "instructions":record.instructions,
    "execution_statistics":backend.execution_statistics(&record), "parameters":backend.parameters(),
    "conjectured_security_bits":backend.parameters().conjectured_bits(),
    "verified":false});
  let report_path = format!("{path}.report.json");
  std::fs::write(&report_path, serde_json::to_vec_pretty(&report)?)?;
  if mode == "plan" {
    report.as_object_mut().unwrap().remove("execution_statistics");
    println!("{}", report);
    return Ok(());
  }
  if !batch.fits {
    eprintln!("proving estimate exceeds budget; see {report_path}");
    std::process::exit(75);
  }
  let layout = batch
    .layout
    .as_ref()
    .ok_or("the proving plan has no incremental layout")?;
  std::fs::write(format!("{path}.layout.json"), serde_json::to_vec(layout)?)?;
  let result = backend.prove_incremental_timed(
    &record,
    &input.entry,
    &args,
    &[],
    layout,
    batch.retention(),
    batch.pipelined,
  );
  drop(record);
  drop(hints);
  let run = result?;
  let proof = run.proof;
  let raw = proof.to_bytes()?;
  let mut bytes = MAGIC.to_vec();
  bytes.extend(&raw);
  let key = backend.verifying_key_bytes()?;
  let claim = backend.claim(&input.entry, &args, &[])?;
  VerifyingKey::from_bytes(&key)?
    .verify(std::slice::from_ref(&claim), &proof)?;
  std::fs::write(path, bytes)?;
  // Sidecars make the proof immediately consumable by the recursive verifier.
  std::fs::write(format!("{path}.vk"), &key)?;
  let mut claims = 1u64.to_le_bytes().to_vec();
  claims.extend_from_slice(&(claim.len() as u64).to_le_bytes());
  for v in claim {
    claims.extend_from_slice(&v.as_canonical_u64().to_le_bytes());
  }
  std::fs::write(format!("{path}.claims"), claims)?;
  report["verified"] = true.into();
  report["trace_seconds"] = run.trace_seconds.into();
  report["proving_seconds"] = run.proving_seconds.into();
  report["population"] = serde_json::to_value(&run.population)?;
  report["peak_rss_bytes"] =
    aiur::trace::stark::planning::peak_resident_memory().into();
  report["shards"] = proof.proofs.len().into();
  report["proof_bytes"] = raw.len().into();
  report["key_digest"] = blake3::hash(&key).to_hex().to_string().into();
  std::fs::write(report_path, serde_json::to_vec_pretty(&report)?)?;
  report.as_object_mut().unwrap().remove("execution_statistics");
  println!("{}", report);
  Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VerifyPinMode {
  DefaultKeys,
  KeysFile(std::path::PathBuf),
  ArtifactDigest(String),
  AllowUnpinned,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct IxvmPin {
  artifact_digest: String,
  key_digest: Option<String>,
  source: String,
}

fn is_hex_digest(s: &str) -> bool {
  s.len() == 64 && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

fn parse_verify_cli(
  raw: &[String],
) -> Result<(Vec<String>, VerifyPinMode), String> {
  if raw.get(1).map(String::as_str) != Some("verify") {
    return Ok((raw.to_vec(), VerifyPinMode::DefaultKeys));
  }
  let mut positional = Vec::with_capacity(raw.len());
  let mut pin: Option<VerifyPinMode> = None;
  let mut set_pin = |next: VerifyPinMode| -> Result<(), String> {
    if pin.is_some() {
      return Err(
        "conflicting verify pin flags: choose at most one of --keys, --artifact-digest, or --allow-unpinned"
          .into(),
      );
    }
    pin = Some(next);
    Ok(())
  };
  let mut i = 0;
  while i < raw.len() {
    match raw[i].as_str() {
      "--allow-unpinned" => {
        set_pin(VerifyPinMode::AllowUnpinned)?;
        i += 1;
      },
      "--keys" => {
        let path = raw.get(i + 1).ok_or("missing path argument for --keys")?;
        set_pin(VerifyPinMode::KeysFile(std::path::PathBuf::from(path)))?;
        i += 2;
      },
      "--artifact-digest" => {
        let digest = raw
          .get(i + 1)
          .ok_or("missing hex digest argument for --artifact-digest")?
          .to_ascii_lowercase();
        if !is_hex_digest(&digest) {
          return Err(format!(
            "invalid --artifact-digest {digest:?}: expected 64 hex characters"
          ));
        }
        set_pin(VerifyPinMode::ArtifactDigest(digest))?;
        i += 2;
      },
      arg if i >= 2 && arg.starts_with("--") => {
        return Err(format!("unknown verify flag {arg:?}"));
      },
      _ => {
        positional.push(raw[i].clone());
        i += 1;
      },
    }
  }
  Ok((positional, pin.unwrap_or(VerifyPinMode::DefaultKeys)))
}

fn parse_ixvm_pin(contents: &str, source: &str) -> Result<IxvmPin, String> {
  let mut found: Option<IxvmPin> = None;
  for (lineno, raw_line) in contents.lines().enumerate() {
    let line = raw_line.split('#').next().unwrap_or("").trim();
    if line.is_empty() {
      continue;
    }
    let fields: Vec<_> = line.split_whitespace().collect();
    if fields.first().copied() != Some("ixvm") {
      continue;
    }
    if fields.len() < 3 {
      return Err(format!("{source}:{}: malformed ixvm pin line", lineno + 1));
    }
    let artifact_digest = fields[1].to_ascii_lowercase();
    let key_digest = fields[2].to_ascii_lowercase();
    if !is_hex_digest(&artifact_digest) || !is_hex_digest(&key_digest) {
      return Err(format!(
        "{source}:{}: malformed ixvm hex digest",
        lineno + 1
      ));
    }
    if found.is_some() {
      return Err(format!("{source}:{}: duplicate ixvm pin line", lineno + 1));
    }
    found = Some(IxvmPin {
      artifact_digest,
      key_digest: Some(key_digest),
      source: source.to_owned(),
    });
  }
  found.ok_or_else(|| format!("{source}: missing ixvm pin entry"))
}

fn locate_default_keys_file() -> Option<std::path::PathBuf> {
  let rel = std::path::Path::new("tools/formal-aiur.keys");
  if rel.is_file() {
    return Some(rel.to_path_buf());
  }
  if let Ok(exe) = std::env::current_exe() {
    for ancestor in exe.ancestors() {
      let candidate = ancestor.join(rel);
      if candidate.is_file() {
        return Some(candidate);
      }
    }
  }
  let manifest_fallback = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("../../tools/formal-aiur.keys");
  if manifest_fallback.is_file() {
    return Some(manifest_fallback);
  }
  None
}

fn resolve_verify_pin(mode: &VerifyPinMode) -> Result<Option<IxvmPin>, String> {
  match mode {
    VerifyPinMode::AllowUnpinned => Ok(None),
    VerifyPinMode::ArtifactDigest(digest) => Ok(Some(IxvmPin {
      artifact_digest: digest.clone(),
      key_digest: None,
      source: "--artifact-digest".to_owned(),
    })),
    VerifyPinMode::KeysFile(path) => {
      let text = std::fs::read_to_string(path)
        .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
      Ok(Some(parse_ixvm_pin(&text, &path.display().to_string())?))
    },
    VerifyPinMode::DefaultKeys => {
      let path = locate_default_keys_file().ok_or_else(|| {
        "cannot locate tools/formal-aiur.keys to verify artifact digest pin \
         (pass --keys PATH, --artifact-digest HEX, or --allow-unpinned)"
          .to_owned()
      })?;
      let text = std::fs::read_to_string(&path)
        .map_err(|e| format!("failed to read {}: {e}", path.display()))?;
      Ok(Some(parse_ixvm_pin(&text, &path.display().to_string())?))
    },
  }
}

fn check_artifact_digest(
  actual: &str,
  pin: Option<&IxvmPin>,
) -> Result<(), String> {
  let Some(pin) = pin else {
    return Ok(());
  };
  if actual != pin.artifact_digest {
    return Err(format!(
      "artifact digest {actual} does not match pinned ixvm digest {} from {} \
       (pass --allow-unpinned to verify against an unpinned artifact)",
      pin.artifact_digest, pin.source
    ));
  }
  Ok(())
}

fn check_key_digest(actual: &str, expected: &str) -> Result<(), String> {
  if actual != expected {
    return Err(format!(
      "derived verifying key digest {actual} does not match pinned ixvm key digest {expected}"
    ));
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parse_default_formal_aiur_keys_and_validate_digest() {
    let pin = resolve_verify_pin(&VerifyPinMode::DefaultKeys)
      .unwrap()
      .expect("default keys file yields an ixvm pin");
    assert!(is_hex_digest(&pin.artifact_digest));
    let key = pin.key_digest.as_deref().expect("ixvm pin includes key digest");
    assert!(is_hex_digest(key));
    check_artifact_digest(&pin.artifact_digest, Some(&pin)).unwrap();
    check_key_digest(key, key).unwrap();

    let wrong = "0".repeat(64);
    let err = check_artifact_digest(&wrong, Some(&pin)).unwrap_err();
    assert!(err.contains("does not match pinned ixvm digest"), "{err}");
    let err = check_key_digest(&wrong, key).unwrap_err();
    assert!(err.contains("does not match pinned ixvm key digest"), "{err}");
  }

  #[test]
  fn parse_verify_cli_supports_pin_flags_and_rejects_conflicts() {
    let args =
      |xs: &[&str]| xs.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
    let (pos, mode) = parse_verify_cli(&args(&[
      "ixvm-proof",
      "verify",
      "a.ixa",
      "in.ixi",
      "p.bin",
    ]))
    .unwrap();
    assert_eq!(pos.len(), 5);
    assert_eq!(mode, VerifyPinMode::DefaultKeys);

    let (pos, mode) = parse_verify_cli(&args(&[
      "ixvm-proof",
      "verify",
      "a.ixa",
      "in.ixi",
      "p.bin",
      "--allow-unpinned",
    ]))
    .unwrap();
    assert_eq!(pos.len(), 5);
    assert_eq!(mode, VerifyPinMode::AllowUnpinned);

    let hex = "a".repeat(64);
    let (pos, mode) = parse_verify_cli(&args(&[
      "ixvm-proof",
      "verify",
      "a.ixa",
      "in.ixi",
      "p.bin",
      "--artifact-digest",
      &hex,
    ]))
    .unwrap();
    assert_eq!(pos.len(), 5);
    assert_eq!(mode, VerifyPinMode::ArtifactDigest(hex.clone()));

    assert!(
      parse_verify_cli(&args(&[
        "ixvm-proof",
        "verify",
        "a.ixa",
        "in.ixi",
        "p.bin",
        "--allow-unpinned",
        "--artifact-digest",
        &hex,
      ]))
      .is_err()
    );
    assert!(
      parse_verify_cli(&args(&[
        "ixvm-proof",
        "verify",
        "a.ixa",
        "in.ixi",
        "p.bin",
        "--artifact-digest",
        "not-a-digest",
      ]))
      .is_err()
    );
  }

  #[test]
  fn parse_ixvm_pin_rejects_missing_or_malformed_entries() {
    assert!(
      parse_ixvm_pin("# comment only\nparameters log_blowup 2\n", "test")
        .is_err()
    );
    assert!(parse_ixvm_pin("ixvm short digest\n", "test").is_err());
    let dup = format!(
      "ixvm {} {} 0\nixvm {} {} 0\n",
      "1".repeat(64),
      "2".repeat(64),
      "3".repeat(64),
      "4".repeat(64)
    );
    assert!(parse_ixvm_pin(&dup, "test").is_err());
  }
}
