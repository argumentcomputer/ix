//! Prove and verify one invocation of a program lowered from IxCC's first-order
//! IR (the execution package `ixcc-aiur -o PACKAGE.ixa` writes), on the CPU
//! prover with the default parameters, and check that the verifier refuses
//! the same proof under a changed claim, and a proof made for a changed output.
//!
//! This is `prove.rs` with the host advice a lowered program reads: the
//! `UInt64` library's byte decompositions and `ixcc.divmod`. The package
//! carries no hint data. Nothing here is on the verifier's side: the verifier
//! reads the compiled circuits and the public call alone.
use aiur::field::FieldBackend;
use aiur::{
  artifact::ExecutionPackage,
  hints::HintChannels,
  trace::{
    TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use multi_stark::p3_matrix::Matrix;
use serde_json::json;
use std::{error::Error, time::Instant};

/// Peak resident set size of this process in kilobytes, where the platform
/// reports it.
fn peak_rss_kb() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse().ok()
}

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let path = args
    .get(1)
    .ok_or("usage: ixcc_prove PACKAGE.ixa [PROOF.bin] [REPORT.json]")?;
  let total = Instant::now();
  let start = Instant::now();
  let (package, digest) = ExecutionPackage::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {digest}");
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let field = program.field();
  let address = field.decode(&package.args)?;
  let mut channels = HintChannels::new();
  aiur::library::u64::register(&mut channels, field)?;
  aiur::library::ixcc::register(&mut channels, field)?;
  let hints = program.prepare_hint_channels(&package.hints, &channels)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry =
    &program.program().entries.first().ok_or("no selected entrypoint")?.name;
  let prepare_seconds = start.elapsed().as_secs_f64();

  let parameters = Parameters::default();
  eprintln!("Setting up circuits and committing fixed tables...");
  let start = Instant::now();
  let backend = Backend::new(&plan, parameters)?;
  let setup_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let record = hints.execute(entry, address.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let witness = backend.generate(&record, entry, &address)?;
  let witness_seconds = start.elapsed().as_secs_f64();
  // The independent trace writer and its constraint check, outside the
  // measured witness and proving times.
  let start = Instant::now();
  let reference = plan.generate_reference(&record, entry, &address, true)?;
  plan.check(&record, &reference, entry, &address)?;
  let check_seconds = start.elapsed().as_secs_f64();

  let statistics = backend.statistics();
  let circuits: Vec<_> = statistics
    .iter()
    .zip(&witness.traces)
    .map(|(s, t)| {
      let mut value = serde_json::to_value(s).unwrap();
      value["height"] = json!(t.height());
      value
    })
    .collect();
  let rows: usize = witness.traces.iter().map(|t| t.height()).sum();
  let active = witness.traces.iter().filter(|t| t.height() > 0).count();
  let stage1_words: usize = witness.traces.iter().map(|t| t.values.len()).sum();
  let output = record.output.clone();
  drop(record);
  eprintln!(
    "Proving {active} active circuits ({rows} rows, {stage1_words} stage-1 words)..."
  );
  let start = Instant::now();
  let proof = backend.prove(entry, &address, &output, witness)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let bytes = proof.to_bytes()?;
  let proof = Proof::from_bytes(&bytes)?;
  eprintln!("Verifying serialized proof ({} bytes)...", bytes.len());
  let start = Instant::now();
  backend.verify(entry, &address, &output, &proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  // What the run has cost up to here; the controls below are not part of it.
  let total_seconds = total.elapsed().as_secs_f64();
  let peak_rss_kb = peak_rss_kb();

  // Negative controls. For every claim that differs from the proved one in a
  // single output word or a single argument word, the verifier must refuse
  // the proof. For a changed output it must also refuse a proof that the
  // prover makes for that output from the honest execution (`forged`),
  // unless the changed output is not a value of the result type at all.
  let flip = |words: &[_], index: usize| -> Result<Vec<_>, String> {
    let mut changed = words.to_vec();
    changed[index] = field.from_u64(field.try_to_u64(changed[index])? ^ 1);
    Ok(changed)
  };
  let mut rejections = Vec::new();
  for index in 0..output.len() {
    let wrong = flip(&output, index)?;
    match backend.verify(entry, &address, &wrong, &proof) {
      Ok(()) => {
        return Err(
          format!("verifier accepted a wrong output (word {index})").into(),
        );
      },
      Err(error) => {
        let record = hints.execute(entry, address.clone())?;
        let witness = backend.generate(&record, entry, &address)?;
        let forged = match backend.prove(entry, &address, &wrong, witness) {
          Err(refused) => format!("no proof: {refused}"),
          Ok(forged) => {
            match backend.verify(entry, &address, &wrong, &forged) {
              Ok(()) => {
                return Err(
                  format!("verifier accepted a forged output (word {index})")
                    .into(),
                );
              },
              Err(rejected) => format!("rejected: {rejected}"),
            }
          },
        };
        rejections.push(json!({
          "changed": "output", "word": index, "claimed": wrong,
          "error": error, "forged": forged,
        }));
      },
    }
  }
  for index in 0..address.len() {
    let wrong = flip(&address, index)?;
    match backend.verify(entry, &wrong, &output, &proof) {
      Ok(()) => {
        return Err(
          format!("verifier accepted a wrong argument (word {index})").into(),
        );
      },
      Err(error) => rejections.push(json!({
        "changed": "argument", "word": index, "claimed": wrong, "error": error,
      })),
    }
  }

  if let Some(path) = args.get(2) {
    std::fs::write(path, &bytes)?;
  }
  let report = json!({
      "artifact_blake3": digest.to_string(),
      "entry": entry, "args": address, "output": output, "parameters": parameters,
      "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds,
      "execution_seconds": execution_seconds, "witness_seconds": witness_seconds,
      "check_seconds": check_seconds,
      "prove_seconds": prove_seconds, "verify_seconds": verify_seconds,
      "total_seconds": total_seconds,
      "peak_rss_kb": peak_rss_kb,
      "proof_bytes": bytes.len(), "rows": rows, "active_circuits": active,
      "stage1_words": stage1_words,
      "verified": true, "rejected_wrong_claims": rejections.len(),
      "rejections": rejections, "circuits": circuits,
  });
  if let Some(path) = args.get(3) {
    serde_json::to_writer_pretty(
      std::io::BufWriter::new(std::fs::File::create(path)?),
      &report,
    )?;
  }
  // Circuit details go in the report; stdout is a short summary.
  let mut summary = report;
  summary.as_object_mut().unwrap().remove("circuits");
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}
