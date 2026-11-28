//! Prove and verify one invocation of a program lowered from IxCC's first-order
//! IR (the execution package `ixcc-aiur -o PACKAGE.ixa` writes), on the CPU
//! prover with the default parameters, and check that the verifier refuses
//! the same proof under a changed claim, and a proof made for a changed output.
//!
//! This is `prove.rs` with the host advice a lowered program reads: the
//! `UInt32` and `UInt64` libraries' byte decompositions, `ixcc.divmod`,
//! `ixcc.divmod64`, and universal Tier-2 `ixcc.guess.<fn>` advice. The package
//! carries no hint data. Nothing here is on the verifier's side: the verifier
//! reads the compiled circuits and the public call alone.
//!
//! When the run asked for `ixcc.divmod64`, the controls also re-execute the
//! invocation under three wrong answers on that channel (a quotient one too
//! large with the true remainder; one too small with the remainder plus the
//! divisor; one too large with the remainder minus the divisor, wrapping),
//! and require each execution to fail.
//!
//! `--args N,N,...` replaces the package's arguments (one compiled program,
//! several invocations). `--advice ADVICE.ixa` loads the unmodified pre-guess
//! bytecode package (`ixcc-aiur --advice-out ADVICE.ixa`) to automatically
//! answer every `"ixcc.guess.<fn>"` channel with zero per-function hardcoding.
//! `--tamper-hint CHANNEL` intentionally corrupts the advice for `CHANNEL` to
//! verify wrong-hint rejection directly. `--no-controls` skips the reference
//! trace check and the negative controls, for measurements: the report's times,
//! rows and peak memory are then of executing, proving and verifying alone.
//! `--pin PIN.json` checks the pin `ixcc-aiur` wrote beside the package (the
//! BLAKE3 of the file, and of the compiled program alone) before anything else,
//! and refuses the package on a mismatch.
use aiur::field::FieldBackend;
use aiur::{
  artifact::{
    self, Digest, EXECUTION_MAGIC, ExecutionPackage, PACKAGE_MAGIC, Package,
  },
  bytecode::Program,
  hints::HintChannels,
  library::ixcc::{DIVMOD64, divmod_u64},
  trace::{
    TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use multi_stark::p3_matrix::Matrix;
use serde_json::json;
use std::{
  error::Error,
  sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
  },
  time::Instant,
};

/// Wrong `ixcc.divmod64` answers, each from the true quotient and remainder.
type Lie = fn(u64, u64) -> (u64, u64);
const LIES: [(&str, Lie); 3] = [
  ("q+1, r", |x, y| {
    let (q, r) = divmod_u64(x, y);
    (q.wrapping_add(1), r)
  }),
  ("q-1, r+y", |x, y| {
    let (q, r) = divmod_u64(x, y);
    (q.wrapping_sub(1), r.wrapping_add(y))
  }),
  ("q+1, r-y", |x, y| {
    let (q, r) = divmod_u64(x, y);
    (q.wrapping_add(1), r.wrapping_sub(y))
  }),
];

const USAGE: &str = "usage: ixcc_prove PACKAGE.ixa [PROOF.bin] [REPORT.json] \
                     [--args N,N,...] [--advice ADVICE.ixa] \
                     [--tamper-hint CHANNEL] [--no-controls] [--pin PIN.json]";

fn load_advice_program(
  path: &str,
) -> Result<(Program, Digest), Box<dyn Error>> {
  let (raw_bytes, digest) = artifact::read(path.as_ref())?;
  let package = if raw_bytes.starts_with(PACKAGE_MAGIC) {
    Package::decode(&raw_bytes)
      .map_err(|e| format!("invalid advice package {path}: {e}"))?
  } else if raw_bytes.starts_with(EXECUTION_MAGIC) {
    ExecutionPackage::decode(&raw_bytes)
      .map_err(|e| format!("invalid advice execution package {path}: {e}"))?
      .package
  } else {
    return Err(format!(
      "unrecognized advice artifact magic in {path} (expected IXAIURP\\0 or IXAIURX\\0)"
    )
    .into());
  };
  Ok((package.program, digest))
}

/// Peak resident set size of this process in kilobytes, where the platform
/// reports it.
fn peak_rss_kb() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse().ok()
}

/// The compiled program alone, as `ixcc-aiur` hashes it for the pin: a
/// package with the file's program and no trace section.
fn program_only(program: &Program) -> Vec<u8> {
  Package { program: program.clone(), trace: None }.encode()
}

/// Whether `program` (a package without a trace section) is, up to its last
/// byte (the trace option's tag), the embedded package's prefix in `file`.
fn embedded(file: &[u8], program: &[u8]) -> bool {
  let Some((_, prefix)) = program.split_last() else { return false };
  let Some(start) =
    file.windows(PACKAGE_MAGIC.len()).take(32).position(|w| w == PACKAGE_MAGIC)
  else {
    return false;
  };
  file.get(start..start + prefix.len()) == Some(prefix)
}

/// Check the pin `ixcc-aiur` wrote beside a package (`PACKAGE.ixa.pin.json`)
/// against the file's bytes, before anything is decoded for proving: the
/// BLAKE3 of the whole file (`package_blake3`), and the BLAKE3 of the
/// compiled program alone (`program_blake3`), recomputed from the decoded
/// program, whose bytes must also be the file's own. Any mismatch refuses.
fn check_pin(
  pin_path: &str,
  file: &[u8],
  digest: Digest,
) -> Result<serde_json::Value, Box<dyn Error>> {
  let pin: serde_json::Value =
    serde_json::from_slice(&std::fs::read(pin_path)?)?;
  let pinned = |key: &str| -> Result<Digest, String> {
    let hex =
      pin[key].as_str().ok_or_else(|| format!("pin {pin_path}: no {key}"))?;
    Digest::from_hex(hex)
  };
  let package_pin = pinned("package_blake3")?;
  let program_pin = pinned("program_blake3")?;
  let mut mismatches = Vec::new();
  if digest != package_pin {
    mismatches
      .push(format!("package_blake3: file {digest}, pin {package_pin}"));
  }
  // The program check also runs when the file's digest already differs, so
  // that the refusal says which parts differ.
  let decoded_program = if file.starts_with(PACKAGE_MAGIC) {
    Package::decode(file).map(|pkg| pkg.program)
  } else if file.starts_with(EXECUTION_MAGIC) {
    ExecutionPackage::decode(file).map(|exec| exec.package.program)
  } else {
    Err(
      "unrecognized artifact magic (expected IXAIURP\\0 or IXAIURX\\0)".into(),
    )
  };
  match decoded_program {
    Ok(prog) => {
      let program = program_only(&prog);
      let program_digest = Digest::of(&program);
      if program_digest != program_pin {
        mismatches.push(format!(
          "program_blake3: file {program_digest}, pin {program_pin}"
        ));
      }
      if !embedded(file, &program) {
        mismatches.push(
          "program_blake3: the re-encoded program is not the file's bytes"
            .into(),
        );
      }
    },
    Err(error) => mismatches
      .push(format!("program_blake3: the file does not decode ({error})")),
  }
  if !mismatches.is_empty() {
    return Err(
      format!("pin {pin_path} refused: {}", mismatches.join("; ")).into(),
    );
  }
  Ok(json!({
    "pin": pin_path, "package_blake3": package_pin.to_string(),
    "program_blake3": program_pin.to_string(), "checked": true,
  }))
}

fn main() -> Result<(), Box<dyn Error>> {
  let mut args = Vec::new();
  let mut override_args: Option<Vec<u64>> = None;
  let mut advice_path: Option<String> = None;
  let mut tamper_hint: Option<String> = None;
  let mut controls = true;
  let mut pin_path: Option<String> = None;
  let mut raw = std::env::args();
  while let Some(arg) = raw.next() {
    match arg.as_str() {
      "--args" => {
        let list = raw.next().ok_or("--args needs a comma-separated list")?;
        override_args = Some(
          list
            .split(',')
            .filter(|word| !word.is_empty())
            .map(str::parse)
            .collect::<Result<_, _>>()?,
        );
      },
      "--advice" => {
        advice_path = Some(raw.next().ok_or("--advice needs a path")?);
      },
      "--tamper-hint" => {
        tamper_hint =
          Some(raw.next().ok_or("--tamper-hint needs a channel name")?);
      },
      "--no-controls" => controls = false,
      "--pin" => pin_path = Some(raw.next().ok_or("--pin needs a file")?),
      _ => args.push(arg),
    }
  }
  let path = args.get(1).ok_or(USAGE)?;
  let total = Instant::now();
  let start = Instant::now();
  let (raw_bytes, digest) = artifact::read(path.as_ref())?;
  let pin = match &pin_path {
    Some(pin_path) => check_pin(pin_path, &raw_bytes, digest)?,
    None => serde_json::Value::Null,
  };
  let (package, embedded_args, embedded_hints, kind) = if raw_bytes
    .starts_with(PACKAGE_MAGIC)
  {
    let pkg = Package::decode(&raw_bytes)
      .map_err(|e| format!("invalid program package {path}: {e}"))?;
    (pkg, Vec::new(), Vec::new(), "program")
  } else if raw_bytes.starts_with(EXECUTION_MAGIC) {
    let exec = ExecutionPackage::decode(&raw_bytes)
      .map_err(|e| format!("invalid execution package {path}: {e}"))?;
    (exec.package, exec.args, exec.hints, "execution")
  } else {
    return Err(format!(
        "unrecognized artifact magic in {path} (expected IXAIURP\\0 or IXAIURX\\0)"
      )
      .into());
  };
  drop(raw_bytes);
  eprintln!("artifact {path} ({kind}): blake3 {digest}");
  let (program, trace) = package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let field = program.field();
  let address =
    field.decode(override_args.as_deref().unwrap_or(&embedded_args))?;
  let divmod64_counter = Arc::new(AtomicUsize::new(0));
  let counter = divmod64_counter.clone();
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, field)?;
  aiur::library::u64::register(&mut channels, field)?;
  aiur::library::ixcc::register_divmod(&mut channels, field)?;
  aiur::library::ixcc::register_divmod64_with(
    &mut channels,
    field,
    move |x, y| {
      counter.fetch_add(1, Ordering::Relaxed);
      divmod_u64(x, y)
    },
  )?;
  let mut advice_digest: Option<Digest> = None;
  let mut advice_raw_program: Option<Program> = None;
  let mut guess_channels: Vec<String> = Vec::new();
  if let Some(adv_path) = &advice_path {
    let (adv_prog, adv_dig) = load_advice_program(adv_path)?;
    eprintln!("advice {adv_path}: blake3 {adv_dig}");
    advice_digest = Some(adv_dig);
    advice_raw_program = Some(adv_prog.clone());
    let checked_adv = adv_prog.check_field::<multi_stark::types::Val>()?;
    guess_channels = if let Some(ch) = &tamper_hint {
      let (regs, _) = aiur::library::ixcc::register_tampered_advice_program(
        &mut channels,
        &program,
        checked_adv,
        ch,
      )?;
      regs
    } else {
      aiur::library::ixcc::register_advice_program(
        &mut channels,
        &program,
        checked_adv,
      )?
    };
    if !guess_channels.is_empty() {
      eprintln!("registered guess channels: {guess_channels:?}");
    }
  } else if tamper_hint.is_some() {
    return Err("--tamper-hint requires --advice ADVICE.ixa".into());
  }
  let hints = program.prepare_hint_channels(&embedded_hints, &channels)?;
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
  let divmod64_calls = divmod64_counter.load(Ordering::Relaxed);

  let start = Instant::now();
  let witness = backend.generate(&record, entry, &address)?;
  let witness_seconds = start.elapsed().as_secs_f64();
  // The independent trace writer and its constraint check, outside the
  // measured witness and proving times.
  let start = Instant::now();
  if controls {
    let reference = plan.generate_reference(&record, entry, &address, true)?;
    plan.check(&record, &reference, entry, &address)?;
  }
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
  // Rows of the fixed tables and of the memory argument, apart from the
  // program's own circuits.
  let rows_named = |prefix: &str| -> usize {
    statistics
      .iter()
      .zip(&witness.traces)
      .filter(|(s, _)| s.name.starts_with(prefix))
      .map(|(_, t)| t.height())
      .sum()
  };
  let table_rows = rows_named("<table:");
  let rom_rows = rows_named("<ROM:");
  let program_rows = rows - table_rows - rom_rows;
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
  let checked_outputs = if controls { output.len() } else { 0 };
  let checked_arguments = if controls { address.len() } else { 0 };
  for index in 0..checked_outputs {
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
  for index in 0..checked_arguments {
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

  // Wrong `ixcc.divmod64` advice: the lowered program checks `q * y + r = x`
  // without overflow and `r < y` on the words, so each wrong answer must lose
  // the execution. Only when the honest run asked the channel at all.
  let mut advice_rejections = Vec::new();
  if controls && divmod64_calls > 0 {
    for (name, lie) in LIES {
      let mut bad_channels = HintChannels::new();
      aiur::library::u32::register(&mut bad_channels, field)?;
      aiur::library::u64::register(&mut bad_channels, field)?;
      aiur::library::ixcc::register_divmod(&mut bad_channels, field)?;
      aiur::library::ixcc::register_divmod64_with(
        &mut bad_channels,
        field,
        lie,
      )?;
      if let Some(adv_raw) = &advice_raw_program {
        let checked_adv =
          adv_raw.clone().check_field::<multi_stark::types::Val>()?;
        aiur::library::ixcc::register_advice_program(
          &mut bad_channels,
          &program,
          checked_adv,
        )?;
      }
      let lying =
        program.prepare_hint_channels(&embedded_hints, &bad_channels)?;
      match lying.execute(entry, address.clone()) {
        Ok(_) => {
          return Err(
            format!("execution accepted a wrong {DIVMOD64} answer ({name})")
              .into(),
          );
        },
        Err(error) => advice_rejections
          .push(json!({ "advice": name, "error": error.to_string() })),
      }
    }
  }

  // Wrong-hint negative controls: for every registered `"ixcc.guess.*"`
  // channel, perturb its host advice (+1 mod p on the last word) and verify
  // that every invoked channel is rejected by the circuit's verified checker
  // (or constraint / STARK verifier if assertions are deferred).
  let mut wrong_hint_controls = Vec::new();
  if controls
    && tamper_hint.is_none()
    && let Some(adv_raw) = &advice_raw_program
  {
    for ch in &guess_channels {
      let mut bad_channels = HintChannels::new();
      aiur::library::u32::register(&mut bad_channels, field)?;
      aiur::library::u64::register(&mut bad_channels, field)?;
      aiur::library::ixcc::register(&mut bad_channels, field)?;
      let checked_adv =
        adv_raw.clone().check_field::<multi_stark::types::Val>()?;
      let (_, hits) = aiur::library::ixcc::register_tampered_advice_program(
        &mut bad_channels,
        &program,
        checked_adv,
        ch,
      )?;
      let bad_hints =
        program.prepare_hint_channels(&embedded_hints, &bad_channels)?;
      match bad_hints.execute(entry, address.clone()) {
        Err(error) => {
          wrong_hint_controls.push(json!({
            "tampered_channel": ch,
            "invocations": hits.load(Ordering::Relaxed),
            "rejected": true,
            "stage": "execute",
            "error": error.to_string(),
          }));
        },
        Ok(bad_record) => {
          let invoked = hits.load(Ordering::Relaxed);
          if invoked == 0 {
            wrong_hint_controls.push(json!({
              "tampered_channel": ch,
              "invocations": 0,
              "rejected": false,
              "stage": "not_invoked",
            }));
          } else {
            let bad_out = bad_record.output.clone();
            let check_err = plan
              .generate_reference(&bad_record, entry, &address, true)
              .and_then(|reference| {
                plan.check(&bad_record, &reference, entry, &address)
              });
            match check_err {
              Err(error) => {
                wrong_hint_controls.push(json!({
                  "tampered_channel": ch,
                  "invocations": invoked,
                  "rejected": true,
                  "stage": "trace_check",
                  "error": error,
                }));
              },
              Ok(()) => {
                let bad_witness =
                  backend.generate(&bad_record, entry, &address)?;
                match backend
                  .prove(entry, &address, &bad_out, bad_witness)
                  .and_then(|p| backend.verify(entry, &address, &bad_out, &p))
                {
                  Err(error) => {
                    wrong_hint_controls.push(json!({
                      "tampered_channel": ch,
                      "invocations": invoked,
                      "rejected": true,
                      "stage": "stark_verify",
                      "error": error,
                    }));
                  },
                  Ok(()) => {
                    return Err(
                      format!(
                        "circuit accepted a tampered hint on channel {ch:?} \
                       ({invoked} invocations)!"
                      )
                      .into(),
                    );
                  },
                }
              },
            }
          }
        },
      }
    }
  }
  let rejected_wrong_hints = wrong_hint_controls
    .iter()
    .filter(|entry| entry["rejected"].as_bool() == Some(true))
    .count();

  if let Some(path) = args.get(2) {
    std::fs::write(path, &bytes)?;
  }
  let report = json!({
      "artifact_blake3": digest.to_string(),
      "pin": pin,
      "advice_blake3": advice_digest.map(|d| d.to_string()),
      "guess_channels": guess_channels,
      "entry": entry, "args": address, "output": output, "parameters": parameters,
      "prepare_seconds": prepare_seconds, "setup_seconds": setup_seconds,
      "execution_seconds": execution_seconds, "witness_seconds": witness_seconds,
      "check_seconds": check_seconds,
      "prove_seconds": prove_seconds, "verify_seconds": verify_seconds,
      "total_seconds": total_seconds,
      "peak_rss_kb": peak_rss_kb,
      "proof_bytes": bytes.len(), "rows": rows, "active_circuits": active,
      "program_rows": program_rows, "table_rows": table_rows,
      "rom_rows": rom_rows, "controls": controls,
      "stage1_words": stage1_words,
      "verified": true, "rejected_wrong_claims": rejections.len(),
      "rejections": rejections,
      "divmod64_calls": divmod64_calls,
      "rejected_wrong_advice": advice_rejections.len(),
      "advice_rejections": advice_rejections,
      "rejected_wrong_hints": rejected_wrong_hints,
      "wrong_hint_controls": wrong_hint_controls,
      "circuits": circuits,
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
