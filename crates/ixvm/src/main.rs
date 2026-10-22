//! Run a Lean-produced IxVM execution package without transporting the full
//! query record back through JSON. Execution uses the same VM as the Lean FFI.
use aiur::{
  Program,
  field::{FieldBackend, NativeField},
  hints::HintEntry,
};
// The embedding chooses multi-stark's reference configuration; the VM is generic.
type HostField = NativeField<multi_stark::types::Val>;
type CheckedProgram = aiur::bytecode::CheckedProgram<HostField>;
type Execution = aiur::execute::Execution<HostField>;
use serde::Deserialize;
use std::{error::Error, time::Instant};

#[path = "../../../tools/bench/profile.rs"]
mod profile;

use ixvm as ixvm_hints;

#[derive(Deserialize)]
struct Package {
  program: Program,
  address: Vec<u64>,
  hints: Vec<HintEntry>,
  #[serde(default)]
  invalid_address: Vec<u64>,
}

fn run(
  program: &CheckedProgram,
  name: &str,
  args: Vec<u64>,
  hints: &[HintEntry],
) -> Result<Execution, Box<dyn Error>> {
  let args = program.field().decode(&args)?;
  let start = Instant::now();
  let result = ixvm_hints::prepare(program, hints)?.execute(name, args)?;
  let elapsed = start.elapsed();
  if !result.output.is_empty() {
    return Err(format!("{name} returned a non-unit result").into());
  }
  let uses: u64 = result.queries.values().map(|q| q.multiplicity).sum();
  println!(
    "{name}: OK ({:.3}s, {} instructions, {} queries, {} query uses, {} ROM cells)",
    elapsed.as_secs_f64(),
    result.instructions,
    result.queries.len(),
    uses,
    result.memory.len(),
  );
  Ok(result)
}

fn benchmark(
  program: &CheckedProgram,
  package: &Package,
  samples: usize,
) -> Result<(), Box<dyn Error>> {
  if samples == 0 {
    return Err("benchmark requires at least one sample".into());
  }
  let start = Instant::now();
  let hints = ixvm_hints::prepare(program, &package.hints)?;
  let preparation_seconds = start.elapsed().as_secs_f64();
  let profiler = profile::Profiler::from_env()?;
  let mut times = Vec::with_capacity(samples);
  let mut counts = None;
  let address = program.field().decode(&package.address)?;
  for i in 0..samples + 3 {
    let args = address.clone();
    let profile = if i >= 3 {
      profiler.as_ref().map(|p| p.start("new-aiur", i - 3)).transpose()?
    } else {
      None
    };
    let start = Instant::now();
    let result = hints.execute("IxVM::verify_transitive", args)?;
    let seconds = start.elapsed().as_secs_f64();
    drop(profile);
    assert!(result.output.is_empty());
    let observed = (
      result.instructions,
      result.queries.len(),
      result
        .queries
        .keys()
        .filter(|q| q.function < program.program().functions.len())
        .count(),
      result.queries.values().map(|q| q.multiplicity).sum::<u64>(),
      result.memory.len(),
    );
    if let Some(expected) = counts {
      assert_eq!(observed, expected, "fresh runs must do the same work");
    }
    counts = Some(observed);
    if i == 0 && std::env::var_os("AIUR_QUERY_STATS").is_some() {
      let mut rows = vec![
        (0usize, 0u64);
        program.program().functions.len()
          + program.program().maps.len()
      ];
      for (key, output) in result.queries.iter() {
        rows[key.function].0 += 1;
        rows[key.function].1 += output.multiplicity;
      }
      let mut rows: Vec<_> = rows.into_iter().enumerate().collect();
      rows.sort_by_key(|(_, (unique, _))| std::cmp::Reverse(*unique));
      for (id, (unique, uses)) in rows.into_iter().take(35) {
        eprintln!(
          "{unique:>8} queries {uses:>8} uses {}",
          program.callable_name(id).unwrap()
        );
      }
    }
    if i >= 3 {
      times.push(seconds);
    }
    // Drop the returned query record outside the measured interval.
  }
  let (instructions, queries, function_queries, uses, memory) = counts.unwrap();
  println!(
    "{}",
    serde_json::json!({
        "engine": "new-aiur-bytecode", "warmups": 3,
        "seconds": times, "hint_preparation_seconds": preparation_seconds,
        "instructions": instructions, "queries": queries, "query_uses": uses,
        "function_queries": function_queries, "map_queries": queries - function_queries,
        "rom_cells": memory,
    })
  );
  Ok(())
}

fn rejected(
  program: &CheckedProgram,
  label: &str,
  args: Vec<u64>,
  hints: &[HintEntry],
  reason: &str,
) -> Result<(), Box<dyn Error>> {
  let args = program.field().decode(&args)?;
  match ixvm_hints::prepare(program, hints)?
    .execute("IxVM::verify_constant", args)
  {
    Ok(_) => Err(format!("accepted {label}").into()),
    Err(e) if e.message.contains(reason) => {
      println!("{label}: rejected ({e})");
      Ok(())
    },
    Err(e) => {
      Err(format!("{label}: wrong rejection: {e}; expected {reason}").into())
    },
  }
}

fn negatives(
  program: &CheckedProgram,
  package: &Package,
) -> Result<(), Box<dyn Error>> {
  let mut key = vec![2];
  key.extend(&package.address);
  let info = package
    .hints
    .iter()
    .position(|h| h.key == key && h.output.len() == 2)
    .ok_or("fixture has no target stream")?;
  let offset = package.hints[info].output[0];
  let byte = package
    .hints
    .iter()
    .position(|h| h.key == [2, offset] && h.output.len() == 1)
    .ok_or("fixture has no target byte")?;
  let mut bad = package.hints.clone();
  bad[byte].output[0] ^= 1;
  rejected(
    program,
    "corrupted serialization",
    package.address.clone(),
    &bad,
    "hash of the supplied bytes",
  )?;

  let mut bad = package.hints.clone();
  let mut digest = package.address.clone();
  digest[0] ^= 1;
  bad[info].key[1..].copy_from_slice(&digest);
  rejected(
    program,
    "wrong Blake3 address",
    digest,
    &bad,
    "hash of the supplied bytes",
  )?;

  let mut bad = package.hints.clone();
  bad.remove(byte);
  rejected(
    program,
    "missing byte hint",
    package.address.clone(),
    &bad,
    "missing hint",
  )?;
  if !package.invalid_address.is_empty() {
    rejected(
      program,
      "correctly hashed invalid proof",
      package.invalid_address.clone(),
      &package.hints,
      "inferred type is not def-eq",
    )?;
  }
  Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let path = args.get(1).ok_or(
        "usage: ixvm PACKAGE.json [all|primitives|serde|constant|transitive|negative|bench [SAMPLES]|record OUTPUT.json]",
    )?;
  let mode = args.get(2).map(String::as_str).unwrap_or("all");
  let package: Package = serde_json::from_slice(&std::fs::read(path)?)?;
  let program =
    package.program.clone().check_field::<multi_stark::types::Val>()?;
  if mode == "validate" {
    let fixture: serde_json::Value = serde_json::from_slice(&std::fs::read(
      args.get(3).ok_or("validate requires FIXTURE.json")?,
    )?)?;
    let hints = ixvm_hints::prepare(&program, &package.hints)?;
    let mut cases = vec![];
    for name in [
      "verify_transitive",
      "verify_constant",
      "verify_serde",
      "check_primitives",
      "check_port_cases",
    ] {
      let input = if name.starts_with("check_") {
        vec![]
      } else {
        package.address.clone()
      };
      let result = hints
        .execute(&format!("IxVM::{name}"), program.field().decode(&input)?);
      cases.push(serde_json::json!({"entry": name, "accepted": result.is_ok(), "error": result.err().map(|e| e.to_string())}));
    }
    let mut serde_failures = vec![];
    for row in fixture["constants"].as_array().unwrap() {
      let input: Vec<u64> = serde_json::from_value(row["address"].clone())?;
      let input = program.field().decode(&input)?;
      if let Err(error) = hints.execute("IxVM::verify_serde", input) {
        serde_failures.push(
                    serde_json::json!({"address": row["address"], "error": error.to_string()}),
                );
      }
    }
    let accepted = cases.iter().all(|case| case["accepted"] == true)
      && serde_failures.is_empty();
    println!(
      "{}",
      serde_json::json!({"cases": cases, "serde_cases": fixture["constants"].as_array().unwrap().len(), "serde_failures": serde_failures})
    );
    if !accepted {
      return Err("IxVM validation failed; see the case report".into());
    }
    return Ok(());
  }
  if mode == "record" {
    let result = ixvm_hints::prepare(&program, &package.hints)?.execute(
      "IxVM::verify_transitive",
      program.field().decode(&package.address)?,
    )?;
    let mut queries: Vec<_> = result.queries.iter().collect();
    queries.sort_by_key(|(key, _)| *key);
    let output = args.get(3).ok_or("record requires an output path")?;
    let file = std::io::BufWriter::new(std::fs::File::create(output)?);
    serde_json::to_writer(
      file,
      &serde_json::json!({
          "output": result.output, "queries": queries,
          "memory": result.memory, "instructions": result.instructions,
      }),
    )?;
    return Ok(());
  }
  if mode == "bench" {
    return benchmark(
      &program,
      &package,
      args.get(3).map(|s| s.parse()).transpose()?.unwrap_or(20),
    );
  }
  let entries = [
    ("primitives", "IxVM::check_primitives"),
    ("serde", "IxVM::verify_serde"),
    ("constant", "IxVM::verify_constant"),
    ("transitive", "IxVM::verify_transitive"),
  ];
  if mode != "all"
    && mode != "negative"
    && !entries.iter().any(|(m, _)| *m == mode)
  {
    return Err(format!("unknown mode: {mode}").into());
  }
  for (selected, entry) in entries {
    if mode == "all" || mode == selected {
      run(
        &program,
        entry,
        if selected == "primitives" { vec![] } else { package.address.clone() },
        &package.hints,
      )?;
    }
  }
  if mode == "all" || mode == "negative" {
    negatives(&program, &package)?;
  }
  Ok(())
}
