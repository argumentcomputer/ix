//! Inspect and convert compiler artifacts.
//!
//! - `aiur-artifact convert IN.json OUT.aiur [--name N] [--compiler C]
//!   [--source-hex HEX] [--key K]`: validate a JSON package
//!   (`{"program": ..., "trace": ...}`) and write it as a binary artifact.
//! - `aiur-artifact json IN.aiur OUT.json`: export the diagnostic JSON form.
//! - `aiur-artifact info IN.aiur`: print the header, metadata, section sizes
//!   and digests.
//! - `aiur-artifact compare A B`: report the first component in which two
//!   artifacts (binary, or JSON when the name ends in `.json`) differ; exits
//!   with status 1 when they do. Metadata is not compared.
use aiur::Program;
use aiur::artifact::{self, Metadata, Package};
use aiur::trace::{TraceArtifact, TracePlan};
use std::path::Path;
use std::process::ExitCode;

const USAGE: &str = "usage:
  aiur-artifact convert IN.json OUT.aiur [--name N] [--compiler C] [--source-hex HEX] [--key K]
  aiur-artifact json IN.aiur OUT.json
  aiur-artifact info IN.aiur
  aiur-artifact compare A B";

const GOLDILOCKS: u64 = 0xffff_ffff_0000_0001;

fn main() -> ExitCode {
  let args: Vec<String> = std::env::args().skip(1).collect();
  match run(&args) {
    Ok(code) => code,
    Err(e) => {
      eprintln!("aiur-artifact: {e}");
      ExitCode::from(2)
    },
  }
}

fn run(args: &[String]) -> Result<ExitCode, String> {
  match args {
    [cmd, input, output, options @ ..] if cmd == "convert" => {
      convert(Path::new(input), Path::new(output), options)?;
      Ok(ExitCode::SUCCESS)
    },
    [cmd, input, output] if cmd == "json" => {
      let package = artifact::read(Path::new(input))?;
      let json = artifact::to_json(&package.program, &package.trace)?;
      std::fs::write(output, json)
        .map_err(|e| format!("cannot write {output}: {e}"))?;
      Ok(ExitCode::SUCCESS)
    },
    [cmd, input] if cmd == "info" => {
      info(Path::new(input))?;
      Ok(ExitCode::SUCCESS)
    },
    [cmd, a, b] if cmd == "compare" => {
      let (a, b) = (load(Path::new(a))?, load(Path::new(b))?);
      match aiur::artifact::first_difference(&a, &b) {
        None => {
          println!("identical");
          Ok(ExitCode::SUCCESS)
        },
        Some(difference) => {
          println!("differ: {difference}");
          Ok(ExitCode::FAILURE)
        },
      }
    },
    _ => Err(USAGE.into()),
  }
}

fn convert(
  input: &Path,
  output: &Path,
  options: &[String],
) -> Result<(), String> {
  let mut metadata = Metadata::default();
  let mut options = options.iter();
  while let Some(flag) = options.next() {
    let value =
      options.next().ok_or_else(|| format!("{flag} needs a value"))?.clone();
    match flag.as_str() {
      "--name" => metadata.name = value,
      "--compiler" => metadata.compiler = value,
      "--key" => metadata.key = value,
      "--source-hex" => metadata.source = parse_hex(&value)?,
      _ => return Err(format!("unknown option {flag}\n{USAGE}")),
    }
  }
  let bytes = std::fs::read(input)
    .map_err(|e| format!("cannot read {}: {e}", input.display()))?;
  let (program, trace) = artifact::from_json(&bytes)?;
  validate(&program, &trace)?;
  artifact::write_atomic(output, &Package { program, trace, metadata })
}

fn validate(program: &Program, trace: &TraceArtifact) -> Result<(), String> {
  if program.modulus == GOLDILOCKS {
    let checked = program.clone().check_field::<multi_stark::types::Val>()?;
    TracePlan::new(&checked, trace.clone())?;
  } else {
    let checked = program.clone().check()?;
    TracePlan::new(&checked, trace.clone())?;
  }
  Ok(())
}

fn parse_hex(text: &str) -> Result<[u8; 32], String> {
  let error = || format!("--source-hex needs 64 hex digits, got {text:?}");
  if text.len() != 64 || !text.is_ascii() {
    return Err(error());
  }
  let mut out = [0u8; 32];
  for (byte, pair) in out.iter_mut().zip(text.as_bytes().chunks(2)) {
    let pair = std::str::from_utf8(pair).map_err(|_| error())?;
    *byte = u8::from_str_radix(pair, 16).map_err(|_| error())?;
  }
  Ok(out)
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn info(path: &Path) -> Result<(), String> {
  let bytes = std::fs::read(path)
    .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
  let package = artifact::read(path)?;
  let sections = artifact::sections(&bytes)?;
  let digest = artifact::content_digest(&package.program, &package.trace)?;
  let m = &package.metadata;
  println!("magic     {:?}", String::from_utf8_lossy(&artifact::MAGIC));
  println!("version   {}", artifact::VERSION);
  println!("modulus   {}", package.program.modulus);
  println!("name      {}", m.name);
  println!("compiler  {}", m.compiler);
  println!("source    {}", hex(&m.source));
  println!("key       {}", m.key);
  for (tag, len) in sections {
    let name = match tag {
      artifact::SECTION_METADATA => "metadata",
      artifact::SECTION_BYTECODE => "bytecode",
      artifact::SECTION_TRACE => "trace",
      _ => "groups",
    };
    println!("section   {tag} {name}: {len} bytes");
  }
  println!(
    "contents  {} functions, {} chips, {} groups",
    package.program.functions.len(),
    package.trace.chips.len(),
    package.trace.groups.len()
  );
  println!("content   {}", hex(&digest));
  println!("file      {}", hex(&bytes[bytes.len() - 32..]));
  Ok(())
}

fn load(path: &Path) -> Result<(Program, TraceArtifact), String> {
  if path.extension().is_some_and(|e| e == "json") {
    let bytes = std::fs::read(path)
      .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    artifact::from_json(&bytes)
  } else {
    let package = artifact::read(path)?;
    Ok((package.program, package.trace))
  }
}
