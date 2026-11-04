//! Committed sources and build-script support for compiled trace bundles.
//!
//! [`sources`] renders a bundle as files to commit in one directory: a CUDA
//! unit per compiled circuit and `bundle.rs`, the Rust binding. A bundle
//! crate depends on `aiur` with `cuda` and on `multi-stark` (for its CUDA
//! field header), calls [`build`] on that directory from `build.rs`, and
//! includes `bundle.rs`, which defines
//! `pub static BUNDLE: aiur::trace::stark::compiled::Bundle`.
//!
//! Objects are cached in `OUT_DIR` under a key covering the nvcc version,
//! its path and flags, the field header and the unit source, as the legacy
//! CUDA build does.
use crate::{
  Described,
  cuda::{CompiledCircuit, Selection, emit},
};
use std::{
  env,
  fmt::Write as _,
  path::{Path, PathBuf},
  process::Command,
};

/// The file name of a bundle's Rust binding.
pub const BINDING: &str = "bundle.rs";

/// The source files of the bundle `tag` for `described`, as (file name,
/// contents) pairs: every supported circuit's unit and the binding. Every
/// file starts with `preamble`, which must consist of `//` comment lines,
/// followed by the population fingerprint.
pub fn sources(
  described: &Described,
  tag: &str,
  preamble: &str,
) -> Result<Vec<(String, String)>, String> {
  if preamble.lines().any(|line| !line.starts_with("//")) {
    return Err("the preamble must consist of `//` comment lines".into());
  }
  let emitted = emit(described, &Selection::All, tag)?;
  let header = format!(
    "{preamble}// Population fingerprint {} (compiled ABI {}).\n",
    described.fingerprint,
    aiur::trace::describe::COMPILED_ABI_VERSION
  );
  let mut files = Vec::with_capacity(emitted.circuits.len() + 1);
  for c in &emitted.circuits {
    files.push((c.file.clone(), format!("{header}{}", c.source)));
  }
  let binding = binding(
    tag,
    &described.program,
    &described.fingerprint,
    &emitted.circuits,
    &emitted.skipped,
  );
  files.push((BINDING.to_owned(), format!("{header}{binding}")));
  Ok(files)
}

/// What a bundle crate compiles.
pub struct Config<'a> {
  /// The bundle's tag, as given to [`sources`].
  pub tag: &'a str,
  /// The directory [`sources`] was written to.
  pub directory: &'a Path,
}

fn rerun_env(name: &str) -> Option<String> {
  println!("cargo:rerun-if-env-changed={name}");
  env::var(name).ok()
}

/// Compiles and links the bundle's units, and writes their `ptxas -v`
/// report to `$OUT_DIR/<tag>.ptxas`, which the binding includes.
pub fn build(config: &Config<'_>) {
  if let Err(error) = try_build(config) {
    panic!("compiled trace bundle {}: {error}", config.tag);
  }
}

/// A unit of a bundle directory: its file name and source.
struct Unit {
  file: String,
  source: String,
}

fn try_build(config: &Config<'_>) -> Result<(), String> {
  let out =
    PathBuf::from(env::var_os("OUT_DIR").ok_or("Cargo did not set OUT_DIR")?);
  let directory = config.directory;
  println!("cargo:rerun-if-changed={}", directory.display());
  let mut units = vec![];
  for entry in std::fs::read_dir(directory)
    .map_err(|e| format!("{}: {e}", directory.display()))?
  {
    let path = entry.map_err(|e| e.to_string())?.path();
    if path.extension().is_some_and(|e| e == "cu") {
      println!("cargo:rerun-if-changed={}", path.display());
      let file = path
        .file_name()
        .and_then(|f| f.to_str())
        .ok_or_else(|| format!("{}: not a UTF-8 name", path.display()))?
        .to_owned();
      let source = std::fs::read_to_string(&path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
      units.push(Unit { file, source });
    }
  }
  units.sort_by(|a, b| a.file.cmp(&b.file));
  let library = format!("aiur_tracegen_{}", config.tag);
  let ptxas = compile(&out, &units, &library)?;
  std::fs::write(out.join(format!("{}.ptxas", config.tag)), &ptxas)
    .map_err(|e| e.to_string())?;
  Ok(())
}

fn binding(
  tag: &str,
  program: &aiur::Program,
  fingerprint: &str,
  circuits: &[CompiledCircuit],
  skipped: &[(String, String)],
) -> String {
  let mut s = String::new();
  s.push_str("unsafe extern \"C\" {\n");
  for c in circuits {
    let _ = writeln!(
      s,
      "fn {}(device: i32, circuit: *const ::core::ffi::c_void, callees: *const u32, \
       callee_count: u32, output: *mut u64, base: u64, first: u64, rows: u64, height: u64, \
       error: *mut ::core::ffi::c_void, status: *mut ::core::ffi::c_void) -> i32;",
      c.symbol
    );
  }
  s.push_str("}\n");
  let _ = writeln!(
    s,
    "/// The compiled trace bundle; register it with \
     `aiur::trace::stark::compiled::register`.\n\
     pub static BUNDLE: ::aiur::trace::stark::compiled::Bundle = \
     ::aiur::trace::stark::compiled::Bundle {{\n\
     tag: {tag:?},\nabi: {abi},\nprogram: {program:?},\nfingerprint: {fingerprint:?},\ncircuits: &[",
    abi = aiur::trace::describe::COMPILED_ABI_VERSION,
    program = aiur::trace::describe::program_identity(program),
  );
  for c in circuits {
    let _ = writeln!(
      s,
      "::aiur::trace::stark::compiled::CompiledCircuit {{ name: {:?}, members: &{:?}, \
       callees: &{:?}, launch: {} }},",
      c.name, c.members, c.callees, c.symbol
    );
  }
  s.push_str("],\nskipped: &[");
  for (name, reason) in skipped {
    let _ = writeln!(s, "({name:?}, {reason:?}),");
  }
  let _ = writeln!(
    s,
    "],\nptxas: include_str!(concat!(env!(\"OUT_DIR\"), \"/{tag}.ptxas\")),\n}};"
  );
  s
}

fn nvcc_path() -> std::ffi::OsString {
  if let Some(nvcc) = env::var_os("NVCC") {
    return nvcc;
  }
  if let Some(root) =
    env::var_os("CUDA_HOME").or_else(|| env::var_os("CUDA_PATH"))
  {
    let candidate = PathBuf::from(root).join("bin/nvcc");
    if candidate.is_file() {
      return candidate.into_os_string();
    }
  }
  "nvcc".into()
}

/// `MULTI_STARK_CUDA_ARCHS` when set, otherwise the visible GPUs'
/// architectures, otherwise sm_80, as `aiur`'s own CUDA build chooses.
fn architectures() -> Result<Vec<String>, String> {
  let configured = rerun_env("MULTI_STARK_CUDA_ARCHS").or_else(|| {
    let output = Command::new("nvidia-smi")
      .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
      .output()
      .ok()?;
    let text = String::from_utf8(output.stdout).ok()?;
    let mut found: Vec<String> = text
      .lines()
      .map(|line| line.chars().filter(char::is_ascii_digit).collect())
      .filter(|arch: &String| !arch.is_empty())
      .collect();
    found.sort();
    found.dedup();
    (!found.is_empty()).then(|| found.join(","))
  });
  let architectures: Vec<String> = configured
    .unwrap_or_else(|| "80".into())
    .split(',')
    .map(str::trim)
    .filter(|a| !a.is_empty())
    .map(str::to_owned)
    .collect();
  if architectures.is_empty()
    || !architectures.iter().all(|a| a.chars().all(|c| c.is_ascii_digit()))
  {
    return Err("invalid MULTI_STARK_CUDA_ARCHS".into());
  }
  Ok(architectures)
}

/// Compiles every unit (cached), archives them into `lib{library}.a` and
/// links it. Returns the `ptxas -v` report of every unit.
fn compile(
  out: &Path,
  units: &[Unit],
  library: &str,
) -> Result<String, String> {
  for name in ["NVCC", "CUDA_HOME", "CUDA_PATH"] {
    rerun_env(name);
  }
  let nvcc = nvcc_path();
  let include =
    PathBuf::from(env::var_os("DEP_MULTI_STARK_CUDA_INCLUDE").ok_or(
      "the bundle crate must depend on multi-stark with its cuda feature",
    )?);
  let header = include.join("goldilocks.cuh");
  println!("cargo:rerun-if-changed={}", header.display());
  let mut flags: Vec<String> = [
    "--std=c++17",
    "--cudart=static",
    "--default-stream=per-thread",
    "-O3",
    "-lineinfo",
    "--compiler-options=-fPIC",
    "--ptxas-options=-v",
    "--diag-suppress=177",
  ]
  .map(str::to_owned)
  .to_vec();
  for architecture in architectures()? {
    flags.push(format!(
      "-gencode=arch=compute_{architecture},code=sm_{architecture}"
    ));
  }
  let version = Command::new(&nvcc)
    .arg("--version")
    .output()
    .map_err(|e| format!("cannot run nvcc: {e}"))?;
  if !version.status.success() {
    return Err("nvcc --version failed".into());
  }
  let mut key = blake3::Hasher::new();
  key.update(&version.stdout);
  key.update(nvcc.as_encoded_bytes());
  for flag in &flags {
    key.update(flag.as_bytes());
    key.update(&[0]);
  }
  key.update(
    &std::fs::read(&header)
      .map_err(|e| format!("{}: {e}", header.display()))?,
  );
  let jobs: Vec<_> = units
    .iter()
    .map(|u| {
      let mut hash = key.clone();
      hash.update(u.source.as_bytes());
      let name = u.file.strip_suffix(".cu").unwrap_or(&u.file);
      let stem =
        out.join(format!("{name}-{}", &hash.finalize().to_hex()[..32]));
      (u, stem)
    })
    .collect();
  let workers =
    std::thread::available_parallelism().map_or(1, std::num::NonZero::get);
  let next = std::sync::atomic::AtomicUsize::new(0);
  let results: Vec<Result<(), String>> = std::thread::scope(|scope| {
    let handles: Vec<_> = (0..workers.min(jobs.len()))
      .map(|_| {
        scope.spawn(|| {
          let mut results = vec![];
          loop {
            let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let Some((u, stem)) = jobs.get(i) else { break };
            results.push(unit(&nvcc, &flags, &include, u, stem));
          }
          results
        })
      })
      .collect();
    handles
      .into_iter()
      .flat_map(|h| h.join().expect("nvcc worker panicked"))
      .collect()
  });
  results.into_iter().collect::<Result<Vec<_>, _>>()?;
  let mut report = String::new();
  for (u, stem) in &jobs {
    let log =
      std::fs::read_to_string(stem.with_extension("ptxas")).unwrap_or_default();
    let _ = writeln!(report, "== {}", u.file);
    for line in log.lines().filter(|l| {
      (l.contains("ptxas info") && !l.contains("Compiling entry"))
        || l.contains("bytes stack frame")
    }) {
      let _ = writeln!(report, "{}", line.trim());
    }
  }
  let archive = out.join(format!("lib{library}.a"));
  let _ = std::fs::remove_file(&archive);
  if !jobs.is_empty() {
    let status = Command::new(&nvcc)
      .arg("--lib")
      .arg("-o")
      .arg(&archive)
      .args(jobs.iter().map(|(_, stem)| stem.with_extension("o")))
      .status()
      .map_err(|e| format!("cannot run nvcc --lib: {e}"))?;
    if !status.success() {
      return Err(format!("nvcc archive failed: {status}"));
    }
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static={library}");
  }
  Ok(report)
}

fn unit(
  nvcc: &std::ffi::OsStr,
  flags: &[String],
  include: &Path,
  u: &Unit,
  stem: &Path,
) -> Result<(), String> {
  let object = stem.with_extension("o");
  if object.is_file() {
    return Ok(());
  }
  let source = stem.with_extension("cu");
  std::fs::write(&source, &u.source).map_err(|e| e.to_string())?;
  let output = Command::new(nvcc)
    .args(flags)
    .arg("-I")
    .arg(include)
    .arg("-c")
    .arg(&source)
    .arg("-o")
    .arg(&object)
    .output()
    .map_err(|e| format!("cannot run nvcc: {e}"))?;
  if !output.status.success() {
    let _ = std::fs::remove_file(&object);
    return Err(format!(
      "nvcc failed for {} ({}): {}",
      u.file,
      source.display(),
      String::from_utf8_lossy(&output.stderr)
    ));
  }
  std::fs::write(stem.with_extension("ptxas"), &output.stderr)
    .map_err(|e| e.to_string())
}
