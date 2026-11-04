//! Build-script support for compiled trace bundles.
//!
//! A bundle crate depends on `aiur` with `cuda` and on `multi-stark` (for
//! its CUDA field header), and calls [`build`] from `build.rs`. It then
//! includes `$OUT_DIR/bundle.rs`, which defines
//! `pub static BUNDLE: aiur::trace::stark::compiled::Bundle`.
//!
//! The artifact path comes from an environment variable; Cargo reruns the
//! build when the variable, the file or the selection change. Objects are
//! cached in `OUT_DIR` under a key covering the nvcc version, its path and
//! flags, the field header and the unit source, as the legacy CUDA build does.
use crate::cuda::{Emitted, Selection, emit};
use std::{
  env,
  fmt::Write as _,
  path::{Path, PathBuf},
  process::Command,
};

/// What a bundle crate compiles.
pub struct Config<'a> {
  /// Distinguishes this bundle's symbols from others in the same binary.
  pub tag: &'a str,
  /// Names the exported execution package.
  pub artifact_variable: &'a str,
  /// Optionally selects circuits: unset or `all` compiles every supported
  /// circuit, otherwise a JSON array of circuit names.
  pub selection_variable: &'a str,
}

fn rerun_env(name: &str) -> Option<String> {
  println!("cargo:rerun-if-env-changed={name}");
  env::var(name).ok()
}

/// Generates, compiles and links the bundle; writes `$OUT_DIR/bundle.rs`.
pub fn build(config: &Config<'_>) {
  if let Err(error) = try_build(config) {
    panic!("compiled trace bundle {}: {error}", config.tag);
  }
}

fn try_build(config: &Config<'_>) -> Result<(), String> {
  let out =
    PathBuf::from(env::var_os("OUT_DIR").ok_or("Cargo did not set OUT_DIR")?);
  let artifact = rerun_env(config.artifact_variable).ok_or_else(|| {
    format!("{} must name the exported artifact", config.artifact_variable)
  })?;
  println!("cargo:rerun-if-changed={artifact}");
  let selection = match rerun_env(config.selection_variable).as_deref() {
    None | Some("" | "all") => Selection::All,
    Some(names) => {
      Selection::Named(serde_json::from_str(names).map_err(|e| {
        format!(
          "{} must be `all` or a JSON array: {e}",
          config.selection_variable
        )
      })?)
    },
  };
  let described = crate::describe_file(Path::new(&artifact))?;
  let emitted = emit(&described, &selection, config.tag)?;
  let library = format!("aiur_tracegen_{}", config.tag);
  let ptxas = compile(&out, &emitted, &library)?;
  let rust = binding(
    config.tag,
    &described.program,
    &described.fingerprint,
    &emitted,
    &ptxas,
  );
  std::fs::write(out.join("bundle.rs"), rust).map_err(|e| e.to_string())?;
  std::fs::write(out.join("ptxas.txt"), &ptxas).map_err(|e| e.to_string())?;
  Ok(())
}

fn binding(
  tag: &str,
  program: &aiur::Program,
  fingerprint: &str,
  emitted: &Emitted,
  ptxas: &str,
) -> String {
  let mut s = String::new();
  s.push_str("unsafe extern \"C\" {\n");
  for c in &emitted.circuits {
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
  for c in &emitted.circuits {
    let _ = writeln!(
      s,
      "::aiur::trace::stark::compiled::CompiledCircuit {{ name: {:?}, members: &{:?}, \
       callees: &{:?}, launch: {} }},",
      c.name, c.members, c.callees, c.symbol
    );
  }
  s.push_str("],\nskipped: &[");
  for (name, reason) in &emitted.skipped {
    let _ = writeln!(s, "({name:?}, {reason:?}),");
  }
  let _ = writeln!(s, "],\nptxas: {ptxas:?},\n}};");
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
  emitted: &Emitted,
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
  let jobs: Vec<_> = emitted
    .circuits
    .iter()
    .map(|c| {
      let mut hash = key.clone();
      hash.update(c.source.as_bytes());
      let stem =
        out.join(format!("{}-{}", c.symbol, &hash.finalize().to_hex()[..32]));
      (c, stem)
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
            let Some((circuit, stem)) = jobs.get(i) else { break };
            results.push(unit(&nvcc, &flags, &include, circuit, stem));
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
  for (circuit, stem) in &jobs {
    let log =
      std::fs::read_to_string(stem.with_extension("ptxas")).unwrap_or_default();
    let _ = writeln!(report, "== {} ({})", circuit.name, circuit.symbol);
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
  circuit: &crate::cuda::CompiledCircuit,
  stem: &Path,
) -> Result<(), String> {
  let object = stem.with_extension("o");
  if object.is_file() {
    return Ok(());
  }
  let source = stem.with_extension("cu");
  std::fs::write(&source, &circuit.source).map_err(|e| e.to_string())?;
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
      circuit.name,
      source.display(),
      String::from_utf8_lossy(&output.stderr)
    ));
  }
  std::fs::write(stem.with_extension("ptxas"), &output.stderr)
    .map_err(|e| e.to_string())
}
