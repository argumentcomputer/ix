//! CUDA build isolation. A no-op unless Cargo enables the `cuda` feature, so
//! CPU builds need neither nvcc nor CUDA headers. With it, compiles the GPU
//! stage-one population (`cuda/population.cu`) against multi-stark's shared
//! Goldilocks header, using multi-stark's stream and runtime conventions.

use std::env;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Command;

/// Toolchain metadata from multi-stark's CUDA build, so the population
/// kernels target the same compiler and GPUs as the backend they feed.
fn multi_stark_cuda(key: &str) -> OsString {
  env::var_os(format!("DEP_MULTI_STARK_CUDA_{key}"))
    .unwrap_or_else(|| panic!("multi-stark's CUDA build did not report {key}"))
}

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-changed=cuda/population.cu");
  println!("cargo:rerun-if-env-changed=NVCC_CCBIN");
  println!("cargo:rerun-if-env-changed=NVCC_PREPEND_FLAGS");
  println!("cargo:rerun-if-env-changed=NVCC_APPEND_FLAGS");
  if env::var_os("CARGO_FEATURE_CUDA").is_none() {
    return;
  }
  let nvcc = multi_stark_cuda("NVCC");
  let out_dir =
    PathBuf::from(env::var_os("OUT_DIR").expect("Cargo did not set OUT_DIR"));
  let include = PathBuf::from(
    env::var_os("DEP_MULTI_STARK_CUDA_INCLUDE")
      .expect("multi-stark exports its CUDA field header directory"),
  );
  println!(
    "cargo:rerun-if-changed={}",
    include.join("goldilocks.cuh").display()
  );
  let object = out_dir.join("population.o");
  let library = out_dir.join("libaiur_population.a");
  let mut compile = Command::new(&nvcc);
  compile.args([
    "--std=c++17",
    "--cudart=static",
    "--default-stream=per-thread",
    "-O3",
    "-lineinfo",
    "--compiler-options=-fPIC",
  ]);
  let architectures = multi_stark_cuda("ARCHS")
    .into_string()
    .expect("CUDA architectures are ASCII");
  for architecture in architectures.split(',') {
    compile.arg(format!(
      "-gencode=arch=compute_{architecture},code=sm_{architecture}"
    ));
  }
  compile
    .arg("-I")
    .arg(&include)
    .args(["-c", "cuda/population.cu", "-o"])
    .arg(&object);
  let status = compile.status().expect("failed to execute nvcc");
  assert!(status.success(), "nvcc failed for cuda/population.cu: {status}");
  let _ = std::fs::remove_file(&library);
  let status = Command::new(&nvcc)
    .arg("--lib")
    .arg("-o")
    .arg(&library)
    .arg(&object)
    .status()
    .expect("failed to archive CUDA objects");
  assert!(status.success(), "nvcc archive failed: {status}");
  println!("cargo:rustc-link-search=native={}", out_dir.display());
  println!("cargo:rustc-link-lib=static=aiur_population");
  // Bundle the CUDA runtime so staticlib consumers (Lean) also resolve the
  // population kernels' registration symbols.
  println!("cargo:rustc-link-lib=static=cudart_static");
  for library in ["dl", "rt", "pthread", "stdc++"] {
    println!("cargo:rustc-link-lib=dylib={library}");
  }
  for directory in env::split_paths(&multi_stark_cuda("LIB_DIRS")) {
    if directory.is_dir() {
      println!("cargo:rustc-link-search=native={}", directory.display());
    }
  }
}
