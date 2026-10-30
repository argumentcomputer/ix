//! CUDA build isolation.
//!
//! This build script is deliberately a no-op unless Cargo enables the
//! `cuda` feature. Normal CPU builds therefore need neither nvcc nor CUDA
//! headers/libraries.

use std::env;
use std::ffi::OsString;
use std::path::PathBuf;
use std::process::Command;

/// Toolchain metadata from multi-stark's CUDA build, so the trace writers
/// target the same compiler and GPUs as the backend they link against.
fn multi_stark_cuda(key: &str) -> OsString {
  env::var_os(format!("DEP_MULTI_STARK_CUDA_{key}"))
    .unwrap_or_else(|| panic!("multi-stark's CUDA build did not report {key}"))
}

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-env-changed=NVCC_CCBIN");
  println!("cargo:rerun-if-env-changed=NVCC_PREPEND_FLAGS");
  println!("cargo:rerun-if-env-changed=NVCC_APPEND_FLAGS");

  if env::var_os("CARGO_FEATURE_CUDA").is_none() {
    return;
  }

  assert_eq!(
    env::var("CARGO_CFG_TARGET_OS").as_deref(),
    Ok("linux"),
    "the first-party CUDA backend currently supports Linux targets only"
  );
  assert_eq!(
    env::var("CARGO_CFG_TARGET_ARCH").as_deref(),
    Ok("x86_64"),
    "the first-party CUDA backend currently supports x86_64 targets only"
  );

  // Every aiur CUDA source belongs to the generated trace writers; the bare
  // `cuda` feature only enables multi-stark's device backend.
  if env::var_os("CARGO_FEATURE_CUDA_TRACE_CODEGEN").is_none() {
    return;
  }
  let nvcc = multi_stark_cuda("NVCC");
  let architectures: Vec<String> = multi_stark_cuda("ARCHS")
    .into_string()
    .expect("CUDA architectures are ASCII")
    .split(',')
    .map(str::to_owned)
    .collect();
  let out_dir =
    PathBuf::from(env::var_os("OUT_DIR").expect("Cargo did not set OUT_DIR"));
  let library = out_dir.join("libaiur_trace_cuda.a");
  let include = env::var_os("DEP_MULTI_STARK_CUDA_INCLUDE")
    .expect("cuda-trace-codegen requires multi-stark's shared CUDA field header metadata");
  let includes = vec![PathBuf::from("cuda"), PathBuf::from(&include)];
  let headers = [
    PathBuf::from("cuda/trace_runtime.cuh"),
    PathBuf::from("cuda/trace_primitives.cuh"),
    PathBuf::from(include).join("goldilocks.cuh"),
  ];
  let mut sources = vec![PathBuf::from("cuda/trace_runtime.cu")];
  {
    for manifest_path in [
      "cuda/trace-manifest.json",
      "cuda/generated/production/trace-manifest.json",
    ] {
      println!("cargo:rerun-if-changed={manifest_path}");
      let manifest: serde_json::Value = serde_json::from_slice(
        &std::fs::read(manifest_path).expect("missing trace manifest"),
      )
      .expect("invalid trace manifest");
      assert_eq!(
        manifest["abi"].as_u64(),
        Some(2),
        "unsupported trace manifest ABI"
      );
      for unit in manifest["units"].as_array().expect("manifest units") {
        let path =
          PathBuf::from(unit["source"].as_str().expect("CUDA unit source"));
        assert!(
          path
            .components()
            .all(|c| matches!(c, std::path::Component::Normal(_)))
            && path.starts_with("cuda/generated")
            && path.extension().is_some_and(|e| e == "cu"),
          "CUDA unit path must be inside cuda/generated"
        );
        let bytes = std::fs::read(&path).expect("missing generated CUDA unit");
        let digest: Vec<u8> = serde_json::from_value(unit["digest"].clone())
          .expect("CUDA unit digest");
        assert_eq!(
          blake3::hash(&bytes).as_bytes().as_slice(),
          digest,
          "generated CUDA unit differs from its manifest: {}",
          path.display()
        );
        assert!(!sources.contains(&path), "duplicate CUDA unit");
        sources.push(path);
      }
    }
  }
  let mut common = vec![
    "--std=c++17".to_owned(),
    "--cudart=static".to_owned(),
    "--default-stream=per-thread".to_owned(),
    "-O3".to_owned(),
    "-lineinfo".to_owned(),
    "--compiler-options=-fPIC".to_owned(),
    "--ptxas-options=-v".to_owned(),
  ];
  for architecture in &architectures {
    common.push(format!(
      "-gencode=arch=compute_{architecture},code=sm_{architecture}"
    ));
  }
  // Exact-architecture cubins avoid PTX newer than the installed driver.
  let version = Command::new(&nvcc)
    .arg("--version")
    .output()
    .expect("failed to query nvcc version");
  assert!(version.status.success(), "nvcc --version failed");
  let mut key = blake3::Hasher::new();
  key.update(&version.stdout);
  key.update(nvcc.as_encoded_bytes());
  for arg in &common {
    key.update(arg.as_bytes());
    key.update(&[0]);
  }
  for include in &includes {
    key.update(include.as_os_str().as_encoded_bytes());
    key.update(&[0]);
  }
  for header in &headers {
    println!("cargo:rerun-if-changed={}", header.display());
    key.update(&std::fs::read(header).expect("missing CUDA header"));
  }
  let mut objects = Vec::new();
  for source in sources {
    println!("cargo:rerun-if-changed={}", source.display());
    let mut hash = key.clone();
    hash.update(&std::fs::read(&source).expect("missing CUDA source"));
    let object = out_dir.join(format!("{}.o", hash.finalize().to_hex()));
    if !object.is_file() {
      let mut command = Command::new(&nvcc);
      command.args(&common);
      for include in &includes {
        command.arg("-I").arg(include);
      }
      command.arg("-c").arg(&source).arg("-o").arg(&object);
      let output = command.output().expect("failed to execute nvcc");
      std::io::Write::write_all(&mut std::io::stderr(), &output.stderr)
        .unwrap();
      if !output.status.success() {
        let _ = std::fs::remove_file(&object);
        panic!("nvcc failed for {}: {}", source.display(), output.status);
      }
    }
    objects.push(object);
  }
  let _ = std::fs::remove_file(&library);
  let status = Command::new(&nvcc)
    .arg("--lib")
    .arg("-o")
    .arg(&library)
    .args(&objects)
    .status()
    .expect("failed to archive CUDA objects");
  assert!(status.success(), "nvcc archive failed: {status}");

  println!("cargo:rustc-link-search=native={}", out_dir.display());
  println!("cargo:rustc-link-lib=static=aiur_trace_cuda");
  // Bundle the CUDA runtime into Rust staticlib consumers as well as normal
  // Cargo binaries. Dynamic native dependencies are not propagated through
  // a Rust staticlib to a foreign final linker (for example, Lean/Lake),
  // which otherwise leaves the CUDA registration and runtime symbols
  // unresolved. This remains entirely behind the `cuda` feature.
  println!("cargo:rustc-link-lib=static=cudart_static");
  println!("cargo:rustc-link-lib=dylib=dl");
  println!("cargo:rustc-link-lib=dylib=rt");
  println!("cargo:rustc-link-lib=dylib=pthread");
  println!("cargo:rustc-link-lib=dylib=stdc++");

  for directory in env::split_paths(&multi_stark_cuda("LIB_DIRS")) {
    if directory.is_dir() {
      println!("cargo:rustc-link-search=native={}", directory.display());
    }
  }
}
