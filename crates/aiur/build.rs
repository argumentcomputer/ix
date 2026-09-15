//! CUDA build isolation.
//!
//! This build script is deliberately a no-op unless Cargo enables the
//! `cuda` feature. Normal CPU builds therefore need neither nvcc nor CUDA
//! headers/libraries.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-changed=cuda/blake3_trace.cu");
  println!("cargo:rerun-if-env-changed=NVCC");
  println!("cargo:rerun-if-env-changed=CUDA_HOME");
  println!("cargo:rerun-if-env-changed=CUDA_PATH");
  println!("cargo:rerun-if-env-changed=MULTI_STARK_CUDA_ARCHS");

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

  let nvcc = nvcc_path();
  let out_dir =
    PathBuf::from(env::var_os("OUT_DIR").expect("Cargo did not set OUT_DIR"));
  let library = out_dir.join("libaiur_trace_cuda.a");
  let architectures = cuda_architectures(&nvcc);

  let mut command = Command::new(&nvcc);
  command
    .arg("--lib")
    .arg("--std=c++17")
    .arg("--cudart=static")
    .arg("--default-stream=per-thread")
    .arg("-O3")
    .arg("-lineinfo")
    .arg("--compiler-options=-fPIC")
    .arg("-o")
    .arg(&library)
    .arg("cuda/blake3_trace.cu");

  for architecture in &architectures {
    command.arg(format!(
      "-gencode=arch=compute_{architecture},code=sm_{architecture}"
    ));
  }
  // Emit native cubins only. A toolkit can produce PTX newer than the
  // installed driver understands even when both support the GPU's native
  // ISA (for example nvcc 13.3 with a CUDA-13.2-capable production
  // driver). In that case the runtime may select the incompatible PTX and
  // reject an otherwise usable exact-architecture cubin with error 222.

  let status = command.status().unwrap_or_else(|error| {
    panic!(
      "failed to execute {:?}: {error}; install the CUDA toolkit or set NVCC",
      nvcc
    )
  });
  assert!(status.success(), "nvcc failed with status {status}");

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

  for directory in cuda_library_directories(&nvcc) {
    if directory.is_dir() {
      println!("cargo:rustc-link-search=native={}", directory.display());
    }
  }
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

fn cuda_architectures(nvcc: &std::ffi::OsStr) -> Vec<String> {
  let supported = supported_architectures(nvcc);
  let configured = env::var("MULTI_STARK_CUDA_ARCHS").ok().map_or_else(
    || {
      let preferred = ["80", "86", "89", "90", "100", "120"];
      let selected = preferred
        .into_iter()
        .filter(|architecture| {
          supported.iter().any(|item| item == architecture)
        })
        .collect::<Vec<_>>();
      let defaults = if selected.is_empty() {
        detect_nvidia_architectures().unwrap_or_else(|| "80".to_owned())
      } else {
        selected.join(",")
      };
      (defaults, false)
    },
    |value| (value, true),
  );
  let (configured, explicitly_configured) = configured;
  let architectures: Vec<_> = configured
        .split(',')
        .map(str::trim)
        .filter(|architecture| !architecture.is_empty())
        .map(|architecture| {
            assert!(
                (2..=3).contains(&architecture.len())
                    && architecture.chars().all(|character| character.is_ascii_digit()),
                "invalid CUDA architecture {architecture:?}; expected comma-separated numbers such as 80,90"
            );
            assert!(
                !explicitly_configured
                    || supported.is_empty()
                    || supported.iter().any(|item| item == architecture),
                "nvcc does not support CUDA architecture sm_{architecture}"
            );
            architecture.to_owned()
        })
        .collect();
  assert!(
    !architectures.is_empty(),
    "MULTI_STARK_CUDA_ARCHS must contain at least one architecture"
  );
  architectures
}

fn supported_architectures(nvcc: &std::ffi::OsStr) -> Vec<String> {
  let Ok(output) = Command::new(nvcc).arg("--list-gpu-code").output() else {
    return Vec::new();
  };
  if !output.status.success() {
    return Vec::new();
  }
  String::from_utf8_lossy(&output.stdout)
    .split_whitespace()
    .filter_map(|code| code.strip_prefix("sm_"))
    .filter(|code| code.chars().all(|character| character.is_ascii_digit()))
    .map(str::to_owned)
    .collect()
}

/// Detect the architecture of the installed GPU when building on the target
/// machine. This avoids requiring users to translate `nvidia-smi`'s `12.0`
/// compute capability into nvcc's `sm_120` spelling. Cross builds and hosts
/// without a visible GPU retain the portable sm_80 default and can still set
/// `MULTI_STARK_CUDA_ARCHS` explicitly.
fn detect_nvidia_architectures() -> Option<String> {
  let output = Command::new("nvidia-smi")
    .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
    .output()
    .ok()?;
  if !output.status.success() {
    return None;
  }
  let capabilities = String::from_utf8(output.stdout).ok()?;
  let mut architectures = capabilities
    .lines()
    .map(|capability| {
      capability
        .chars()
        .filter(|character| character.is_ascii_digit())
        .collect::<String>()
    })
    .filter(|architecture| !architecture.is_empty())
    .collect::<Vec<_>>();
  architectures.sort_unstable();
  architectures.dedup();
  (!architectures.is_empty()).then(|| architectures.join(","))
}

fn cuda_library_directories(nvcc: &std::ffi::OsStr) -> Vec<PathBuf> {
  let root = env::var_os("CUDA_HOME")
    .or_else(|| env::var_os("CUDA_PATH"))
    .map(PathBuf::from)
    .or_else(|| {
      let nvcc = Path::new(nvcc);
      nvcc
        .is_absolute()
        .then(|| nvcc.parent()?.parent().map(Path::to_path_buf))
        .flatten()
    })
    .unwrap_or_else(|| PathBuf::from("/usr/local/cuda"));
  vec![root.join("lib64"), root.join("targets/x86_64-linux/lib")]
}
