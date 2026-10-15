//! KZG CUDA kernels for the compression crate.
//!
//! Without the `cuda` feature this script does nothing, so CPU builds need
//! neither nvcc nor the CUDA headers and libraries. With it, the BLS12-381
//! sppark instantiation and the KZG kernels are compiled into their own
//! archive, isolated from multi-stark's Goldilocks instantiation by the
//! symbol renames in `cuda/kzg_sppark.cuh`.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

const SOURCES: &[&str] = &[
  "cuda/kzg.cu",
  "cuda/kzg_quotient.cuh",
  "cuda/kzg_srs.cuh",
  "cuda/kzg_lookup.cuh",
  "cuda/kzg_passes.cuh",
  "cuda/kzg_transfer.cuh",
  "cuda/kzg_profile.cuh",
  "cuda/kzg_runtime.cpp",
  "cuda/kzg_sppark.cuh",
];

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  for source in SOURCES {
    println!("cargo:rerun-if-changed={source}");
  }
  for variable in [
    "NVCC",
    "CUDA_HOME",
    "CUDA_PATH",
    "NVCC_CCBIN",
    "NVCC_PREPEND_FLAGS",
    "NVCC_APPEND_FLAGS",
    "IX_KZG_CUDA_ARCHS",
    "MULTI_STARK_CUDA_ARCHS",
  ] {
    println!("cargo:rerun-if-env-changed={variable}");
  }
  if env::var_os("CARGO_FEATURE_CUDA").is_some() {
    build_kzg_cuda();
  }
}

fn build_kzg_cuda() {
  assert_eq!(
    env::var("CARGO_CFG_TARGET_OS").as_deref(),
    Ok("linux"),
    "the KZG CUDA backend supports Linux targets only"
  );
  assert_eq!(
    env::var("CARGO_CFG_TARGET_ARCH").as_deref(),
    Ok("x86_64"),
    "the KZG CUDA backend supports x86_64 targets only"
  );
  let nvcc = nvcc_path();
  let architectures = cuda_architectures(&nvcc);
  let out = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo sets OUT_DIR"));
  let architecture_header = out.join("kzg_architectures.h");
  std::fs::write(
    &architecture_header,
    format!(
      "#define IX_KZG_CUDA_ARCHITECTURES {{{}}}\n",
      architectures.join(",")
    ),
  )
  .expect("write KZG CUDA architecture list");
  println!(
    "cargo:rustc-env=IX_KZG_CUDA_COMPILED_ARCHS={}",
    architectures.join(",")
  );
  let root = PathBuf::from(
    env::var_os("DEP_SPPARK_ROOT")
      .expect("sppark's build script exports DEP_SPPARK_ROOT"),
  );
  let blst = PathBuf::from(
    env::var_os("DEP_BLST_C_SRC")
      .expect("blst's build script exports DEP_BLST_C_SRC"),
  );
  for directory in ["ec", "ff", "msm", "ntt", "polynomial", "util"] {
    println!("cargo:rerun-if-changed={}", root.join(directory).display());
  }
  let mut objects = Vec::new();
  for (source, name) in
    [("cuda/kzg.cu", "kzg.o"), ("cuda/kzg_runtime.cpp", "kzg_runtime.o")]
  {
    let object = out.join(name);
    let mut command = cuda_compile_command(&nvcc, &architectures);
    command.args([
      "-c",
      "-DFEATURE_BLS12_381",
      "-D__BLST_PORTABLE__",
      "-DMAX_LG_DOMAIN_SIZE=32",
      "-include",
      "cuda/kzg_sppark.cuh",
    ]);
    command.arg(format!("-I{}", root.display()));
    command.arg(format!("-I{}", root.join("util").display()));
    command.arg(format!("-I{}", blst.display()));
    command.arg("-include").arg(&architecture_header);
    let status = command
      .arg(source)
      .arg("-o")
      .arg(&object)
      .status()
      .unwrap_or_else(|error| {
        panic!("failed to execute {nvcc:?}: {error}; install the CUDA toolkit or set NVCC")
      });
    assert!(status.success(), "KZG CUDA compilation failed: {source}");
    objects.push(object);
  }
  let archive = out.join("libix_kzg_cuda.a");
  let status = Command::new(&nvcc)
    .arg("--lib")
    .args(&objects)
    .arg("-o")
    .arg(&archive)
    .status()
    .expect("nvcc archive");
  assert!(status.success(), "KZG CUDA archive failed");
  println!("cargo:rustc-link-search=native={}", out.display());
  println!("cargo:rustc-link-lib=static=ix_kzg_cuda");
  link_cuda_runtime(&nvcc);
}

fn cuda_compile_command(
  nvcc: &std::ffi::OsStr,
  architectures: &[String],
) -> Command {
  let mut command = Command::new(nvcc);
  command.args([
    "--std=c++17",
    "--cudart=static",
    "--default-stream=per-thread",
    "-O3",
    "-lineinfo",
    "--compiler-options=-fPIC",
  ]);
  // Native cubins avoid PTX versions newer than the installed driver's JIT,
  // even when both the toolkit and driver support the GPU's native ISA.
  for architecture in architectures {
    command.arg(format!(
      "-gencode=arch=compute_{architecture},code=sm_{architecture}"
    ));
  }
  command
}

fn link_cuda_runtime(nvcc: &std::ffi::OsStr) {
  // CUDA is bundled into Rust staticlibs. Dynamic host dependencies must
  // also be supplied by foreign final linkers; Lake isolates a static
  // libstdc++ from the same nvcc host compiler in its native archive.
  println!("cargo:rustc-link-lib=static=cudart_static");
  for lib in ["dl", "rt", "pthread", "stdc++"] {
    println!("cargo:rustc-link-lib=dylib={lib}");
  }
  for directory in cuda_library_directories(nvcc) {
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

/// `IX_KZG_CUDA_ARCHS` selects the SM architectures; `MULTI_STARK_CUDA_ARCHS`
/// is honored as a fallback so one variable configures both CUDA backends of a
/// Lake build. Without either, nvcc's supported portable set is used.
fn cuda_architectures(nvcc: &std::ffi::OsStr) -> Vec<String> {
  let supported = supported_architectures(nvcc);
  let configured = env::var("IX_KZG_CUDA_ARCHS")
    .or_else(|_| env::var("MULTI_STARK_CUDA_ARCHS"))
    .ok();
  let (configured, explicitly_configured) = match configured {
    Some(value) => (value, true),
    None => {
      let preferred = ["70", "75", "80", "86", "89", "90", "100", "110", "120"];
      let selected: Vec<_> = preferred
        .into_iter()
        .filter(|architecture| {
          supported.iter().any(|item| item == architecture)
        })
        .collect();
      let defaults = if selected.is_empty() {
        detect_nvidia_architectures().unwrap_or_else(|| "80".to_owned())
      } else {
        selected.join(",")
      };
      (defaults, false)
    },
  };
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
    "IX_KZG_CUDA_ARCHS must contain at least one architecture"
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

fn detect_nvidia_architectures() -> Option<String> {
  let output = Command::new("nvidia-smi")
    .args(["--query-gpu=compute_cap", "--format=csv,noheader"])
    .output()
    .ok()?;
  if !output.status.success() {
    return None;
  }
  let capabilities = String::from_utf8(output.stdout).ok()?;
  let mut architectures: Vec<String> = capabilities
    .lines()
    .map(|capability| {
      capability
        .chars()
        .filter(|character| character.is_ascii_digit())
        .collect()
    })
    .filter(|architecture: &String| !architecture.is_empty())
    .collect();
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
