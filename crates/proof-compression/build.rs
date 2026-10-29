//! Native proving backends.
//!
//! Without the `cuda` feature the crate needs neither nvcc nor the CUDA
//! toolkit. With it, the BN254 KZG kernels and, with `plonk`, gnark's PLONK
//! kernels are linked against one sppark source into `libix_bn254_cuda.so`.
//! The library carries a private C++ runtime, unwinder and CUDA runtime and
//! exports only its C entry points, so it can join a process that links a
//! different C++ runtime (the Lean executable links LLVM's libc++).
//!
//! `IX_RUNTIME_ARTIFACTS` names every shared library an executable built from
//! this crate must ship beside itself, as a JSON array of
//! `{"source": <absolute path>, "path": <path relative to lib/>}`. ICICLE's
//! CUDA backend plugins are loaded at runtime and appear only here.

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

const SOURCES: &[&str] = &[
  "cuda/kzg.cu",
  "cuda/kzg_curve.cuh",
  "cuda/kzg_conformance.cuh",
  "cuda/kzg_quotient.cuh",
  "cuda/kzg_srs.cuh",
  "cuda/kzg_lookup.cuh",
  "cuda/kzg_passes.cuh",
  "cuda/kzg_transfer.cuh",
  "cuda/kzg_profile.cuh",
  "cuda/kzg_runtime.cpp",
  "cuda/plonk/plonk.cu",
  "cuda/plonk/ix_plonk_bn254.h",
];

const LIBRARY: &str = "libix_bn254_cuda.so";

const EXPORTS: &str = r"{
    global: ix_kzg_*; ix_plonk_bn254_*;
    local: *;
};";

/// A shared library to install at `lib/<path>` beside the executable.
struct RuntimeArtifact {
  source: PathBuf,
  path: String,
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
#[path = "build/gnark.rs"]
mod gnark;

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
    "CC",
    "IX_KZG_CUDA_ARCHS",
    "MULTI_STARK_CUDA_ARCHS",
  ] {
    println!("cargo:rerun-if-env-changed={variable}");
  }
  let mut artifacts = Vec::new();
  if env::var_os("CARGO_FEATURE_CUDA").is_some() {
    artifacts.push(RuntimeArtifact {
      source: build_bn254_cuda(),
      path: LIBRARY.to_owned(),
    });
  }
  // cgo links the PLONK entry points against the library built above.
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  artifacts.extend(gnark::build());
  println!("cargo:rustc-env=IX_RUNTIME_ARTIFACTS={}", manifest(&artifacts));
}

fn manifest(artifacts: &[RuntimeArtifact]) -> String {
  let entries: Vec<_> = artifacts
    .iter()
    .map(|artifact| {
      let source = artifact.source.to_str().unwrap_or_else(|| {
        panic!("runtime artifact path {:?} is not UTF-8", artifact.source)
      });
      format!(
        r#"{{"source":{},"path":{}}}"#,
        json_string(source),
        json_string(&artifact.path)
      )
    })
    .collect();
  format!("[{}]", entries.join(","))
}

fn json_string(value: &str) -> String {
  let mut quoted = String::with_capacity(value.len() + 2);
  quoted.push('"');
  for character in value.chars() {
    match character {
      '"' => quoted.push_str("\\\""),
      '\\' => quoted.push_str("\\\\"),
      character if character.is_control() => {
        quoted.push_str(&format!("\\u{:04x}", u32::from(character)));
      },
      character => quoted.push(character),
    }
  }
  quoted.push('"');
  quoted
}

/// Builds `libix_bn254_cuda.so` in `OUT_DIR` and links it into this crate.
fn build_bn254_cuda() -> PathBuf {
  assert_eq!(
    env::var("CARGO_CFG_TARGET_OS").as_deref(),
    Ok("linux"),
    "the BN254 CUDA backend supports Linux targets only"
  );
  assert_eq!(
    env::var("CARGO_CFG_TARGET_ARCH").as_deref(),
    Ok("x86_64"),
    "the BN254 CUDA backend supports x86_64 targets only"
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
  .expect("write BN254 CUDA architecture list");
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
  let mut sources = vec!["cuda/kzg.cu", "cuda/kzg_runtime.cpp"];
  if env::var_os("CARGO_FEATURE_PLONK").is_some() {
    sources.push("cuda/plonk/plonk.cu");
  }
  let mut objects = Vec::new();
  for source in sources {
    let object = out.join(Path::new(source).with_extension("o").file_name().unwrap());
    let mut command = cuda_compile_command(&nvcc, &architectures);
    command.args([
      "-c",
      "-DFEATURE_BN254",
      "-D__BLST_PORTABLE__",
      "-DMAX_LG_DOMAIN_SIZE=28",
    ]);
    command.arg(format!("-I{}", root.display()));
    command.arg(format!("-I{}", root.join("util").display()));
    command.arg(format!("-I{}", blst.display()));
    command.arg("-include").arg(&architecture_header);
    // sppark's MSM sort kernel is an ordinary definition in its header;
    // kzg.cu supplies the library's only instance.
    if source != "cuda/kzg.cu" {
      command.arg("-D__MSM_SORT_DONT_IMPLEMENT__");
    }
    run(command.arg(source).arg("-o").arg(&object));
    objects.push(object);
  }
  // The host-side field arithmetic calls blst's portable assembly.
  let compiler = env::var_os("CC").unwrap_or_else(|| "cc".into());
  let blst_root = blst.parent().expect("blst sources live under src/");
  for (source, name) in [
    (blst.join("server.c"), "blst_server.o"),
    (blst_root.join("build/assembly.S"), "blst_assembly.o"),
  ] {
    let object = out.join(name);
    run(Command::new(&compiler)
      .args(["-O3", "-fPIC", "-fvisibility=hidden", "-D__BLST_PORTABLE__"])
      .arg(format!("-I{}", blst.display()))
      .arg("-c")
      .arg(source)
      .arg("-o")
      .arg(&object));
    objects.push(object);
  }
  let exports = out.join("ix_bn254_cuda.map");
  std::fs::write(&exports, EXPORTS).expect("write BN254 CUDA export map");
  let library = out.join(LIBRARY);
  run(Command::new(&nvcc)
    .args([
      "--shared",
      "--cudart=static",
      "--compiler-options=-static-libstdc++,-static-libgcc",
    ])
    .arg(format!(
      "-Xlinker=-z,defs,-soname,{LIBRARY},--version-script,{}",
      exports.display()
    ))
    .arg("-o")
    .arg(&library)
    .args(&objects)
    .args(["-ldl", "-lrt", "-lpthread"]));
  println!("cargo:rustc-link-search=native={}", out.display());
  println!("cargo:rustc-link-lib=dylib=ix_bn254_cuda");
  println!("cargo:rustc-link-arg=-Wl,-rpath,{}", out.display());
  // Tests query the CUDA runtime directly.
  for directory in cuda_library_directories(&nvcc) {
    if directory.is_dir() {
      println!("cargo:rustc-link-search=native={}", directory.display());
    }
  }
  library
}

fn run(command: &mut Command) {
  let status = command
    .status()
    .unwrap_or_else(|error| panic!("failed to execute {command:?}: {error}"));
  assert!(status.success(), "{command:?} failed with {status}");
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
/// Lake build. Without either, the installed GPU architectures are detected.
fn cuda_architectures(nvcc: &std::ffi::OsStr) -> Vec<String> {
  let supported = supported_architectures(nvcc);
  let configured = env::var("IX_KZG_CUDA_ARCHS")
    .or_else(|_| env::var("MULTI_STARK_CUDA_ARCHS"))
    .ok()
    .or_else(detect_nvidia_architectures)
    .expect("no NVIDIA GPU detected; set IX_KZG_CUDA_ARCHS or MULTI_STARK_CUDA_ARCHS for the target GPU");
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
        supported.is_empty()
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
