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
//! `{"source": <absolute path>, "path": <path relative to lib/>, "link": <bool>}`.
//! A Rust static archive does not carry its shared-library dependencies, so a
//! final link of one must also link each `"link": true` library. The others,
//! ICICLE's CUDA backend plugins, are only loaded at runtime.

use std::env;
use std::ffi::OsString;
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
  link: bool,
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
    "NVCC_CCBIN",
    "NVCC_PREPEND_FLAGS",
    "NVCC_APPEND_FLAGS",
    "CC",
    "IX_KZG_CUDA_ARCHS",
  ] {
    println!("cargo:rerun-if-env-changed={variable}");
  }
  let mut artifacts = Vec::new();
  if env::var_os("CARGO_FEATURE_CUDA").is_some() {
    let multi_stark = PathBuf::from(multi_stark_cuda("LIBRARY"));
    artifacts.push(RuntimeArtifact {
      path: multi_stark
        .file_name()
        .and_then(|name| name.to_str())
        .expect("multi-stark's CUDA library has a UTF-8 file name")
        .to_owned(),
      source: multi_stark,
      link: true,
    });
    artifacts.push(RuntimeArtifact {
      source: build_bn254_cuda(),
      path: LIBRARY.to_owned(),
      link: true,
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
        r#"{{"source":{},"path":{},"link":{}}}"#,
        json_string(source),
        json_string(&artifact.path),
        artifact.link
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

/// Toolchain metadata from multi-stark's CUDA build, which this crate's
/// Goldilocks backend links against.
fn multi_stark_cuda(key: &str) -> OsString {
  env::var_os(format!("DEP_MULTI_STARK_CUDA_{key}"))
    .unwrap_or_else(|| panic!("multi-stark's CUDA build did not report {key}"))
}

/// `IX_KZG_CUDA_ARCHS`, or else the architectures multi-stark compiled its
/// backend for.
fn kzg_architectures() -> Vec<String> {
  let selected = env::var("IX_KZG_CUDA_ARCHS").unwrap_or_else(|_| {
    multi_stark_cuda("ARCHS")
      .into_string()
      .expect("CUDA architectures are ASCII")
  });
  let architectures: Vec<String> = selected
    .split(',')
    .map(str::trim)
    .filter(|architecture| !architecture.is_empty())
    .map(str::to_owned)
    .collect();
  assert!(
    !architectures.is_empty()
      && architectures.iter().all(|architecture| {
        (2..=3).contains(&architecture.len())
          && architecture.chars().all(|c| c.is_ascii_digit())
      }),
    "invalid CUDA architectures {selected:?}; expected numbers such as 80,90"
  );
  architectures
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
  let nvcc = multi_stark_cuda("NVCC");
  let architectures = kzg_architectures();
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
    let object =
      out.join(Path::new(source).with_extension("o").file_name().unwrap());
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
    run(
      Command::new(&compiler)
        .args(["-O3", "-fPIC", "-fvisibility=hidden", "-D__BLST_PORTABLE__"])
        .arg(format!("-I{}", blst.display()))
        .arg("-c")
        .arg(source)
        .arg("-o")
        .arg(&object),
    );
    objects.push(object);
  }
  let exports = out.join("ix_bn254_cuda.map");
  std::fs::write(&exports, EXPORTS).expect("write BN254 CUDA export map");
  let library = out.join(LIBRARY);
  run(
    Command::new(&nvcc)
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
      .args(["-ldl", "-lrt", "-lpthread"]),
  );
  println!("cargo:rustc-link-search=native={}", out.display());
  println!("cargo:rustc-link-lib=dylib=ix_bn254_cuda");
  println!("cargo:rustc-link-arg=-Wl,-rpath,{}", out.display());
  // Tests query the CUDA runtime directly.
  for directory in env::split_paths(&multi_stark_cuda("LIB_DIRS")) {
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
