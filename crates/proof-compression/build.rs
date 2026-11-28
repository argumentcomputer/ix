//! Native proving backends.
//!
//! Without the `cuda` feature the crate needs neither nvcc nor the CUDA
//! toolkit. With it, the BN254 KZG kernels (plus, with `plonk`, the BN254
//! PLONK kernels) are linked against sppark into `libix_bn254_cuda.so`, and
//! the BLS12-381 KZG kernels (plus, with `plonk`, the BLS12-381 PLONK kernels)
//! are linked into `libix_bls12_381_cuda.so`.
//! Each library carries a private C++ runtime, unwinder and CUDA runtime and
//! exports only its curve-prefixed C entry points, so both curves coexist
//! cleanly alongside a process that links a different C++ runtime (the Lean
//! executable links LLVM's libc++).
//!
//! `IX_RUNTIME_ARTIFACTS` names every shared library an executable built from
//! this crate must ship beside itself, as a JSON array of
//! `{"source": <absolute path>, "path": <path relative to lib/>, "link": <bool>}`.
//! A Rust static archive does not carry its shared-library dependencies, so a
//! final link of one must also link each `"link": true` library.

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
  "cuda/plonk/ix_plonk_bls12_381.h",
];

const BN254_LIBRARY: &str = "libix_bn254_cuda.so";
const BLS12_381_LIBRARY: &str = "libix_bls12_381_cuda.so";

const BN254_EXPORTS: &str = r"{
    global: ix_kzg_*; ix_plonk_bn254_*;
    local: *;
};";

const BLS12_381_EXPORTS: &str = r"{
    global: ix_kzg_bls12_381_*; ix_plonk_bls12_381_*;
    local: *;
};";

/// A shared library to install at `lib/<path>` beside the executable.
struct RuntimeArtifact {
  source: PathBuf,
  path: String,
  link: bool,
}

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
    let (bn254, bls12_381) = build_kzg_cuda();
    artifacts.push(RuntimeArtifact {
      source: bn254,
      path: BN254_LIBRARY.to_owned(),
      link: true,
    });
    artifacts.push(RuntimeArtifact {
      source: bls12_381,
      path: BLS12_381_LIBRARY.to_owned(),
      link: true,
    });
  }
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

/// Parameters for one curve's CUDA shared library.
struct CurveCudaSpec<'a> {
  prefix: &'a str,
  library: &'a str,
  link_name: &'a str,
  map_name: &'a str,
  exports: &'a str,
  feature_flag: &'a str,
  domain_flag: &'a str,
  include_plonk: bool,
}

/// Builds `libix_bn254_cuda.so` and `libix_bls12_381_cuda.so` in `OUT_DIR`
/// and links both into this crate.
fn build_kzg_cuda() -> (PathBuf, PathBuf) {
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
  // The host-side field arithmetic calls blst's portable assembly. Both curve
  // libraries link the same hidden objects.
  let compiler = env::var_os("CC").unwrap_or_else(|| "cc".into());
  let blst_root = blst.parent().expect("blst sources live under src/");
  let mut shared_objects = Vec::new();
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
    shared_objects.push(object);
  }
  let build_one = |spec: &CurveCudaSpec<'_>| -> PathBuf {
    let mut sources = vec!["cuda/kzg.cu", "cuda/kzg_runtime.cpp"];
    if spec.include_plonk && env::var_os("CARGO_FEATURE_PLONK").is_some() {
      sources.push("cuda/plonk/plonk.cu");
    }
    let mut objects = Vec::new();
    for source in sources {
      let stem = Path::new(source)
        .file_stem()
        .and_then(|name| name.to_str())
        .expect("CUDA source has UTF-8 stem");
      let object = out.join(format!("{}_{stem}.o", spec.prefix));
      let mut command = cuda_compile_command(&nvcc, &architectures);
      command.args([
        "-c",
        spec.feature_flag,
        "-D__BLST_PORTABLE__",
        spec.domain_flag,
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
    objects.extend(shared_objects.iter().cloned());
    let exports = out.join(spec.map_name);
    std::fs::write(&exports, spec.exports).expect("write KZG CUDA export map");
    let library = out.join(spec.library);
    run(
      Command::new(&nvcc)
        .args([
          "--shared",
          "--cudart=static",
          "--compiler-options=-static-libstdc++,-static-libgcc",
        ])
        .arg(format!(
          "-Xlinker=-z,defs,-soname,{},--version-script,{}",
          spec.library,
          exports.display()
        ))
        .arg("-o")
        .arg(&library)
        .args(&objects)
        .args(["-ldl", "-lrt", "-lpthread"]),
    );
    println!("cargo:rustc-link-lib=dylib={}", spec.link_name);
    library
  };
  println!("cargo:rustc-link-search=native={}", out.display());
  let bn254 = build_one(&CurveCudaSpec {
    prefix: "bn254",
    library: BN254_LIBRARY,
    link_name: "ix_bn254_cuda",
    map_name: "ix_bn254_cuda.map",
    exports: BN254_EXPORTS,
    feature_flag: "-DFEATURE_BN254",
    domain_flag: "-DMAX_LG_DOMAIN_SIZE=28",
    include_plonk: true,
  });
  let bls12_381 = build_one(&CurveCudaSpec {
    prefix: "bls12_381",
    library: BLS12_381_LIBRARY,
    link_name: "ix_bls12_381_cuda",
    map_name: "ix_bls12_381_cuda.map",
    exports: BLS12_381_EXPORTS,
    feature_flag: "-DFEATURE_BLS12_381",
    domain_flag: "-DMAX_LG_DOMAIN_SIZE=32",
    include_plonk: true,
  });
  println!("cargo:rustc-link-arg=-Wl,-rpath,{}", out.display());
  // Tests query the CUDA runtime directly.
  for directory in env::split_paths(&multi_stark_cuda("LIB_DIRS")) {
    if directory.is_dir() {
      println!("cargo:rustc-link-search=native={}", directory.display());
    }
  }
  (bn254, bls12_381)
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
