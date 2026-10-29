use std::{
  env,
  ffi::OsString,
  fs,
  hash::{Hash, Hasher},
  path::PathBuf,
  process::Command,
};

/// BLAKE3 over the module definition and every non-test Go source, in path
/// order: what compiles the final circuits and serializes their keys.
fn source_digest(source: &std::path::Path) -> String {
  let mut files = vec![source.join("go.mod"), source.join("go.sum")];
  let mut directories = vec![source.to_path_buf()];
  let mut sources = Vec::new();
  while let Some(directory) = directories.pop() {
    for entry in fs::read_dir(&directory).unwrap() {
      let path = entry.unwrap().path();
      let name = path.file_name().unwrap().to_string_lossy().into_owned();
      if path.is_dir() {
        if name != "vendor" && name != "testdata" {
          directories.push(path);
        }
      } else if name.ends_with(".go") && !name.ends_with("_test.go") {
        sources.push(path);
      }
    }
  }
  sources.sort();
  files.extend(sources);
  let mut hasher = blake3::Hasher::new();
  for file in files {
    let relative = file.strip_prefix(source).unwrap().to_string_lossy();
    hasher.update(relative.as_bytes());
    hasher.update(&[0]);
    let bytes = fs::read(&file).unwrap();
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(&bytes);
  }
  hasher.finalize().to_hex().to_string()
}

pub(super) fn build() -> Vec<super::RuntimeArtifact> {
  let manifest = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());
  let source =
    manifest.join("../../tools/plonk-wrapper").canonicalize().unwrap();
  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
  println!("cargo:rerun-if-changed={}", source.display());
  for variable in [
    "GO",
    "PATH",
    "GOROOT",
    "IX_GNARK_GO_VERSION",
    "CGO_CFLAGS",
    "CGO_LDFLAGS",
    "CC",
    "CXX",
    "IX_GROTH16_ICICLE_ROOT",
  ] {
    println!("cargo:rerun-if-env-changed={variable}");
  }
  let go = env::var_os("GO").unwrap_or_else(|| OsString::from("go"));
  let selected = PathBuf::from(&go);
  let executable = if selected.components().count() > 1 {
    source.join(&selected)
  } else {
    env::split_paths(&env::var_os("PATH").unwrap_or_default())
      .map(|directory| source.join(directory).join(&selected))
      .find(|path| path.is_file())
      .unwrap_or_else(|| panic!("cannot find {go:?} in PATH"))
  };
  println!("cargo:rerun-if-changed={}", executable.display());
  println!(
    "cargo:rustc-env=IX_GNARK_SOURCE_BLAKE3={}",
    source_digest(&source)
  );
  let toolchain = Command::new(&go)
    .current_dir(&source)
    .env("GOTOOLCHAIN", "local")
    .args(["env", "GOROOT", "GOTOOLDIR"])
    .output()
    .expect("inspect Go toolchain");
  assert!(
    toolchain.status.success(),
    "Go toolchain query failed: {}",
    String::from_utf8_lossy(&toolchain.stderr)
  );
  let toolchain = String::from_utf8(toolchain.stdout)
    .expect("Go toolchain paths must be UTF-8");
  let mut paths = toolchain.lines();
  let root = PathBuf::from(paths.next().expect("Go did not report GOROOT"));
  let tools = PathBuf::from(paths.next().expect("Go did not report GOTOOLDIR"));
  for path in [
    root.join("bin/go"),
    root.join("VERSION"),
    tools.join("compile"),
    tools.join("link"),
    tools.join("cgo"),
  ] {
    println!("cargo:rerun-if-changed={}", path.display());
  }
  let mut command = Command::new(&go);
  command
    .current_dir(&source)
    .env("CGO_ENABLED", "1")
    .env("GOTOOLCHAIN", "local")
    .env("GOCACHE", out.join("go-cache"));
  let target_os = env::var("CARGO_CFG_TARGET_OS").unwrap();
  let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
  command.env(
    "GOOS",
    match target_os.as_str() {
      "linux" => "linux",
      "macos" => "darwin",
      _ => panic!("gnark supports Linux and macOS"),
    },
  );
  command.env(
    "GOARCH",
    match target_arch.as_str() {
      "x86_64" => "amd64",
      "aarch64" => "arm64",
      _ => panic!("gnark supports x86_64 and aarch64"),
    },
  );
  command.args([
    "build",
    "-buildvcs=false",
    "-trimpath",
    "-buildmode=c-archive",
  ]);
  command.arg(if source.join("vendor").is_dir() {
    "-mod=vendor"
  } else {
    "-mod=readonly"
  });
  let cuda = env::var_os("CARGO_FEATURE_CUDA").is_some();
  let mut tags = Vec::new();
  if env::var_os("CARGO_FEATURE_PLONK").is_some() {
    tags.push("plonk");
  }
  if env::var_os("CARGO_FEATURE_GROTH16").is_some() {
    tags.push("groth16");
  }
  let mut linker_flags = env::var("CGO_LDFLAGS").unwrap_or_default();
  let mut artifacts = Vec::new();
  if cuda && env::var_os("CARGO_FEATURE_PLONK").is_some() {
    assert_eq!(target_os, "linux", "PLONK CUDA requires Linux");
    assert_eq!(target_arch, "x86_64", "PLONK CUDA requires x86_64");
    let header = manifest.join("cuda/plonk/ix_plonk_bn254.h");
    println!("cargo:rerun-if-changed={}", header.display());
    // cgo does not include headers outside its package in its cache key.
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    fs::read(&header).unwrap().hash(&mut hash);
    let cflags = format!(
      "{} -I{} -DIX_PLONK_HEADER_{:x}=1",
      env::var("CGO_CFLAGS").unwrap_or_default(),
      header.parent().unwrap().display(),
      hash.finish()
    );
    tags.push("cuda");
    command.env("CGO_CFLAGS", cflags);
    // build.rs places libix_bn254_cuda.so in OUT_DIR before cgo links.
    linker_flags.push_str(&format!(" -L{}", out.display()));
  }
  if cuda && env::var_os("CARGO_FEATURE_GROTH16").is_some() {
    assert_eq!(target_os, "linux", "Groth16 CUDA requires Linux");
    assert_eq!(target_arch, "x86_64", "Groth16 CUDA requires x86_64");
    let root = env::var_os("IX_GROTH16_ICICLE_ROOT")
      .filter(|value| !value.is_empty())
      .map_or_else(|| PathBuf::from("/usr/local"), PathBuf::from);
    let root = root.canonicalize().unwrap_or_else(|error| {
      panic!(
        "ICICLE installation {} is unavailable: {error}; install the pinned BN254 libraries under /usr/local or set IX_GROTH16_ICICLE_ROOT",
        root.display()
      )
    });
    let library = root.join("lib");
    for name in [
      "libicicle_device.so",
      "libicicle_field_bn254.so",
      "libicicle_curve_bn254.so",
      "backend/cuda/libicicle_backend_cuda_device.so",
      "backend/bn254/cuda/libicicle_backend_cuda_field_bn254.so",
      "backend/bn254/cuda/libicicle_backend_cuda_curve_bn254.so",
    ] {
      let file = library.join(name);
      assert!(
        file.is_file(),
        "missing ICICLE library {}; install the pinned BN254 libraries under /usr/local or set IX_GROTH16_ICICLE_ROOT",
        file.display()
      );
      println!("cargo:rerun-if-changed={}", file.display());
      artifacts
        .push(super::RuntimeArtifact { source: file, path: name.to_owned() });
    }
    for name in ["icicle_device", "icicle_field_bn254", "icicle_curve_bn254"] {
      println!("cargo:rustc-link-lib=dylib={name}");
    }
    let backend = library.join("backend");
    println!("cargo:rerun-if-changed={}", backend.display());
    println!("cargo:rustc-link-search=native={}", library.display());
    println!("cargo:rustc-link-lib=dylib=stdc++");
    println!("cargo:rustc-link-lib=dylib=m");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", library.display());
    println!("cargo:rustc-env=IX_GROTH16_ICICLE_ROOT={}", root.display());
    println!("cargo:rustc-env=IX_GROTH16_ICICLE_BACKEND={}", backend.display());
    linker_flags.push_str(&format!(" -L{}", library.display()));
    tags.push("icicle");
  }
  if !tags.is_empty() {
    command.arg(format!("-tags={}", tags.join(",")));
  }
  command.env("CGO_LDFLAGS", linker_flags);
  let archive = out.join("libix_gnark.a");
  let status = command
    .arg("-o")
    .arg(&archive)
    .arg(".")
    .status()
    .unwrap_or_else(|e| panic!("cannot run {go:?}: {e}"));
  assert!(status.success(), "gnark archive build failed");
  let header = out.join("libix_gnark.h");
  bindgen::Builder::default()
    .header(header.to_string_lossy())
    .clang_arg(format!("-I{}", source.display()))
    .allowlist_function("ix_gnark_.*")
    .allowlist_type("ix_gnark_.*")
    .layout_tests(false)
    .generate_comments(false)
    .generate()
    .expect("gnark C bindings")
    .write_to_file(out.join("gnark_bindings.rs"))
    .expect("write gnark bindings");
  println!("cargo:rustc-link-search=native={}", out.display());
  println!("cargo:rustc-link-lib=static=ix_gnark");
  if target_os == "macos" {
    println!("cargo:rustc-link-lib=framework=CoreFoundation");
    println!("cargo:rustc-link-lib=framework=Security");
  } else {
    println!("cargo:rustc-link-lib=dylib=pthread");
    println!("cargo:rustc-link-lib=dylib=dl");
  }
  artifacts
}
