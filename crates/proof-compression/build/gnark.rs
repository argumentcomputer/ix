use std::{
  env,
  ffi::OsString,
  fs,
  hash::{Hash, Hasher},
  path::PathBuf,
  process::Command,
};

pub(super) fn build() {
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
    "IX_PLONK_CUDA_LIBRARY",
    "IX_PLONK_SPPARK_SOURCE",
    "IX_PLONK_BLST_SOURCE",
    "IX_PLONK_CUDA_ARCHS",
    "IX_GROTH16_ICICLE_ROOT",
    "NVCC",
    "CUDA_HOME",
    "CUDA_PATH",
    "NVCC_CCBIN",
    "NVCC_PREPEND_FLAGS",
    "NVCC_APPEND_FLAGS",
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
  let mut linker_flags = env::var("CGO_LDFLAGS").unwrap_or_default();
  if cuda && env::var_os("CARGO_FEATURE_PLONK").is_some() {
    assert_eq!(target_os, "linux", "PLONK CUDA requires Linux");
    assert_eq!(target_arch, "x86_64", "PLONK CUDA requires x86_64");
    let native = manifest.join("cuda/plonk");
    let library = match env::var_os("IX_PLONK_CUDA_LIBRARY") {
      Some(path) => PathBuf::from(path),
      None => {
        let build = out.join("plonk-native");
        let sppark = env::var_os("IX_PLONK_SPPARK_SOURCE")
          .or_else(|| env::var_os("DEP_SPPARK_ROOT"))
          .expect("set IX_PLONK_SPPARK_SOURCE or IX_PLONK_CUDA_LIBRARY");
        let blst = env::var_os("IX_PLONK_BLST_SOURCE")
          .or_else(|| {
            env::var_os("DEP_BLST_C_SRC").and_then(|path| {
              PathBuf::from(path).parent().map(|p| p.as_os_str().to_owned())
            })
          })
          .expect("set IX_PLONK_BLST_SOURCE or IX_PLONK_CUDA_LIBRARY");
        let status = Command::new("python3")
          .arg(native.join("build.py"))
          .arg("--sppark")
          .arg(sppark)
          .arg("--blst")
          .arg(blst)
          .arg("--out")
          .arg(&build)
          .status()
          .expect("native PLONK build");
        assert!(status.success(), "native PLONK build failed");
        build.join("libix_plonk_bn254_cuda.so")
      },
    }
    .canonicalize()
    .expect("PLONK CUDA library is missing");
    let directory = library.parent().unwrap();
    let packaged_header =
      directory.parent().unwrap().join("include/ix_plonk_bn254.h");
    let header = if packaged_header.is_file() {
      packaged_header
    } else {
      native.join("ix_plonk_bn254.h")
    };
    println!("cargo:rerun-if-changed={}", native.display());
    println!("cargo:rerun-if-changed={}", library.display());
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
    linker_flags
      .push_str(&format!(" -L{} -lix_plonk_bn254_cuda", directory.display()));
    println!("cargo:rustc-link-search=native={}", directory.display());
    println!("cargo:rustc-link-lib=dylib=ix_plonk_bn254_cuda");
    println!("cargo:rustc-link-lib=dylib=stdc++");
    println!(
      "cargo:rustc-link-arg-bin=ix-compression-worker=-Wl,-rpath,$ORIGIN/../lib"
    );
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", directory.display());
    // A library outside OUT_DIR needs an explicit path for packaging.
    println!("cargo:rustc-env=IX_PLONK_CUDA_LIBRARY={}", library.display());
  }
  if cuda && env::var_os("CARGO_FEATURE_GROTH16").is_some() {
    assert_eq!(target_os, "linux", "Groth16 CUDA requires Linux");
    assert_eq!(target_arch, "x86_64", "Groth16 CUDA requires x86_64");
    let root = PathBuf::from(
      env::var_os("IX_GROTH16_ICICLE_ROOT")
        .expect("set IX_GROTH16_ICICLE_ROOT to the pinned ICICLE installation"),
    )
    .canonicalize()
    .expect("ICICLE installation is missing");
    let library = root.join("lib");
    for name in ["icicle_device", "icicle_field_bn254", "icicle_curve_bn254"] {
      let file = library.join(format!("lib{name}.so"));
      assert!(file.is_file(), "missing ICICLE library {}", file.display());
      println!("cargo:rerun-if-changed={}", file.display());
      println!("cargo:rustc-link-lib=dylib={name}");
    }
    let backend = library.join("backend");
    assert!(backend.is_dir(), "ICICLE backend directory is missing");
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
}
