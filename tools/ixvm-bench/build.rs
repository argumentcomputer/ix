use std::{env, fs, path::PathBuf};

fn main() {
  println!("cargo:rerun-if-env-changed=IXVM_BENCH_CODEGEN_PREFIX");
  if env::var_os("CARGO_FEATURE_CODEGEN").is_none() {
    return;
  }
  let prefix = env::var("IXVM_BENCH_CODEGEN_PREFIX")
    .expect("codegen requires IXVM_BENCH_CODEGEN_PREFIX (without .rs/.json)");
  let out = PathBuf::from(env::var_os("OUT_DIR").unwrap());
  for extension in ["rs", "json"] {
    let source = PathBuf::from(format!("{prefix}.{extension}"))
      .canonicalize()
      .expect("generate the constrained Rust and JSON export first");
    println!("cargo:rerun-if-changed={}", source.display());
    fs::copy(source, out.join(format!("generated.{extension}"))).unwrap();
  }
  fs::write(
    out.join("module.rs"),
    format!("#[path = {:?}] mod generated;\n", out.join("generated.rs")),
  )
  .unwrap();
}
