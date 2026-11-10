//! Generates the native executor of `tests/fixtures/coverage.json` into
//! `$OUT_DIR/coverage.rs`.
fn main() {
  let fixture = "tests/fixtures/coverage.json";
  println!("cargo:rerun-if-changed={fixture}");
  let bytes = std::fs::read(fixture).expect("the coverage fixture reads");
  let program: aiur::Program =
    serde_json::from_slice(&bytes).expect("the coverage fixture parses");
  let program = program.check().expect("the coverage fixture checks");
  let source = aiur_codegen::native_executor(&program, "Coverage")
    .expect("the coverage fixture generates");
  let out = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
  std::fs::write(out.join("coverage.rs"), source).unwrap();
}
