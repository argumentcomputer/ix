//! Generates the native executor of `tests/fixtures/coverage.aiur` into
//! `$OUT_DIR/coverage.rs`.
fn main() {
  let fixture = "tests/fixtures/coverage.aiur";
  println!("cargo:rerun-if-changed={fixture}");
  let package = aiur::artifact::read(std::path::Path::new(fixture))
    .expect("the coverage fixture loads");
  let program = package.program.check().expect("the coverage fixture checks");
  let source = aiur_codegen::native_executor(&program, "Coverage")
    .expect("the coverage fixture generates");
  let out = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
  std::fs::write(out.join("coverage.rs"), source).unwrap();
}
