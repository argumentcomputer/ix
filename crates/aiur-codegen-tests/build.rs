//! Generates the native executors of `tests/fixtures/{coverage,heights}.json`
//! into `$OUT_DIR/{coverage,heights}.rs` and of the depth fixture
//! (`crates/aiur/tests/fixtures/depth.ixa`) into `$OUT_DIR/depth.rs`.
fn main() {
  let out = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());

  for (name, executor) in [("coverage", "Coverage"), ("heights", "Heights")] {
    let fixture = format!("tests/fixtures/{name}.json");
    println!("cargo:rerun-if-changed={fixture}");
    let bytes = std::fs::read(&fixture).expect("the fixture reads");
    let program: aiur::Program =
      serde_json::from_slice(&bytes).expect("the fixture parses");
    let program = program.check().expect("the fixture checks");
    let source = aiur_codegen::native_executor(&program, executor)
      .expect("the fixture generates");
    std::fs::write(out.join(format!("{name}.rs")), source).unwrap();
  }

  let fixture = "../aiur/tests/fixtures/depth.ixa";
  println!("cargo:rerun-if-changed={fixture}");
  let bytes = std::fs::read(fixture).expect("the depth fixture reads");
  let package =
    aiur::artifact::Package::decode(&bytes).expect("the depth fixture parses");
  let program = package.program.check().expect("the depth fixture checks");
  let source = aiur_codegen::native_executor(&program, "Depth")
    .expect("the depth fixture generates");
  std::fs::write(out.join("depth.rs"), source).unwrap();
}
