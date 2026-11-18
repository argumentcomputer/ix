//! With feature `cuda`, generates the trace bundles of `aiur`'s depth,
//! grouping and memory fixtures into `$OUT_DIR/{depth,grouping,memory}` and
//! compiles them.
fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  #[cfg(feature = "cuda")]
  for (tag, fixture, depth) in [
    ("depth", "../aiur/tests/fixtures/depth.ixa", true),
    ("grouping", "../aiur/tests/fixtures/grouping.ixa", false),
    ("memory", "../aiur/tests/fixtures/memory.ixa", false),
  ] {
    println!("cargo:rerun-if-changed={fixture}");
    let (package, _) =
      aiur::artifact::Package::load(std::path::Path::new(fixture))
        .expect("the fixture loads");
    let (program, trace) = package.traced().expect("the fixture is traced");
    let mut program = program.check().expect("the fixture checks");
    if depth {
      program.track_depth(&trace).expect("the fixture tracks depth");
    }
    let described =
      aiur_tracegen::describe(&program, trace).expect("the fixture describes");
    let out = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    let directory = out.join(tag);
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    for (name, contents) in
      aiur_tracegen::bundle::sources(&described, tag, "// Test fixture.\n")
        .expect("the fixture's bundle generates")
    {
      std::fs::write(directory.join(name), contents).unwrap();
    }
    aiur_tracegen::bundle::build(&aiur_tracegen::bundle::Config {
      tag,
      directory: &directory,
    });
  }
}
