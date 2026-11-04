//! Checks that `lake build ix` generated the sources, and compiles the
//! trace writers with feature `cuda`.
use std::path::Path;

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  if std::env::var_os("CARGO_FEATURE_EXECUTORS").is_none() {
    return;
  }
  let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("../../.lake/build/formal-generated");
  for name in ["ixvm", "verifier", "aggregation"] {
    let path = directory.join("native").join(format!("{name}.rs"));
    assert!(
      path.is_file(),
      "{} is missing; `lake build ix` generates it",
      path.display()
    );
  }
  #[cfg(feature = "cuda")]
  for tag in ["ixvm", "verifier", "aggregation"] {
    let cuda = directory.join("cuda").join(tag);
    assert!(
      cuda.is_dir(),
      "{} is missing; `lake build ix` generates it when CUDA is enabled",
      cuda.display()
    );
    aiur_tracegen::bundle::build(&aiur_tracegen::bundle::Config {
      tag,
      directory: &cuda,
    });
  }
}
