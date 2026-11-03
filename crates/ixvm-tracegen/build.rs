//! Generates and compiles the IxVM trace writers when `kernel` is enabled.
fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  #[cfg(feature = "kernel")]
  aiur_tracegen::bundle::build(&aiur_tracegen::bundle::Config {
    tag: "ixvm",
    artifact_variable: "AIUR_IXVM_ARTIFACT",
    selection_variable: "AIUR_IXVM_TRACEGEN_CIRCUITS",
  });
}
