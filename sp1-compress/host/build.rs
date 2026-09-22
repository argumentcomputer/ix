fn main() {
  // Switching between lint-only and production builds must invalidate the
  // build-script result so `include_elf!` never reuses a skipped artifact.
  println!("cargo:rerun-if-env-changed=SP1_SKIP_PROGRAM_BUILD");
  // The zkVM uses Succinct's target toolchain, whose version string trails
  // the repository's host compiler. The pinned multi-stark source is shared
  // byte-for-byte with the host and deliberately declares the host MSRV, so
  // let cargo-prove compile it rather than rejecting it on metadata alone.
  let args =
    sp1_build::BuildArgs { ignore_rust_version: true, ..Default::default() };
  sp1_build::build_program_with_args("../guest", args.clone());
  sp1_build::build_program_with_args("../guest-mathlib-2026-09-03", args);
}
