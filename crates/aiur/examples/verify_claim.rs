//! Verify a proof of `entry(args) = output` against the key recompiled from a
//! package's program. The arguments and the output are supplied by the
//! verifier, as signed integers (one per line or whitespace-separated); the
//! package's execution data (arguments, hints) is not read.
//!
//! `verify_claim PACKAGE.ixa PROOF ARGS.txt OUTPUT.txt`
use aiur::field::FieldBackend;
use aiur::{
  artifact::ExecutionPackage,
  trace::{
    TracePlan,
    stark::{Backend, Parameters, Proof},
  },
};
use std::{error::Error, fs, time::Instant};

const P: i128 = 18446744069414584321;

fn words(path: &str) -> Result<Vec<u64>, Box<dyn Error>> {
  fs::read_to_string(path)?
    .split_whitespace()
    .map(|w| Ok(w.parse::<i128>()?.rem_euclid(P) as u64))
    .collect()
}

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let [_, package, proof, args_path, output_path] = args.as_slice() else {
    return Err(
      "usage: verify_claim PACKAGE.ixa PROOF ARGS.txt OUTPUT.txt".into(),
    );
  };
  let start = Instant::now();
  let (package, digest) = ExecutionPackage::load(package.as_ref())?;
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry =
    &program.program().entries.first().ok_or("no selected entrypoint")?.name;
  let backend = Backend::new(&plan, Parameters::default())?;
  let setup = start.elapsed().as_secs_f64();
  let call = program.field().decode(&words(args_path)?)?;
  let output = program.field().decode(&words(output_path)?)?;
  let bytes = fs::read(proof)?;
  let start = Instant::now();
  let proof = Proof::from_bytes(&bytes)?;
  backend.verify(entry, &call, &output, &proof)?;
  println!(
    "verified {entry}: package {digest}, proof blake3 {} ({} bytes), {} argument words, {} output words; key setup {setup:.2} s, verify {:.2} s",
    blake3::hash(&bytes).to_hex(),
    bytes.len(),
    call.len(),
    output.len(),
    start.elapsed().as_secs_f64()
  );
  Ok(())
}
