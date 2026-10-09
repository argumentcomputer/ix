//! Complete fixed-profile recursive verification of a parity proof.
//! `cargo run --release --example parity_recursive` also proves the verifier.
//! Add `-- --check-only` to check its constraints without the large outer proof.

#[path = "../tests/support/parity.rs"]
mod parity;

use std::time::Instant;

use ix_proof_compression::fri::build_fixed_verifier;
use ix_proof_compression::fri::expand_pcs_witness;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::Val;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let check_only = match std::env::args().skip(1).collect::<Vec<_>>().as_slice()
  {
    [] => false,
    [flag] if flag == "--check-only" => true,
    _ => return Err("usage: parity_recursive [--check-only]".into()),
  };
  let (inner, key) = System::new(parity::config(), parity::circuit_inputs());
  let claim = parity::claim(parity::Function::Even, 100, true);
  let proof = inner.prove(
    &key,
    &claim,
    SystemWitness::from_stage_1(
      parity::traces(parity::Function::Even, 100),
      &inner,
    ),
  );
  inner.verify(&claim, &proof).expect("native inner proof");
  let start = Instant::now();
  let (circuit, inputs) =
    build_fixed_verifier(&inner, parity::LOG_HEIGHT, &[3]);
  println!(
    "Full verifier: {} gates, {} lookups, {} public coordinates; build {:?}",
    circuit.gates().len(),
    circuit.lookups().len(),
    circuit.public_values().len(),
    start.elapsed()
  );
  println!("Frontend costs: {:?}", circuit.stats());
  println!("STARK layout: {:?}", circuit.multi_stark_layout()?);
  let expanded = expand_pcs_witness(&inner, &inputs.shape, &proof, &[&claim])?;
  let start = Instant::now();
  let mut witness = circuit.witness();
  expanded.assign(&mut witness, &inputs)?;
  let assignment = witness.generate()?;
  assert_eq!(assignment.public_values(), claim);
  println!("All verifier constraints satisfied; witness {:?}", start.elapsed());
  if check_only {
    return Ok(());
  }

  let start = Instant::now();
  let compiled = circuit.lower_to_multi_stark(Val::from_u32(103))?;
  println!(
    "Outer computation trace: {} rows × {} columns; lowering {:?}",
    compiled.main_height(),
    compiled.main_width(),
    start.elapsed()
  );
  let claims = compiled.claims(&claim)?;
  let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
  let traces = compiled.traces(&assignment)?;
  let circuit_inputs = compiled.circuit_inputs();
  // The fixed layout and witness recipe are not needed during proving.
  // Release them before constructing the large commitment data.
  drop(compiled);
  drop(assignment);
  let start = Instant::now();
  let (outer, outer_key) = System::new(parity::config(), circuit_inputs);
  println!("Outer setup: {:?}", start.elapsed());
  let start = Instant::now();
  let outer_proof = outer.prove_multiple_claims(
    &outer_key,
    &refs,
    SystemWitness::from_stage_1(traces, &outer),
  );
  println!(
    "Outer proving: {:?}; {} bytes",
    start.elapsed(),
    outer_proof.to_bytes()?.len()
  );
  let start = Instant::now();
  outer.verify_multiple_claims(&refs, &outer_proof).expect("recursive proof");
  println!("Outer verification: {:?}", start.elapsed());
  let mut wrong = claims.clone();
  wrong[3][3] = Val::ZERO;
  assert!(
    outer
      .verify_multiple_claims(
        &wrong.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        &outer_proof
      )
      .is_err()
  );
  println!(
    "Verified is_even(100) = true through the complete verifier circuit; wrong public result rejected."
  );
  println!(
    "Fixed equal-height binary profile; bounded field-sampling retries. {} queries: development security only.",
    parity::NUM_QUERIES
  );
  // Linux reports whole-process peak RSS, including circuit construction,
  // lowering, setup and proving. Other platforms simply omit this metric.
  if let Ok(status) = std::fs::read_to_string("/proc/self/status")
    && let Some(peak) = status.lines().find(|line| line.starts_with("VmHWM:"))
  {
    println!(
      "Whole-process peak RSS: {}",
      peak.trim_start_matches("VmHWM:").trim()
    );
  }
  Ok(())
}
