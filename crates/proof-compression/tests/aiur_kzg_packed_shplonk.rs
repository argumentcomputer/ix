//! Compiled Aiur circuits proved through multi-stark with packed SHPLONK
//! openings instead of per-column KZG.

use std::sync::Arc;

use aiur::{
  artifact::WidePackage, bytecode::CheckedProgram, field::FieldBackend,
  trace::TracePlan,
};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    kzg::{Compiler, circuit_inputs},
  },
  kzg::{Srs, packed_shplonk::PackedShplonkConfig},
};
use multi_stark::system::{System, SystemWitness};

const ENTRY: &str = "BN254Trace::run";

fn plan() -> TracePlan<'static, Bn254> {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap();
  let trace = package.trace.unwrap();
  let mut checked: CheckedProgram<Bn254> =
    package.program.check_with(Bn254).unwrap();
  checked.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(checked), trace).unwrap()
}

#[test]
fn compiled_aiur_program_proves_with_packed_shplonk_openings() {
  let plan = plan();
  let compiler = Compiler::new(&plan).unwrap();
  let srs = Arc::new(Srs::unsafe_dev_setup(256, b"aiur-packed-shplonk-test"));
  let (system, key) = System::new(
    PackedShplonkConfig::new(srs, 8),
    circuit_inputs(&plan).unwrap(),
  );
  let f = |value| Bn254.from_u64(value);
  for (n, x, expected) in
    [(3, Bn254.neg(Bn254.one()), f(9)), (129, f(0), f(128))]
  {
    let args = [f(n), x];
    let record = plan.program().execute(ENTRY, args.to_vec()).unwrap();
    assert_eq!(record.output, [expected]);
    let public = plan.public_args(&record, ENTRY, &args).unwrap();
    let claim = plan.public_claim(ENTRY, &public, &record.output).unwrap();
    let traces = compiler.generate(&record, ENTRY, &args).unwrap();
    let proof =
      system.prove(&key, &claim, SystemWitness::from_stage_1(traces, &system));
    system.verify(&claim, &proof).unwrap();
    let mut changed = claim.clone();
    *changed.last_mut().unwrap() += f(1);
    assert!(system.verify(&changed, &proof).is_err());
    let packs = [
      &proof.commitments.stage_1_trace,
      &proof.commitments.stage_2_trace,
      &proof.commitments.quotient_chunks,
    ]
    .map(|c| c.packs.len());
    let columns: usize = proof
      .commitments
      .stage_1_trace
      .matrices
      .iter()
      .chain(&proof.commitments.stage_2_trace.matrices)
      .chain(&proof.commitments.quotient_chunks.matrices)
      .map(|m| m.width as usize)
      .sum();
    // Every round has fewer points than columns; the opening adds two.
    assert!(packs.iter().sum::<usize>() + 2 < columns);
  }
}
