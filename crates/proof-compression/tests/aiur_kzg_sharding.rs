//! Function circuits split into several power-of-two shards. Each shard is a
//! copy of the compiled circuit in the system with its own trace; LogUp
//! balances over all circuits, so the copies together carry the rows one
//! circuit carried before.
use std::sync::Arc;

use aiur::{
  artifact::WidePackage, bytecode::CheckedProgram, field::FieldBackend,
  trace::TracePlan,
};
use ix_proof_compression::{
  aiur_backend::{
    Bn254,
    compress_bn::decompose,
    kzg::{Compiler, circuit_inputs},
  },
  kzg::{KzgConfig, Scalar, Srs},
};
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::traits::Algebra;
use p3_matrix::dense::RowMajorMatrix;

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

fn piece(
  trace: &RowMajorMatrix<Scalar>,
  rows: std::ops::Range<usize>,
  height: usize,
) -> RowMajorMatrix<Scalar> {
  let width = trace.width;
  let mut values = vec![Scalar::ZERO; height * width];
  let real = &trace.values[rows.start * width..rows.end * width];
  values[..real.len()].copy_from_slice(real);
  RowMajorMatrix::new(values, width)
}

struct Sharded {
  inputs: Vec<CircuitInputs<Scalar>>,
  traces: Vec<RowMajorMatrix<Scalar>>,
  /// `(circuit, heights)` of every circuit split into several shards.
  split: Vec<(usize, Vec<usize>)>,
}

/// Replace every function circuit with more than one real row by copies,
/// one per piece of [`decompose`]; `overlap` repeats the first real row of
/// each later shard's predecessor, which a sound verifier must reject.
fn shard(
  plan: &TracePlan<'_, Bn254>,
  record: &aiur::Execution<Bn254>,
  traces: Vec<RowMajorMatrix<Scalar>>,
  pieces: usize,
  overlap: bool,
) -> Sharded {
  let inputs = circuit_inputs(plan).unwrap();
  let layout = plan.layout().unwrap();
  let mut rows = vec![0usize; inputs.len()];
  for (function, &chip) in plan.function_chips().iter().enumerate() {
    rows[layout.placements[chip].circuit] +=
      record.queries.callable_rows(function).unwrap();
  }
  let compiler = Compiler::new(plan).unwrap();
  let functions = compiler.function_circuits();
  assert_eq!(
    rows[..functions],
    compiler.raw_row_counts(record).unwrap()[..functions]
  );
  let mut sharded = Sharded { inputs: vec![], traces: vec![], split: vec![] };
  for (index, ((input, trace), name)) in
    inputs.into_iter().zip(traces).zip(compiler.names()).enumerate()
  {
    let heights = decompose(rows[index], pieces);
    if name.starts_with('<') || heights.len() < 2 {
      sharded.inputs.push(input);
      sharded.traces.push(trace);
      continue;
    }
    let mut start = 0;
    for &height in &heights {
      let end = (start + height).min(rows[index]);
      let from = if overlap && start != 0 { start - 1 } else { start };
      let take = (end - from).min(height);
      sharded.traces.push(piece(&trace, from..from + take, height));
      sharded.inputs.push(input.clone());
      start = end;
    }
    sharded.split.push((index, heights));
  }
  sharded
}

#[test]
fn sharded_function_circuits_prove_and_verify() {
  let plan = plan();
  let f = |value| Bn254.from_u64(value);
  let args = [f(129), f(0)];
  let record = plan.program().execute(ENTRY, args.to_vec()).unwrap();
  let public = plan.public_args(&record, ENTRY, &args).unwrap();
  let claim = plan.public_claim(ENTRY, &public, &record.output).unwrap();
  let traces =
    Compiler::new(&plan).unwrap().generate(&record, ENTRY, &args).unwrap();
  let srs = Arc::new(Srs::unsafe_dev_setup(1 << 10, b"aiur-kzg-sharding-test"));

  let mut proved_split = false;
  for pieces in [2, 3] {
    let sharded = shard(&plan, &record, traces.clone(), pieces, false);
    assert!(!sharded.split.is_empty(), "no circuit was split");
    proved_split = true;
    eprintln!("pieces {pieces}: split {:?}", sharded.split);
    let (system, key) =
      System::new(KzgConfig::new(srs.clone(), 8), sharded.inputs.clone());
    let witness = SystemWitness::from_stage_1(sharded.traces.clone(), &system);
    let proof = system.prove(&key, &claim, witness);
    system.verify(&claim, &proof).unwrap();
    let mut changed = claim.clone();
    *changed.last_mut().unwrap() += Bn254.one();
    assert!(system.verify(&changed, &proof).is_err());
  }
  assert!(proved_split);

  // A row repeated across a shard boundary leaves its lookups unbalanced.
  let sharded = shard(&plan, &record, traces, 2, true);
  let (system, key) =
    System::new(KzgConfig::new(srs, 8), sharded.inputs.clone());
  let witness = SystemWitness::from_stage_1(sharded.traces, &system);
  let proved = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    system.prove(&key, &claim, witness)
  }));
  match proved {
    Ok(proof) => {
      let verdict = system.verify(&claim, &proof);
      eprintln!("overlapping shards: verifier says {verdict:?}");
      assert!(verdict.is_err());
    },
    Err(_) => eprintln!("overlapping shards: prover refused"),
  }
}

#[test]
fn decomposition_rounds_only_the_last_piece() {
  assert_eq!(decompose(1_310_720, 3), [1 << 20, 1 << 18]);
  assert_eq!(decompose(1_250_000, 3), [1 << 20, 1 << 17, 1 << 17]);
  assert_eq!(decompose(5, 2), [4, 1]);
  assert_eq!(decompose(7, 2), [4, 4]);
  assert_eq!(decompose(8, 3), [8]);
  assert_eq!(decompose(0, 3), Vec::<usize>::new());
}
