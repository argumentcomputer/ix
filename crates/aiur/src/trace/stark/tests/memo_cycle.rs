//! The memo-cycle soundness gap, closed. `fn loop(x: Field) -> Field {
//! loop(x) }` never returns. Without the depth pass, one forged row claiming
//! `loop(0) = 42` with provide multiplicity 2 paid for its own self-call and
//! for the public claim, and the STARK verified (Track A finding A0.1, job
//! `depth-1`).
//!
//! Under the depth pass (Track A, H1) `loop` is recursive: its row provides
//! `loop(x, d)` and its self-call is an exact slot demanding `loop(x, d - 1)`.
//! The forged row's demand never matches its own provide, for any depth word,
//! multiplicity or claimed result; a cycle through more rows would need
//! `p / 2^24` of them, beyond the verifiers' row bound
//! ([`MAX_BATCH_ROWS`]). The circuit is the one the Lean exporter emits for
//! `Depth::loop` in `Aiur/Examples/Depth.lean`.
use super::*;
use multi_stark::batch::Retention;

const LOOP: &str = "Depth::loop";

/// A stage-one witness with only `loop` rows `(x, result, d, m)`: the other
/// function circuits are empty and the fixed tables unused.
fn forged_traces(
  backend: &Backend<'_, '_>,
  rows: &[(u64, u64, u64, u64)],
) -> Vec<RowMajorMatrix<Val>> {
  let chip =
    backend.plan.artifact.chips.iter().find(|c| c.name == LOOP).unwrap();
  // Columns: x, the self-call's result (also the output), d, activation.
  let [x, d] = chip.inputs[..] else { panic!("loop takes x and d") };
  let Polynomial::Var(out) = chip.output[0] else { panic!("loop output") };
  assert_eq!(chip.depth.column, Some(d));
  assert_eq!(chip.width, 4);
  let ci = backend.names.iter().position(|n| n == LOOP).unwrap();
  backend
    .system
    .circuits
    .iter()
    .enumerate()
    .map(|(i, circuit)| {
      let width = circuit.main_width;
      if i == ci {
        let mut values = vec![];
        for &(x_value, result, depth, m) in rows {
          let mut row = vec![Val::ZERO; width];
          row[x] = Val::from_u64(x_value);
          row[out] = Val::from_u64(result);
          row[d] = Val::from_u64(depth);
          row[chip.activation] = Val::ONE;
          row[chip.width] = Val::from_u64(m);
          values.extend(row);
        }
        values.resize(rows.len().next_power_of_two() * width, Val::ZERO);
        RowMajorMatrix::new(values, width)
      } else {
        let height = circuit.preprocessed_height;
        RowMajorMatrix::new(Val::zero_vec(height * width), width)
      }
    })
    .collect()
}

fn prove(
  backend: &Backend<'_, '_>,
  rows: &[(u64, u64, u64, u64)],
  depth: u64,
  result: u64,
) -> Proof {
  let claim = backend.claim(LOOP, &[0, depth], &[result]).unwrap();
  let witness =
    SystemWitness::from_stage_1(forged_traces(backend, rows), &backend.system);
  backend.system.prove(&backend.key, &claim, witness)
}

#[test]
fn cyclic_memo_row_no_longer_forges_a_nonterminating_call() {
  let (program, artifact) = super::depth::depth_fixture();
  // The honest executor refuses: the query is still in progress when it
  // recurses.
  let refused = program.execute(LOOP, vec![0]).unwrap_err();
  assert!(refused.message.contains("already being evaluated"), "{refused}");
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  // A recursive entry's claim carries a depth word.
  assert!(backend.claim(LOOP, &[0], &[42]).is_err());

  // The former forgery: one row, provide multiplicity 2, for every claimed
  // result and depth word. Its self-call demands `loop(0, d - 1)`, which no
  // row provides.
  for result in [42, 7] {
    for depth in [0, 1, 5, Val::ORDER_U64 - 1] {
      let forged = prove(&backend, &[(0, result, depth, 2)], depth, result);
      assert!(
        backend.verify(LOOP, &[0, depth], &[result], &forged).is_err(),
        "loop(0) = {result} at depth {depth}"
      );
    }
  }
  // Rows chained by depth cannot close the cycle either: the lowest row's
  // self-call still demands one level below it.
  let chain = [(0, 42, 3, 1), (0, 42, 2, 1), (0, 42, 1, 1), (0, 42, 0, 1)];
  let forged = prove(&backend, &chain, 3, 42);
  assert!(backend.verify(LOOP, &[0, 3], &[42], &forged).is_err());
}

#[test]
fn batch_verifier_rejects_the_cyclic_memo_row() {
  let (program, artifact) = super::depth::depth_fixture();
  let plan = TracePlan::new(&program, artifact).unwrap();
  let backend = Backend::for_batch(&plan, parameters()).unwrap();
  for (rows, shards) in [(1, 1), (4, 2)] {
    let forged: Vec<_> = (0..rows).map(|_| (0, 42, 5, 2)).collect();
    let error = backend
      .prove_batch_stage_1(
        LOOP,
        &[0, 5],
        &[42],
        forged_traces(&backend, &forged),
        rows / shards,
        Retention::Retain,
      )
      .unwrap_err();
    assert!(error.contains("verification failed"), "{error}");
  }
}
