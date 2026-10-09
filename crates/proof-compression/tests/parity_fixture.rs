//! Pin the inner statement and fixed shape before building its circuit verifier.

#[path = "support/parity.rs"]
mod parity;

use std::collections::HashMap;

use multi_stark::eval::VarValues;
use multi_stark::eval::eval_expr;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_matrix::Matrix;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::system::CircuitInputs;
use multi_stark::system::System;
use multi_stark::system::SystemWitness;
use multi_stark::types::Val;
use parity::{Function, HEIGHT, LOG_HEIGHT, NUM_QUERIES};

/// Check the actual constraints and exact message multiset, independently
/// of the honest witness generator and the probabilistic proof protocol.
fn relations_hold(
  inputs: &[CircuitInputs<Val>],
  traces: &[RowMajorMatrix<Val>],
  claim: &[Val],
) -> bool {
  if inputs.len() != 2 || traces.len() != 2 {
    return false;
  }
  let mut balance = HashMap::from([(claim.to_vec(), Val::ONE)]);
  for (input, trace) in inputs.iter().zip(traces) {
    if trace.height() != HEIGHT || trace.width() != input.main_width {
      return false;
    }
    let prep = input.preprocessed.as_ref().unwrap();
    for row in 0..HEIGHT {
      let main = trace.row_slice(row).unwrap();
      let fixed = prep.row_slice(row).unwrap();
      let view = VarValues {
        main: [&main, &main],
        preprocessed: [&fixed, &fixed],
        stage2: [&[], &[]],
        publics: &[],
        is_first_row: Val::from_bool(row == 0),
        is_last_row: Val::from_bool(row + 1 == HEIGHT),
        is_transition: Val::from_bool(row + 1 < HEIGHT),
      };
      if input.constraints.iter().any(|e| eval_expr(e, &view) != Val::ZERO) {
        return false;
      }
      for lookup in &input.lookups {
        let args = lookup.args.iter().map(|e| eval_expr(e, &view)).collect();
        *balance.entry(args).or_insert(Val::ZERO) +=
          eval_expr(&lookup.multiplicity, &view);
      }
    }
  }
  balance.values().all(|&value| value == Val::ZERO)
}

#[test]
fn parity_fixture_all_inputs_and_dummy_rows() {
  let inputs = parity::circuit_inputs();
  for function in Function::ALL {
    for n in 0..HEIGHT {
      let traces = parity::traces(function, n);
      let claim = parity::claim(function, n, function.result(n));
      assert!(relations_hold(&inputs, &traces, &claim), "{function:?}({n})");
      let live_rows = traces
        .iter()
        .flat_map(|trace| trace.values.as_chunks::<2>().0)
        .filter(|row| row[0] == Val::ONE)
        .count();
      assert_eq!(live_rows, n + 1);
      let wrong = parity::claim(function, n, !function.result(n));
      assert!(!relations_hold(&inputs, &traces, &wrong));
    }
  }
}

#[test]
fn parity_fixture_binds_every_cell_including_dummies() {
  let inputs = parity::circuit_inputs();
  let claim = parity::claim(Function::Odd, 17, true);
  let mut traces = parity::traces(Function::Odd, 17);
  for circuit in 0..2 {
    for cell in 0..HEIGHT * 2 {
      let original = traces[circuit].values[cell];
      // Flip boolean cells so rejection must involve more than just
      // the boolean constraint (e.g. missing calls or dummy results).
      traces[circuit].values[cell] = Val::ONE - original;
      assert!(!relations_hold(&inputs, &traces, &claim), "{circuit}:{cell}");
      traces[circuit].values[cell] = original;
    }
  }
  // Flip the result along the WHOLE chain and the public result too:
  // the call messages still cancel, but the terminal base case rejects.
  for trace in &mut traces {
    for row in trace.values.as_chunks_mut::<2>().0 {
      if row[0] == Val::ONE {
        row[1] = Val::ONE - row[1];
      }
    }
  }
  assert!(!relations_hold(
    &inputs,
    &traces,
    &parity::claim(Function::Odd, 17, false)
  ));
}

#[test]
fn parity_fixture_proofs_share_one_key_and_shape() {
  let (system, key) = System::new(parity::config(), parity::circuit_inputs());
  assert!(system.preprocessed_commit.is_some());
  for function in Function::ALL {
    for n in [0, 1, 17, 100, 127] {
      let claim = parity::claim(function, n, function.result(n));
      let witness =
        SystemWitness::from_stage_1(parity::traces(function, n), &system);
      let proof = system.prove(&key, &claim, witness);
      // Even n=0 keeps the all-dummy other circuit active at 128 rows.
      assert_eq!(proof.active, vec![true; 2]);
      assert_eq!(proof.log_degrees, vec![LOG_HEIGHT; 2]);
      let fri = &proof.opening_proof;
      assert_eq!(fri.commit_phase_commits.len(), usize::from(LOG_HEIGHT));
      assert_eq!(fri.commit_pow_witnesses.len(), usize::from(LOG_HEIGHT));
      assert_eq!(fri.commit_phase_openings.len(), usize::from(LOG_HEIGHT));
      assert_eq!(fri.final_poly.len(), 1);
      // Main, stage 2, quotient, and preprocessing: each input batch
      // opens both matrices at each query, with fixed column widths.
      assert_eq!(fri.input_openings.len(), 4);
      for (opening, width) in fri.input_openings.iter().zip([2, 4, 2, 2]) {
        assert_eq!(opening.opened_values.len(), NUM_QUERIES);
        for query in &opening.opened_values {
          assert_eq!(query.len(), 2);
          assert!(query.iter().all(|row| row.len() == width));
        }
      }
      for opening in &fri.commit_phase_openings {
        assert_eq!(opening.log_arity, 1);
        assert_eq!(opening.sibling_values.len(), NUM_QUERIES);
        assert!(opening.sibling_values.iter().all(|row| row.len() == 1));
      }
      // Pruned sibling digest counts vary with query overlap. They
      // are deliberately not treated as a fixed wire-format shape.
      system.verify(&claim, &proof).unwrap();
      let wrong = parity::claim(function, n, !function.result(n));
      assert!(system.verify(&wrong, &proof).is_err());
      let mut resized = proof.clone();
      resized.log_degrees[0] -= 1;
      assert!(system.verify(&claim, &resized).is_err());
    }
  }
}

#[test]
fn parity_fixture_rejects_missing_recursive_call() {
  let inputs = parity::circuit_inputs();
  let claim = parity::claim(Function::Even, 18, true);
  let mut traces = parity::traces(Function::Even, 18);
  // Erase odd(17), leaving the rows individually valid, but an unmatched
  // call from even(18) and an unmatched return from even(16).
  traces[Function::Odd.index()].values[17 * 2..18 * 2].fill(Val::ZERO);
  assert!(!relations_hold(&inputs, &traces, &claim));
  let (system, key) = System::new(parity::config(), inputs);
  let proof =
    system.prove(&key, &claim, SystemWitness::from_stage_1(traces, &system));
  assert!(system.verify(&claim, &proof).is_err());
}

#[test]
#[should_panic(expected = "parity fixture supports arguments 0..128")]
fn parity_fixture_rejects_out_of_range_arguments() {
  parity::traces(Function::Even, HEIGHT);
}
