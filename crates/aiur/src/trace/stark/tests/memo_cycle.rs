//! The memo-cycle soundness gap. `fn loop(x: Field) -> Field { loop(x) }`
//! never returns, yet one forged row claiming `loop(0) = 42` with provide
//! multiplicity 2 pays for its own self-call and for the public claim. Nothing
//! in the verifier relates a call to its callees' calls, so the cyclic memo
//! table balances and the STARK verifies.
//!
//! Track A (H1: a depth word on recursive chips, `d_callee < d_caller`, plus a
//! row-count bound) must turn this acceptance into a rejection. When the depth
//! pass lands in the Rust lowering (A3), flip the final assertion: the same
//! forged row has no depth assignment, because its self-call would need
//! `d = d - 1 - gap`.
use super::*;

/// The physical chip the verified compiler emits for `loop` before activation:
/// column 0 is `x`, column 1 is the self-call's result, which is also the
/// output (`Aiur/AiurTests/Memo.lean` holds the same chip in the scalar model).
fn looping() -> (CheckedProgram, TraceArtifact) {
  let program: Program = serde_json::from_value(json!({
      "version":1,"modulus":Val::ORDER_U64,"enums":[],"maps":[],"tables":[],
      "functions":[{"name":"loop","params":[f()],"result":f(),"registers":2,"code":[
          {"op":"call","function":0,"args":[0],"dest":[1]},
          {"op":"ret","value":[1]}]}],
      "entries":[{"name":"loop","function":0,"inputs":[f()],"output":f()}]
  }))
  .unwrap();
  let artifact = raw_artifact(json!({
      "version":1,"modulus":Val::ORDER_U64,
      "functions":[{"name":"loop","chip":"loop","witnesses":2,"inputs":[0],"output":[1],
          "steps":[step(json!({"op":"call","name":"loop","args":[v(0)],"dest":[1]}))],
          "writes":writes(2)}],
      "chips":[{"name":"loop","width":2,"inputs":[0],"output":[v(1)],"constraints":[],
          "sends":[{"channel":"loop","args":[v(0)],"result":[1],"enable":k(1)}],
          "memory":[]}]
  }));
  (program.check().unwrap(), artifact)
}

/// Prove a one-row `loop` trace: columns `x`, the self-call result (also the
/// output), the activation selector and the provide multiplicity.
fn prove_row(backend: &Backend<'_, '_>, row: [u64; 4], claim: u64) -> Proof {
  let row = row.map(Val::from_u64).to_vec();
  let witness = SystemWitness::from_stage_1(
    vec![RowMajorMatrix::new(row, 4)],
    &backend.system,
  );
  backend.prove("loop", &[0], &[claim], witness).unwrap()
}

#[test]
fn cyclic_memo_row_forges_a_nonterminating_call() {
  let (program, artifact) = looping();
  // The honest executor refuses: the query is still in progress when it
  // recurses. That check is prover-side only.
  let refused = program.execute("loop", vec![0]).unwrap_err();
  assert!(refused.message.contains("already being evaluated"), "{refused}");

  let plan = TracePlan::new(&program, activate(artifact)).unwrap();
  let backend = Backend::new(&plan, parameters()).unwrap();
  assert_eq!(backend.system.circuits.len(), 1);
  // Unit provide weight is sound without acyclicity: the self-call and the
  // public claim are two demands, one provide does not balance them.
  let unit = prove_row(&backend, [0, 42, 1, 1], 42);
  assert!(backend.verify("loop", &[0], &[42], &unit).is_err());
  // A result the row does not provide does not balance either.
  let other = prove_row(&backend, [0, 42, 1, 2], 43);
  assert!(backend.verify("loop", &[0], &[43], &other).is_err());

  // The forgery. With φ the fingerprint of [CALL, loop, 0, 42]: the pull
  // contributes -2/(β-φ), the self push +1/(β-φ) and the public claim
  // +1/(β-φ). The sum is zero and the only multiplicity constraint,
  // (1 - activation)·m = 0, holds. Every verifier check passes.
  for result in [42, 7] {
    let forged = prove_row(&backend, [0, result, 1, 2], result);
    // Today's verifier ACCEPTS a claim that no evaluation of `loop` returns.
    // Track A (A3) must flip this to `is_err()`: under H1 the self-call is an
    // exact intra-SCC slot whose callee depth word is `d - 1`, so the row's
    // own provided message (depth `d`) never matches its demand (`d - 1`).
    backend.verify("loop", &[0], &[result], &forged).unwrap();
  }
}
