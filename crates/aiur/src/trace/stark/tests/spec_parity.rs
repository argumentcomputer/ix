//! Cross-language parity tests between `crates/aiur/src/trace/stark.rs` +
//! `lookup_groups::retune` and the formalized Lean reference spec in
//! `Aiur/Aiur/MultiStarkSpec.lean` (`WS 2B-2`).
use super::*;
use crate::trace::stark::tests::depth::depth_fixture;
use multi_stark::{
  eval::VarValues,
  expr::Expr,
  lookup::{Lookup, LookupValues},
  p3_field::{Field, PrimeCharacteristicRing},
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, System, SystemWitness},
  types::{
    CommitmentParameters, ExtVal, FriParameters, GoldilocksBlake3Config,
  },
};

#[derive(Debug, PartialEq, Eq)]
struct SpecSummary {
  name: &'static str,
  stage1_width: usize,
  stage2_width: usize,
  preprocessed_width: usize,
  preprocessed_height: usize,
  lookups: usize,
  lookup_group_size: usize,
  quotient_degree: usize,
  constraint_count: usize,
  max_constraint_degree: usize,
}

/// Exact table verified simultaneously by `Aiur/AiurTests/MultiStarkSpec.lean`
/// (`expectedDepthFixtureSummaries`) for `crates/aiur/tests/fixtures/depth.ixa`
/// at `log_blowup = 1`, `segmented = true`.
const EXPECTED_DEPTH_FIXTURE: &[SpecSummary] = &[
  SpecSummary {
    name: "Depth::run",
    stage1_width: 7,
    stage2_width: 6,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 3,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 9,
    max_constraint_degree: 2,
  },
  SpecSummary {
    name: "Depth::even",
    stage1_width: 7,
    stage2_width: 2,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 11,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "Depth::odd",
    stage1_width: 7,
    stage2_width: 2,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 11,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "Depth::fib",
    stage1_width: 14,
    stage2_width: 8,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 7,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 24,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "Depth::loop",
    stage1_width: 5,
    stage2_width: 4,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 7,
    max_constraint_degree: 2,
  },
  SpecSummary {
    name: "Depth::top",
    stage1_width: 4,
    stage2_width: 4,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 7,
    max_constraint_degree: 2,
  },
  SpecSummary {
    name: "Depth::owned",
    stage1_width: 6,
    stage2_width: 2,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 10,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "Depth::link",
    stage1_width: 4,
    stage2_width: 4,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 2,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 7,
    max_constraint_degree: 2,
  },
  SpecSummary {
    name: "<table:Depth::range16_inputs>",
    stage1_width: 1,
    stage2_width: 2,
    preprocessed_width: 2,
    preprocessed_height: 65536,
    lookups: 1,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 2,
    max_constraint_degree: 2,
  },
  SpecSummary {
    name: "<table:Depth::range8_inputs>",
    stage1_width: 1,
    stage2_width: 2,
    preprocessed_width: 2,
    preprocessed_height: 256,
    lookups: 1,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 2,
    max_constraint_degree: 2,
  },
];

#[test]
fn depth_fixture_matches_lean_multistark_spec() {
  let (program, trace) = depth_fixture();
  let plan = TracePlan::new(&program, trace).unwrap();
  let backend = Backend::for_batch_verification(&plan, parameters()).unwrap();
  let stats = backend.statistics();
  assert_eq!(stats.len(), EXPECTED_DEPTH_FIXTURE.len());
  for ((s, c), expected) in stats
    .iter()
    .zip(&backend.system.circuits)
    .zip(EXPECTED_DEPTH_FIXTURE)
  {
    assert_eq!(
      (
        s.name.as_str(),
        s.stage1_width,
        s.stage2_width,
        s.preprocessed_width,
        s.preprocessed_height,
        s.lookups,
        s.lookup_group_size,
        s.quotient_degree,
        c.constraint_count,
        c.max_constraint_degree,
      ),
      (
        expected.name,
        expected.stage1_width,
        expected.stage2_width,
        expected.preprocessed_width,
        expected.preprocessed_height,
        expected.lookups,
        expected.lookup_group_size,
        expected.quotient_degree,
        expected.constraint_count,
        expected.max_constraint_degree,
      ),
      "Rust/Lean MultiStarkSpec mismatch on circuit {}",
      s.name
    );
  }
}

/// Numerical witness check of `Aiur.MultiStarkSpec.retune_logup_equiv`:
/// `lookup_groups::retune` (including balanced reordering of mixed-degree
/// lookups and `group > 1` chunking) leaves the exact `Fp2` LogUp total sum
/// bit-for-bit identical to the ungrouped `group = 1` rational sum.
#[test]
fn retune_preserves_exact_logup_rational_sum_and_matches_lean_degrees() {
  let make_config = || {
    GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: 2, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 2,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    )
  };
  let lin = |i: u32| Lookup::push(Expr::main(0), vec![Expr::main(i)]);
  let quad =
    |i: u32| Lookup::push(Expr::main(0), vec![Expr::main(i) * Expr::main(i)]);
  let build_inputs = || {
    vec![
      CircuitInputs {
        main_width: 4,
        lookups: (0..14).map(|i| quad(1 + (i % 3))).collect(),
        ..Default::default()
      },
      CircuitInputs {
        main_width: 4,
        lookups: vec![lin(1), quad(2), lin(3)],
        ..Default::default()
      },
      CircuitInputs {
        main_width: 2,
        lookups: (0..11).map(|_| lin(1)).collect(),
        ..Default::default()
      },
      CircuitInputs {
        main_width: 2,
        lookups: (0..28).map(|_| lin(1)).collect(),
        ..Default::default()
      },
    ]
  };
  let (ungrouped, _) = System::new(make_config(), build_inputs());
  let (mut retuned, _) = System::new(make_config(), build_inputs());
  for circuit in &mut retuned.circuits {
    lookup_groups::retune(circuit, 4, 2);
  }
  // Exact metadata parity with `AiurMultiStarkSpecTests.checkMixedDegreeRetune`.
  let expected_meta = [
    (2usize, 4usize, 14usize, 14usize, 5usize),
    (2, 2, 4, 4, 3),
    (2, 2, 12, 12, 3),
    (4, 4, 14, 14, 5),
  ];
  for (c, (g, q, s2, cc, md)) in retuned.circuits.iter().zip(expected_meta) {
    assert_eq!(
      (
        c.lookup_group_size,
        c.quotient_degree(),
        c.stage_2_width,
        c.constraint_count,
        c.max_constraint_degree,
      ),
      (g, q, s2, cc, md)
    );
  }
  // Balanced reordering on circuit 1 matches Lean `[(1, 1), (1, 1), (1, 2)]`.
  let degs1: Vec<(u32, u32)> = retuned.circuits[1]
    .graph
    .lookups
    .iter()
    .map(|l| {
      let md = retuned.circuits[1].graph.degrees[l.multiplicity.index()];
      let pd = l
        .args
        .iter()
        .map(|&a| retuned.circuits[1].graph.degrees[a.index()])
        .max()
        .unwrap_or(0);
      (md, pd)
    })
    .collect();
  assert_eq!(degs1, vec![(1, 1), (1, 1), (1, 2)]);

  // Verify exact LogUp rational sum equivalence in Fp2 before vs after retune
  // on concrete multi-row traces over multiple (alpha, beta) pairs.
  let traces = vec![
    RowMajorMatrix::new(
      [3, 5, 7, 11, 2, 13, 17, 19].map(Val::from_u64).to_vec(),
      4,
    ),
    RowMajorMatrix::new(
      [4, 23, 29, 31, 6, 37, 41, 43].map(Val::from_u64).to_vec(),
      4,
    ),
    RowMajorMatrix::new([5, 47, 8, 53].map(Val::from_u64).to_vec(), 2),
    RowMajorMatrix::new([9, 59, 12, 61].map(Val::from_u64).to_vec(), 2),
  ];
  let w_ungrouped = SystemWitness::from_stage_1(traces.clone(), &ungrouped);
  let w_retuned = SystemWitness::from_stage_1(traces.clone(), &retuned);
  let g_ungrouped: Vec<_> =
    ungrouped.circuits.iter().map(|c| c.lookup_group_size).collect();
  let g_retuned: Vec<_> =
    retuned.circuits.iter().map(|c| c.lookup_group_size).collect();
  for (a, b) in [(1000000007u64, 1000000009u64), (42424242, 987654321)] {
    let alpha = ExtVal::from_u64(a);
    let beta = ExtVal::from_u64(b);
    let (_, sums_ungrouped) = LookupValues::stage_2_traces(
      &w_ungrouped.lookups,
      &g_ungrouped,
      alpha,
      &beta,
      ExtVal::ZERO,
    );
    let (_, sums_retuned) = LookupValues::stage_2_traces(
      &w_retuned.lookups,
      &g_retuned,
      alpha,
      &beta,
      ExtVal::ZERO,
    );
    assert_eq!(sums_ungrouped, sums_retuned);
    // Cross-check each circuit's running accumulator against the direct
    // ungrouped rational sum ∑_row ∑_slot m / (β + ∑_k γ^k · arg_k),
    // matching `Aiur.MultiStarkSpec.fingerprint` and `multi_stark/src/lookup.rs`.
    let mut direct_running = Vec::with_capacity(traces.len());
    let mut running = ExtVal::ZERO;
    for (circuit, matrix) in ungrouped.circuits.iter().zip(&traces) {
      let mut total = ExtVal::ZERO;
      for r in 0..matrix.height() {
        let row = &matrix.values[r * matrix.width..(r + 1) * matrix.width];
        let view = VarValues {
          main: [row, row],
          preprocessed: [&[], &[]],
          stage2: [&[], &[]],
          publics: &[],
          is_first_row: Val::ZERO,
          is_last_row: Val::ZERO,
          is_transition: Val::ONE,
        };
        let mut buf = vec![];
        circuit.graph.sweep_lookup_prefix(&view, &mut buf);
        for lv in circuit.graph.lookup_values(&buf) {
          let mut fp = ExtVal::ZERO;
          let mut pow = ExtVal::ONE;
          for &arg in &lv.args {
            fp += pow * ExtVal::from(arg);
            pow *= beta;
          }
          total += ExtVal::from(lv.multiplicity) * (alpha + fp).inverse();
        }
      }
      running += total;
      direct_running.push(running);
    }
    assert_eq!(sums_retuned, direct_running);
  }
}

/// End-to-end `N6b` test for typed `ptr_eq`:
/// - `Instruction::PtrEq` binary artifact round-trip (tag 14),
/// - bytecode dead-code elimination + copy-prop + fast dispatch execution,
/// - Multi-STARK proof & verification of the exact 2-branch `Choose`/`Failure`
///   gadget emitted by `Optimized/Compile.lean` & `Trace/Compile.lean`,
/// - rejection of forged wrong `ptr_eq` claims.
#[test]
fn ptr_eq_bytecode_round_trips_and_proves_end_to_end() {
  let sub = |a: Json, b: Json| json!({"sub": [a, b]});
  let mul = |a: Json, b: Json| json!({"mul": [a, b]});
  let add = |a: Json, b: Json| json!({"add": [a, b]});
  let p = Val::ORDER_U64;
  // Function `cmp(x, y) -> Field`:
  //   let p = &x; let q = &y; ptr_eq(p, q)
  // Witnesses:
  //   0: input x, 1: input y, 2: output (= s_eq),
  //   3: p = &x, 4: q = &y,
  //   5: s_eq (p == q), 6: s_neq (p != q), 7: inv ((p - q)^-1 in s_neq).
  let raw_program: Program = serde_json::from_value(json!({
    "version": 2,
    "modulus": p,
    "enums": [],
    "tables": [],
    "maps": [],
    "functions": [{
      "name": "cmp",
      "params": [f(), f()],
      "result": f(),
      "registers": 6,
      "code": [
        {"op": "store", "type": f(), "value": [0], "dest": 2},
        {"op": "store", "type": f(), "value": [1], "dest": 3},
        {"op": "ptr_eq", "dest": 4, "left": 2, "right": 3},
        {"op": "ptr_eq", "dest": 5, "left": 2, "right": 2},
        {"op": "ret", "value": [4]}
      ]
    }],
    "entries": [{
      "name": "cmp",
      "function": 0,
      "inputs": [f(), f()],
      "output": f()
    }]
  }))
  .unwrap();

  let trace = activate(raw_artifact(json!({
    "version": 1,
    "modulus": p,
    "functions": [{
      "name": "cmp",
      "chip": "cmp",
      "witnesses": 8,
      "inputs": [0, 1],
      "output": [2],
      "steps": [
        step(json!({"op": "store", "type": f(), "values": [v(0)], "dest": 3})),
        step(json!({"op": "store", "type": f(), "values": [v(1)], "dest": 4})),
        step(json!({"op": "choose", "dest": [5, 6], "tests": [[sub(v(3), v(4))], []]})),
        {"guard": v(6), "action": {"op": "failure", "dest": [7], "differences": [sub(v(3), v(4))]}},
        step(json!({"op": "assign", "dest": [2], "values": [v(5)]}))
      ],
      "writes": writes(8)
    }],
    "chips": [{
      "name": "cmp",
      "width": 8,
      "inputs": [0, 1],
      "output": [v(2)],
      "constraints": [
        mul(v(5), sub(v(5), k(1))),
        mul(v(6), sub(v(6), k(1))),
        mul(v(5), v(6)),
        sub(add(v(5), v(6)), k(1)),
        mul(v(5), sub(v(3), v(4))),
        mul(v(6), sub(mul(sub(v(3), v(4)), v(7)), k(1))),
        sub(v(2), v(5))
      ],
      "sends": [],
      "memory": [
        {"type": f(), "address": v(3), "values": [v(0)], "enable": k(1)},
        {"type": f(), "address": v(4), "values": [v(1)], "enable": k(1)}
      ]
    }]
  })));

  let pkg = crate::artifact::Package {
    program: raw_program.clone(),
    trace: Some(trace.clone()),
  };
  let bytes = pkg.encode();
  let decoded = crate::artifact::Package::decode(&bytes).unwrap();
  assert_eq!(decoded, pkg);

  let checked = decoded.program.check_field::<Val>().unwrap();
  let plan = TracePlan::new(&checked, decoded.trace.unwrap()).unwrap();
  let backend = Backend::for_batch_verification(&plan, parameters()).unwrap();
  let key =
    VerifyingKey::from_bytes(&backend.verifying_key_bytes().unwrap()).unwrap();

  let g = Val::from_u64;

  // Case 1: equal values -> interned to identical ROM address -> ptr_eq = 1.
  let rec_eq = checked.execute("cmp", vec![g(42), g(42)]).unwrap();
  assert_eq!(rec_eq.output, vec![g(1)]);
  let w_eq = backend.generate(&rec_eq, "cmp", &[g(42), g(42)]).unwrap();
  let proof_eq = backend
    .prove_batch(
      "cmp",
      &[g(42), g(42)],
      &[g(1)],
      w_eq,
      1,
      multi_stark::batch::Retention::Regenerate,
    )
    .unwrap();
  key
    .verify(&[backend.claim("cmp", &[g(42), g(42)], &[g(1)]).unwrap()], &proof_eq)
    .unwrap();
  assert!(
    key
      .verify(
        &[backend.claim("cmp", &[g(42), g(42)], &[g(0)]).unwrap()],
        &proof_eq
      )
      .is_err(),
    "forged ptr_eq=0 on equal pointers must be rejected"
  );

  // Case 2: distinct values -> distinct ROM addresses -> ptr_eq = 0.
  let rec_ne = checked.execute("cmp", vec![g(42), g(43)]).unwrap();
  assert_eq!(rec_ne.output, vec![g(0)]);
  let w_ne = backend.generate(&rec_ne, "cmp", &[g(42), g(43)]).unwrap();
  let proof_ne = backend
    .prove_batch(
      "cmp",
      &[g(42), g(43)],
      &[g(0)],
      w_ne,
      1,
      multi_stark::batch::Retention::Regenerate,
    )
    .unwrap();
  key
    .verify(&[backend.claim("cmp", &[g(42), g(43)], &[g(0)]).unwrap()], &proof_ne)
    .unwrap();
  assert!(
    key
      .verify(
        &[backend.claim("cmp", &[g(42), g(43)], &[g(1)]).unwrap()],
        &proof_ne
      )
      .is_err(),
    "forged ptr_eq=1 on distinct pointers must be rejected"
  );
}
