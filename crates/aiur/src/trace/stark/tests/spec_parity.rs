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
  for ((s, c), expected) in
    stats.iter().zip(&backend.system.circuits).zip(EXPECTED_DEPTH_FIXTURE)
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
    .verify(
      &[backend.claim("cmp", &[g(42), g(42)], &[g(1)]).unwrap()],
      &proof_eq,
    )
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
    .verify(
      &[backend.claim("cmp", &[g(42), g(43)], &[g(0)]).unwrap()],
      &proof_ne,
    )
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

/// Exact `C6` vectorized ROM summaries verified simultaneously by
/// `Aiur/AiurTests/MultiStarkSpec.lean` (`expectedVectorizedRomSummaries`)
/// for widths `[1, 3, 5, 13]` at `blowup = 4` (`log_blowup = 2`), `segmented = true`.
const EXPECTED_VECTORIZED_ROM_SUMMARIES: &[SpecSummary] = &[
  SpecSummary {
    name: "<ROM:1>",
    stage1_width: 25,
    stage2_width: 10,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 10,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 35,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "<ROM:3>",
    stage1_width: 41,
    stage2_width: 10,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 10,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 35,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "<ROM:5>",
    stage1_width: 29,
    stage2_width: 6,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 6,
    lookup_group_size: 2,
    quotient_degree: 2,
    constraint_count: 19,
    max_constraint_degree: 3,
  },
  SpecSummary {
    name: "<ROM:13>",
    stage1_width: 16,
    stage2_width: 6,
    preprocessed_width: 0,
    preprocessed_height: 0,
    lookups: 3,
    lookup_group_size: 1,
    quotient_degree: 1,
    constraint_count: 10,
    max_constraint_degree: 2,
  },
];

/// Build a multi-width ROM program (`driver`, `store_local`, `store_owned`)
/// that exercises widths `[1, 3, 5, 13]` with `local_n` calls to `store_local`
/// and `owned_n` calls to `store_owned` (allowing partitioned streaming across
/// non-`K`-aligned `MEMSEG` intervals).
fn multi_width_rom_fixture(
  local_n: usize,
  owned_n: usize,
) -> (CheckedProgram<NativeField<Val>>, TraceArtifact) {
  let p = Val::ORDER_U64;
  let tup = |w: usize| json!({"kind": "tuple", "items": vec![f(); w]});
  let widths = [1usize, 3, 5, 13];
  let unit = json!({"kind": "tuple", "items": []});
  let store_fn_json = |name: &str| {
    // param 0 = x; reg 1 = 1; reg 2 = x+1; reg 3 = x+2;
    // regs 4..8 = ptrs for widths 1, 3, 5, 13; regs 8..11 = loaded width-3 tuple.
    let mut code = vec![
      json!({"op": "literal", "dest": 1, "value": 1}),
      json!({"op": "binary", "operator": "add", "left": 0, "right": 1, "dest": 2}),
      json!({"op": "binary", "operator": "add", "left": 2, "right": 1, "dest": 3}),
    ];
    for (idx, &w) in widths.iter().enumerate() {
      let vals: Vec<usize> = (0..w)
        .map(|k| match k {
          1 => 2,
          2 => 3,
          _ => 0,
        })
        .collect();
      code.push(
        json!({"op": "store", "type": tup(w), "value": vals, "dest": 4 + idx}),
      );
    }
    code.push(
      json!({"op": "load", "type": tup(3), "pointer": 5, "dest": [8, 9, 10]}),
    );
    code.push(json!({"op": "ret", "value": []}));
    json!({
      "name": name,
      "params": [f()],
      "result": unit,
      "registers": 11,
      "code": code
    })
  };
  let store_trace_fn = |name: &str| {
    // witnesses: 0 = x, 1..5 = ptrs (1,3,5,13), 5..8 = loaded width-3 tuple
    let mut steps = Vec::new();
    for (idx, &w) in widths.iter().enumerate() {
      let vals: Vec<Json> = (0..w)
        .map(|j| match j {
          1 => json!({"add": [v(0), k(1)]}),
          2 => json!({"add": [v(0), k(2)]}),
          _ => v(0),
        })
        .collect();
      steps.push(step(
        json!({"op": "store", "type": tup(w), "values": vals, "dest": 1 + idx}),
      ));
    }
    steps.push(step(
      json!({"op": "load", "type": tup(3), "address": v(2), "dest": [5, 6, 7]}),
    ));
    json!({
      "name": name,
      "chip": name,
      "witnesses": 8,
      "inputs": [0],
      "output": [],
      "steps": steps,
      "writes": writes(8)
    })
  };
  let store_chip = |name: &str| {
    let mut memory = Vec::new();
    for (idx, &w) in widths.iter().enumerate() {
      let vals: Vec<Json> = (0..w)
        .map(|j| match j {
          1 => json!({"add": [v(0), k(1)]}),
          2 => json!({"add": [v(0), k(2)]}),
          _ => v(0),
        })
        .collect();
      memory.push(json!({"type": tup(w), "address": v(1 + idx), "values": vals, "enable": k(1)}));
    }
    memory.push(json!({
      "type": tup(3),
      "address": v(2),
      "values": [v(5), v(6), v(7)],
      "enable": k(1)
    }));
    json!({
      "name": name,
      "width": 8,
      "inputs": [0],
      "output": [],
      "constraints": [],
      "sends": [],
      "memory": memory
    })
  };

  // driver(seed): calls store_local(seed + i) for i in 0..local_n,
  // then store_owned(seed + 1000 + j) for j in 0..owned_n, returns seed.
  let mut driver_code = Vec::new();
  let mut driver_steps = Vec::new();
  let mut driver_sends = Vec::new();
  let mut next_reg = 1usize;
  for i in 0..local_n {
    let c_reg = next_reg;
    let arg_reg = next_reg + 1;
    next_reg += 2;
    driver_code
      .push(json!({"op": "literal", "dest": c_reg, "value": i as u64}));
    driver_code.push(json!({"op": "binary", "operator": "add", "left": 0, "right": c_reg, "dest": arg_reg}));
    driver_code.push(
      json!({"op": "call", "function": 1, "args": [arg_reg], "dest": []}),
    );
    let arg_expr = json!({"add": [v(0), k(i as u64)]});
    driver_steps.push(step(json!({
      "op": "call", "name": "store_local", "args": [arg_expr], "dest": []
    })));
    driver_sends.push(json!({
      "channel": "store_local",
      "args": [arg_expr],
      "result": [],
      "enable": k(1)
    }));
  }
  for j in 0..owned_n {
    let offset = 1000 + j;
    let c_reg = next_reg;
    let arg_reg = next_reg + 1;
    next_reg += 2;
    driver_code
      .push(json!({"op": "literal", "dest": c_reg, "value": offset as u64}));
    driver_code.push(json!({"op": "binary", "operator": "add", "left": 0, "right": c_reg, "dest": arg_reg}));
    driver_code.push(
      json!({"op": "call", "function": 2, "args": [arg_reg], "dest": []}),
    );
    let arg_expr = json!({"add": [v(0), k(offset as u64)]});
    driver_steps.push(step(json!({
      "op": "call", "name": "store_owned", "args": [arg_expr], "dest": []
    })));
    driver_sends.push(json!({
      "channel": "store_owned",
      "args": [arg_expr],
      "result": [],
      "enable": k(1)
    }));
  }
  driver_code.push(json!({"op": "ret", "value": [0]}));
  let driver_width = 1;

  let program: Program = serde_json::from_value(json!({
    "version": 2,
    "modulus": p,
    "enums": [],
    "tables": [],
    "maps": [],
    "functions": [
      {
        "name": "driver",
        "params": [f()],
        "result": f(),
        "registers": next_reg,
        "code": driver_code
      },
      store_fn_json("store_local"),
      store_fn_json("store_owned")
    ],
    "entries": [{
      "name": "driver",
      "function": 0,
      "inputs": [f()],
      "output": f()
    }]
  }))
  .unwrap();

  let artifact = activate(raw_artifact(json!({
    "version": 1,
    "modulus": p,
    "functions": [
      {
        "name": "driver",
        "chip": "driver",
        "witnesses": driver_width,
        "inputs": [0],
        "output": [0],
        "steps": driver_steps,
        "writes": writes(driver_width)
      },
      store_trace_fn("store_local"),
      store_trace_fn("store_owned")
    ],
    "chips": [
      {
        "name": "driver",
        "width": driver_width,
        "inputs": [0],
        "output": [v(0)],
        "constraints": [],
        "sends": driver_sends,
        "memory": []
      },
      store_chip("store_local"),
      store_chip("store_owned")
    ]
  })));

  (program.check_field::<Val>().unwrap(), artifact)
}

#[test]
fn vectorized_rom_matches_lean_multistark_spec_and_cuts_rom3_cells() {
  assert_eq!(rom_lanes(1), 8);
  assert_eq!(rom_lanes(3), 8);
  assert_eq!(rom_lanes(4), 8);
  assert_eq!(rom_lanes(5), 4);
  assert_eq!(rom_lanes(12), 4);
  assert_eq!(rom_lanes(13), 1);

  let (program, artifact) = multi_width_rom_fixture(8, 0);
  let plan = TracePlan::new(&program, artifact).unwrap();
  let scalar_backend = Backend::for_batch_verification_with_rom_layout(
    &plan,
    Parameters::DEFAULT,
    RomLayout::Scalar,
  )
  .unwrap();
  let vec_backend = Backend::for_batch_verification_with_rom_layout(
    &plan,
    Parameters::DEFAULT,
    RomLayout::Vectorized,
  )
  .unwrap();
  assert_eq!(scalar_backend.rom_layout(), RomLayout::Scalar);
  assert_eq!(vec_backend.rom_layout(), RomLayout::Vectorized);

  // Exact 10-field parity against `AiurMultiStarkSpecTests.expectedVectorizedRomSummaries`.
  let vec_stats = vec_backend.statistics();
  let rom_base = vec_backend.members.len() + vec_backend.tables.len();
  assert_eq!(
    vec_stats.len() - rom_base,
    EXPECTED_VECTORIZED_ROM_SUMMARIES.len()
  );
  for ((s, c), expected) in vec_stats[rom_base..]
    .iter()
    .zip(&vec_backend.system.circuits[rom_base..])
    .zip(EXPECTED_VECTORIZED_ROM_SUMMARIES)
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
      "C6 Rust/Lean MultiStarkSpec mismatch on {}",
      s.name
    );
  }

  // Verify `<ROM:3>` cell/RAM & `max_log` savings on an 8-entry execution.
  let record = program.execute("driver", vec![Val::from_u64(10)]).unwrap();
  assert_eq!(record.memory.width_cells(3).len(), 8);
  let scalar_rows = scalar_backend.execution_rows(&record);
  let vec_rows = vec_backend.execution_rows(&record);
  let rom3_idx = rom_base + 1;
  assert_eq!(scalar_rows[rom3_idx], 8);
  assert_eq!(vec_rows[rom3_idx], 1);
  // 8 rows -> 1 row cuts `max_log` by 3 (log2(8) = 3 -> log2(1) = 0).
  assert_eq!(scalar_rows[rom3_idx].ilog2() - vec_rows[rom3_idx].ilog2(), 3);

  let s_rom3 = &scalar_backend.statistics()[rom3_idx];
  let v_rom3 = &vec_stats[rom3_idx];
  let scalar_cells =
    (s_rom3.stage1_width + s_rom3.stage2_width + s_rom3.quotient_degree * 2)
      * scalar_rows[rom3_idx];
  let vec_cells =
    (v_rom3.stage1_width + v_rom3.stage2_width + v_rom3.quotient_degree * 2)
      * vec_rows[rom3_idx];
  assert_eq!(scalar_cells, 112);
  assert_eq!(vec_cells, 55);
  assert!(vec_cells * 2 < scalar_cells);
}

#[test]
fn vectorized_rom_proves_verifies_and_rejects_tampering() {
  let g = Val::from_u64;
  let params = Parameters {
    log_blowup: 2,
    num_queries: 110,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 0,
  };

  // 1. Partial-only row (n = 7), exact-full row (n = 8), and multi-row + partial tail (n = 17).
  for n in [7usize, 8, 17] {
    let (program, artifact) = multi_width_rom_fixture(n, 0);
    let plan = TracePlan::new(&program, artifact).unwrap();
    let record = program.execute("driver", vec![g(1)]).unwrap();
    assert_eq!(record.output, vec![g(1)]);

    // Standalone (non-segmented) proof + verify.
    let standalone =
      Backend::new_with_rom_layout(&plan, params, RomLayout::Vectorized)
        .unwrap();
    let witness = standalone.generate(&record, "driver", &[g(1)]).unwrap();
    let proof = standalone.prove("driver", &[g(1)], &[g(1)], witness).unwrap();
    standalone.verify("driver", &[g(1)], &[g(1)], &proof).unwrap();

    // Segmented multi-shard batch proof (max_rows = 2) + verify via VerifyingKey.
    let batch =
      Backend::for_batch_with_rom_layout(&plan, params, RomLayout::Vectorized)
        .unwrap();
    let witness_b = batch.generate(&record, "driver", &[g(1)]).unwrap();
    let batch_proof = batch
      .prove_batch(
        "driver",
        &[g(1)],
        &[g(1)],
        witness_b,
        2,
        multi_stark::batch::Retention::Regenerate,
      )
      .unwrap();
    let vk =
      VerifyingKey::from_bytes(&batch.verifying_key_bytes().unwrap()).unwrap();
    vk.verify(
      &[batch.claim("driver", &[g(1)], &[g(1)]).unwrap()],
      &batch_proof,
    )
    .unwrap();

    // Normalized fixed-shape proof with headroom padding rows.
    let rows = batch.execution_rows(&record);
    let log_heights = batch.normalized_log_heights(&rows, 1).unwrap();
    let (claim, norm_proof) = batch
      .prove_normalized("driver", &[g(1)], &[g(1)], record, &log_heights)
      .unwrap();
    vk.verify(&[claim], &norm_proof).unwrap();
  }

  // 2. Non-K-aligned multi-shard streaming (`[0, 10)` on shard 0 + `[10, 17)` on shard 1).
  let (stream_prog, stream_art) = multi_width_rom_fixture(10, 7);
  let stream_plan = TracePlan::new(&stream_prog, stream_art).unwrap();
  let stream_backend = Backend::for_batch_with_rom_layout(
    &stream_plan,
    params,
    RomLayout::Vectorized,
  )
  .unwrap();
  let stream_hints = stream_prog.prepare_hints(&[]).unwrap();
  let caller = stream_hints
    .execute_partition(
      Some(("driver", vec![g(5)])),
      crate::execute::Partition {
        function: 2,
        owned: vec![],
        memory_start: 0,
        memory_end: 100,
        heights: None,
      },
      None,
    )
    .unwrap();
  let owned_args: Vec<Vec<Val>> =
    (0..7).map(|j| vec![g(5 + 1000 + j)]).collect();
  let mut owner = stream_hints
    .execute_partition(
      None,
      crate::execute::Partition {
        function: 2,
        owned: owned_args.clone(),
        memory_start: 10,
        memory_end: 100,
        heights: None,
      },
      None,
    )
    .unwrap();
  for a in &owned_args {
    owner.absorb_deferred(2, a, 1).unwrap();
  }
  let mut intervals: Vec<_> = [
    stream_backend.record_shape(&caller).unwrap(),
    stream_backend.record_shape(&owner).unwrap(),
  ]
  .into_iter()
  .flat_map(|s| s.memory_intervals)
  .collect();
  intervals.sort_unstable();
  assert!(intervals.contains(&(3, 0, 10)));
  assert!(intervals.contains(&(3, 10, 17)));
  let shard_traces = [
    stream_backend.generate_stage_1(&caller, "driver", &[g(5)]).unwrap(),
    stream_backend.generate_record_stage_1(&owner).unwrap(),
  ];
  let streamed = stream_backend
    .prove_streamed_stage_1(
      "driver",
      &[g(5)],
      &[g(5)],
      StreamPlan {
        shards: 2,
        memory_intervals: intervals,
        retention: multi_stark::batch::Retention::Retain,
      },
      |i| Ok(shard_traces[i].clone()),
    )
    .unwrap();
  stream_backend.verify_batch("driver", &[g(5)], &[g(5)], &streamed).unwrap();

  // 3. Five negative tamper tests on vectorized `<ROM:3>` (`K = 8`, `stride = 5`, `n = 10` -> 2 rows: 8 + 2).
  let (t_prog, t_art) = multi_width_rom_fixture(10, 0);
  let t_plan = TracePlan::new(&t_prog, t_art).unwrap();
  let t_backend =
    Backend::for_batch_with_rom_layout(&t_plan, params, RomLayout::Vectorized)
      .unwrap();
  let t_rec = t_prog.execute("driver", vec![g(1)]).unwrap();
  let good_traces =
    t_backend.generate_stage_1(&t_rec, "driver", &[g(1)]).unwrap();
  let rom3_ci = t_backend.members.len() + t_backend.tables.len() + 1;
  let claim = t_backend.claim("driver", &[g(1)], &[g(1)]).unwrap();
  let good_msgs = || {
    let mut msgs = Vec::new();
    for &w in &[1usize, 3, 5, 13] {
      msgs.push(multi_stark::batch::BatchMessage::pull(
        batch::memseg_args(w, Val::ZERO).to_vec(),
      ));
      msgs.push(multi_stark::batch::BatchMessage::push(
        batch::memseg_args(w, Val::from_usize(10)).to_vec(),
      ));
    }
    msgs
  };
  let prove_and_verify = |traces: Vec<RowMajorMatrix<Val>>,
                          messages: Vec<
    multi_stark::batch::BatchMessage<GoldilocksBlake3Config>,
  >| {
    let witness = t_backend.witness_from_main(traces);
    let proof = t_backend.system.prove_batch(
      &t_backend.key,
      vec![multi_stark::batch::ShardInput {
        claims: vec![claim.clone()],
        witness,
      }],
      messages,
    );
    t_backend.verify_batch("driver", &[g(1)], &[g(1)], &proof)
  };
  // Sanity: untampered traces verify.
  prove_and_verify(good_traces.clone(), good_msgs()).unwrap();

  let stride = 3 + 2; // 5 cols per lane
  let width = 1 + 8 * stride; // 41
  assert_eq!(good_traces[rom3_ci].width, width);
  assert_eq!(good_traces[rom3_ci].height(), 2);

  // Tamper 1: non-prefix lane gap on row 0 (`active_1 = 0, count_1 = 0` while `active_2 = 1`).
  {
    let mut bad = good_traces.clone();
    let off = 1 + stride;
    bad[rom3_ci].values[off] = Val::ZERO;
    bad[rom3_ci].values[off + 1] = Val::ZERO;
    assert!(
      prove_and_verify(bad, good_msgs()).is_err(),
      "tamper 1 (non-prefix lane gap) must fail verification"
    );
  }

  // Tamper 2: inactive lane with nonzero count on partial row 1 (`active_7 = 0`, set `count_7 = 1`).
  {
    let mut bad = good_traces.clone();
    let row1 = width;
    let off = 1 + 7 * stride;
    assert_eq!(bad[rom3_ci].values[row1 + off + 1], Val::ZERO);
    bad[rom3_ci].values[row1 + off] = Val::ONE;
    assert!(
      prove_and_verify(bad, good_msgs()).is_err(),
      "tamper 2 (inactive lane with nonzero count) must fail verification"
    );
  }

  // Tamper 3: partial row 0 (`active_7 = 0, count_7 = 0`) followed by active row 1 (`active_0 = 1`).
  {
    let mut bad = good_traces.clone();
    let off = 1 + 7 * stride;
    bad[rom3_ci].values[off] = Val::ZERO;
    bad[rom3_ci].values[off + 1] = Val::ZERO;
    assert!(
      prove_and_verify(bad, good_msgs()).is_err(),
      "tamper 3 (partial row before active next row) must fail verification"
    );
  }

  // Tamper 4: bad `base_addr` stride across transition (row 1 `base_addr`: 8 -> 9).
  {
    let mut bad = good_traces.clone();
    bad[rom3_ci].values[width] = Val::from_u64(9);
    assert!(
      prove_and_verify(bad, good_msgs()).is_err(),
      "tamper 4 (bad base_addr stride) must fail verification"
    );
  }

  // Tamper 5a: wrong `MEMSEG` end boundary (`10 -> 11`) on `<ROM:3>`.
  {
    let mut bad_msgs = good_msgs();
    bad_msgs[3].args[2] = Val::from_u64(11);
    assert!(
      prove_and_verify(good_traces.clone(), bad_msgs).is_err(),
      "tamper 5a (wrong MEMSEG end boundary) must fail verification"
    );
  }

  // Tamper 5b: corrupted payload word in `<ROM:3>` row 0 lane 3.
  {
    let mut bad = good_traces.clone();
    let off = 1 + 3 * stride + 2;
    bad[rom3_ci].values[off] += Val::ONE;
    assert!(
      prove_and_verify(bad, good_msgs()).is_err(),
      "tamper 5b (corrupted ROM payload word) must fail verification"
    );
  }
}
