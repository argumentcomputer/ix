use super::*;
use ixby_flock::ixby::{
  control::ControlCapacities,
  decode::{InputCapacities, PrimitiveSet, ProgramCapacities},
  exec::{SemanticProfile, compile_exec_profile, expected_statement},
  machine::MachineCapacities,
};
use std::time::Instant;

#[path = "blake3_table_tests.rs"]
mod blake3_table_tests;

#[path = "basis_table_tests.rs"]
mod basis_table_tests;

#[path = "closure_tests.rs"]
mod closure_tests;

const CAPACITY: MachineCapacities = MachineCapacities {
  program: ProgramCapacities {
    bytes: 256,
    functions: 2,
    blocks: 4,
    operands: 2,
  },
  control: ControlCapacities { locals: 4, continuations: 2, arguments: 2 },
  input: InputCapacities { bytes: 64, values: 2 },
  output_bytes: 64,
  steps: 24,
};

fn setup() -> CompiledExec {
  compile_exec_profile(
    SemanticProfile::scalar(CAPACITY).unwrap(),
    CAPACITY,
    PrimitiveSet::scalar(),
  )
  .unwrap()
}

// Hand-authored first-order IxBy programs, with explicit canonical byte order.
// Guest construction is used by the proof producer only, never replay/setup.
fn program(branch: bool) -> Vec<u8> {
  let mut bytes = b"IXBY\0\0\0\0".to_vec();
  for value in [0u32, 0, 1, 1, 0, if branch { 3 } else { 1 }] {
    bytes.extend(value.to_le_bytes());
  }
  bytes.extend(1u32.to_le_bytes());
  if branch {
    bytes.extend([6, 0]); // branch (local 0), blocks 1 and 2
    for value in [0u32, 1, 2] {
      bytes.extend(value.to_le_bytes());
    }
    for value in [true, false] {
      bytes.extend(1u32.to_le_bytes());
      bytes.extend([1, 1, 0, u8::from(value)]); // ret literal Bool
    }
  } else {
    bytes.extend([1, 0]); // ret local 0
    bytes.extend(0u32.to_le_bytes());
  }
  bytes
}

fn input(value: bool) -> Vec<u8> {
  let mut bytes = b"IXBI\0\0\0\0".to_vec();
  bytes.extend(1u32.to_le_bytes());
  bytes.extend([0, 0, u8::from(value)]);
  bytes
}

fn output(value: bool) -> Vec<u8> {
  [b"IXBO\0\0\0\0".as_slice(), &[0, 0, u8::from(value)]].concat()
}

fn hash(tag: u8, parent: &[u8], bytes: &[u8]) -> [u8; 32] {
  let mut hash = blake3::Hasher::new();
  hash.update(b"IxBy/commit/v0\0");
  hash.update(&[tag]);
  hash.update(parent);
  hash.update(bytes);
  *hash.finalize().as_bytes()
}

fn prove(
  setup: &CompiledExec,
  branch: bool,
  value: bool,
) -> (ExecCommitmentsV0, Vec<u8>) {
  let code = program(branch);
  let input = input(value);
  let output = output(value);
  let program = hash(1, &setup.identities().profile, &code);
  let commitments = ExecCommitmentsV0 {
    program,
    input: hash(2, &program, &input),
    output: hash(3, &program, &output),
  };
  let expected = expected_statement(setup.profile(), &code, &input, &output);
  assert_eq!(
    expected.0,
    commitments.statement_digest(setup.identities().profile)
  );
  (commitments, setup.prove(expected, &code, &input).unwrap())
}

fn topology(w: &ExecReplayWitness<'_>) -> Vec<[u8; 32]> {
  let tape = w.transcript();
  let fold = w.matrix_accumulator();
  vec![
    w.binding().topology_digest(),
    *tape.shape_digest(),
    tape.chained_blake3().topology_digest(),
    tape.f128_algebra().topology_digest(),
    w.wiring().trace().topology_digest(),
    w.merged_pcs().trace().topology_digest(),
    w.multipoint_assist().trace().topology_digest(),
    w.inner_ligerito().trace().topology_digest(),
    *fold.shape_digest(),
    fold.chained_blake3().topology_digest(),
    fold.trace().topology_digest(),
    fold.circuit_structure_trace().topology_digest(),
    fold.jagged_trace().topology_digest(),
  ]
}

#[test]
#[ignore = "real generic Exec proofs and complete native replay; no terminal FFLONK proof"]
fn different_guests_have_identical_complete_replay_topology() {
  let setup = setup();
  let binding = compile_exec_binding(&setup).unwrap();
  let compiled = crate::compile_exec_replay(&setup).unwrap();
  let recompiled = crate::compile_exec_replay(&setup).unwrap();
  assert_eq!(compiled.identities(), recompiled.identities());
  assert_ne!(compiled.identities().digest(), [0; 32]);
  assert_eq!(compiled.binding(), &binding);
  assert!(std::ptr::eq(compiled.exec_setup(), &setup));
  let identity = setup.identities();
  let mut first_topology = None;
  for (branch, value) in [(false, false), (true, false), (true, true)] {
    let start = Instant::now();
    let (commitments, bytes) = prove(&setup, branch, value);
    let witness = compiled.replay(commitments, &bytes).unwrap();
    assert_eq!(witness.topology_digest(), compiled.identities().digest());
    assert_eq!(
      crate::compile_exec_replay(&setup).unwrap().identities(),
      compiled.identities()
    );
    eprintln!(
      "Exec replay branch={branch} value={value}: {:.3}s; {:?}",
      start.elapsed().as_secs_f64(),
      witness.census()
    );
    let actual = topology(&witness);
    if let Some(expected) = &first_topology {
      assert_eq!(&actual, expected);
    } else {
      first_topology = Some(actual);
    }
    assert_eq!(&binding, witness.binding());
    assert_eq!(setup.identities(), identity);
    assert_eq!(compile_exec_binding(&setup).unwrap(), binding);
    assert!(witness.census().matrix_accumulator.root_claims > 0);
    assert!(witness.census().inner_ligerito.path_digests > 0);
    // Strict rejection is at the generic Exec boundary, with no fallback.
    if !branch {
      for at in [0, 7, 8, 39, 40, bytes.len() / 2, bytes.len() - 1] {
        let mut bad = bytes.clone();
        bad[at] ^= 1;
        assert!(replay_exec(&setup, commitments, &bad).is_err());
      }
      for tag in [*b"IXFLK301", *b"IXFLK302"] {
        let mut bad = bytes.clone();
        bad[..8].copy_from_slice(&tag);
        assert!(replay_exec(&setup, commitments, &bad).is_err());
      }
      let mut bad = commitments;
      bad.input[0] ^= 1;
      assert!(replay_exec(&setup, bad, &bytes).is_err());
      let mut trailing = bytes.clone();
      trailing.push(0);
      assert!(replay_exec(&setup, commitments, &trailing).is_err());
      assert!(
        replay_exec(&setup, commitments, &bytes[..bytes.len() - 1]).is_err()
      );
    }
  }
}

#[test]
#[ignore = "matrix-free complete generic Exec R1CS/PLONK census, diagnostic roots still public"]
fn complete_generic_exec_constraint_census() {
  let setup = setup();
  let start = Instant::now();
  let (commitments, bytes) = prove(&setup, false, false);
  let witness = replay_exec(&setup, commitments, &bytes).unwrap();
  eprintln!(
    "Exec native replay ready in {:.3}s; starting complete matrix-free census",
    start.elapsed().as_secs_f64()
  );
  let census = crate::census_exec_replay_observed(&witness, move |progress| {
    eprintln!(
      "Exec census {:.3}s: {progress:?}; {}",
      start.elapsed().as_secs_f64(),
      memory_summary()
    );
  })
  .unwrap();
  eprintln!(
    "Exec complete root-conditional census in {:.3}s: {census:#?}",
    start.elapsed().as_secs_f64()
  );
  let capacity = ix_fflonk::plan_fflonk_capacity(&census.plonk).unwrap();
  eprintln!(
    "Exec root-conditional FFLONK capacity (not a proof): {capacity:#?}"
  );
  assert!(census.r1cs.census().constraints > 1_000_000);
  assert_eq!(census.r1cs.census().constraints_by_phase.len(), 7);
  assert!(census.root_conditional_public_scalar_bytes > 64);
}

fn memory_summary() -> String {
  std::fs::read_to_string("/proc/self/status")
    .map(|status| {
      status
        .lines()
        .filter(|line| {
          line.starts_with("VmHWM:") || line.starts_with("VmPeak:")
        })
        .collect::<Vec<_>>()
        .join("; ")
    })
    .unwrap_or_else(|_| "process memory counters unavailable".into())
}

#[test]
#[ignore = "real fixed interpreter tables: exact MLE differential and compressed-node census, not terminal proving"]
fn exact_fixed_root_tables_match_all_native_evaluators() {
  check_fixed_root_tables(None);
}

#[test]
#[ignore = "bounded positive/mixed cofactor-XOR experiments; failures are reported, no rewrite is adopted"]
fn fixed_root_table_davio_census() {
  check_fixed_root_tables(Some(false));
  check_fixed_root_tables(Some(true));
}

fn check_fixed_root_tables(rewrite_mode: Option<bool>) {
  use flock_prover::{
    circuit::SigmaAssertion,
    matrix_fold::{
      JaggedRowWeight, JaggedTable, Weight, bilinear, jagged_bilinear,
    },
  };
  use ix_stage4_trace::{
    F128FixedTableDavioLimitsV0, F128FixedTableLimitsV0, F128FixedTableNodeV0,
    F128FixedTableV0, F128MatrixSideV1,
  };

  fn point(bits: u32, seed: u64) -> Vec<F128> {
    (0..bits)
      .map(|i| {
        let i = u64::from(i);
        F128::new(
          seed.wrapping_mul(i + 17),
          (seed ^ i).wrapping_mul(0x9e3779b97f4a7c15),
        )
      })
      .collect()
  }
  fn evaluate(table: &F128FixedTableV0, point: &[F128]) -> F128 {
    assert_eq!(point.len(), table.order().len());
    let mut values = Vec::new();
    for node in table.nodes() {
      let value = match *node {
        F128FixedTableNodeV0::Constant(bytes) => F128::new(
          u64::from_le_bytes(bytes[..8].try_into().unwrap()),
          u64::from_le_bytes(bytes[8..].try_into().unwrap()),
        ),
        F128FixedTableNodeV0::Branch { coordinate, low, high } => {
          let low = values[low as usize];
          low + point[coordinate as usize] * (low + values[high as usize])
        },
        F128FixedTableNodeV0::Davio { coordinate, base, slope, complement } => {
          let factor = point[coordinate as usize]
            + if complement { F128::ONE } else { F128::ZERO };
          values[base as usize] + factor * values[slope as usize]
        },
      };
      values.push(value);
    }
    values[table.root() as usize]
  }
  fn report(name: &str, table: &F128FixedTableV0) {
    let constants = table
      .nodes()
      .iter()
      .filter(|node| matches!(node, F128FixedTableNodeV0::Constant(_)))
      .count();
    let constant = |index: u32| {
      matches!(table.nodes()[index as usize], F128FixedTableNodeV0::Constant(_))
    };
    let general_products = table
      .nodes()
      .iter()
      .filter(|node| match **node {
        F128FixedTableNodeV0::Constant(_) => false,
        F128FixedTableNodeV0::Branch { low, high, .. } => {
          !constant(low) || !constant(high)
        },
        F128FixedTableNodeV0::Davio { slope, .. } => !constant(slope),
      })
      .count();
    eprintln!(
      "fixed table {name}: {} sparse nonzeros, {} nodes ({constants} constants), {} coordinates, {general_products} general product sites",
      table.nonzero_entries(),
      table.nodes().len(),
      table.order().len()
    );
  }
  fn rewrite(
    name: &str,
    table: &F128FixedTableV0,
    mode: Option<bool>,
  ) -> Option<F128FixedTableV0> {
    let mixed = mode?;
    let start = Instant::now();
    let limits = F128FixedTableDavioLimitsV0 {
      working_nodes: 4_000_000,
      nodes: 2_000_000,
      xor_calls: 20_000_000,
    };
    let result = if mixed {
      table.mixed_davio(limits)
    } else {
      table.positive_davio(limits)
    };
    eprintln!(
      "Davio rewrite {name} mixed={mixed}: {:.3}s",
      start.elapsed().as_secs_f64()
    );
    match result {
      Ok(table) => {
        report(&format!("{name} Davio"), &table);
        Some(table)
      },
      Err(error) => {
        eprintln!("Davio rewrite {name} exceeded its prototype bound: {error}");
        None
      },
    }
  }

  let setup = setup();
  let replay = crate::compile_exec_replay(&setup).unwrap();
  let started = Instant::now();
  let tables = crate::compile_exec_root_tables(
    &replay,
    F128FixedTableLimitsV0 { entries: 64_000_000, nodes: 2_000_000 },
  )
  .unwrap();
  eprintln!(
    "exact root table compilation: {:.3}s, {} source entries, digest {:?}; {}",
    started.elapsed().as_secs_f64(),
    tables.source_entries(),
    tables.digest(),
    memory_summary()
  );
  assert!(std::ptr::eq(tables.exec_setup(), &setup));
  assert_eq!(tables.matrices().len(), 46);
  for (id, table) in tables.matrices() {
    let name = format!("Boolean {} {:?}", id.table, id.side);
    report(&name, table);
    let davio = rewrite(&name, table, rewrite_mode);
    let ty = &setup.verifier_shape().registry.boolean_types()
      [usize::try_from(id.table).unwrap()];
    let matrix = match id.side {
      F128MatrixSideV1::A => &ty.a_0,
      F128MatrixSideV1::B => &ty.b_0,
    };
    for seed in [7, 0x9821] {
      let row = point(id.variables, seed);
      let column = point(id.variables, seed + 11);
      let expected =
        bilinear(&Weight::eq(row.clone()), &Weight::eq(column.clone()), matrix);
      assert_eq!(
        evaluate(table, &[row.clone(), column.clone()].concat()),
        expected,
        "Boolean {} {:?}",
        id.table,
        id.side
      );
      if let Some(davio) = &davio {
        assert_eq!(
          evaluate(davio, &[row, column].concat()),
          expected,
          "{name} Davio"
        );
      }
    }
  }
  let (id, table) = tables.structure();
  report("structure", table);
  let davio = rewrite("structure", table, rewrite_mode);
  for seed in [19, 0xaf13] {
    let row = point(id.row_variables, seed);
    let column = point(id.column_variables, seed + 3);
    let expected = bilinear(
      &Weight::eq(row.clone()),
      &Weight::eq(column.clone()),
      &SigmaAssertion::matrix(&setup.verifier_shape().circuit),
    );
    assert_eq!(
      evaluate(table, &[row.clone(), column.clone()].concat()),
      expected,
      "structure"
    );
    if let Some(davio) = &davio {
      assert_eq!(
        evaluate(davio, &[row, column].concat()),
        expected,
        "structure Davio"
      );
    }
  }
  let (id, table) = tables.jagged();
  report("jagged", table);
  let davio = rewrite("jagged", table, rewrite_mode);
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    setup.pcs_params().m - 7,
  );
  let native = JaggedTable::from_params(&params);
  for seed in [27, 0xb517] {
    let row = point(id.row_variables, seed);
    let column = point(id.column_variables, seed + 9);
    let expected =
      jagged_bilinear(&JaggedRowWeight::eq(row.clone()), &column, &native);
    assert_eq!(
      evaluate(table, &[row.clone(), column.clone()].concat()),
      expected,
      "jagged"
    );
    if let Some(davio) = &davio {
      assert_eq!(
        evaluate(davio, &[row, column].concat()),
        expected,
        "jagged Davio"
      );
    }
  }
}

#[test]
#[ignore = "bounded setup-only variable-order experiment for the largest fixed tables; no proving"]
fn fixed_root_table_variable_order_census() {
  use ix_stage4_trace::{F128FixedTableLimitsV0, F128FixedTableV0};

  let setup = setup();
  for table in [0, 9] {
    let ty = &setup.verifier_shape().registry.boolean_types()[table];
    let bits = u32::try_from(ty.k_log).unwrap();
    let orders = [
      (
        "row-msb/col-msb",
        (0..bits).rev().chain((bits..2 * bits).rev()).collect::<Vec<_>>(),
      ),
      (
        "col-msb/row-msb",
        (bits..2 * bits).rev().chain((0..bits).rev()).collect(),
      ),
      ("row-lsb/col-lsb", (0..2 * bits).collect()),
      ("col-lsb/row-lsb", (bits..2 * bits).chain(0..bits).collect()),
      ("interleaved-lsb", (0..bits).flat_map(|i| [i, bits + i]).collect()),
      (
        "interleaved-msb",
        (0..bits).rev().flat_map(|i| [i, bits + i]).collect(),
      ),
    ];
    for (side, matrix) in [("A", &ty.a_0), ("B", &ty.b_0)] {
      for (name, order) in &orders {
        let start = Instant::now();
        let entries =
          matrix.rows.iter().enumerate().flat_map(|(row, columns)| {
            columns.iter().map(move |&column| {
              (row as u64 | ((column as u64) << bits), 1u128.to_le_bytes())
            })
          });
        let result = F128FixedTableV0::compile(
          order,
          entries,
          F128FixedTableLimitsV0 { entries: 32_000_000, nodes: 2_000_000 },
        );
        eprintln!(
          "fixed table {table} {side} {name}: nodes {:?}, {:.3}s",
          result.as_ref().map(|x| x.nodes().len()),
          start.elapsed().as_secs_f64()
        );
      }
    }
  }
}

#[test]
#[ignore = "materialized R1CS for one actual approved table only, not a closed Exec proof"]
fn actual_registry_table_materialization_matches_native() {
  use ark_bls12_381::Fr;
  use ark_ff::Field;
  use flock_prover::matrix_fold::{Weight, bilinear};
  use ix_stage4_trace::{F128FixedTableLimitsV0, F128FixedTableV0};
  use ix_terminal_circuit::{
    ConstraintPhase, R1csBuilder, alloc_f128_private,
    constrain_f128_fixed_table, enforce_f128_equal,
  };

  fn bytes(value: F128) -> [u8; 16] {
    (u128::from(value.lo) | (u128::from(value.hi) << 64)).to_le_bytes()
  }

  let setup = setup();
  let ty = &setup.verifier_shape().registry.boolean_types()[19];
  let bits = u32::try_from(ty.k_log).unwrap();
  let matrix = &ty.a_0;
  let entries = matrix.rows.iter().enumerate().flat_map(|(row, columns)| {
    columns.iter().map(move |&column| {
      (row as u64 | ((column as u64) << bits), 1u128.to_le_bytes())
    })
  });
  let order = (0..bits).rev().flat_map(|i| [i, bits + i]).collect::<Vec<_>>();
  let table = F128FixedTableV0::compile(
    &order,
    entries,
    F128FixedTableLimitsV0 { entries: 1000, nodes: 100 },
  )
  .unwrap();
  assert_eq!(table.nonzero_entries(), 768);
  assert_eq!(table.nodes().len(), 43);
  let mut first_shape = None;
  for seed in [0u64, 0x8913] {
    let point = (0..2 * bits)
      .map(|i| {
        F128::new(seed.wrapping_mul(u64::from(i) + 1), seed ^ u64::from(i))
      })
      .collect::<Vec<_>>();
    let expected = bytes(bilinear(
      &Weight::eq(point[..bits as usize].to_vec()),
      &Weight::eq(point[bits as usize..].to_vec()),
      matrix,
    ));
    let phase = ConstraintPhase::MatrixFold;
    let mut builder = R1csBuilder::new();
    let point = point
      .into_iter()
      .map(|x| alloc_f128_private(&mut builder, bytes(x), phase).unwrap())
      .collect::<Vec<_>>();
    let output =
      constrain_f128_fixed_table(&mut builder, &table, &point, phase).unwrap();
    assert_eq!(*output.value(), expected);
    let claimed = alloc_f128_private(&mut builder, expected, phase).unwrap();
    enforce_f128_equal(&mut builder, &output, &claimed, phase);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(r1cs.census().private_variables, 229_797);
    assert_eq!(r1cs.census().constraints, 230_853);
    assert_eq!(r1cs.census().nonzero_terms, 1_068_466);
    for &bit in &[claimed.bit_variables()[0], claimed.bit_variables()[127]] {
      let mut bad = witness.clone();
      bad.set(bit, Fr::ONE - bad.assignment()[bit.index() as usize]).unwrap();
      assert!(r1cs.check(&bad).is_err());
    }
    if let Some(digest) = first_shape {
      assert_eq!(r1cs.digest(), digest);
    } else {
      first_shape = Some(r1cs.digest());
    }
    eprintln!(
      "actual Boolean table 19 A materialized R1CS: {:?}; {}",
      r1cs.census(),
      memory_summary()
    );
  }
}
