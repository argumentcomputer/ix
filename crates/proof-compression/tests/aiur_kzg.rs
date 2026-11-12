use std::sync::Arc;

use aiur::{
  artifact::WidePackage,
  bytecode::CheckedProgram,
  field::FieldBackend,
  trace::{DepthSlot, Polynomial, TracePlan},
};
use ix_proof_compression::{
  aiur_backend::{Bn254, kzg::Backend},
  kzg::{KzgConfig, Srs},
};
use multi_stark::system::SystemWitness;

const ENTRY: &str = "BN254Trace::run";

fn package() -> WidePackage {
  WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-trace.ixa"
  ))
  .unwrap()
}

fn plan(package: WidePackage) -> TracePlan<'static, Bn254> {
  let trace = package.trace.unwrap();
  let mut checked: CheckedProgram<Bn254> =
    package.program.check_with(Bn254).unwrap();
  checked.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(checked), trace).unwrap()
}

fn config() -> KzgConfig {
  // Deterministic toxic waste is confined to these protocol regressions.
  KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(64, b"aiur-bn254-compiler-test")),
    8,
  )
}

#[test]
fn compiled_bn254_recursion_maps_and_rom_prove_expected_calls() {
  let plan = plan(package());
  assert!(plan.artifact().chips.iter().any(|chip| chip.depth.column.is_some()));
  assert!(plan.artifact().chips.iter().any(|chip| !chip.memory.is_empty()));
  let backend = Backend::new(&plan, config()).unwrap();
  assert!(
    backend.circuit_names().iter().any(|name| name.starts_with("<table:"))
  );
  assert!(backend.circuit_names().iter().any(|name| name.starts_with("<ROM:")));
  let f = |value| Bn254.from_u64(value);
  let minus_one = Bn254.neg(Bn254.one());
  for (n, x, expected) in
    [(0, f(0), minus_one), (3, minus_one, f(9)), (5, f(0), f(4))]
  {
    let args = [f(n), x];
    let record = plan.program().execute(ENTRY, args.to_vec()).unwrap();
    assert_eq!(record.output, [expected]);
    let public = plan.public_args(&record, ENTRY, &args).unwrap();
    let witness = backend.generate(&record, ENTRY, &args).unwrap();
    let proof = backend.prove(ENTRY, &public, &[expected], witness).unwrap();
    backend.verify(ENTRY, &public, &[expected], &proof).unwrap();
    assert!(
      backend.verify(ENTRY, &public, &[expected + f(1)], &proof).is_err()
    );
    let mut wrong_args = public.clone();
    wrong_args[0] += f(1);
    assert!(backend.verify(ENTRY, &wrong_args, &[expected], &proof).is_err());
    assert!(backend.claim(ENTRY, &public[..1], &[expected]).is_err());
    assert!(backend.claim(ENTRY, &public, &[]).is_err());
  }
}

#[test]
fn verifier_rejects_forged_multiplicities_rom_depth_and_activation() {
  let plan = plan(package());
  let backend = Backend::new(&plan, config()).unwrap();
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(ENTRY, args.to_vec()).unwrap();
  let public = plan.public_args(&record, ENTRY, &args).unwrap();
  let witness = backend.generate(&record, ENTRY, &args).unwrap();
  let honest =
    backend.prove(ENTRY, &public, &record.output, witness.clone()).unwrap();
  backend.verify(ENTRY, &public, &record.output, &honest).unwrap();

  let rom = backend
    .circuit_names()
    .iter()
    .position(|name| name.starts_with("<ROM:"))
    .unwrap();
  let fixed = backend
    .circuit_names()
    .iter()
    .position(|name| name.starts_with("<table:"))
    .unwrap();
  let layout = plan.layout().unwrap();
  let (depth_chip, chip) = plan
    .artifact()
    .chips
    .iter()
    .enumerate()
    .find(|(_, chip)| chip.depth.column.is_some())
    .unwrap();
  let placement = &layout.placements[depth_chip];
  let depth = placement.columns[chip.depth.column.unwrap()];
  let mut mutations = vec![
    (rom, 0),
    (rom, 2),
    (rom, 3),
    (fixed, 0),
    (placement.circuit, depth),
    (placement.circuit, placement.selector),
  ];
  mutations
    .push((placement.circuit, witness.traces[placement.circuit].width - 1));
  for (circuit, column) in mutations {
    let mut traces = witness.traces.clone();
    traces[circuit].values[column] += Bn254.one();
    let forged = SystemWitness::from_stage_1(traces, backend.system());
    let proof = backend.prove(ENTRY, &public, &record.output, forged).unwrap();
    assert!(
      backend.verify(ENTRY, &public, &record.output, &proof).is_err(),
      "accepted altered circuit {circuit} column {column}"
    );
  }
  let mut bad = honest.clone();
  bad.log_degrees[0] = u8::MAX;
  assert!(backend.verify(ENTRY, &public, &record.output, &bad).is_err());
  let mut bad = honest.clone();
  bad.active[fixed] = false;
  assert!(backend.verify(ENTRY, &public, &record.output, &bad).is_err());
  let mut bad = honest;
  bad.active.pop();
  assert!(backend.verify(ENTRY, &public, &record.output, &bad).is_err());
}

#[test]
fn proof_binds_compiler_fixed_tables_and_setup_capacity() {
  let original = package();
  let plan = plan(original.clone());
  let backend = Backend::new(&plan, config()).unwrap();
  let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
  let record = plan.program().execute(ENTRY, args.to_vec()).unwrap();
  let public = plan.public_args(&record, ENTRY, &args).unwrap();
  let proof = backend
    .prove(
      ENTRY,
      &public,
      &record.output,
      backend.generate(&record, ENTRY, &args).unwrap(),
    )
    .unwrap();

  let mut changed = original;
  let output_table = changed
    .program
    .maps
    .iter()
    .find(|map| map.name == "BN254Trace::lookup")
    .unwrap()
    .output;
  changed.program.tables[output_table].rows[1][0] = 8u64.into();
  let changed = self::plan(changed);
  let changed_backend = Backend::new(&changed, config()).unwrap();
  assert!(
    changed_backend.verify(ENTRY, &public, &record.output, &proof).is_err()
  );

  let small = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(2, b"aiur-small-capacity")),
    8,
  );
  let small = Backend::new(&plan, small).unwrap();
  assert!(
    small.generate(&record, ENTRY, &args).err().unwrap().contains("capacity")
  );
  let low_degree = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(64, b"aiur-small-degree")),
    1,
  );
  assert!(
    Backend::new(&plan, low_degree).err().unwrap().contains("quotient degree")
  );
}

#[test]
fn compiler_grouping_preserves_calls_and_rejects_forged_selection() {
  let original = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-grouped.ixa"
  ))
  .unwrap();
  let plan = plan(original.clone());
  assert_eq!(plan.artifact().groups.len(), 1);
  assert_eq!(plan.artifact().groups[0].members.len(), 3);
  let layout = plan.layout().unwrap();
  let backend = Backend::new(&plan, config()).unwrap();
  let entry = "BN254Grouped::run";
  for (input, expected) in
    [(Bn254.zero(), 29), (Bn254.from_u64(2), 72), (Bn254.neg(Bn254.one()), 21)]
  {
    let args = [input];
    let output = [Bn254.from_u64(expected)];
    let record = plan.program().execute(entry, args.to_vec()).unwrap();
    assert_eq!(record.output, output);
    let witness = backend.generate(&record, entry, &args).unwrap();
    let proof = backend.prove(entry, &args, &output, witness.clone()).unwrap();
    backend.verify(entry, &args, &output, &proof).unwrap();
    assert!(
      backend.verify(entry, &args, &[output[0] + Bn254.one()], &proof).is_err()
    );

    if input == Bn254.from_u64(2) {
      let group = &plan.artifact().groups[0];
      let chip = plan
        .artifact()
        .chips
        .iter()
        .position(|chip| chip.name == group.members[0].name)
        .unwrap();
      let circuit = layout.placements[chip].circuit;
      let first =
        &witness.traces[circuit].values[..witness.traces[circuit].width];
      let selected = group
        .members
        .iter()
        .find(|member| first[member.selector] == Bn254.one())
        .unwrap();
      let other = group
        .members
        .iter()
        .find(|member| member.selector != selected.selector)
        .unwrap();
      for replace in [false, true] {
        let mut traces = witness.traces.clone();
        traces[circuit].values[other.selector] = Bn254.one();
        if replace {
          traces[circuit].values[selected.selector] = Bn254.zero();
        }
        let forged = SystemWitness::from_stage_1(traces, backend.system());
        let proof = backend.prove(entry, &args, &output, forged).unwrap();
        assert!(backend.verify(entry, &args, &output, &proof).is_err());
      }
    }
  }
  for constraint in
    [Polynomial::Const(Bn254.modulus()), Polynomial::Var(usize::MAX)]
  {
    let mut malformed = original.clone();
    malformed.trace.as_mut().unwrap().groups[0].constraints.push(constraint);
    let malformed = self::plan(malformed);
    assert!(Backend::new(&malformed, config()).is_err());
  }
}

#[test]
fn compiler_gap_ranges_and_recursive_public_depth_are_proven() {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-gap.ixa"
  ))
  .unwrap();
  let plan = plan(package);
  assert_eq!(plan.artifact().limbs, [16, 8]);
  assert_eq!(plan.depth_range_tables().count(), 2);
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(1 << 16, b"aiur-depth-gap-test")),
    8,
  );
  let backend = Backend::new(&plan, config).unwrap();
  let entry = "BN254Gap::run";
  let args = [Bn254.from_u64(6), Bn254.neg(Bn254.one())];
  let output = [Bn254.from_u64(7)];
  let record = plan.program().execute(entry, args.to_vec()).unwrap();
  assert_eq!(record.output, output);
  let trace = plan.generate(&record, entry, &args, true).unwrap();
  assert!(trace.ranges.0.iter().all(|counts| counts.iter().sum::<u64>() > 0));
  let witness = backend.witness(&record, &trace, entry, &args).unwrap();
  let proof = backend.prove(entry, &args, &output, witness.clone()).unwrap();
  backend.verify(entry, &args, &output, &proof).unwrap();

  for (table, _) in plan.depth_range_tables() {
    let mut forged = trace.clone();
    forged.ranges.0[table][0] += 1;
    let forged = backend.witness(&record, &forged, entry, &args).unwrap();
    let proof = backend.prove(entry, &args, &output, forged).unwrap();
    assert!(backend.verify(entry, &args, &output, &proof).is_err());
  }

  let layout = plan.layout().unwrap();
  let (chip, column, row) = plan
    .artifact()
    .chips
    .iter()
    .enumerate()
    .find_map(|(chip, definition)| {
      definition.depth.slots.iter().find_map(|slot| {
        let DepthSlot::Gap { column } = *slot else { return None };
        (0..trace.matrices[chip].unpadded_height)
          .find(|&row| trace.matrices[chip].row(row)[column] != Bn254.zero())
          .map(|row| (chip, column, row))
      })
    })
    .expect("unequal recursive calls must use a nonzero depth gap");
  let placement = &layout.placements[chip];
  assert!(!placement.grouped);
  let mut traces = witness.traces.clone();
  let width = traces[placement.circuit].width;
  traces[placement.circuit].values[row * width + placement.columns[column]] =
    Bn254.neg(Bn254.one());
  let forged = SystemWitness::from_stage_1(traces, backend.system());
  let proof = backend.prove(entry, &args, &output, forged).unwrap();
  assert!(backend.verify(entry, &args, &output, &proof).is_err());

  let recursive = "BN254Gap::fib";
  let args = [Bn254.from_u64(7)];
  let output = [Bn254.from_u64(13)];
  let record = plan.program().execute(recursive, args.to_vec()).unwrap();
  assert_eq!(record.output, output);
  let public = plan.public_args(&record, recursive, &args).unwrap();
  assert_eq!(public.len(), args.len() + 1);
  assert!(backend.claim(recursive, &args, &output).is_err());
  let proof = backend
    .prove(
      recursive,
      &public,
      &output,
      backend.generate(&record, recursive, &args).unwrap(),
    )
    .unwrap();
  backend.verify(recursive, &public, &output, &proof).unwrap();
  let mut wrong_depth = public;
  *wrong_depth.last_mut().unwrap() += Bn254.one();
  assert!(backend.verify(recursive, &wrong_depth, &output, &proof).is_err());
}
