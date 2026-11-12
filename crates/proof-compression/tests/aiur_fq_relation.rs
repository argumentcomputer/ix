use std::{collections::HashSet, path::PathBuf, sync::Arc};

use aiur::{
  artifact::WidePackage,
  bytecode::Instruction,
  field::FieldBackend,
  hints::HintChannels,
  trace::{Action, TracePlan},
};
use ark_bn254::{Fq, Fr};
use ark_ff::{BigInteger, Field, PrimeField};
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, fq_relation, kzg::Backend},
  kzg::{KzgConfig, Scalar, Srs},
  recursive::native_field::{integer, modulus, scalar},
};
use multi_stark::system::SystemWitness;
use num_bigint::BigUint;

fn plan() -> TracePlan<'static, Bn254> {
  let path = std::env::var_os("AIUR_FQ_RELATION_FIXTURE").map_or_else(
    || {
      PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../aiur/tests/fixtures/bn254-fq-relation.ixa")
    },
    PathBuf::from,
  );
  let package = WidePackage::decode(&std::fs::read(path).unwrap()).unwrap();
  let trace = package.trace.unwrap();
  let mut program = package.program.check_with(Bn254).unwrap();
  program.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(program), trace).unwrap()
}

fn channels() -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  fq::register(&mut channels).unwrap();
  fq_relation::register(&mut channels).unwrap();
  channels
}

fn arguments(values: &[Fq]) -> Vec<Scalar> {
  values.iter().copied().flat_map(fq::encode).collect()
}

fn poisoned(
  plan: &TracePlan<'_, Bn254>,
  target: &'static str,
  change: impl Fn(&[Scalar], &mut Vec<Scalar>) + Send + Sync + 'static,
) -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  let mut seen = HashSet::new();
  let change = Arc::new(change);
  for function in &plan.program().program().functions {
    for instruction in &function.code {
      let Instruction::Hint { channel, r#type, key_type, .. } = instruction
      else {
        continue;
      };
      if !seen.insert(channel.clone()) {
        continue;
      }
      let name = channel.clone();
      let change = change.clone();
      channels
        .insert(
          channel,
          key_type.clone(),
          r#type.clone(),
          move |input, output| {
            let candidate = if name.starts_with("bn254.fq_relation.") {
              fq_relation::advice(&name, input)
            } else {
              fq::advice(&name, input)
            };
            let mut candidate =
              candidate.unwrap_or_else(|_| vec![Bn254.zero(); output.len()]);
            if name == target {
              change(input, &mut candidate);
            }
            output.copy_from_slice(&candidate);
            Ok(())
          },
        )
        .unwrap();
    }
  }
  channels
}

#[test]
fn signed_advice_and_integer_bounds_match_the_source_contract() {
  let one = BigUint::from(1u8);
  let radix = &one << fq_relation::LIMB_BITS;
  let prime = modulus();
  let fr = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
  let maximum = &prime - 1u8;
  let expression_bound = 12u8 * &radix * &radix + 3u8 * &radix + 4u8;
  let coefficient_bound = 16u8 * &radix * &radix + 3u8 * &radix + 4u8;
  let carry_bias = &one << (fq_relation::CARRY_BITS - 1);
  let quotient_bias = &one << (fq_relation::QUOTIENT_BITS - 1);
  assert!(2u8 * &expression_bound < fr);
  assert!(
    (3u8 * &maximum * &maximum + 3u8 * &maximum + 4u8) / &prime < quotient_bias
  );
  assert!(
    (&radix + 1u8) * &coefficient_bound + (&radix * &radix + 1u8) * &carry_bias
      < fr
  );
  assert!(
    (&radix + 1u8) * coefficient_bound + &carry_bias
      < &radix * &radix * &carry_bias
  );
  let encoded = fq::encode(-Fq::from(1));
  let mut coefficients = [Bn254.zero(); 8];
  for i in 0..4 {
    for j in 0..4 {
      coefficients[i + j] += encoded[i] * encoded[j];
    }
  }
  coefficients[0] -= Bn254.one();
  for sign in [Bn254.one(), -Bn254.one()] {
    let input = coefficients.map(|value| sign * value);
    let advice = fq_relation::advice("bn254.fq_relation.zero", &input).unwrap();
    assert_eq!(advice.len(), fq_relation::ADVICE_LEN);
    let quotient =
      advice[..4].iter().rev().fold(BigUint::from(0u8), |value, &limb| {
        (value << fq_relation::LIMB_BITS) + integer(limb)
      });
    assert_eq!(
      quotient,
      if sign == Bn254.one() {
        &quotient_bias + &prime - 2u8
      } else {
        &quotient_bias - &prime + 2u8
      }
    );
    assert!(advice[4..].iter().all(|&v| integer(v).bits() <= 89));
  }
  coefficients[0] += Bn254.one();
  assert!(
    fq_relation::advice("bn254.fq_relation.zero", &coefficients).is_err()
  );
  for invalid in [scalar(&expression_bound), -scalar(&expression_bound)] {
    assert!(
      fq_relation::advice("bn254.fq_relation.zero", &[invalid; 8]).is_err()
    );
  }
  assert!(fq_relation::advice("bn254.fq_relation.zero", &[]).is_err());
}

#[test]
fn compiled_relations_accept_signed_boundaries_and_g1_equations() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let mut values = vec![
    Fq::from(0),
    Fq::from(1),
    -Fq::from(1),
    -Fq::from(2),
    Fq::from_le_bytes_mod_order(
      &((BigUint::from(1u8) << 80usize) - 1u8).to_bytes_le(),
    ),
  ];
  values.extend((0u64..8).map(|i| {
    Fq::from_le_bytes_mod_order(blake3::hash(&i.to_le_bytes()).as_bytes())
  }));
  for (i, &a) in values.iter().enumerate() {
    let b = values[(i + 3) % values.len()];
    executor
      .execute("FqRelationTest::product", arguments(&[a, b, a * b]))
      .unwrap();
    let residue = Fq::from(3) * a * a + Fq::from(3) * a + Fq::from(4);
    for entry in
      ["FqRelationTest::max_weight", "FqRelationTest::negative_weight"]
    {
      executor.execute(entry, arguments(&[a, residue])).unwrap();
    }
    executor.execute("FqRelationTest::cancel", arguments(&[a])).unwrap();
    let xb = a + Fq::from(1);
    let yb = b + Fq::from(7);
    let slope = (yb - b) / (xb - a);
    let x = slope * slope - a - xb;
    let y = slope * (a - x) - b;
    for (entry, args) in [
      ("FqRelationTest::add_slope", vec![a, b, xb, yb, slope]),
      ("FqRelationTest::x_coordinate", vec![slope, a, xb, x]),
      ("FqRelationTest::y_coordinate", vec![slope, a, x, b, y]),
    ] {
      executor.execute(entry, arguments(&args)).unwrap();
    }
    if let Some(inverse) = (Fq::from(2) * b).inverse() {
      let slope = Fq::from(3) * a * a * inverse;
      executor
        .execute("FqRelationTest::double_slope", arguments(&[a, b, slope]))
        .unwrap();
    }
  }
  executor
    .execute(
      "FqRelationTest::curve",
      arguments(&[Fq::from(1), Fq::from(1), Fq::from(2)]),
    )
    .unwrap();
  for value in 0..=4 {
    executor
      .execute("FqRelationTest::constant", vec![Bn254.from_u64(value)])
      .unwrap();
  }
  for (entry, bits) in
    [("FqRelationTest::range17", 17), ("FqRelationTest::range89", 89)]
  {
    let limit = BigUint::from(1u8) << bits;
    executor.execute(entry, vec![scalar(&(&limit - 1u8))]).unwrap();
    assert!(executor.execute(entry, vec![scalar(&limit)]).is_err());
    assert!(executor.execute(entry, vec![-Bn254.one()]).is_err());
  }
}

#[test]
fn compiled_constraints_reject_forged_advice_and_excess_weights() {
  let plan = plan();
  let args = arguments(&[-Fq::from(1), -Fq::from(1), Fq::from(1)]);
  for (target, index) in (0..fq_relation::ADVICE_LEN)
    .map(|i| ("bn254.fq_relation.zero", i))
    .chain([("bn254.fq_relation.u16_17", 1), ("bn254.fq_relation.u16_89", 5)])
  {
    let channels = poisoned(&plan, target, move |_, candidate| {
      candidate[index] += Bn254.one();
    });
    let executor =
      plan.program().prepare_hint_channels(&[], &channels).unwrap();
    assert!(
      executor.execute("FqRelationTest::product", args.clone()).is_err(),
      "accepted forged {target}[{index}]"
    );
  }
  for (channel, entry) in [
    ("bn254.fq_relation.u16_17", "FqRelationTest::range17"),
    ("bn254.fq_relation.u16_89", "FqRelationTest::range89"),
  ] {
    let channels = poisoned(&plan, channel, |_, candidate| {
      candidate[0] += Bn254.from_u64(65536);
      candidate[1] -= Bn254.one();
    });
    assert!(
      plan
        .program()
        .prepare_hint_channels(&[], &channels)
        .unwrap()
        .execute(entry, vec![Bn254.from_u64(65536)])
        .is_err()
    );
  }
  for (channel, entry, bits, top) in [
    ("bn254.fq_relation.u16_17", "FqRelationTest::range17", 17, 2),
    ("bn254.fq_relation.u16_89", "FqRelationTest::range89", 89, 512),
  ] {
    let channels = poisoned(&plan, channel, move |_, candidate| {
      let last = candidate.len() - 1;
      candidate[last] = Bn254.from_u64(top);
    });
    assert!(
      plan
        .program()
        .prepare_hint_channels(&[], &channels)
        .unwrap()
        .execute(entry, vec![scalar(&(BigUint::from(1u8) << bits))])
        .is_err()
    );
  }
  // A failed native hint is replaced with arbitrary advice, so rejection
  // below depends on the compiled constraints rather than the callback.
  let channels = poisoned(&plan, "bn254.fq_relation.zero", |_, _| {});
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  assert!(
    executor
      .execute(
        "FqRelationTest::product",
        arguments(&[Fq::from(2), Fq::from(3), Fq::from(7)])
      )
      .is_err()
  );
  assert!(
    executor
      .execute(
        "FqRelationTest::curve",
        arguments(&[Fq::from(1), Fq::from(1), Fq::from(3)])
      )
      .is_err()
  );
  for entry in
    ["FqRelationTest::product_overflow", "FqRelationTest::linear_overflow"]
  {
    assert!(executor.execute(entry, arguments(&[Fq::from(0)])).is_err());
  }
  assert!(
    executor
      .execute("FqRelationTest::constant", vec![Bn254.from_u64(5)])
      .is_err()
  );
  assert!(
    executor.execute("FqRelationTest::constant", vec![-Bn254.one()]).is_err()
  );
  assert!(
    executor
      .execute("FqRelationTest::constant_overflow", vec![Bn254.from_u64(3)])
      .is_err()
  );
  let mask = (BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  for noncanonical in [modulus(), modulus() + 1u8] {
    let invalid = (0..4)
      .map(|i| scalar(&((&noncanonical >> (i * fq::LIMB_BITS)) & &mask)))
      .chain(arguments(&[Fq::from(1), Fq::from(0)]))
      .collect();
    assert!(executor.execute("FqRelationTest::product", invalid).is_err());
  }
}

#[test]
fn kzg_relations_reject_altered_quotient_and_carry_columns() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let capacity = plan
    .program()
    .program()
    .tables
    .iter()
    .map(|table| table.rows.len())
    .max()
    .unwrap_or(1)
    .max(1024)
    .next_power_of_two();
  let backend = Backend::new(
    &plan,
    KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(capacity, b"aiur-fq-relation-test")),
      8,
    ),
  )
  .unwrap();
  let x = -Fq::from(2);
  let residue = Fq::from(3) * x * x + Fq::from(3) * x + Fq::from(4);
  let args = arguments(&[x, residue]);
  let (function, fill) = plan
    .artifact()
    .functions
    .iter()
    .enumerate()
    .find(|(_, fill)| fill.name == "BN254FqRelation::assert_zero")
    .unwrap();
  let dest = fill
    .steps
    .iter()
    .find_map(|step| match &step.action {
      Action::Hint { channel, dest, .. }
        if channel == "bn254.fq_relation.zero" =>
      {
        Some(dest)
      },
      _ => None,
    })
    .unwrap();
  let chip = plan.function_chips()[function];
  let layout = plan.layout().unwrap();
  let placement = &layout.placements[chip];
  assert!(!placement.grouped);
  for entry in ["FqRelationTest::max_weight", "FqRelationTest::negative_weight"]
  {
    let record = executor.execute(entry, args.clone()).unwrap();
    let witness = backend.generate(&record, entry, &args).unwrap();
    let proof = backend.prove(entry, &args, &[], witness.clone()).unwrap();
    backend.verify(entry, &args, &[], &proof).unwrap();
    let mut positions = vec![];
    for &source in &dest[4..] {
      let column =
        fill.writes.iter().find(|write| write.source == source).unwrap().column;
      positions.push((placement.circuit, placement.columns[column]));
    }
    // Linear elimination removes the four quotient columns from the
    // relation chip; their values still appear as range-function inputs.
    let bias = BigUint::from(1u8) << (fq_relation::QUOTIENT_BITS - 1);
    let magnitude = 3u8 * modulus() - 9u8;
    let quotient = if entry == "FqRelationTest::max_weight" {
      bias + magnitude
    } else {
      bias - magnitude
    };
    let mask = (BigUint::from(1u8) << fq_relation::LIMB_BITS) - 1u8;
    for i in 0..4 {
      let value =
        scalar(&((&quotient >> (i * fq_relation::LIMB_BITS)) & &mask));
      let function_name =
        if i == 3 { "BN254FqRelation::range17" } else { "BN254Fq::range80" };
      let (function, range_fill) = plan
        .artifact()
        .functions
        .iter()
        .enumerate()
        .find(|(_, fill)| fill.name == function_name)
        .unwrap();
      let chip = plan.function_chips()[function];
      let range_placement = &layout.placements[chip];
      assert!(!range_placement.grouped);
      let input_column = range_fill
        .writes
        .iter()
        .find(|write| write.source == range_fill.inputs[0])
        .unwrap()
        .column;
      let column = range_placement.columns[input_column];
      let activation =
        range_placement.columns[plan.artifact().chips[chip].activation];
      let trace = &witness.traces[range_placement.circuit];
      let row = trace
        .values
        .chunks(trace.width)
        .position(|row| row[column] == value && row[activation] == Bn254.one())
        .unwrap();
      positions.push((range_placement.circuit, row * trace.width + column));
    }
    for (circuit, cell) in positions {
      let mut traces = witness.traces.clone();
      traces[circuit].values[cell] += Bn254.one();
      let forged = SystemWitness::from_stage_1(traces, backend.system());
      let proof = backend.prove(entry, &args, &[], forged).unwrap();
      assert!(backend.verify(entry, &args, &[], &proof).is_err());
    }
  }
}
