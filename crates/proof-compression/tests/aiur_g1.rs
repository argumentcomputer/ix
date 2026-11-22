use std::{collections::HashSet, sync::Arc};

use aiur::{
  FieldWord,
  artifact::WidePackage,
  bytecode::Instruction,
  field::FieldBackend,
  hints::HintChannels,
  trace::{Action, TracePlan},
};
use ark_bn254::{Fq, Fr, G1Affine};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, g1, kzg::Backend},
  kzg::{KzgConfig, Scalar, Srs},
  recursive::native_field::modulus,
};
use num_bigint::BigUint;

fn plan() -> TracePlan<'static, Bn254> {
  let override_bytes = std::env::var_os("AIUR_G1_FIXTURE")
    .map(|path| std::fs::read(path).unwrap());
  let bytes = override_bytes
    .as_deref()
    .unwrap_or(include_bytes!("../../aiur/tests/fixtures/bn254-g1.ixa"));
  let package = WidePackage::decode(bytes).unwrap();
  let trace = package.trace.unwrap();
  let mut checked = package.program.check_with(Bn254).unwrap();
  checked.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(checked), trace).unwrap()
}

fn channels() -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  fq::register(&mut channels).unwrap();
  g1::register(&mut channels).unwrap();
  channels
}

fn scalar(value: &BigUint) -> Scalar {
  let digits = value.to_u64_digits();
  let mut limbs = [0; 4];
  limbs[..digits.len()].copy_from_slice(&digits);
  Bn254.decode_words(&[FieldWord::from_limbs_le(limbs)]).unwrap()[0]
}

fn limbs(value: &BigUint) -> Vec<Scalar> {
  let mask = (BigUint::from(1u8) << 80usize) - 1u8;
  (0..4).map(|i| scalar(&((value >> (80 * i)) & &mask))).collect()
}

fn bytes(point: G1Affine) -> Vec<Scalar> {
  let mut bytes = vec![];
  point.serialize_compressed(&mut bytes).unwrap();
  bytes.into_iter().map(|byte| Bn254.from_u64(u64::from(byte))).collect()
}

fn poisoned(
  plan: &TracePlan<'_, Bn254>,
  target: &'static str,
  change: impl Fn(&[Scalar], &mut Vec<Scalar>) + Send + Sync + 'static,
) -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  let change = Arc::new(change);
  let mut seen = HashSet::new();
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
            // Arbitrary fallback advice keeps rejection attributable to
            // the source constraints when a forged operand invalidates a
            // later native callback's arithmetic preconditions.
            let mut values = g1::advice(&name, input)
              .unwrap_or_else(|_| vec![Bn254.zero(); output.len()]);
            if name == target {
              change(input, &mut values);
            }
            output.copy_from_slice(&values);
            Ok(())
          },
        )
        .unwrap();
    }
  }
  channels
}

#[test]
fn affine_advice_is_canonical_and_rejects_invalid_denominators() {
  let g = G1Affine::generator();
  for multiplier in [1u64, 2, 7, 123456789, u64::MAX] {
    let a = (g * Fr::from(multiplier)).into_affine();
    let b = (a + g).into_affine();
    let double_input = g1::encode(a)[..8].to_vec();
    let add_input: Vec<_> = double_input
      .iter()
      .copied()
      .chain(g1::encode(b)[..8].iter().copied())
      .collect();
    for (channel, input, slope, expected) in [
      (
        "bn254.g1.affine_double",
        double_input,
        Fq::from(3u8) * a.x.square() / (a.y + a.y),
        (a + a).into_affine(),
      ),
      (
        "bn254.g1.affine_add",
        add_input,
        (b.y - a.y) / (b.x - a.x),
        (a + b).into_affine(),
      ),
    ] {
      let candidate = g1::advice(channel, &input).unwrap();
      assert_eq!(candidate.len(), 12);
      assert_eq!(fq::decode(&candidate[..4]).unwrap(), slope);
      assert_eq!(candidate[4..], g1::encode(expected)[..8]);
      assert!(fq::decode(&candidate[4..8]).is_ok());
      assert!(fq::decode(&candidate[8..]).is_ok());
    }
  }
  assert!(g1::advice("bn254.g1.affine_double", &[]).is_err());
  assert!(g1::advice("bn254.g1.affine_add", &[]).is_err());
  assert!(g1::advice("bn254.g1.affine_double", &[Bn254.zero(); 8]).is_err());
  let equal_x: Vec<_> = g1::encode(g)[..8]
    .iter()
    .copied()
    .chain(g1::encode(-g)[..8].iter().copied())
    .collect();
  assert!(g1::advice("bn254.g1.affine_add", &equal_x).is_err());
  let mut invalid = g1::encode(g)[..8].to_vec();
  invalid[..4].copy_from_slice(&limbs(&(modulus() + 1u8)));
  assert!(g1::advice("bn254.g1.affine_double", &invalid).is_err());
}

#[test]
fn source_relations_reject_forged_slopes_coordinates_and_aliases() {
  let plan = plan();
  let g = G1Affine::generator();
  let two = (g + g).into_affine();
  for (channel, entry, args) in [
    ("bn254.g1.affine_double", "G1Test::double", g1::encode(g).to_vec()),
    (
      "bn254.g1.affine_add",
      "G1Test::add",
      g1::encode(g).into_iter().chain(g1::encode(two)).collect(),
    ),
  ] {
    for index in 0..12 {
      let channels = poisoned(&plan, channel, move |_, output| {
        output[index] += Bn254.one();
      });
      let executor =
        plan.program().prepare_hint_channels(&[], &channels).unwrap();
      assert!(
        executor.execute(entry, args.clone()).is_err(),
        "accepted {channel}[{index}]"
      );
    }
    for offset in [0, 4, 8] {
      let channels = poisoned(&plan, channel, move |_, output| {
        let value = fq::decode(&output[offset..offset + 4]).unwrap();
        let alias = modulus()
          + BigUint::from_bytes_le(&value.into_bigint().to_bytes_le());
        output[offset..offset + 4].copy_from_slice(&limbs(&alias));
      });
      assert!(
        plan
          .program()
          .prepare_hint_channels(&[], &channels)
          .unwrap()
          .execute(entry, args.clone())
          .is_err()
      );
      let channels = poisoned(&plan, channel, move |_, output| {
        output[offset] = scalar(&(BigUint::from(1u8) << fq::LIMB_BITS));
      });
      assert!(
        plan
          .program()
          .prepare_hint_channels(&[], &channels)
          .unwrap()
          .execute(entry, args.clone())
          .is_err()
      );
    }
    let channels = poisoned(&plan, channel, move |_, output| {
      output[4..].copy_from_slice(&g1::encode(g)[..8]);
    });
    assert!(
      plan
        .program()
        .prepare_hint_channels(&[], &channels)
        .unwrap()
        .execute(entry, args)
        .is_err()
    );
  }
  for index in 0..7 {
    let channels =
      poisoned(&plan, "bn254.fq_relation.zero", move |_, output| {
        output[index] += Bn254.one();
      });
    assert!(
      plan
        .program()
        .prepare_hint_channels(&[], &channels)
        .unwrap()
        .execute("G1Test::valid", g1::encode(g).to_vec())
        .is_err()
    );
  }
}

#[test]
fn complete_group_operations_match_arkworks_and_reject_invalid_points() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let g = G1Affine::generator();
  let points = [
    G1Affine::identity(),
    g,
    -g,
    (g * Fr::from(2)).into_affine(),
    (g * Fr::from(7)).into_affine(),
  ];
  for &point in &points {
    let raw = g1::encode(point).to_vec();
    assert_eq!(
      executor.execute("G1Test::valid", raw.clone()).unwrap().output,
      raw
    );
    assert_eq!(
      executor.execute("G1Test::neg", raw.clone()).unwrap().output,
      g1::encode(-point)
    );
    assert_eq!(
      executor.execute("G1Test::double", raw).unwrap().output,
      g1::encode((point + point).into_affine())
    );
    for &other in &points {
      let args =
        g1::encode(point).into_iter().chain(g1::encode(other)).collect();
      assert_eq!(
        executor.execute("G1Test::add", args).unwrap().output,
        g1::encode((point + other).into_affine())
      );
    }
  }
  let mut invalid = vec![g1::encode(g).to_vec(); 5];
  invalid[0][8] = Bn254.from_u64(2);
  invalid[1][8] = Bn254.one();
  invalid[2][4] = Bn254.from_u64(3);
  invalid[3][0] = scalar(&(BigUint::from(1u8) << 80usize));
  invalid[4][..4].copy_from_slice(&limbs(&(modulus() + 1u8)));
  invalid.push(vec![Bn254.zero(); 9]);
  for raw in invalid {
    assert!(g1::decode(&raw).is_err());
    assert!(executor.execute("G1Test::valid", raw).is_err());
  }
}

#[test]
fn full_scalar_multiplication_and_msm_use_canonical_fr_digits() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let g = G1Affine::generator();
  let wide = Fr::from_le_bytes_mod_order(
    &((BigUint::from(1u8) << 160usize) + 3u8).to_bytes_le(),
  );
  for value in
    [Fr::from(0), Fr::from(1), Fr::from(2), Fr::from(7), wide, -Fr::from(1)]
  {
    let args = g1::encode(g).into_iter().chain([Scalar(value)]).collect();
    assert_eq!(
      executor.execute("G1Test::mul", args).unwrap().output,
      g1::encode((g * value).into_affine())
    );
    let scalar_record =
      executor.execute("G1Test::scalar", vec![Scalar(value)]).unwrap();
    assert_eq!(
      scalar_record.output,
      limbs(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()))
    );
  }
  for (a, s, b, t) in [
    (g, Fr::from(3), -g, Fr::from(2)),
    (g, Fr::from(1), -g, Fr::from(1)),
    (G1Affine::identity(), wide, g, Fr::from(0)),
  ] {
    let args = g1::encode(a)
      .into_iter()
      .chain([Scalar(s)])
      .chain(g1::encode(b))
      .chain([Scalar(t)])
      .collect();
    let expected = (a * s + b * t).into_affine();
    assert_eq!(
      executor.execute("G1Test::msm2", args).unwrap().output,
      g1::encode(expected)
    );
  }
  let r = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
  let channels = poisoned(&plan, "bn254.g1.scalar", move |_, output| {
    output[..4].copy_from_slice(&limbs(&r));
    output[4..8].fill(scalar(&((BigUint::from(1u8) << 80usize) - 1u8)));
    output[8..12].fill(Bn254.one());
  });
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("G1Test::scalar", vec![Bn254.zero()])
      .is_err()
  );
  for index in [0, 1] {
    let channels = poisoned(&plan, "bn254.g1.halve", move |_, output| {
      output[index] += Bn254.one()
    });
    let args = g1::encode(g).into_iter().chain([Bn254.from_u64(3)]).collect();
    assert!(
      plan
        .program()
        .prepare_hint_channels(&[], &channels)
        .unwrap()
        .execute("G1Test::mul", args)
        .is_err()
    );
  }
}

#[test]
fn compressed_points_and_nested_commitments_match_transcript_encoding() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let g = G1Affine::generator();
  for point in [
    G1Affine::identity(),
    g,
    -g,
    (g * Fr::from(2)).into_affine(),
    -(g * Fr::from(2)).into_affine(),
  ] {
    let raw = g1::encode(point).to_vec();
    assert_eq!(
      executor.execute("G1Test::encode", raw.clone()).unwrap().output,
      bytes(point)
    );
    assert_eq!(
      executor.execute("G1Test::decode", bytes(point)).unwrap().output,
      raw
    );
  }
  let rows = vec![vec![g], vec![-g]];
  let mut encoded = vec![];
  rows.serialize_compressed(&mut encoded).unwrap();
  assert_eq!(encoded.len(), 88);
  let expected: Vec<_> =
    encoded.into_iter().map(|byte| Bn254.from_u64(u64::from(byte))).collect();
  let args = g1::encode(g).into_iter().chain(g1::encode(-g)).collect();
  assert_eq!(
    executor.execute("G1Test::commitment2", args).unwrap().output,
    expected
  );

  let mut invalid = vec![bytes(g); 3];
  invalid[0][31] = Bn254.from_u64(0xc0);
  invalid[1][31] = Bn254.from_u64(0x40);
  invalid[2][0] = Bn254.from_u64(256);
  invalid.push(
    Fq::MODULUS
      .to_bytes_le()
      .into_iter()
      .map(|byte| Bn254.from_u64(u64::from(byte)))
      .collect(),
  );
  let mut uncompressed = vec![];
  g.serialize_uncompressed(&mut uncompressed).unwrap();
  invalid.push(
    uncompressed
      .into_iter()
      .map(|byte| Bn254.from_u64(u64::from(byte)))
      .collect(),
  );
  for input in invalid {
    assert!(g1::advice("bn254.g1.decode", &input).is_err());
    assert!(executor.execute("G1Test::decode", input).is_err());
  }
  let channels = poisoned(&plan, "bn254.g1.sign", |_, output| {
    output[7] = Bn254.one() - output[7]
  });
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("G1Test::encode", g1::encode(-g).to_vec())
      .is_err()
  );
  let channels = poisoned(&plan, "bn254.g1.decode", move |_, output| {
    output.copy_from_slice(&g1::encode(g))
  });
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("G1Test::decode", bytes(-g))
      .is_err()
  );
}

#[test]
fn actual_compiler_kzg_proves_complete_addition_scalar_multiplication_and_msm()
{
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let g = G1Affine::generator();
  let cases: [(&str, Vec<Scalar>, G1Affine); 3] = [
    (
      "G1Test::add",
      g1::encode(g).into_iter().chain(g1::encode(-g)).collect(),
      G1Affine::identity(),
    ),
    (
      "G1Test::mul",
      g1::encode(g).into_iter().chain([Scalar(-Fr::from(1))]).collect(),
      -g,
    ),
    (
      "G1Test::msm2",
      g1::encode(g)
        .into_iter()
        .chain([Bn254.from_u64(3)])
        .chain(g1::encode(-g))
        .chain([Bn254.from_u64(2)])
        .collect(),
      g,
    ),
  ];
  for (entry, args, expected) in cases {
    let record = executor.execute(entry, args.clone()).unwrap();
    assert_eq!(record.output, g1::encode(expected));
    let trace = plan.generate(&record, entry, &args, true).unwrap();
    let height = trace
      .matrices
      .iter()
      .map(|matrix| matrix.height)
      .max()
      .unwrap()
      .max(
        plan
          .program()
          .program()
          .tables
          .iter()
          .map(|table| table.rows.len())
          .max()
          .unwrap_or(256),
      )
      .max(256)
      .next_power_of_two();
    assert!(height <= 1 << 17, "unexpected G1 test trace height {height}");
    let backend = Backend::new(
      &plan,
      KzgConfig::new(
        Arc::new(Srs::unsafe_dev_setup(height, b"aiur-g1-test")),
        8,
      ),
    )
    .unwrap();
    let witness = backend.witness(&record, &trace, entry, &args).unwrap();
    let forged_traces = if entry == "G1Test::add" {
      let mut traces = witness.traces.clone();
      let chip =
        plan.function_chips()[plan.program().entry(entry).unwrap().function];
      let layout = plan.layout().unwrap();
      let placement = &layout.placements[chip];
      let column = placement.columns[plan.artifact().chips[chip].inputs[0]];
      traces[placement.circuit].values[column] += Bn254.one();
      Some(traces)
    } else {
      None
    };
    let proof = backend.prove(entry, &args, &record.output, witness).unwrap();
    backend.verify(entry, &args, &g1::encode(expected), &proof).unwrap();
    let wrong = if expected.infinity { g } else { G1Affine::identity() };
    assert!(backend.verify(entry, &args, &g1::encode(wrong), &proof).is_err());
    if let Some(traces) = forged_traces {
      let forged = multi_stark::system::SystemWitness::from_stage_1(
        traces,
        backend.system(),
      );
      let proof = backend.prove(entry, &args, &record.output, forged).unwrap();
      assert!(
        backend.verify(entry, &args, &g1::encode(expected), &proof).is_err()
      );
    }
  }
}

#[test]
fn kzg_rejects_forged_affine_slope_and_coordinate_columns() {
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
      Arc::new(Srs::unsafe_dev_setup(capacity, b"aiur-g1-affine-test")),
      8,
    ),
  )
  .unwrap();
  let g = G1Affine::generator();
  let two = (g + g).into_affine();
  for (entry, function_name, channel, args, expected) in [
    (
      "G1Test::double",
      "BN254G1::double",
      "bn254.g1.affine_double",
      g1::encode(g).to_vec(),
      two,
    ),
    (
      "G1Test::add",
      "BN254G1::add",
      "bn254.g1.affine_add",
      g1::encode(g).into_iter().chain(g1::encode(two)).collect(),
      (g + two).into_affine(),
    ),
  ] {
    let record = executor.execute(entry, args.clone()).unwrap();
    assert_eq!(record.output, g1::encode(expected));
    let witness = backend.generate(&record, entry, &args).unwrap();
    let proof =
      backend.prove(entry, &args, &record.output, witness.clone()).unwrap();
    backend.verify(entry, &args, &record.output, &proof).unwrap();
    let (function, fill) = plan
      .artifact()
      .functions
      .iter()
      .enumerate()
      .find(|(_, fill)| fill.name == function_name)
      .unwrap();
    let dest = fill
      .steps
      .iter()
      .find_map(|step| match &step.action {
        Action::Hint { channel: name, dest, .. } if name == channel => {
          Some(dest)
        },
        _ => None,
      })
      .unwrap();
    let chip = plan.function_chips()[function];
    let layout = plan.layout().unwrap();
    let placement = &layout.placements[chip];
    assert!(!placement.grouped);
    for advice_index in [0, 4, 8] {
      let column = fill
        .writes
        .iter()
        .find(|write| write.source == dest[advice_index])
        .unwrap_or_else(|| panic!("missing {channel}[{advice_index}] column"))
        .column;
      let mut traces = witness.traces.clone();
      traces[placement.circuit].values[placement.columns[column]] +=
        Bn254.one();
      let forged = multi_stark::system::SystemWitness::from_stage_1(
        traces,
        backend.system(),
      );
      let proof = backend.prove(entry, &args, &record.output, forged).unwrap();
      assert!(backend.verify(entry, &args, &record.output, &proof).is_err());
    }
  }
}
