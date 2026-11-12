use std::{collections::HashSet, sync::Arc};

use aiur::{
  FieldWord,
  artifact::WidePackage,
  bytecode::Instruction,
  field::FieldBackend,
  hints::HintChannels,
  trace::{Action, TracePlan},
};
use ark_bn254::Fq;
use ark_ff::{BigInteger, Field, PrimeField};
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, kzg::Backend},
  kzg::{KzgConfig, Scalar, Srs},
  recursive::native_field::{integer, modulus},
};
use multi_stark::system::SystemWitness;
use num_bigint::BigUint;

fn plan() -> TracePlan<'static, Bn254> {
  let package = WidePackage::decode(include_bytes!(
    "../../aiur/tests/fixtures/bn254-fq.ixa"
  ))
  .unwrap();
  let trace = package.trace.unwrap();
  let mut checked = package.program.check_with(Bn254).unwrap();
  checked.track_depth(&trace).unwrap();
  TracePlan::new(Arc::new(checked), trace).unwrap()
}

fn scalar(value: &BigUint) -> Scalar {
  let mut limbs = [0; 4];
  let digits = value.to_u64_digits();
  limbs[..digits.len()].copy_from_slice(&digits);
  Bn254.decode_words(&[FieldWord::from_limbs_le(limbs)]).unwrap()[0]
}

fn raw(value: &BigUint) -> Vec<Scalar> {
  let mask = (BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  (0..4).map(|i| scalar(&((value >> (i * fq::LIMB_BITS)) & &mask))).collect()
}

fn channels() -> HintChannels<Scalar> {
  let mut channels = HintChannels::new();
  fq::register(&mut channels).unwrap();
  channels
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
            let mut candidate = if name == "bn254.fq.inverse"
              && name == target
              && input.iter().all(|&value| value == Bn254.zero())
            {
              vec![Bn254.zero(); 4]
            } else {
              fq::advice(&name, input)?
            };
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
fn native_advice_preserves_eighty_bit_limbs_and_integer_bounds() {
  let p = modulus();
  let r = BigUint::from_bytes_le(&ark_bn254::Fr::MODULUS.to_bytes_le());
  let radix = BigUint::from(1u8) << fq::LIMB_BITS;
  assert!((32u8 * &radix * &radix + 32u8 * &radix) < r);
  for value in [
    BigUint::from(0u8),
    BigUint::from(1u8),
    &radix - 1u8,
    radix.clone(),
    &p - 1u8,
  ] {
    let expected = Fq::from_le_bytes_mod_order(&value.to_bytes_le());
    assert_eq!(fq::decode(&fq::encode(expected)).unwrap(), expected);
    assert_eq!(raw(&value), fq::encode(expected));
  }
  let high = &radix - 1u8;
  let bytes = fq::advice("bn254.fq.bytes80", &[scalar(&high)]).unwrap();
  assert_eq!(bytes.len(), 10);
  assert!(bytes.iter().all(|&byte| byte == Bn254.from_u64(255)));
  let words = fq::advice("bn254.fq.u16_80", &[scalar(&high)]).unwrap();
  assert_eq!(words, vec![Bn254.from_u64(65535); 5]);
  for bits in [80usize, 84] {
    let limit = BigUint::from(1u8) << bits;
    let channel = format!("bn254.fq.u16_{bits}");
    let words = fq::advice(&channel, &[scalar(&(&limit - 1u8))]).unwrap();
    let recomposed =
      words.iter().enumerate().fold(BigUint::from(0u8), |sum, (i, value)| {
        sum + (BigUint::from(Bn254.try_to_u64(*value).unwrap()) << (16 * i))
      });
    assert_eq!(recomposed, &limit - 1u8);
    assert!(fq::advice(&channel, &[scalar(&limit)]).is_err());
  }
  assert!(Bn254.try_to_u64(scalar(&high)).is_err());
  assert!(fq::advice("bn254.fq.bytes80", &[scalar(&radix)]).is_err());
  assert!(
    fq::advice("bn254.fq.bytes84", &[scalar(&(BigUint::from(1u8) << 84))])
      .is_err()
  );
  assert!(fq::decode(&raw(&p)).is_err());
  assert!(fq::advice("bn254.fq.inverse", &[Bn254.zero(); 4]).is_err());
  let negative: Vec<_> =
    raw(&(&p / 2u8)).into_iter().chain(raw(&(&p / 3u8))).collect();
  let positive: Vec<_> = raw(&high).into_iter().chain(raw(&high)).collect();
  let bias = 8u8 * &radix;
  assert!(
    fq::advice("bn254.fq.mul", &negative).unwrap()[8..]
      .iter()
      .any(|&carry| integer(carry) < bias)
  );
  assert!(
    fq::advice("bn254.fq.mul", &positive).unwrap()[8..]
      .iter()
      .any(|&carry| integer(carry) > bias)
  );
}

#[test]
fn compiled_arithmetic_matches_base_field_at_boundaries() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let mut values = vec![
    Fq::from(0),
    Fq::from(1),
    -Fq::from(1),
    -Fq::from(2),
    Fq::from_le_bytes_mod_order(&(BigUint::from(1u8) << 80usize).to_bytes_le()),
  ];
  for i in 0u64..8 {
    let hash = blake3::hash(&i.to_le_bytes());
    values.push(Fq::from_le_bytes_mod_order(hash.as_bytes()));
  }
  for (i, &a) in values.iter().enumerate() {
    let b = values[(i * 7 + 3) % values.len()];
    let args: Vec<_> = fq::encode(a).into_iter().chain(fq::encode(b)).collect();
    for (entry, expected) in
      [("FqTest::add", a + b), ("FqTest::sub", a - b), ("FqTest::mul", a * b)]
    {
      let record = executor.execute(entry, args.clone()).unwrap();
      assert_eq!(record.output, fq::encode(expected), "{entry} for pair {i}");
    }
    let record =
      executor.execute("FqTest::canonical", fq::encode(a).to_vec()).unwrap();
    assert_eq!(record.output, fq::encode(a));
    if let Some(inverse) = a.inverse() {
      let record =
        executor.execute("FqTest::inverse", fq::encode(a).to_vec()).unwrap();
      assert_eq!(record.output, fq::encode(inverse));
    }
  }
  for noncanonical in
    [modulus(), modulus() + 1u8, (BigUint::from(1u8) << 320) - 1u8]
  {
    assert!(executor.execute("FqTest::canonical", raw(&noncanonical)).is_err());
  }
  assert!(executor.execute("FqTest::inverse", vec![Bn254.zero(); 4]).is_err());
  for (entry, bits) in [("FqTest::range80", 80usize), ("FqTest::range84", 84)] {
    let limit = BigUint::from(1u8) << bits;
    executor.execute(entry, vec![scalar(&(&limit - 1u8))]).unwrap();
    assert!(executor.execute(entry, vec![scalar(&limit)]).is_err());
  }
}

#[test]
fn source_constraints_reject_forged_quotients_carries_ranges_and_zero_inverse()
{
  let plan = plan();
  let args: Vec<_> = fq::encode(-Fq::from(1))
    .into_iter()
    .chain(fq::encode(-Fq::from(2)))
    .collect();
  for (target, entry, index) in [
    ("bn254.fq.mul", "FqTest::mul", 4),
    ("bn254.fq.mul", "FqTest::mul", 8),
    ("bn254.fq.mul", "FqTest::mul", 14),
    ("bn254.fq.add", "FqTest::add", 4),
    ("bn254.fq.sub", "FqTest::sub", 4),
    ("bn254.fq.canonical", "FqTest::mul", 7),
    ("bn254.fq.u16_80", "FqTest::mul", 4),
    ("bn254.fq.u16_84", "FqTest::mul", 5),
  ] {
    let channels =
      poisoned(&plan, target, move |_, output| output[index] += Bn254.one());
    let executor =
      plan.program().prepare_hint_channels(&[], &channels).unwrap();
    assert!(
      executor.execute(entry, args.clone()).is_err(),
      "accepted forged {target}[{index}]"
    );
  }
  let channels = poisoned(&plan, "bn254.fq.u16_80", |_, output| {
    output[0] = Bn254.from_u64(65536)
  });
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("FqTest::mul", args)
      .is_err()
  );
  let channels = poisoned(&plan, "bn254.fq.u16_80", |_, output| {
    output[0] += Bn254.from_u64(65536);
    output[1] -= Bn254.one();
  });
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("FqTest::range80", vec![Bn254.from_u64(65536)])
      .is_err()
  );
  let channels =
    poisoned(&plan, "bn254.fq.inverse", |_, output| output[0] = Bn254.one());
  assert!(
    plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("FqTest::inverse", vec![Bn254.zero(); 4])
      .is_err()
  );
}

#[test]
fn compiled_fq_kzg_proofs_reject_altered_quotient_and_carry_columns() {
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
      Arc::new(Srs::unsafe_dev_setup(capacity, b"aiur-fq-test")),
      8,
    ),
  )
  .unwrap();
  let a = Fq::from_le_bytes_mod_order(&(modulus() / 2u8).to_bytes_le());
  let b = Fq::from_le_bytes_mod_order(&(modulus() / 3u8).to_bytes_le());
  let positive = Fq::from_le_bytes_mod_order(
    &((BigUint::from(1u8) << 80usize) - 1u8).to_bytes_le(),
  );
  let pair: Vec<_> = fq::encode(a).into_iter().chain(fq::encode(b)).collect();
  for (entry, args, expected) in [
    ("FqTest::add", pair.clone(), a + b),
    ("FqTest::sub", pair.clone(), a - b),
    ("FqTest::mul", pair, a * b),
    (
      "FqTest::mul",
      fq::encode(positive).into_iter().chain(fq::encode(positive)).collect(),
      positive * positive,
    ),
    ("FqTest::inverse", fq::encode(b).to_vec(), b.inverse().unwrap()),
  ] {
    let record = executor.execute(entry, args.clone()).unwrap();
    assert_eq!(record.output, fq::encode(expected));
    let witness = backend.generate(&record, entry, &args).unwrap();
    let proof =
      backend.prove(entry, &args, &record.output, witness.clone()).unwrap();
    backend.verify(entry, &args, &fq::encode(expected), &proof).unwrap();
    assert!(
      backend
        .verify(entry, &args, &fq::encode(expected + Fq::from(1)), &proof)
        .is_err()
    );
    if entry == "FqTest::mul" {
      let (function, fill) = plan
        .artifact()
        .functions
        .iter()
        .enumerate()
        .find(|(_, fill)| fill.name == "BN254Fq::mul")
        .unwrap();
      let dest = fill
        .steps
        .iter()
        .find_map(|step| match &step.action {
          Action::Hint { channel, dest, .. } if channel == "bn254.fq.mul" => {
            Some(dest)
          },
          _ => None,
        })
        .unwrap();
      let chip = plan.function_chips()[function];
      let layout = plan.layout().unwrap();
      let placement = &layout.placements[chip];
      assert!(!placement.grouped);
      for advice_index in [4, 8] {
        let column = fill
          .writes
          .iter()
          .find(|write| write.source == dest[advice_index])
          .unwrap()
          .column;
        let mut traces = witness.traces.clone();
        traces[placement.circuit].values[placement.columns[column]] +=
          Bn254.one();
        let forged = SystemWitness::from_stage_1(traces, backend.system());
        let proof =
          backend.prove(entry, &args, &record.output, forged).unwrap();
        assert!(backend.verify(entry, &args, &record.output, &proof).is_err());
      }
    }
  }
}
