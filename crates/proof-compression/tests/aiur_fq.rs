use std::{
  collections::HashSet,
  sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
  },
};

use aiur::{
  FieldWord,
  artifact::WidePackage,
  bytecode::Instruction,
  field::FieldBackend,
  hints::HintChannels,
  trace::{Action, Polynomial, TracePlan},
};
use ark_bn254::Fq;
use ark_ff::{BigInteger, Field, PrimeField};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq,
    kzg::{Backend, circuit_inputs},
  },
  kzg::{KzgConfig, Scalar, Srs},
  recursive::native_field::{integer, modulus},
};
use multi_stark::{
  expr::{Expr, Source},
  system::{System, SystemWitness},
};
use num_bigint::BigUint;

fn plan() -> TracePlan<'static, Bn254> {
  let override_bytes = std::env::var_os("AIUR_FQ_FIXTURE")
    .map(|path| std::fs::read(path).unwrap());
  let bytes = override_bytes
    .as_deref()
    .unwrap_or(include_bytes!("../../aiur/tests/fixtures/bn254-fq.ixa"));
  let package = WidePackage::decode(bytes).unwrap();
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
            // Failed host advice becomes a candidate so invalid inputs reach
            // the source's constraints instead of stopping in the advice code.
            let mut candidate = fq::advice(&name, input)
              .unwrap_or_else(|_| vec![Bn254.zero(); output.len()]);
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
  assert!((64u8 * radix.pow(3) + 64u8 * radix.pow(2) + 64u8 * &radix) < r);
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
  let paired_positive: Vec<_> =
    raw(&(radix.pow(2) - 1u8)).into_iter().chain(raw(&high)).collect();
  let retained = fq::advice("bn254.fq.mul_pairs", &paired_positive).unwrap();
  assert_eq!(integer(retained[8]), &bias + &radix - 2u8);
  assert!(
    fq::advice("bn254.fq.mul_pairs", &negative).unwrap()[8..]
      .iter()
      .all(|&carry| integer(carry) < bias)
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
fn canonical_prefix_checks_boundaries_with_zero_fallback_range_advice() {
  let plan = plan();
  let fallbacks = Arc::new(AtomicUsize::new(0));
  let observed = Arc::clone(&fallbacks);
  let channels = poisoned(&plan, "bn254.fq.u16_80", move |input, output| {
    if fq::advice("bn254.fq.u16_80", input).is_err() {
      assert_eq!(*output, vec![Bn254.zero(); 5]);
      observed.fetch_add(1, Ordering::Relaxed);
    }
  });
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let prime = modulus();
  let mut values =
    vec![BigUint::from(0u8), &prime - 1u8, prime.clone(), &prime + 1u8];
  let scalar_prime =
    BigUint::from_bytes_le(&ark_bn254::Fr::MODULUS.to_bytes_le());
  values.extend([
    &scalar_prime - 1u8,
    scalar_prime.clone(),
    &scalar_prime + 1u8,
  ]);
  for limb in 0..4 {
    let bits = fq::LIMB_BITS * limb;
    let prefix = (&prime >> bits) << bits;
    let step = BigUint::from(1u8) << bits;
    values.extend([
      &prefix - 1u8,
      prefix.clone(),
      &prefix + 1u8,
      &prefix + &step - 1u8,
      &prefix + &step,
    ]);
  }
  for value in values {
    let input = raw(&value);
    let result = executor.execute("FqTest::canonical", input.clone());
    if value < prime {
      assert_eq!(result.unwrap().output, input);
    } else {
      assert!(result.is_err(), "accepted noncanonical integer {value}");
    }
  }
  let radix = BigUint::from(1u8) << fq::LIMB_BITS;
  for base in [BigUint::from(0u8), &prime - 1u8] {
    for limb in 0..4 {
      for invalid in [scalar(&radix), -Bn254.one()] {
        let mut input = raw(&base);
        input[limb] = invalid;
        assert!(executor.execute("FqTest::canonical", input).is_err());
      }
    }
  }
  assert!(fallbacks.load(Ordering::Relaxed) > 0);
  let before = fallbacks.load(Ordering::Relaxed);
  let error = executor.execute("FqTest::canonical", raw(&prime)).unwrap_err();
  assert_eq!(fallbacks.load(Ordering::Relaxed), before + 1);
  assert_eq!(error.function, "BN254Fq::range80");
  assert!(error.message.contains("Fq 80-bit decomposition"), "{error}");

  for chunks in [
    vec![Bn254.one(), Bn254.zero(), Bn254.zero(), Bn254.zero(), Bn254.zero()],
    vec![
      Bn254.from_u64(65536),
      -Bn254.one(),
      Bn254.zero(),
      Bn254.zero(),
      Bn254.zero(),
    ],
  ] {
    let supplied = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&supplied);
    let channels = poisoned(&plan, "bn254.fq.u16_80", move |_, output| {
      output.clone_from(&chunks);
      observed.fetch_add(1, Ordering::Relaxed);
    });
    let error = plan
      .program()
      .prepare_hint_channels(&[], &channels)
      .unwrap()
      .execute("FqTest::canonical", vec![Bn254.zero(); 4])
      .unwrap_err();
    assert!(supplied.load(Ordering::Relaxed) > 0);
    assert_eq!(error.function, "BN254Fq::range80");
  }
}

#[test]
fn add_sub_carries_cover_signed_boundaries_and_reject_outside_the_map() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let radix = BigUint::from(1u8) << fq::LIMB_BITS;
  let bias = 8u8 * &radix;
  let allowed = [scalar(&(&bias - 1u8)), scalar(&bias), scalar(&(&bias + 1u8))];
  let mut seen = [false; 3];
  let values = [
    BigUint::from(0u8),
    BigUint::from(1u8),
    &radix - 1u8,
    radix.clone(),
    radix.pow(2) - 1u8,
    radix.pow(2),
    modulus() - 2u8,
    modulus() - 1u8,
  ];
  for a in &values {
    for b in &values {
      let args: Vec<_> = raw(a).into_iter().chain(raw(b)).collect();
      let a = Fq::from_le_bytes_mod_order(&a.to_bytes_le());
      let b = Fq::from_le_bytes_mod_order(&b.to_bytes_le());
      for (channel, entry, expected) in [
        ("bn254.fq.add", "FqTest::add", a + b),
        ("bn254.fq.sub", "FqTest::sub", a - b),
      ] {
        let advice = fq::advice(channel, &args).unwrap();
        for carry in &advice[5..] {
          let index = allowed.iter().position(|value| value == carry).unwrap();
          seen[index] = true;
        }
        let record = executor.execute(entry, args.clone()).unwrap();
        assert_eq!(record.output, fq::encode(expected));
      }
    }
  }
  assert_eq!(seen, [true; 3]);
  for carry in allowed {
    executor.execute("FqTest::add_sub_carry", vec![carry]).unwrap();
  }
  for carry in
    [scalar(&(&bias - 2u8)), scalar(&(&bias + 2u8)), Bn254.zero(), -Bn254.one()]
  {
    assert!(executor.execute("FqTest::add_sub_carry", vec![carry]).is_err());
  }
  for (channel, entry) in
    [("bn254.fq.add", "FqTest::add"), ("bn254.fq.sub", "FqTest::sub")]
  {
    for index in 5..8 {
      let channels = poisoned(&plan, channel, move |_, output| {
        output[index] = allowed[1] + Bn254.from_u64(2);
      });
      assert!(
        plan
          .program()
          .prepare_hint_channels(&[], &channels)
          .unwrap()
          .execute(entry, vec![Bn254.zero(); 8])
          .is_err()
      );
    }
  }
}

#[test]
fn kzg_add_sub_carries_and_fixed_lookup_are_constrained() {
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
    .unwrap()
    .next_power_of_two();
  let backend = Backend::new(
    &plan,
    KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(capacity, b"aiur-fq-add-carry-test")),
      8,
    ),
  )
  .unwrap();
  let radix = BigUint::from(1u8) << fq::LIMB_BITS;
  let boundary = Fq::from_le_bytes_mod_order(&radix.pow(2).to_bytes_le());
  for (entry, function_name, channel, a, expected) in [
    (
      "FqTest::add",
      "BN254Fq::add",
      "bn254.fq.add",
      boundary - Fq::from(1),
      boundary,
    ),
    (
      "FqTest::sub",
      "BN254Fq::sub",
      "bn254.fq.sub",
      boundary,
      boundary - Fq::from(1),
    ),
  ] {
    let args: Vec<_> =
      fq::encode(a).into_iter().chain(fq::encode(Fq::from(1))).collect();
    let record = executor.execute(entry, args.clone()).unwrap();
    assert_eq!(record.output, fq::encode(expected));
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
    for &destination in &dest[5..8] {
      let column = fill
        .writes
        .iter()
        .find(|write| write.source == destination)
        .unwrap()
        .column;
      let mut traces = witness.traces.clone();
      traces[placement.circuit].values[placement.columns[column]] +=
        Bn254.from_u64(3);
      let forged = SystemWitness::from_stage_1(traces, backend.system());
      let proof = backend.prove(entry, &args, &record.output, forged).unwrap();
      assert!(backend.verify(entry, &args, &record.output, &proof).is_err());
    }
  }
  let entry = "FqTest::add_sub_carry";
  let args = [scalar(&(8u8 * &radix))];
  let record = executor.execute(entry, args.to_vec()).unwrap();
  let witness = backend.generate(&record, entry, &args).unwrap();
  let proof = backend.prove(entry, &args, &[], witness.clone()).unwrap();
  backend.verify(entry, &args, &[], &proof).unwrap();
  let chip =
    plan.function_chips()[plan.program().entry(entry).unwrap().function];
  let layout = plan.layout().unwrap();
  let placement = &layout.placements[chip];
  assert!(!placement.grouped);
  let column = placement.columns[plan.artifact().chips[chip].inputs[0]];
  let mut traces = witness.traces;
  traces[placement.circuit].values[column] += Bn254.from_u64(2);
  let forged = SystemWitness::from_stage_1(traces, backend.system());
  let outside = [args[0] + Bn254.from_u64(2)];
  let proof = backend.prove(entry, &outside, &[], forged).unwrap();
  assert!(backend.verify(entry, &outside, &[], &proof).is_err());
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
    ("bn254.fq.mul_pairs", "FqTest::mul", 0),
    ("bn254.fq.mul_pairs", "FqTest::mul", 4),
    ("bn254.fq.mul_pairs", "FqTest::mul", 7),
    ("bn254.fq.mul_pairs", "FqTest::mul", 8),
    ("bn254.fq.mul_pairs", "FqTest::mul", 9),
    ("bn254.fq.mul_pairs", "FqTest::mul", 10),
    ("bn254.fq.add", "FqTest::add", 4),
    ("bn254.fq.sub", "FqTest::sub", 4),
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
  let positive_b = Fq::from_le_bytes_mod_order(
    &((BigUint::from(1u8) << 80usize) - 1u8).to_bytes_le(),
  );
  let positive_a = Fq::from_le_bytes_mod_order(
    &((BigUint::from(1u8) << 160usize) - 1u8).to_bytes_le(),
  );
  let pair: Vec<_> = fq::encode(a).into_iter().chain(fq::encode(b)).collect();
  for (entry, args, expected) in [
    ("FqTest::add", pair.clone(), a + b),
    ("FqTest::sub", pair.clone(), a - b),
    ("FqTest::mul", pair, a * b),
    (
      "FqTest::mul",
      fq::encode(positive_a)
        .into_iter()
        .chain(fq::encode(positive_b))
        .collect(),
      positive_a * positive_b,
    ),
    ("FqTest::inverse", fq::encode(b).to_vec(), b.inverse().unwrap()),
    ("FqTest::canonical", fq::encode(-Fq::from(1)).to_vec(), -Fq::from(1)),
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
          Action::Hint { channel, dest, .. }
            if channel == "bn254.fq.mul_pairs" =>
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
      for advice_index in [4, 7, 8, 9, 10] {
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

#[test]
fn canonical_endpoint_forgery_has_valid_raw_limb_decompositions() {
  let plan = plan();
  let channels = channels();
  let capacity = plan
    .program()
    .program()
    .tables
    .iter()
    .map(|table| table.rows.len())
    .max()
    .unwrap()
    .next_power_of_two();
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(
      capacity,
      b"aiur-fq-canonical-endpoint-test",
    )),
    8,
  );
  let backend = Backend::new(&plan, config.clone()).unwrap();
  let entry = "FqTest::canonical";
  let accepted = raw(&(modulus() - 1u8));
  let rejected = raw(&modulus());
  assert_eq!(&accepted[1..], &rejected[1..]);
  assert_eq!(accepted[0] + Bn254.one(), rejected[0]);
  for limb in &rejected {
    assert!(integer(*limb) < BigUint::from(1u8) << fq::LIMB_BITS);
  }
  let record = plan
    .program()
    .prepare_hint_channels(&[], &channels)
    .unwrap()
    .execute(entry, accepted.clone())
    .unwrap();
  let mut traces = backend.generate(&record, entry, &accepted).unwrap().traces;
  let (function, fill) = plan
    .artifact()
    .functions
    .iter()
    .enumerate()
    .find(|(_, fill)| fill.name == "BN254Fq::range80")
    .unwrap();
  let chip = plan.function_chips()[function];
  let layout = plan.layout().unwrap();
  let placement = &layout.placements[chip];
  assert!(!placement.grouped);
  let input_column = placement.columns[plan.artifact().chips[chip].inputs[0]];
  let range_trace = &traces[placement.circuit];
  let rows: Vec<_> = range_trace
    .values
    .chunks_exact(range_trace.width)
    .enumerate()
    .filter_map(|(i, row)| (row[input_column] == accepted[0]).then_some(i))
    .collect();
  assert_eq!(rows.len(), 1);
  let row_offset = rows[0] * range_trace.width;
  let destinations = fill
    .steps
    .iter()
    .find_map(|step| match &step.action {
      Action::Hint { channel, dest, .. } if channel == "bn254.fq.u16_80" => {
        Some(dest)
      },
      _ => None,
    })
    .unwrap();
  let old_chunks = fq::advice("bn254.fq.u16_80", &[accepted[0]]).unwrap();
  let new_chunks = fq::advice("bn254.fq.u16_80", &[rejected[0]]).unwrap();
  assert!(
    new_chunks.iter().all(|&chunk| Bn254.try_to_u64(chunk).unwrap() < 1 << 16)
  );
  for trace in &mut traces {
    for value in &mut trace.values {
      if *value == accepted[0] {
        *value = rejected[0];
      }
    }
  }
  for ((&destination, old), new) in
    destinations.iter().zip(&old_chunks).zip(&new_chunks)
  {
    let Some(column) = fill
      .writes
      .iter()
      .find(|write| write.source == destination)
      .map(|write| write.column)
    else {
      // Linear elimination reconstructs this chunk from the input and the
      // retained chunks; the emitted lookup values are checked below.
      continue;
    };
    let cell = &mut traces[placement.circuit].values
      [row_offset + placement.columns[column]];
    assert_eq!(*cell, *old);
    *cell = *new;
  }
  let logical_row: Vec<_> = placement
    .columns
    .iter()
    .map(|&column| traces[placement.circuit].values[row_offset + column])
    .collect();
  fn value(polynomial: &Polynomial<FieldWord>, row: &[Scalar]) -> Scalar {
    match polynomial {
      Polynomial::Const(value) => Bn254.from_word(*value),
      Polynomial::Var(column) => row[*column],
      Polynomial::Add(terms) => value(&terms[0], row) + value(&terms[1], row),
      Polynomial::Sub(terms) => value(&terms[0], row) - value(&terms[1], row),
      Polynomial::Mul(terms) => value(&terms[0], row) * value(&terms[1], row),
    }
  }
  let raw_range_chunks: Vec<_> = plan.artifact().chips[chip]
    .sends
    .iter()
    .filter(|send| send.channel == "BN254Fq::limb16")
    .map(|send| value(&send.args[0], &logical_row))
    .collect();
  assert_eq!(raw_range_chunks, new_chunks);

  let mut inputs = circuit_inputs(&plan).unwrap();
  let program = plan.program().program();
  let limb_map =
    program.maps.iter().position(|map| map.name == "BN254Fq::limb16").unwrap();
  let callable =
    Bn254.from_u64(u64::try_from(program.functions.len() + limb_map).unwrap());
  let (table, lookup) = inputs.iter().enumerate().find_map(|(index, input)| {
    input.preprocessed.as_ref()?;
    input.lookups.iter().find(|lookup| matches!(lookup.args.get(1), Some(Expr::Const(value)) if *value == callable))
      .map(|lookup| (index, lookup))
  }).unwrap();
  let Expr::Neg(count) = &lookup.multiplicity else {
    panic!("fixed-map multiplicity")
  };
  let Expr::Var(count_column) = count.as_ref() else {
    panic!("fixed-map count column")
  };
  let Expr::Var(value_column) = lookup.args[2] else {
    panic!("fixed-map value")
  };
  assert_eq!(count_column.source, Source::Main);
  assert_eq!(value_column.source, Source::Preprocessed);
  let fixed = inputs[table].preprocessed.as_ref().unwrap();
  for (old, new) in old_chunks.iter().zip(&new_chunks).filter(|(a, b)| a != b) {
    for (value, increment) in [(old, -Bn254.one()), (new, Bn254.one())] {
      let row = fixed
        .values
        .chunks_exact(fixed.width)
        .position(|row| row[value_column.index as usize] == *value)
        .unwrap();
      let width = traces[table].width;
      let count =
        &mut traces[table].values[row * width + count_column.index as usize];
      if increment == -Bn254.one() {
        assert!(Bn254.try_to_u64(*count).unwrap() > 0);
      }
      *count += increment;
    }
  }

  let claim = backend.claim(entry, &rejected, &rejected).unwrap();
  let proof = backend
    .prove(
      entry,
      &rejected,
      &rejected,
      SystemWitness::from_stage_1(traces.clone(), backend.system()),
    )
    .unwrap();
  assert!(backend.verify(entry, &rejected, &rejected, &proof).is_err());

  fn relax(expr: &mut Expr<Scalar>, old: Scalar, new: Scalar) -> usize {
    match expr {
      Expr::Const(value) if *value == old => {
        *value = new;
        1
      },
      Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) => {
        relax(a, old, new) + relax(b, old, new)
      },
      Expr::Neg(value) => relax(value, old, new),
      _ => 0,
    }
  }
  let comparison = backend
    .circuit_names()
    .iter()
    .position(|name| name == "BN254Fq::canonical_low")
    .unwrap();
  let mut replaced = 0;
  for constraint in &mut inputs[comparison].constraints {
    replaced += relax(constraint, accepted[0], rejected[0]);
  }
  for lookup in &mut inputs[comparison].lookups {
    replaced += relax(&mut lookup.multiplicity, accepted[0], rejected[0]);
    for argument in &mut lookup.args {
      replaced += relax(argument, accepted[0], rejected[0]);
    }
  }
  assert!(replaced > 0);
  // Accepting the same matrices with only p0-1 changed to p0 isolates the
  // strict canonical endpoint from raw ranges and fixed-table membership.
  let (relaxed, key) = System::new(config, inputs);
  let witness = SystemWitness::from_stage_1(traces, &relaxed);
  let proof = relaxed.prove(&key, &claim, witness);
  relaxed.verify(&claim, &proof).unwrap();
}
