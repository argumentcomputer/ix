use aiur::{
  artifact::WidePackage, bytecode::Instruction, field::FieldBackend,
  hints::HintChannels, trace::TracePlan,
};
use ark_bn254::Fq;
use ark_ff::{BigInteger, PrimeField};
use ix_proof_compression::{
  aiur_backend::{Bn254, fq, pairing},
  kzg::Scalar,
  recursive::native_field::integer,
};
use num_bigint::BigUint;
use std::{collections::HashSet, path::PathBuf, sync::Arc};

fn plan() -> TracePlan<'static, Bn254> {
  let path = std::env::var_os("AIUR_FQ_PRODUCTS_FIXTURE").map_or_else(
    || {
      PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../aiur/tests/fixtures/bn254-fq-products.ixa")
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
  let mut result = HintChannels::new();
  fq::register(&mut result).unwrap();
  pairing::register(&mut result).unwrap();
  result
}
fn encoded(value: &BigUint) -> Scalar {
  let words = value.to_u64_digits();
  let mut limbs = [0; 4];
  limbs[..words.len()].copy_from_slice(&words);
  Bn254.from_word(aiur::FieldWord::from_limbs_le(limbs))
}
fn arguments(values: [Fq; 4], subtract: bool) -> Vec<Scalar> {
  values
    .into_iter()
    .flat_map(fq::encode)
    .chain([Bn254.from_u64(u64::from(subtract))])
    .collect()
}

#[test]
fn combined_product_advice_and_source_match_integer_reduction() {
  let plan = plan();
  let channels = channels();
  let executor = plan.program().prepare_hint_channels(&[], &channels).unwrap();
  let p = ix_proof_compression::recursive::native_field::modulus();
  let radix = BigUint::from(1u8) << 80usize;
  let cases = [
    Fq::from(0),
    Fq::from(1),
    -Fq::from(1),
    -Fq::from(2),
    Fq::from_le_bytes_mod_order(&radix.to_bytes_le()),
    Fq::from_le_bytes_mod_order(&(&radix - 1u8).to_bytes_le()),
  ];
  for (i, &a) in cases.iter().enumerate() {
    for values in [
      [a, a, a, a],
      [
        a,
        cases[(i + 1) % cases.len()],
        cases[(i + 2) % cases.len()],
        cases[(i + 3) % cases.len()],
      ],
    ] {
      for subtract in [false, true] {
        let args = arguments(values, subtract);
        let candidate =
          pairing::advice("bn254.pairing.fq_products_pairs", &args).unwrap();
        assert_eq!(candidate.len(), 11);
        let quotient = candidate[4..8]
          .iter()
          .rev()
          .fold(BigUint::from(0u8), |value, &limb| {
            (value << 80usize) + integer(limb)
          });
        assert!(quotient < 3u8 * &p);
        assert!(
          candidate[8..].iter().all(|&carry| integer(carry).bits() <= 86)
        );
        let second = values[2] * values[3];
        let expected =
          values[0] * values[1] + if subtract { -second } else { second };
        assert_eq!(fq::decode(&candidate[..4]).unwrap(), expected);
        assert_eq!(
          executor.execute("FqProductsTest::products", args).unwrap().output,
          fq::encode(expected)
        );
      }
    }
  }
  let a = Fq::from_le_bytes_mod_order(&(radix.pow(2) - 1u8).to_bytes_le());
  let b = Fq::from_le_bytes_mod_order(&(&radix - 1u8).to_bytes_le());
  let positive = pairing::advice(
    "bn254.pairing.fq_products_pairs",
    &arguments([a, b, Fq::from(0), Fq::from(0)], false),
  )
  .unwrap();
  let negative = pairing::advice(
    "bn254.pairing.fq_products_pairs",
    &arguments([Fq::from(0), Fq::from(0), a, b], true),
  )
  .unwrap();
  assert_eq!(integer(positive[8]), 33u8 * &radix - 2u8);
  assert_eq!(integer(negative[8]), 31u8 * &radix + 1u8);
  let scalar_modulus =
    BigUint::from_bytes_le(&ark_bn254::Fr::MODULUS.to_bytes_le());
  assert!(
    128u8 * radix.pow(3) + 128u8 * radix.pow(2) + 128u8 * &radix
      < scalar_modulus
  );
  for value in [BigUint::from(0u8), (BigUint::from(1u8) << 86usize) - 1u8] {
    executor.execute("FqProductsTest::range86", vec![encoded(&value)]).unwrap();
  }
  assert!(
    executor
      .execute(
        "FqProductsTest::range86",
        vec![encoded(&(BigUint::from(1u8) << 86usize))]
      )
      .is_err()
  );
  let mut bad = arguments([Fq::from(1); 4], false);
  bad[16] = Bn254.from_u64(2);
  assert!(executor.execute("FqProductsTest::products", bad).is_err());
}

fn poisoned(
  plan: &TracePlan<'_, Bn254>,
  change: impl Fn(&mut Vec<Scalar>) + Send + Sync + 'static,
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
            let mut candidate =
              if name == "bn254.fq.u16_80" && integer(input[0]).bits() > 80 {
                vec![Bn254.zero(); 5]
              } else if name.starts_with("bn254.pairing.") {
                pairing::advice(&name, input)?
              } else {
                fq::advice(&name, input)?
              };
            if name == "bn254.pairing.fq_products_pairs" {
              change(&mut candidate);
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
fn source_rejects_forged_signed_quotients_carries_and_endpoints() {
  let plan = plan();
  let args =
    arguments([-Fq::from(1), -Fq::from(2), Fq::from(3), Fq::from(7)], true);
  for index in [0usize, 4, 7, 8, 9, 10] {
    let hints = poisoned(&plan, move |values| values[index] += Bn254.one());
    let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
    assert!(
      executor.execute("FqProductsTest::products", args.clone()).is_err(),
      "accepted altered advice slot{index}"
    );
  }
  let hints = poisoned(&plan, |values| values[4] = Bn254.neg(Bn254.one()));
  let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
  let error =
    executor.execute("FqProductsTest::products", args.clone()).err().unwrap();
  assert!(
    !error.to_string().contains("advice value exceeds"),
    "rejection relied on honest decomposition advice"
  );
  let hints = poisoned(&plan, |values| {
    let maximum = encoded(&((BigUint::from(1u8) << 80usize) - 1u8));
    values[4..8].fill(maximum);
  });
  let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
  assert!(executor.execute("FqProductsTest::products", args).is_err());
}

#[test]
fn compiler_product_proofs_reject_retained_advice_mutations() {
  use aiur::trace::Action;
  use ix_proof_compression::{
    aiur_backend::kzg::Backend,
    kzg::{KzgConfig, Srs},
  };
  use multi_stark::system::SystemWitness;
  let plan = plan();
  let hints = channels();
  let executor = plan.program().prepare_hint_channels(&[], &hints).unwrap();
  let backend = Backend::new(
    &plan,
    KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(1 << 16, b"paired-products")),
      8,
    ),
  )
  .unwrap();
  for subtract in [false, true] {
    let args = arguments(
      [-Fq::from(1), -Fq::from(2), Fq::from(3), Fq::from(7)],
      subtract,
    );
    let record =
      executor.execute("FqProductsTest::products", args.clone()).unwrap();
    let witness =
      backend.generate(&record, "FqProductsTest::products", &args).unwrap();
    let proof = backend
      .prove("FqProductsTest::products", &args, &record.output, witness.clone())
      .unwrap();
    backend
      .verify("FqProductsTest::products", &args, &record.output, &proof)
      .unwrap();
    let (function, fill) = plan
      .artifact()
      .functions
      .iter()
      .enumerate()
      .find(|(_, f)| f.name == "BN254FqProducts::reduce")
      .unwrap();
    let dest = fill
      .steps
      .iter()
      .find_map(|step| match &step.action {
        Action::Hint { channel, dest, .. }
          if channel == "bn254.pairing.fq_products_pairs" =>
        {
          Some(dest)
        },
        _ => None,
      })
      .unwrap();
    let layout = plan.layout().unwrap();
    let placement = &layout.placements[plan.function_chips()[function]];
    let columns: Vec<_> = [4, 7, 8, 9, 10]
      .into_iter()
      .filter_map(|i| {
        fill
          .writes
          .iter()
          .find(|write| write.source == dest[i])
          .map(|write| placement.columns[write.column])
      })
      .collect();
    assert!(columns.len() >= 3, "retained carry columns must be covered");
    for column in columns {
      let mut traces = witness.traces.clone();
      traces[placement.circuit].values[column] += Bn254.one();
      let forged = backend
        .prove(
          "FqProductsTest::products",
          &args,
          &record.output,
          SystemWitness::from_stage_1(traces, backend.system()),
        )
        .unwrap();
      assert!(
        backend
          .verify("FqProductsTest::products", &args, &record.output, &forged)
          .is_err()
      );
    }
  }
}
