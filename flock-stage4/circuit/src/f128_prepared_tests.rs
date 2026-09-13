use super::*;
use crate::R1csShapeLimitsV0;

const PHASE: ConstraintPhase = ConstraintPhase::Pcs;

fn oracle(a: [u8; 16], b: [u8; 16]) -> [u8; 16] {
  let mut a = u128::from_le_bytes(a);
  let mut b = u128::from_le_bytes(b);
  let mut out = 0;
  for _ in 0..128 {
    if b & 1 != 0 {
      out ^= a;
    }
    let carry = a >> 127;
    a <<= 1;
    if carry != 0 {
      a ^= 0x87;
    }
    b >>= 1;
  }
  out.to_le_bytes()
}

fn fixture(
  builder: &mut R1csBuilder,
  seed: u128,
) -> (Vec<F128VariablesV1>, Vec<Variable>) {
  let inputs = (0..4)
    .map(|index| {
      alloc_f128_private(
        builder,
        seed
          .wrapping_mul(index + 3)
          .rotate_left(u32::try_from(index).unwrap() * 19)
          .to_le_bytes(),
        PHASE,
      )
      .unwrap()
    })
    .collect::<Vec<_>>();
  let prepared = inputs
    .iter()
    .map(|input| prepare_f128_operand(builder, input, PHASE).unwrap())
    .collect::<Vec<_>>();
  let packed = prepared
    .iter()
    .flat_map(|p| p.leaves.iter().map(|leaf| leaf.packed))
    .collect();
  let mut outputs = inputs.clone();
  for a in 0..2 {
    for b in 2..4 {
      let result = constrain_f128_multiply_prepared(
        builder,
        &prepared[a],
        &prepared[b],
        PHASE,
      )
      .unwrap();
      assert_eq!(
        *result.value(),
        oracle(*inputs[a].value(), *inputs[b].value())
      );
      outputs.push(result);
    }
  }
  (outputs, packed)
}

#[test]
fn shared_operand_preparation_is_value_independent_and_every_wire_is_bound() {
  let mut first = None;
  for seed in [0, 0x81a7_bd49_6910_e87f_251d_03bf_812a_3495] {
    let mut builder = R1csBuilder::new();
    let (words, packed) = fixture(&mut builder, seed);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
    for word in &words {
      for &variable in word.bit_variables() {
        let mut corrupt = witness.clone();
        corrupt
          .set(
            variable,
            Fr::ONE - witness.assignment()[variable.index() as usize],
          )
          .unwrap();
        assert!(r1cs.check(&corrupt).is_err());
      }
    }
    assert_eq!(packed.len(), 4 * 27);
    for variable in packed {
      let mut corrupt = witness.clone();
      corrupt
        .set(
          variable,
          witness.assignment()[variable.index() as usize] + Fr::ONE,
        )
        .unwrap();
      assert!(r1cs.check(&corrupt).is_err());
    }
    if let Some(expected) = &first {
      assert_eq!(&r1cs, expected);
    } else {
      first = Some(r1cs);
    }
  }
  let mut builder = R1csBuilder::new_shape(R1csShapeLimitsV0 {
    variables: 100_000,
    constraints: 100_000,
    nonzero_terms: 1_000_000,
  })
  .unwrap();
  fixture(&mut builder, 0);
  assert_eq!(builder.finish_shape().unwrap(), first.unwrap());
}

#[test]
fn private_zero_is_not_constant_and_constant_and_square_paths_stay_exact() {
  let mut builder = R1csBuilder::new();
  let input = alloc_f128_private(&mut builder, [0; 16], PHASE).unwrap();
  let prepared = prepare_f128_operand(&mut builder, &input, PHASE).unwrap();
  assert_eq!(prepared.leaves.len(), 27);
  for raw in [0u128, 1, 2, u128::MAX] {
    let constant =
      alloc_f128_constant(&mut builder, raw.to_le_bytes(), PHASE).unwrap();
    let constant =
      prepare_f128_operand(&mut builder, &constant, PHASE).unwrap();
    assert!(constant.leaves.is_empty());
    for (left, right) in [(&prepared, &constant), (&constant, &prepared)] {
      let out =
        constrain_f128_multiply_prepared(&mut builder, left, right, PHASE)
          .unwrap();
      assert_eq!(*out.value(), [0; 16]);
    }
  }
  let square =
    constrain_f128_multiply_prepared(&mut builder, &prepared, &prepared, PHASE)
      .unwrap();
  assert_eq!(*square.value(), [0; 16]);
  let (r1cs, witness) = builder.finish().unwrap();
  r1cs.check(&witness).unwrap();

  for seed in [1u128, u128::MAX, 1 << 127, 0x7123_0198_abfe] {
    let mut builder = R1csBuilder::new();
    let a =
      alloc_f128_private(&mut builder, seed.to_le_bytes(), PHASE).unwrap();
    let a = prepare_f128_operand(&mut builder, &a, PHASE).unwrap();
    let square =
      constrain_f128_multiply_prepared(&mut builder, &a, &a, PHASE).unwrap();
    assert_eq!(*square.value(), oracle(seed.to_le_bytes(), seed.to_le_bytes()));
    builder.finish().unwrap();
  }
}

#[test]
fn prepared_emission_propagates_sticky_refusal() {
  let error = R1csError::ResourceLimit {
    resource: "prepared multiplication test",
    limit: 0,
    actual: 1,
  };
  let fail = error.clone();
  let mut builder =
    R1csBuilder::new_projection_observed_fallible(move |_| Err(fail.clone()));
  assert!(alloc_f128_private(&mut builder, [0; 16], PHASE).is_err());
  let mut good = R1csBuilder::new();
  let zero = alloc_f128_constant(&mut good, [0; 16], PHASE).unwrap();
  let prepared = prepare_f128_operand(&mut good, &zero, PHASE).unwrap();
  assert!(
    matches!(prepare_f128_operand(&mut builder, &zero, PHASE), Err(e) if e == error)
  );
  assert_eq!(
    constrain_f128_multiply_prepared(&mut builder, &prepared, &prepared, PHASE),
    Err(error.clone())
  );
  assert_eq!(builder.finish_projection(), Err(error));
}

fn cached_fixture(
  builder: &mut R1csBuilder,
  seed: u128,
  pairs: &[(usize, usize)],
) -> (Vec<F128VariablesV1>, Vec<Variable>) {
  let mut words = (0..4)
    .map(|i| {
      alloc_f128_private(
        builder,
        seed
          .wrapping_mul(i + 1)
          .rotate_left(u32::try_from(i).unwrap() * 29)
          .to_le_bytes(),
        PHASE,
      )
      .unwrap()
    })
    .collect::<Vec<_>>();
  let mut packed = std::collections::BTreeSet::new();
  for &(a, b) in pairs {
    let output =
      constrain_f128_multiply(builder, &words[a], &words[b], PHASE).unwrap();
    assert_eq!(*output.value(), oracle(*words[a].value(), *words[b].value()));
    words.push(output);
    let cache = builder.f128_preparation_cache().unwrap();
    assert!(cache.operands.len() <= cache.capacity);
    assert_eq!(cache.operands.len(), cache.order.len());
    for key in &cache.order {
      packed.extend(cache.operands[key].leaves.iter().map(|leaf| leaf.packed));
    }
  }
  (words, packed.into_iter().collect())
}

#[test]
fn builder_cache_constrains_reused_packs_and_is_value_independent() {
  let pairs = [(0, 2), (0, 3), (1, 2), (1, 3)];
  let mut expected = None;
  for seed in [0, 0x789a_5412_bac4_92e1_8403_bfde_5490_a034] {
    let mut builder = R1csBuilder::new();
    builder.enable_f128_preparation_cache(4).unwrap();
    let (words, packed) = cached_fixture(&mut builder, seed, &pairs);
    // Four DISTINCT wire words remain distinct even when every value is 0.
    assert_eq!(builder.f128_preparation_cache().unwrap().order.len(), 4);
    assert_eq!(packed.len(), 4 * 27);
    let (r1cs, witness) = builder.finish().unwrap();
    for variable in words
      .iter()
      .flat_map(|word| word.bit_variables().iter().copied())
      .chain(packed)
    {
      let mut corrupt = witness.clone();
      corrupt
        .set(
          variable,
          witness.assignment()[variable.index() as usize] + Fr::ONE,
        )
        .unwrap();
      assert!(r1cs.check(&corrupt).is_err());
    }
    if let Some(expected) = &expected {
      assert_eq!(&r1cs, expected);
    } else {
      expected = Some(r1cs);
    }
  }
  let mut builder = crate::r1cs::test_shape_builder();
  builder.enable_f128_preparation_cache(4).unwrap();
  cached_fixture(&mut builder, 0, &pairs);
  assert_eq!(builder.finish_shape().unwrap(), expected.unwrap());
}

#[test]
fn cache_eviction_is_bounded_fifo_and_owned_by_one_builder() {
  let pairs = [(0, 1), (0, 2), (0, 1), (2, 3), (3, 2), (0, 1)];
  for capacity in [1, 2, 4] {
    let mut expected = None;
    // Different builders have overlapping numeric wire indices but never
    // share preparations. All three MUST emit identical defining equations.
    for seed in [0u128, 1, u128::MAX] {
      let mut builder = R1csBuilder::new_projection();
      builder.enable_f128_preparation_cache(capacity).unwrap();
      cached_fixture(&mut builder, seed, &pairs);
      let projection = builder.finish_projection().unwrap();
      if let Some(expected) = &expected {
        assert_eq!(&projection, expected);
      } else {
        expected = Some(projection);
      }
    }
    let mut builder = R1csBuilder::new_shape_projection();
    builder.enable_f128_preparation_cache(capacity).unwrap();
    cached_fixture(&mut builder, 0, &pairs);
    assert_eq!(builder.finish_projection().unwrap(), expected.unwrap());
  }
  let mut builder = R1csBuilder::new();
  builder.enable_f128_preparation_cache(2).unwrap();
  let (words, _) = cached_fixture(&mut builder, 42, &pairs[..2]);
  let cache = builder.f128_preparation_cache().unwrap();
  // A hit on word 0 did NOT refresh its insertion order before word 2.
  assert_eq!(
    cache.order.iter().copied().collect::<Vec<_>>(),
    vec![*words[1].bit_variables(), *words[2].bit_variables()]
  );
  builder.finish().unwrap();
}

#[test]
fn caching_requires_a_fresh_builder_and_preserves_sticky_errors() {
  for mut builder in [
    R1csBuilder::new(),
    crate::r1cs::test_shape_builder(),
    R1csBuilder::new_projection(),
    R1csBuilder::new_shape_projection(),
  ] {
    assert_eq!(builder.f128_preparation_cache_capacity(), None);
    for capacity in [0, F128_PREPARATION_CACHE_MAX_CAPACITY + 1, usize::MAX] {
      assert_eq!(
        builder.enable_f128_preparation_cache(capacity),
        Err(R1csError::InvalidF128PreparationCacheCapacity { capacity })
      );
      assert_eq!(builder.f128_preparation_cache_capacity(), None);
    }
    builder.enforce_zero(PHASE, LinearCombination::zero());
    assert_eq!(
      builder.enable_f128_preparation_cache(2),
      Err(R1csError::BuilderConfigurationLocked)
    );
  }
  for public in [false, true] {
    let mut builder = R1csBuilder::new();
    if public {
      builder.alloc_public(Fr::ZERO).unwrap();
    } else {
      builder.alloc_private(Fr::ZERO).unwrap();
    }
    assert_eq!(
      builder.enable_f128_preparation_cache(2),
      Err(R1csError::BuilderConfigurationLocked)
    );
  }
  let mut builder = R1csBuilder::new();
  builder
    .enable_f128_preparation_cache(F128_PREPARATION_CACHE_MAX_CAPACITY)
    .unwrap();
  assert_eq!(
    builder.enable_f128_preparation_cache(1),
    Err(R1csError::BuilderConfigurationLocked)
  );
  let zero = alloc_f128_constant(&mut builder, [0; 16], PHASE).unwrap();
  let private = alloc_f128_private(&mut builder, [0; 16], PHASE).unwrap();
  for (a, b) in [(&zero, &private), (&private, &zero), (&private, &private)] {
    constrain_f128_multiply(&mut builder, a, b, PHASE).unwrap();
  }
  assert!(builder.f128_preparation_cache().unwrap().order.is_empty());
  builder.finish().unwrap();

  let refusal = R1csError::ObserverFailure("cache test".into());
  let fail = refusal.clone();
  let mut builder =
    R1csBuilder::new_projection_observed_fallible(move |_| Err(fail.clone()));
  builder.enable_f128_preparation_cache(2).unwrap();
  builder.enforce_zero(PHASE, LinearCombination::zero());
  assert_eq!(builder.enable_f128_preparation_cache(2), Err(refusal.clone()));
  assert_eq!(
    constrain_f128_multiply(&mut builder, &zero, &zero, PHASE),
    Err(refusal.clone())
  );
  assert!(builder.f128_preparation_cache().unwrap().order.is_empty());
  assert_eq!(builder.finish_projection(), Err(refusal));
}

#[test]
fn disabled_cache_keeps_the_original_materialized_relation() {
  fn emit(direct: bool) -> CanonicalR1csV1 {
    let mut builder = R1csBuilder::new();
    assert_eq!(builder.f128_preparation_cache_capacity(), None);
    let a = alloc_f128_private(&mut builder, [0x95; 16], PHASE).unwrap();
    let b = alloc_f128_private(&mut builder, [0x4e; 16], PHASE).unwrap();
    if direct {
      let product = karatsuba_product(
        &mut builder,
        &import_variables(&a),
        &import_variables(&b),
        PHASE,
      )
      .unwrap();
      export_product(&mut builder, a.value, b.value, product, PHASE).unwrap();
    } else {
      constrain_f128_multiply(&mut builder, &a, &b, PHASE).unwrap();
    }
    builder.finish().unwrap().0
  }
  assert_eq!(emit(false), emit(true));
}
