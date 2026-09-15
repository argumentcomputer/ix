use super::*;
use crate::R1csShapeLimitsV0;

const PHASE: ConstraintPhase = ConstraintPhase::Pcs;

fn shape_builder() -> R1csBuilder {
  R1csBuilder::new_shape(R1csShapeLimitsV0 {
    variables: 10_000,
    constraints: 10_000,
    nonzero_terms: 100_000,
  })
  .unwrap()
}

fn range(builder: &mut R1csBuilder, value: Fr, maximum: usize) -> Variable {
  let variable = builder.alloc_private(value).unwrap();
  constrain_small_range(builder, RangeWire { variable, value }, maximum, PHASE)
    .unwrap();
  variable
}

fn multiply_polynomials(a: &[Fr], b: &[Fr]) -> Vec<Fr> {
  let mut out = vec![Fr::ZERO; a.len() + b.len() - 1];
  for (i, a) in a.iter().enumerate() {
    for (j, b) in b.iter().enumerate() {
      out[i + j] += *a * b;
    }
  }
  out
}

fn substitute(
  expression: &LinearCombination,
  known: &BTreeMap<Variable, Vec<Fr>>,
) -> Vec<Fr> {
  let mut out = vec![Fr::ZERO];
  for (variable, coefficient) in expression.terms() {
    let polynomial = &known[variable];
    out.resize(out.len().max(polynomial.len()), Fr::ZERO);
    for (i, value) in polynomial.iter().enumerate() {
      out[i] += *value * coefficient;
    }
  }
  while out.len() > 1 && out.last() == Some(&Fr::ZERO) {
    out.pop();
  }
  out
}

#[test]
fn actual_range_constraints_eliminate_to_exact_small_integer_roots() {
  // Symbolically eliminate the ACTUAL emitted definitions. Coefficientwise
  // equality with these factored polynomials proves the range over all Fr,
  // not just sampled witnesses. Repeated middle roots add no allowed values.
  for maximum in 0..=8 {
    let mut builder = shape_builder();
    let carry = range(&mut builder, Fr::ZERO, maximum);
    let r1cs = builder.finish_shape().unwrap();
    assert_eq!(r1cs.constraints().len(), [1, 1, 2, 2, 3, 3, 4, 4, 5][maximum]);
    let mut known = BTreeMap::from([
      (Variable::ONE, vec![Fr::ONE]),
      (carry, vec![Fr::ZERO, Fr::ONE]),
    ]);
    let mut residuals = Vec::new();
    for constraint in r1cs.constraints() {
      let product = multiply_polynomials(
        &substitute(&constraint.a, &known),
        &substitute(&constraint.b, &known),
      );
      if let [(variable, coefficient)] = constraint.c.terms() {
        assert_eq!(*coefficient, Fr::ONE);
        assert!(known.insert(*variable, product).is_none());
      } else {
        assert!(constraint.c.terms().is_empty());
        residuals.push(product);
      }
    }
    assert_eq!(known.len(), usize::try_from(r1cs.variables()).unwrap());
    let mut expected = vec![Fr::ONE];
    for root in 0..=maximum {
      expected =
        multiply_polynomials(&expected, &[-Fr::from(root as u64), Fr::ONE]);
    }
    if [4, 6, 8].contains(&maximum) {
      expected = multiply_polynomials(
        &expected,
        &[-Fr::from((maximum / 2) as u64), Fr::ONE],
      );
    }
    assert_eq!(residuals, vec![expected], "maximum={maximum}");
  }
}

#[test]
fn range_witnesses_cover_all_roots_reject_nonroots_and_bind_auxiliaries() {
  for maximum in 0..=8 {
    let mut setup = shape_builder();
    range(&mut setup, Fr::ZERO, maximum);
    let setup = setup.finish_shape().unwrap();
    for value in 0..=maximum {
      let mut builder = R1csBuilder::new();
      range(&mut builder, Fr::from(value as u64), maximum);
      let (r1cs, witness) = builder.finish().unwrap();
      assert_eq!(r1cs, setup);
      // The carry itself is free to take any admitted root. All auxiliary
      // product wires, however, must equal their defining expressions.
      for index in 2..r1cs.variables() {
        let mut corrupt = witness.clone();
        let variable = Variable::from_index(index);
        corrupt
          .set(variable, witness.assignment()[index as usize] + Fr::ONE)
          .unwrap();
        assert!(r1cs.check(&corrupt).is_err());
      }
    }
    for value in [
      -Fr::ONE,
      Fr::from(maximum as u64 + 1),
      Fr::from(19u64),
      Fr::from(2u64).inverse().unwrap(),
    ] {
      let mut builder = R1csBuilder::new();
      // Generate consistently recomputed auxiliaries for the bad carry;
      // rejection therefore comes from the range polynomial itself.
      range(&mut builder, value, maximum);
      assert!(builder.finish().is_err(), "maximum={maximum}, value={value}");
    }
  }
}

fn leaf(builder: &mut R1csBuilder, width: usize, a: u16, b: u16) {
  let words = [a, b].map(|value| {
    let bits = (0..width)
      .map(|i| {
        alloc_checked_bit(builder, value & (1 << i) != 0, PHASE).unwrap()
      })
      .collect::<Vec<_>>();
    let value = bits.iter().enumerate().fold(0u128, |sum, (i, bit)| {
      sum | (u128::from(bit.value) << (PACKED_COEFFICIENT_BITS * i))
    });
    let packed = builder.alloc_private(Fr::from(value)).unwrap();
    builder.enforce_zero(
      PHASE,
      LinearCombination::from_variable(packed)
        .minus(&pack_polynomial_bits(&bits)),
    );
    (bits, packed)
  });
  let out = packed_polynomial_product_ranged(
    builder,
    &words[0].0,
    &words[1].0,
    words[0].1,
    words[1].1,
    PHASE,
  )
  .unwrap();
  for (degree, bit) in out.iter().enumerate() {
    let parity = (0..width)
      .filter(|&i| degree >= i && degree - i < width)
      .fold(false, |parity, i| {
        parity ^ ((a & (1 << i) != 0) && (b & (1 << (degree - i)) != 0))
      });
    assert_eq!(bit.value, parity);
  }
}

#[test]
fn ranged_convolution_binds_every_input_pack_parity_carry_and_auxiliary() {
  for width in 1..=16 {
    let mut setup = shape_builder();
    leaf(&mut setup, width, 0, 0);
    let setup = setup.finish_shape().unwrap();
    for (a, b) in [(0, 0), (0x9a71, 0x4ab6), (u16::MAX, u16::MAX)] {
      let mut builder = R1csBuilder::new();
      leaf(&mut builder, width, a, b);
      let (r1cs, witness) = builder.finish().unwrap();
      assert_eq!(r1cs, setup);
      for index in 1..r1cs.variables() {
        let mut corrupt = witness.clone();
        corrupt
          .set(
            Variable::from_index(index),
            witness.assignment()[index as usize] + Fr::ONE,
          )
          .unwrap();
        assert!(
          r1cs.check(&corrupt).is_err(),
          "width={width}, variable={index}"
        );
      }
    }
  }
}

#[test]
fn ranged_helpers_reject_invalid_shapes_and_preserve_sticky_refusals() {
  let mut builder = R1csBuilder::new();
  let carry = RangeWire {
    variable: builder.alloc_private(Fr::ZERO).unwrap(),
    value: Fr::ZERO,
  };
  for maximum in [9, usize::MAX] {
    assert_eq!(
      constrain_small_range(&mut builder, carry, maximum, PHASE),
      Err(R1csError::InternalShape)
    );
  }
  for (a, b) in [(0, 0), (1, 2), (17, 17)] {
    let left = vec![BitWire::constant(false); a];
    let right = vec![BitWire::constant(false); b];
    assert!(matches!(
      packed_polynomial_product_ranged(
        &mut builder,
        &left,
        &right,
        Variable::ONE,
        Variable::ONE,
        PHASE
      ),
      Err(R1csError::InternalShape)
    ));
  }
  assert!(builder.finish().unwrap().0.constraints().is_empty());
  let error =
    R1csError::ResourceLimit { resource: "ranged test", limit: 0, actual: 1 };
  let fail = error.clone();
  let mut builder =
    R1csBuilder::new_projection_observed_fallible(move |_| Err(fail.clone()));
  let variable = builder.alloc_private(Fr::ZERO).unwrap();
  let carry = RangeWire { variable, value: Fr::ZERO };
  assert_eq!(
    constrain_small_range(&mut builder, carry, 8, PHASE),
    Err(error.clone())
  );
  assert_eq!(
    constrain_small_range(&mut builder, carry, 0, PHASE),
    Err(error.clone())
  );
  assert_eq!(builder.finish_projection(), Err(error));
}
