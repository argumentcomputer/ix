use super::*;
use ark_ff::BigInt as Limbs;
use interval::GatePlan;

fn reference_plan(coefficients: [i128; 5], bounds: [u64; 3]) -> GatePlan {
  let (low, high) = interval(coefficients, bounds);
  let p = BigInt::from(P);
  if low > -&p && high < p {
    return GatePlan::Direct;
  }
  let shift =
    if low < BigInt::from(0) { (-low + &p - 1) / &p } else { BigInt::from(0) };
  let offset = &shift * &p;
  let max_q: BigInt = (high + &offset) / &p;
  let bits = usize::try_from(max_q.bits()).unwrap();
  let (sign, words) = offset.to_u64_digits();
  assert_ne!(sign, Sign::Minus);
  let mut offset = Limbs::zero();
  offset.0[..words.len()].copy_from_slice(&words);
  GatePlan::Quotient { offset, bits }
}

#[test]
fn fixed_intervals_match_signed_boundaries_and_quotient_bits() {
  let half = i128::from(P / 2);
  for coefficients in [
    [0; 5],
    [0, -1, 0, 0, 0],
    [0, -1, 0, 0, -1],
    [0, 1, 0, 0, 0],
    [0, 1, 0, 0, 1],
    [1, 0, 0, 0, 0],
    [-1, 0, 0, 0, -1],
    [-half, -half, -half, -half, -half],
    [half; 5],
    [half, -half, half, -half, -half],
  ] {
    for bounds in [
      [0; 3],
      [1; 3],
      [P - 2, 1, 0],
      [P - 1; 3],
      [P; 3],
      [P + 1; 3],
      [u64::MAX; 3],
    ] {
      assert_eq!(
        GatePlan::new(coefficients, bounds),
        reference_plan(coefficients, bounds),
        "coefficients={coefficients:?}, bounds={bounds:?}"
      );
    }
  }
  assert_eq!(
    GatePlan::new([0, -1, 0, 0, -1], [P - 1, 0, 0]),
    GatePlan::Quotient { offset: Limbs::from(P), bits: 0 }
  );
  for bit in 1..64 {
    for maximum in [(1u64 << bit) - 1, 1u64 << bit, (1u64 << bit) + 1] {
      let coefficients = [1, 0, 0, 0, 0];
      let bounds = [P, maximum, 0];
      assert_eq!(
        GatePlan::new(coefficients, bounds),
        reference_plan(coefficients, bounds)
      );
    }
  }
  let mut state = 0x5fcd_06a9_8372_b14du64;
  let mut next = || {
    state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
    state
  };
  for _ in 0..16_384 {
    let coefficients = std::array::from_fn(|_| signed(Val::from_u64(next())));
    let bounds = std::array::from_fn(|_| next());
    assert_eq!(
      GatePlan::new(coefficients, bounds),
      reference_plan(coefficients, bounds)
    );
    for coefficient in coefficients {
      assert_eq!(
        signed_scalar(coefficient),
        scalar(&BigInt::from(coefficient))
      );
    }
  }
}
