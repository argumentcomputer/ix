use crate::boolean::{BooleanR1csPlan, generate_boolean_witness};
use flock_prover::{field::F128, union::SlotWitnessDest};

/// Compare every packed column and lincheck stripe against sparse-matrix
/// evaluation, including recycled/poisoned buffers and both elision hints.
pub(super) fn padding<T>(
  plan: &BooleanR1csPlan,
  rows: &[T],
  fill: impl Fn(&T, &mut [bool]),
  generate: impl Fn(SlotWitnessDest<'_>) -> Vec<u8>,
) {
  let expected = generate_boolean_witness(plan, rows, 3, fill);
  for elide_padding_writes in [false, true] {
    let mut z = vec![F128::new(u64::MAX, u64::MAX); expected.0.len()];
    let mut a = z.clone();
    let mut b = z.clone();
    let stripe = generate(SlotWitnessDest {
      z: &mut z,
      a: &mut a,
      b: &mut b,
      elide_padding_writes,
    });
    assert_eq!((z, a, b, stripe), expected);
  }
}
