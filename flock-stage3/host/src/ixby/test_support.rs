use crate::boolean::{BooleanR1csPlan, generate_boolean_witness};
use flock_prover::{field::F128, union::SlotWitnessDest};

/// Retained Init parser fixture with only byte 8 changed from semantics 0 to 2.
/// Its body is unchanged from raw BLAKE3
/// a661dfede7c18bfb915d031393ffb258e65c21940d48039cdf44ab16428fe301.
/// This is a format regression fixture, not a compiler conversion optimization
/// or a transfer of the original execution proof to a new statement.
pub(super) const INIT_PROGRAM_V2_BLAKE3: &str =
  "e2bf515b731c1a00110e19e2ab8478bcf4be002eb3f60de94c0b73775777fea7";

/// The matching Init transports also change only byte 8 from 0 to 2.
pub(super) const INIT_INPUT_V2_BLAKE3: &str =
  "a69ff49c0fcb870029ac92911748cd1ac8c66c2678ca38d3d9ad3a884c21bf8c";
pub(super) const INIT_OUTPUT_V2_BLAKE3: &str =
  "971b7e63a5363c71bc4bf30421b7f06088a02329755473b8e751173beb11719a";

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
