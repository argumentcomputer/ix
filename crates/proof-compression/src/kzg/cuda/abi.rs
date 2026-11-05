//! Zero-copy field and point layouts shared with the native KZG backend.

use super::{BigInt, FftJob, Fq, Fr, G1Affine};
use ark_ff::{FftField, Field, PrimeField};

pub(super) const FQ_LIMBS: usize = 4;

pub(super) type FqLimbs = [u64; FQ_LIMBS];
pub(super) type ProjectiveLimbs = [FqLimbs; 3];
pub(super) const DEVICE_AFFINE_BYTES: usize = 2 * size_of::<FqLimbs>();

// Sppark's 32-bit domain stride cannot represent 2^32.
pub(super) const MAX_FFT_LOG: usize =
  if Fr::TWO_ADICITY < 31 { Fr::TWO_ADICITY as usize } else { 31 };

const _: () = {
  assert!(cfg!(target_endian = "little"));
  assert!(size_of::<Fr>() == size_of::<[u64; 4]>());
  assert!(align_of::<Fr>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(Fr, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<4>, 0) == 0);
  assert!(size_of::<Fq>() == size_of::<FqLimbs>());
  assert!(align_of::<Fq>() == align_of::<FqLimbs>());
  assert!(std::mem::offset_of!(Fq, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<FQ_LIMBS>, 0) == 0);
  assert!(size_of::<G1Affine>() == DEVICE_AFFINE_BYTES + size_of::<u64>());
  assert!(align_of::<G1Affine>() == align_of::<FqLimbs>());
  assert!(std::mem::offset_of!(G1Affine, x) == 0);
  assert!(std::mem::offset_of!(G1Affine, y) == size_of::<FqLimbs>());
  assert!(std::mem::offset_of!(G1Affine, infinity) == DEVICE_AFFINE_BYTES);
  assert!(size_of::<FftJob>() == 40 && align_of::<FftJob>() == 8);
  assert!(std::mem::offset_of!(FftJob, resident_input) == 8);
  assert!(std::mem::offset_of!(FftJob, output) == 16);
  assert!(std::mem::offset_of!(FftJob, input_count) == 24);
  assert!(std::mem::offset_of!(FftJob, resident_output) == 32);
};

unsafe extern "C" {
  fn ix_kzg_check_field_abi(
    fq: *const [FqLimbs; 3],
    fq_bytes: usize,
    fr: *const [[u64; 4]; 3],
    fr_bytes: usize,
  ) -> i32;
}

fn matches_native(fq: &[FqLimbs; 3], fr: &[[u64; 4]; 3]) -> bool {
  // The native check reads only these fixed-size arrays and does not use CUDA.
  unsafe {
    ix_kzg_check_field_abi(fq, size_of_val(fq), fr, size_of_val(fr)) == 0
  }
}

pub(super) fn validate() {
  assert!(
    matches_native(
      &[Fq::MODULUS.0, Fq::ONE.0.0, Fq::R2.0],
      &[Fr::MODULUS.0, Fr::ONE.0.0, Fr::R2.0],
    ),
    "KZG native and Rust field representations differ"
  );
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn native_montgomery_parameters_match_arkworks() {
    validate();
    let fq = [Fq::MODULUS.0, Fq::ONE.0.0, Fq::R2.0];
    let fr = [Fr::MODULUS.0, Fr::ONE.0.0, Fr::R2.0];
    for parameter in 0..3 {
      let mut wrong_fq = fq;
      wrong_fq[parameter].reverse();
      assert!(!matches_native(&wrong_fq, &fr));
      let mut wrong_fr = fr;
      wrong_fr[parameter].reverse();
      assert!(!matches_native(&fq, &wrong_fr));
    }
    assert_ne!(
      unsafe {
        ix_kzg_check_field_abi(&fq, size_of_val(&fq) - 8, &fr, size_of_val(&fr))
      },
      0
    );
  }
}
