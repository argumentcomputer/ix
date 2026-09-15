use crate::KzgVerifierKeyV1;
use ark_bls12_381::{Fr, G1Affine, G2Affine};
use ark_ec::AffineRepr;
use ark_ff::{FftField, Field, One, Zero};
use core::fmt;

/// Validated circuit-specific material needed by the Stage 4 FFLONK verifier.
///
/// Roots of unity are derived canonically from Arkworks' BLS12-381 scalar
/// field configuration rather than accepted as independently supplied values.
/// This prevents a verification key from mixing incompatible root families.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkVerificationKeyV1 {
  num_public_inputs: usize,
  domain_size: u64,
  k1: Fr,
  k2: Fr,
  omega: Fr,
  omega_3: Fr,
  omega_4: Fr,
  omega_8: Fr,
  omega_r: Fr,
  c0: G1Affine,
  kzg: KzgVerifierKeyV1,
}

impl FflonkVerificationKeyV1 {
  pub fn new(
    num_public_inputs: usize,
    domain_size: u64,
    k1: Fr,
    k2: Fr,
    c0: G1Affine,
    kzg: KzgVerifierKeyV1,
  ) -> Result<Self, FflonkVerificationKeyError> {
    if domain_size < 2 || !domain_size.is_power_of_two() {
      return Err(FflonkVerificationKeyError::InvalidDomainSize {
        domain_size,
      });
    }
    let domain_inputs = u64::try_from(num_public_inputs).map_err(|_| {
      FflonkVerificationKeyError::TooManyPublicInputs {
        public_inputs: num_public_inputs,
        domain_size,
      }
    })?;
    if domain_inputs >= domain_size {
      return Err(FflonkVerificationKeyError::TooManyPublicInputs {
        public_inputs: num_public_inputs,
        domain_size,
      });
    }
    if !valid_cosets(k1, k2, domain_size) {
      return Err(FflonkVerificationKeyError::InvalidPermutationCosets);
    }
    if !valid_g1(&c0) {
      return Err(FflonkVerificationKeyError::InvalidC0);
    }
    if !valid_kzg_key(&kzg) {
      return Err(FflonkVerificationKeyError::InvalidKzgKey);
    }

    let omega = Fr::get_root_of_unity(domain_size).ok_or(
      FflonkVerificationKeyError::UnsupportedDomainSize { domain_size },
    )?;
    let omega_3 = Fr::get_root_of_unity(3)
      .ok_or(FflonkVerificationKeyError::MissingRootOfUnity { order: 3 })?;
    let omega_4 = Fr::get_root_of_unity(4)
      .ok_or(FflonkVerificationKeyError::MissingRootOfUnity { order: 4 })?;
    let omega_8 = Fr::get_root_of_unity(8)
      .ok_or(FflonkVerificationKeyError::MissingRootOfUnity { order: 8 })?;
    let omega_r = omega.pow([inverse_of_three_mod_power_of_two(domain_size)]);
    debug_assert_eq!(omega_r.pow([3]), omega);

    Ok(Self {
      num_public_inputs,
      domain_size,
      k1,
      k2,
      omega,
      omega_3,
      omega_4,
      omega_8,
      omega_r,
      c0,
      kzg,
    })
  }

  #[must_use]
  pub const fn num_public_inputs(&self) -> usize {
    self.num_public_inputs
  }

  #[must_use]
  pub const fn domain_size(&self) -> u64 {
    self.domain_size
  }

  #[must_use]
  pub const fn k1(&self) -> Fr {
    self.k1
  }

  #[must_use]
  pub const fn k2(&self) -> Fr {
    self.k2
  }

  #[must_use]
  pub const fn omega(&self) -> Fr {
    self.omega
  }

  #[must_use]
  pub const fn omega_3(&self) -> Fr {
    self.omega_3
  }

  #[must_use]
  pub const fn omega_4(&self) -> Fr {
    self.omega_4
  }

  #[must_use]
  pub const fn omega_8(&self) -> Fr {
    self.omega_8
  }

  #[must_use]
  pub const fn omega_r(&self) -> Fr {
    self.omega_r
  }

  pub const fn c0(&self) -> G1Affine {
    self.c0
  }

  #[must_use]
  pub const fn kzg(&self) -> KzgVerifierKeyV1 {
    self.kzg
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkVerificationKeyError {
  InvalidDomainSize { domain_size: u64 },
  UnsupportedDomainSize { domain_size: u64 },
  TooManyPublicInputs { public_inputs: usize, domain_size: u64 },
  InvalidPermutationCosets,
  InvalidC0,
  InvalidKzgKey,
  MissingRootOfUnity { order: u64 },
}

impl fmt::Display for FflonkVerificationKeyError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidDomainSize { domain_size } => write!(
        formatter,
        "FFLONK domain size {domain_size} is not a power of two of size at least two",
      ),
      Self::UnsupportedDomainSize { domain_size } => write!(
        formatter,
        "BLS12-381 Fr has no configured root for FFLONK domain size {domain_size}",
      ),
      Self::TooManyPublicInputs { public_inputs, domain_size } => write!(
        formatter,
        "FFLONK has {public_inputs} public inputs for domain size {domain_size}",
      ),
      Self::InvalidPermutationCosets => formatter.write_str(
        "FFLONK permutation cosets H, k1*H, and k2*H are not disjoint",
      ),
      Self::InvalidC0 => {
        formatter.write_str("FFLONK C0 is not a valid BLS12-381 G1 point")
      },
      Self::InvalidKzgKey => formatter.write_str(
        "FFLONK KZG verifier key is not canonical BLS12-381 material",
      ),
      Self::MissingRootOfUnity { order } => write!(
        formatter,
        "BLS12-381 Fr has no configured root of unity of order {order}",
      ),
    }
  }
}

impl std::error::Error for FflonkVerificationKeyError {}

fn valid_cosets(k1: Fr, k2: Fr, domain_size: u64) -> bool {
  if k1.is_zero() || k2.is_zero() || k1.is_one() || k2.is_one() || k1 == k2 {
    return false;
  }
  let Some(k2_inverse) = k2.inverse() else {
    return false;
  };
  !k1.pow([domain_size]).is_one()
    && !k2.pow([domain_size]).is_one()
    && !(k1 * k2_inverse).pow([domain_size]).is_one()
}

fn valid_g1(point: &G1Affine) -> bool {
  point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve()
}

fn valid_kzg_key(key: &KzgVerifierKeyV1) -> bool {
  key.g1 == G1Affine::generator()
    && key.g2 == G2Affine::generator()
    && !key.tau_g2.is_zero()
    && key.tau_g2.is_on_curve()
    && key.tau_g2.is_in_correct_subgroup_assuming_on_curve()
}

fn inverse_of_three_mod_power_of_two(modulus: u64) -> u64 {
  if modulus % 3 == 1 { (2 * modulus + 1) / 3 } else { (modulus + 1) / 3 }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::G2Affine;
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::{FftField, PrimeField};

  fn kzg_key() -> KzgVerifierKeyV1 {
    let tau = Fr::from(11_u64);
    KzgVerifierKeyV1 {
      g1: G1Affine::generator(),
      g2: G2Affine::generator(),
      tau_g2: G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
      srs_digest: [7_u8; 32],
    }
  }

  fn valid_key() -> FflonkVerificationKeyV1 {
    FflonkVerificationKeyV1::new(
      3,
      16,
      Fr::GENERATOR,
      Fr::GENERATOR.square(),
      G1Affine::generator(),
      kzg_key(),
    )
    .unwrap()
  }

  #[test]
  fn derives_one_coherent_root_family() {
    let key = valid_key();
    assert_eq!(key.omega().pow([key.domain_size()]), Fr::one());
    assert_ne!(key.omega().pow([key.domain_size() / 2]), Fr::one());
    assert_eq!(key.omega_3().pow([3]), Fr::one());
    assert_ne!(key.omega_3(), Fr::one());
    assert_eq!(key.omega_4().pow([4]), Fr::one());
    assert_eq!(key.omega_8().pow([8]), Fr::one());
    assert_eq!(key.omega_8().square(), key.omega_4());
    assert_eq!(key.omega_r().pow([3]), key.omega());
  }

  #[test]
  fn rejects_invalid_domain_and_public_input_shapes() {
    let args =
      (Fr::GENERATOR, Fr::GENERATOR.square(), G1Affine::generator(), kzg_key());
    assert_eq!(
      FflonkVerificationKeyV1::new(0, 12, args.0, args.1, args.2, args.3),
      Err(FflonkVerificationKeyError::InvalidDomainSize { domain_size: 12 }),
    );
    assert_eq!(
      FflonkVerificationKeyV1::new(16, 16, args.0, args.1, args.2, args.3),
      Err(FflonkVerificationKeyError::TooManyPublicInputs {
        public_inputs: 16,
        domain_size: 16,
      }),
    );
  }

  #[test]
  fn rejects_overlapping_permutation_cosets() {
    assert_eq!(
      FflonkVerificationKeyV1::new(
        1,
        16,
        Fr::one(),
        Fr::GENERATOR,
        G1Affine::generator(),
        kzg_key(),
      ),
      Err(FflonkVerificationKeyError::InvalidPermutationCosets),
    );
  }
}
