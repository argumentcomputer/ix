//! Legacy pipeline Groth16 proof tags and packet bounds for BN254 and
//! BLS12-381.
//!
//! Go/gnark proving and verification in this legacy pipeline module have been
//! retired and removed; use the pure-Rust Groth16 backend in
//! `crate::aiur_backend::groth16`.

use super::{Result, setup::SetupClass, statement};
#[cfg(feature = "groth16")]
use crate::kzg::curve::Curve;
use crate::kzg::curve::{Bls12381, Bn254, KzgCurve};
use std::path::Path;

pub(super) const PROOF_TAG: &[u8; 8] = Bn254::GROTH16_PROOF_TAG;
pub(super) const BLS12_381_PROOF_TAG: &[u8; 8] = Bls12381::GROTH16_PROOF_TAG;

const RETIRED_ERROR: &str = "legacy Go/gnark pipeline Groth16 has been retired \
  and removed; use the pure-Rust Groth16 backend in aiur_backend::groth16";

pub(super) fn retired_error() -> Box<dyn std::error::Error> {
  RETIRED_ERROR.into()
}

fn check_length_for<C: KzgCurve>(packet: &[u8]) -> Result<()> {
  if packet.len() != C::GROTH16_PROOF_BYTES_NO_COMMIT + 32
    && packet.len() != C::GROTH16_PROOF_BYTES_WITH_COMMIT + 32
  {
    return Err("invalid Groth16 packet length".into());
  }
  Ok(())
}

pub(super) fn verify(
  packet: &[u8],
  _claim: &[u8],
  _allow_development: bool,
) -> Result<SetupClass> {
  check_length_for::<Bn254>(packet)?;
  Err(retired_error())
}

pub(super) fn verify_bls12_381(
  packet: &[u8],
  _claim: &[u8],
  _allow_development: bool,
) -> Result<SetupClass> {
  check_length_for::<Bls12381>(packet)?;
  Err(retired_error())
}

#[allow(clippy::extra_unused_type_parameters)]
pub(super) fn check_stage_for<C: KzgCurve>(
  _dir: &Path,
  _expected: &statement::Statement,
  _allow_development: bool,
  _bundled: bool,
  _verifier: &Path,
  _setup: &super::SetupConfig,
  _cache_root: &Path,
) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 compilation; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn compile(_schema: &Path, _out: &Path) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 compilation; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn compile_for_curve(
  _curve: Curve,
  _schema: &Path,
  _out: &Path,
) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 development setup; use
/// `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn setup_development(_dir: &Path) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 development setup; use
/// `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn setup_development_for_curve(_curve: Curve, _dir: &Path) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 MPC setup; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn setup_mpc(_dir: &Path, _descriptor: &Path, _pin: &str) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 MPC setup; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn setup_mpc_for_curve(
  _curve: Curve,
  _dir: &Path,
  _descriptor: &Path,
  _pin: &str,
) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 key import; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn import(_dir: &Path, _descriptor: &Path, _pin: &str) -> Result<()> {
  Err(retired_error())
}

/// Retired legacy Go/gnark Groth16 key import; use `aiur_backend::groth16`.
#[cfg(feature = "groth16")]
pub fn import_for_curve(
  _curve: Curve,
  _dir: &Path,
  _descriptor: &Path,
  _pin: &str,
) -> Result<()> {
  Err(retired_error())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn malformed_envelopes_fail_before_key_access() {
    assert_eq!(PROOF_TAG, b"IXBN\0\0\0\x03");
    assert_eq!(BLS12_381_PROOF_TAG, b"IXCMP\0\0\x06");
    for length in [0, 32, 195, 197, 227, 229, 1 << 20] {
      assert!(
        verify(&vec![0; length], b"claim", false)
          .unwrap_err()
          .to_string()
          .contains("packet length")
      );
    }
    for length in [0, 32, 275, 277, 323, 325, 1 << 20] {
      assert!(
        verify_bls12_381(&vec![0; length], b"claim", false)
          .unwrap_err()
          .to_string()
          .contains("packet length")
      );
    }
    for length in [
      Bn254::GROTH16_PROOF_BYTES_NO_COMMIT + 32,
      Bn254::GROTH16_PROOF_BYTES_WITH_COMMIT + 32,
    ] {
      let err =
        verify(&vec![0; length], b"claim", false).unwrap_err().to_string();
      assert!(
        err.contains("retired") && err.contains("aiur_backend::groth16"),
        "{err}"
      );
    }
    for length in [
      Bls12381::GROTH16_PROOF_BYTES_NO_COMMIT + 32,
      Bls12381::GROTH16_PROOF_BYTES_WITH_COMMIT + 32,
    ] {
      let err = verify_bls12_381(&vec![0; length], b"claim", false)
        .unwrap_err()
        .to_string();
      assert!(
        err.contains("retired") && err.contains("aiur_backend::groth16"),
        "{err}"
      );
    }
  }
}
