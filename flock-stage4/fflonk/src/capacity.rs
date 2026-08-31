use crate::{
  FFLONK_SRS_DEGREE_OVERHEAD, FFLONK_SRS_DOMAIN_MULTIPLIER,
  PLONK_GATE_RECORD_BYTES, PlonkGateCensusV1,
};
use core::fmt;

/// Canonical byte width of one BLS12-381 scalar-field element on disk.
pub const FFLONK_FIELD_STORAGE_BYTES: u64 = 32;
/// Canonical compressed width of one BLS12-381 G1 SRS point.
pub const BLS12_381_G1_COMPRESSED_BYTES: u64 = 48;
/// EIP-2537 uncompressed width of one BLS12-381 G1 point.
pub const BLS12_381_G1_EIP2537_BYTES: u64 = 128;

/// Checked production-storage census for one Stage 4 FFLONK domain.
///
/// These are payload bytes, not a peak-RSS promise: filesystem metadata,
/// sort/FFT scratch space, checksums, and implementation buffering are not
/// included. Public and padding gate rows are deterministic and therefore the
/// gate stream stores constraint rows only.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkCapacityPlanV1 {
  pub domain_size: u64,
  pub required_srs_degree: u64,
  pub required_srs_g1_points: u64,
  pub constraint_gate_stream_bytes: u64,
  pub field_column_bytes: u64,
  pub witness_evaluations_bytes: u64,
  pub retained_preprocessed_polynomials_bytes: u64,
  pub packed_c0_bytes: u64,
  pub largest_packed_polynomial_bytes: u64,
  pub compressed_srs_g1_bytes: u64,
  pub eip2537_srs_g1_bytes: u64,
}

/// Why capacity arithmetic could not represent a proposed census.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FflonkCapacityError {
  InvalidDomain,
  CountOverflow,
}

impl fmt::Display for FflonkCapacityError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidDomain => formatter.write_str(
        "FFLONK capacity census has a non-power-of-two or inconsistent domain",
      ),
      Self::CountOverflow => {
        formatter.write_str("FFLONK capacity byte count overflow")
      },
    }
  }
}

impl std::error::Error for FflonkCapacityError {}

/// Converts an exact PLONK gate census into external-storage payload sizes.
pub fn plan_fflonk_capacity(
  census: &PlonkGateCensusV1,
) -> Result<FflonkCapacityPlanV1, FflonkCapacityError> {
  let active_rows = census
    .public_input_rows
    .checked_add(census.constraint_rows)
    .ok_or(FflonkCapacityError::CountOverflow)?;
  if census.domain_size < 8
    || !census.domain_size.is_power_of_two()
    || active_rows
      .checked_add(census.padding_rows)
      .ok_or(FflonkCapacityError::CountOverflow)?
      != census.domain_size
  {
    return Err(FflonkCapacityError::InvalidDomain);
  }

  let required_srs_degree = census
    .domain_size
    .checked_mul(FFLONK_SRS_DOMAIN_MULTIPLIER)
    .and_then(|degree| degree.checked_add(FFLONK_SRS_DEGREE_OVERHEAD))
    .ok_or(FflonkCapacityError::CountOverflow)?;
  let required_srs_g1_points = required_srs_degree
    .checked_add(1)
    .ok_or(FflonkCapacityError::CountOverflow)?;
  let field_column_bytes =
    bytes(census.domain_size, FFLONK_FIELD_STORAGE_BYTES)?;
  let largest_packed_polynomial_bytes =
    bytes(required_srs_g1_points, FFLONK_FIELD_STORAGE_BYTES)?;

  Ok(FflonkCapacityPlanV1 {
    domain_size: census.domain_size,
    required_srs_degree,
    required_srs_g1_points,
    constraint_gate_stream_bytes: bytes(
      census.constraint_rows,
      u64::try_from(PLONK_GATE_RECORD_BYTES)
        .map_err(|_| FflonkCapacityError::CountOverflow)?,
    )?,
    field_column_bytes,
    witness_evaluations_bytes: bytes(field_column_bytes, 3)?,
    // Eight selectors/sigmas, each retained in evaluation and coefficient form.
    retained_preprocessed_polynomials_bytes: bytes(field_column_bytes, 16)?,
    // C0 interleaves eight size-n coefficient polynomials.
    packed_c0_bytes: bytes(field_column_bytes, 8)?,
    largest_packed_polynomial_bytes,
    compressed_srs_g1_bytes: bytes(
      required_srs_g1_points,
      BLS12_381_G1_COMPRESSED_BYTES,
    )?,
    eip2537_srs_g1_bytes: bytes(
      required_srs_g1_points,
      BLS12_381_G1_EIP2537_BYTES,
    )?,
  })
}

fn bytes(count: u64, width: u64) -> Result<u64, FflonkCapacityError> {
  count.checked_mul(width).ok_or(FflonkCapacityError::CountOverflow)
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::BTreeMap;

  fn census() -> PlonkGateCensusV1 {
    PlonkGateCensusV1 {
      public_input_rows: 1,
      constraint_rows: 5,
      padding_rows: 2,
      domain_size: 8,
      auxiliary_wires: 2,
      rows_by_phase: BTreeMap::new(),
    }
  }

  #[test]
  fn exact_payload_sizes_are_derived_from_the_gate_census() {
    let plan = plan_fflonk_capacity(&census()).unwrap();
    assert_eq!(plan.required_srs_degree, 89);
    assert_eq!(plan.required_srs_g1_points, 90);
    assert_eq!(plan.constraint_gate_stream_bytes, 960);
    assert_eq!(plan.field_column_bytes, 256);
    assert_eq!(plan.witness_evaluations_bytes, 768);
    assert_eq!(plan.retained_preprocessed_polynomials_bytes, 4_096);
    assert_eq!(plan.packed_c0_bytes, 2_048);
    assert_eq!(plan.largest_packed_polynomial_bytes, 2_880);
    assert_eq!(plan.compressed_srs_g1_bytes, 4_320);
    assert_eq!(plan.eip2537_srs_g1_bytes, 11_520);
  }

  #[test]
  fn inconsistent_domain_is_rejected() {
    let mut invalid = census();
    invalid.padding_rows = 3;
    assert_eq!(
      plan_fflonk_capacity(&invalid),
      Err(FflonkCapacityError::InvalidDomain),
    );
  }
}
