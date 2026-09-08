use crate::{
  FFLONK_SRS_DEGREE_OVERHEAD, FFLONK_SRS_DOMAIN_MULTIPLIER,
  KZG_SRS_FILE_CHUNK_POINTS, KZG_SRS_FILE_HEADER_BYTES, KzgSrsFileEncodingV1,
  PLONK_GATE_RECORD_BYTES, PlonkCellV1, PlonkGateCensusV1, PlonkGateV1,
};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::FftField;
use core::fmt;

/// Canonical byte width of one BLS12-381 scalar-field element on disk.
pub const FFLONK_FIELD_STORAGE_BYTES: u64 = 32;
/// Canonical compressed width of one BLS12-381 G1 SRS point.
pub const BLS12_381_G1_COMPRESSED_BYTES: u64 = 48;
/// EIP-2537 uncompressed width of one BLS12-381 G1 point.
pub const BLS12_381_G1_EIP2537_BYTES: u64 = 128;
/// The materialized prover multiplies three degree-(n-1) wire polynomials
/// and degree-(n+2) blinded Z, requiring a size-4n polynomial FFT.
pub const FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER: u64 = 4;

/// Checked production-storage census for one Stage 4 FFLONK domain.
///
/// Storage fields count canonical data, not peak RSS. Filesystem metadata,
/// sort/FFT scratch space, and runtime buffering are excluded. Archive headers
/// and retained SRS authentication indexes have explicit fields. Public and
/// padding gate rows are deterministic, so the stream stores constraint rows only.
/// A sizing census may describe a domain above the field's FFT limit; these
/// payload sizes alone do not establish that the backend can use that domain.
/// The polynomial-FFT requirement and target-specific resident SRS/key lower
/// bound are reported separately from canonical storage widths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkCapacityPlanV1 {
  pub domain_size: u64,
  pub polynomial_fft_domain_size: u64,
  pub supported_polynomial_fft_domain: bool,
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
  /// Compressed G1 payload plus the v1 archive's fixed header.
  pub compressed_file_srs_bytes: u64,
  /// Uncompressed G1 coordinates plus the v1 archive's fixed header.
  pub uncompressed_file_srs_bytes: u64,
  /// One retained 32-byte authentication digest per file-SRS chunk.
  pub file_srs_authentication_bytes: u64,
  /// Lower bound for the resident SRS and materialized proving key on this
  /// target architecture. Includes typed gates, copy cells, retained
  /// polynomials, and affine G1 points. Excludes R1CS, witness, temporary
  /// buffers, spare Vec capacity, allocator overhead, and process memory.
  pub materialized_srs_and_key_minimum_bytes: u64,
  /// Materialized proving key plus a file-SRS authentication index. Uses the
  /// same exclusions as the resident-SRS bound, and excludes temporary SRS
  /// decoding/MSM buffers, reader state, filesystem cache, and I/O buffers.
  pub file_srs_and_key_minimum_bytes: u64,
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
  let polynomial_fft_domain_size =
    bytes(census.domain_size, FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER)?;
  let retained_key_bytes_per_row = u64::try_from(
    size_of::<PlonkGateV1>()
      + 3 * size_of::<PlonkCellV1>()
      + 24 * size_of::<Fr>(),
  )
  .map_err(|_| FflonkCapacityError::CountOverflow)?;
  let srs_point_bytes = u64::try_from(size_of::<G1Affine>())
    .map_err(|_| FflonkCapacityError::CountOverflow)?;
  let materialized_srs_and_key_minimum_bytes =
    bytes(census.domain_size, retained_key_bytes_per_row)?
      .checked_add(bytes(required_srs_g1_points, srs_point_bytes)?)
      .ok_or(FflonkCapacityError::CountOverflow)?;
  let compressed_srs_g1_bytes =
    bytes(required_srs_g1_points, BLS12_381_G1_COMPRESSED_BYTES)?;
  let compressed_file_srs_bytes = compressed_srs_g1_bytes
    .checked_add(KZG_SRS_FILE_HEADER_BYTES as u64)
    .ok_or(FflonkCapacityError::CountOverflow)?;
  let uncompressed_file_srs_bytes = bytes(
    required_srs_g1_points,
    KzgSrsFileEncodingV1::Uncompressed.point_bytes() as u64,
  )?
  .checked_add(KZG_SRS_FILE_HEADER_BYTES as u64)
  .ok_or(FflonkCapacityError::CountOverflow)?;
  let file_srs_authentication_bytes = bytes(
    required_srs_g1_points.div_ceil(KZG_SRS_FILE_CHUNK_POINTS as u64),
    32,
  )?;
  let file_srs_and_key_minimum_bytes =
    bytes(census.domain_size, retained_key_bytes_per_row)?
      .checked_add(file_srs_authentication_bytes)
      .ok_or(FflonkCapacityError::CountOverflow)?;

  Ok(FflonkCapacityPlanV1 {
    domain_size: census.domain_size,
    polynomial_fft_domain_size,
    supported_polynomial_fft_domain: polynomial_fft_domain_size
      <= (1_u64 << Fr::TWO_ADICITY),
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
    compressed_srs_g1_bytes,
    eip2537_srs_g1_bytes: bytes(
      required_srs_g1_points,
      BLS12_381_G1_EIP2537_BYTES,
    )?,
    materialized_srs_and_key_minimum_bytes,
    compressed_file_srs_bytes,
    uncompressed_file_srs_bytes,
    file_srs_authentication_bytes,
    file_srs_and_key_minimum_bytes,
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
    assert_eq!(plan.compressed_file_srs_bytes, 4_536);
    assert_eq!(plan.uncompressed_file_srs_bytes, 8_856);
    assert_eq!(plan.file_srs_authentication_bytes, 32);
    assert_eq!(plan.polynomial_fft_domain_size, 32);
    assert!(plan.supported_polynomial_fft_domain);
  }

  #[test]
  fn base_domain_support_does_not_imply_a_prover_or_ram_fit() {
    let mut large = census();
    large.domain_size = 1u64 << 31;
    large.padding_rows = large.domain_size - large.active_rows();
    let plan = plan_fflonk_capacity(&large).unwrap();
    assert_eq!(plan.polynomial_fft_domain_size, 1u64 << 33);
    assert!(!plan.supported_polynomial_fft_domain);
    assert!(plan.materialized_srs_and_key_minimum_bytes > 512_000_000_000);
    large.domain_size >>= 1;
    large.padding_rows = large.domain_size - large.active_rows();
    let plan = plan_fflonk_capacity(&large).unwrap();
    assert!(plan.supported_polynomial_fft_domain);
    assert_eq!(plan.file_srs_authentication_bytes, 4_718_624);
    assert!(plan.file_srs_and_key_minimum_bytes > 512_000_000_000);
    assert!(
      plan.file_srs_and_key_minimum_bytes
        < plan.materialized_srs_and_key_minimum_bytes
    );
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
