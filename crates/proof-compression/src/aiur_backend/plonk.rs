//! The terminal PLONK circuit: the Lean-checked constraint system
//! (`plonk_export`, `ix-aiur-scs-v1`) proved by the pure-Rust (+ optional
//! Ix-CUDA) native backend ([`native`]), and the witness of its input wires
//! ([`scs`]).

use super::AiurCurve;
use crate::kzg::{CurveScalar, Scalar, curve::Bn254 as Bn254Curve};
use aiur::field::FieldBackend;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::Serialize;

pub mod native;
pub mod scs;

/// The format of the terminal stage description `plonk_export` reads.
pub const TERMINAL_FORMAT: &str = "ix-aiur-plonk-terminal-v1";
/// Largest power-of-two PLONK domain within the Ignition/Filecoin ceremonies.
/// Setup also requires an authenticated file containing the actual `domain + 3`
/// powers.
pub const MAX_DOMAIN: usize = crate::pipeline::plonk_limits::MAX_DOMAIN;
pub const MAX_PUBLIC_INPUTS: usize = 1 << 15;

/// Canonical big-endian field words, in typed public-call order, for curve `C`.
pub fn public_bytes_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<Vec<u8>, String> {
  if values.len() > MAX_PUBLIC_INPUTS {
    return Err("too many Aiur PLONK public fields".into());
  }
  let mut out = Vec::with_capacity(32 * values.len());
  for value in values {
    put_scalar_for::<C>(&mut out, *value);
  }
  Ok(out)
}

/// Canonical big-endian BN254 field words, in typed public-call order.
pub fn public_bytes(values: &[Scalar]) -> Result<Vec<u8>, String> {
  public_bytes_for::<Bn254Curve>(values)
}

fn put_scalar_for<C: AiurCurve>(out: &mut Vec<u8>, value: CurveScalar<C>) {
  for limb in value.canonical_limbs_le().into_iter().rev() {
    out.extend(limb.to_be_bytes());
  }
}

/// The terminal's pairing configuration: external pairing check of the two
/// private output points against these G2 anchors.
#[derive(Clone, Debug, Serialize)]
pub struct Pairing {
  pub curve: &'static str,
  pub encoding: &'static str,
  pub g2: [[String; 4]; 2],
}

/// A compiler ROM trace (`[count, active, address, words…]`, consecutive
/// addresses from 0) as the rows of `romCircuit` (`[mult, words…]`, row `a`
/// at address `a`; the address is the table's fixed column).
fn rom_rows_for<C: AiurCurve>(
  trace: &RowMajorMatrix<CurveScalar<C>>,
) -> Result<RowMajorMatrix<CurveScalar<C>>, String> {
  let width = trace.width.checked_sub(2).ok_or("ROM trace without words")?;
  let mut values = Vec::with_capacity(trace.height() * width);
  for (a, row) in trace.values.chunks(trace.width).enumerate() {
    if row[1] == C::FIELD.one() {
      if row[2] != C::FIELD.from_u64(a as u64) {
        return Err("nonconsecutive ROM addresses".into());
      }
    } else if row.iter().any(|&x| x != C::FIELD.zero()) {
      return Err("an inactive ROM row is not zero".into());
    }
    values.push(row[0]);
    values.extend_from_slice(&row[3..]);
  }
  Ok(RowMajorMatrix::new(values, width))
}
