//! The terminal PLONK circuit: the Lean-checked constraint system
//! (`plonk_export`, `ix-aiur-scs-v1`) compiled by gnark ([`gnark`]), and the
//! witness of its input wires ([`scs`]).

use super::Bn254;
use crate::kzg::Scalar;
use aiur::field::FieldBackend;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::Serialize;

#[cfg(feature = "plonk")]
pub mod gnark;
pub mod scs;

/// The format of the terminal stage description `plonk_export` reads.
pub const TERMINAL_FORMAT: &str = "ix-aiur-plonk-terminal-v1";
/// Largest power-of-two PLONK domain within the Ignition ceremony. Setup also
/// requires an authenticated file containing the actual `domain + 3` powers.
pub const MAX_DOMAIN: usize = crate::pipeline::plonk_limits::MAX_DOMAIN;
pub const MAX_PUBLIC_INPUTS: usize = 1 << 15;

/// Canonical big-endian field words, in typed public-call order.
pub fn public_bytes(values: &[Scalar]) -> Result<Vec<u8>, String> {
  if values.len() > MAX_PUBLIC_INPUTS {
    return Err("too many Aiur PLONK public fields".into());
  }
  let mut out = Vec::with_capacity(32 * values.len());
  for value in values {
    put_scalar(&mut out, *value);
  }
  Ok(out)
}

fn put_scalar(out: &mut Vec<u8>, value: Scalar) {
  for limb in value.canonical_limbs_le().into_iter().rev() {
    out.extend(limb.to_be_bytes());
  }
}

/// The terminal's pairing configuration: gnark's `PairingCheck` of the two
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
fn rom_rows(
  trace: &RowMajorMatrix<Scalar>,
) -> Result<RowMajorMatrix<Scalar>, String> {
  let width = trace.width.checked_sub(2).ok_or("ROM trace without words")?;
  let mut values = Vec::with_capacity(trace.height() * width);
  for (a, row) in trace.values.chunks(trace.width).enumerate() {
    if row[1] == Bn254.one() {
      if row[2] != Bn254.from_u64(a as u64) {
        return Err("nonconsecutive ROM addresses".into());
      }
    } else if row.iter().any(|&x| x != Bn254.zero()) {
      return Err("an inactive ROM row is not zero".into());
    }
    values.push(row[0]);
    values.extend_from_slice(&row[3..]);
  }
  Ok(RowMajorMatrix::new(values, width))
}
