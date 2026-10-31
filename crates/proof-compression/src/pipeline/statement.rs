//! The public statement of an aggregate root proof: eighteen Goldilocks
//! words, the Aiur claim row of the `ix_aggr` entrypoint. The caller derives
//! it from its aggregation backend exactly as `ix verify --aggregate` does;
//! here it is carried from the root claims through every stage's claim rows
//! into the final packet, and bound to the claim it belongs to by its last
//! eight words, the packed BLAKE3 digest of the claim bytes.

use super::Result;
use crate::kzg::Scalar;
use ark_ff::PrimeField;
use p3_field::PrimeField64;

pub(crate) const WORDS: usize = 18;
pub(crate) type Statement = [u64; WORDS];

/// Where the packed claim digest sits in the statement.
const CLAIM_DIGEST: std::ops::Range<usize> = 10..18;

/// The packed form of a 32-byte digest: eight little-endian `u32` words.
fn packed(digest: &[u8; 32]) -> [u64; 8] {
  let mut words = [0; 8];
  for (word, bytes) in words.iter_mut().zip(digest.as_chunks::<4>().0) {
    *word = u64::from(u32::from_le_bytes(*bytes));
  }
  words
}

/// Parse a statement in the batch claims layout, one claim of 18 words,
/// as written to `root-claims.bin` and produced by `MultiStark.serializeClaims`.
pub(crate) fn from_claims_bytes(bytes: &[u8]) -> Result<Statement> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() || words.len() != 2 + WORDS {
    return Err("statement must hold one claim of 18 words".into());
  }
  let words: Vec<_> = words.iter().map(|w| u64::from_le_bytes(*w)).collect();
  if words[0] != 1 || words[1] != usize_u64(WORDS) {
    return Err("statement must hold one claim of 18 words".into());
  }
  let mut statement = [0; WORDS];
  for (slot, &word) in statement.iter_mut().zip(&words[2..]) {
    if word >= multi_stark::types::Val::ORDER_U64 {
      return Err("statement word is not a canonical field element".into());
    }
    *slot = word;
  }
  Ok(statement)
}

pub(crate) fn to_claims_bytes(statement: &Statement) -> Vec<u8> {
  let mut bytes = Vec::with_capacity(8 * (2 + WORDS));
  for word in [1, usize_u64(WORDS)].into_iter().chain(statement.iter().copied())
  {
    bytes.extend(word.to_le_bytes());
  }
  bytes
}

/// A statement belongs to `claim` only if it ends in the claim's packed
/// digest; the leading words name the backend and entrypoint it was proved by.
pub(crate) fn bind_claim(claim: &[u8], statement: &Statement) -> Result<()> {
  if statement[CLAIM_DIGEST] != packed(blake3::hash(claim).as_bytes()) {
    return Err("statement does not end in the digest of this claim".into());
  }
  Ok(())
}

fn usize_u64(value: usize) -> u64 {
  u64::try_from(value).expect("statement length fits in u64")
}

fn scalar_word(value: Scalar) -> Result<u64> {
  let limbs = value.0.into_bigint().0;
  if limbs[1..].iter().any(|&limb| limb != 0)
    || limbs[0] >= multi_stark::types::Val::ORDER_U64
  {
    return Err("statement word is not a canonical field element".into());
  }
  Ok(limbs[0])
}

/// The statement carried by `values`, eighteen scalar words.
pub(crate) fn from_scalars(values: &[Scalar]) -> Result<Statement> {
  if values.len() != WORDS {
    return Err("statement must hold 18 words".into());
  }
  let mut statement = [0; WORDS];
  for (slot, &value) in statement.iter_mut().zip(values) {
    *slot = scalar_word(value)?;
  }
  Ok(statement)
}

/// The statement carried by a stage's claim rows: rows `1..=18` hold one
/// word each in their last column, behind the zero anchor of row `0`.
pub(crate) fn from_rows(claims: &[Vec<Scalar>]) -> Result<Statement> {
  let schema = super::stages::statement::Statement::from_claims(claims, WORDS)?;
  from_scalars(&schema.public_values(claims)?)
}

/// A statement for `claim` behind the given backend and entrypoint words.
pub(crate) fn with_claim(prefix: &[u64; 10], claim: &[u8]) -> Statement {
  let mut statement = [0; WORDS];
  statement[..10].copy_from_slice(prefix);
  statement[CLAIM_DIGEST]
    .copy_from_slice(&packed(blake3::hash(claim).as_bytes()));
  statement
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::traits::{Algebra, Field};

  #[test]
  fn claims_layout_round_trips_and_binds_the_claim() {
    let statement = with_claim(&[0, 293, 1, 2, 3, 4, 5, 6, 7, 8], b"claim");
    let bytes = to_claims_bytes(&statement);
    assert_eq!(bytes.len(), 8 * 20);
    assert_eq!(from_claims_bytes(&bytes).unwrap(), statement);
    bind_claim(b"claim", &statement).unwrap();
    assert!(bind_claim(b"other", &statement).is_err());
    assert!(from_claims_bytes(&bytes[..bytes.len() - 8]).is_err());
    let mut wrong_count = bytes.clone();
    wrong_count[0] = 2;
    assert!(from_claims_bytes(&wrong_count).is_err());
    let mut noncanonical = bytes.clone();
    noncanonical[16..24].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(from_claims_bytes(&noncanonical).is_err());
  }

  #[test]
  fn claim_rows_expose_the_statement_in_their_last_column() {
    let statement = with_claim(&[0, 293, 1, 2, 3, 4, 5, 6, 7, 8], b"claim");
    let rows: Vec<Vec<Scalar>> = std::iter::once(0)
      .chain(statement)
      .enumerate()
      .map(|(i, word)| {
        vec![
          Scalar::from_u8(93),
          Scalar::ONE,
          Scalar::from_usize(i),
          Scalar::from_u64(word),
        ]
      })
      .collect();
    assert_eq!(from_rows(&rows).unwrap(), statement);
    assert!(from_rows(&rows[..18]).is_err());
    let mut wide = rows.clone();
    wide[3][3] = Scalar::from_u64(u64::MAX);
    assert!(from_rows(&wide).is_err());
  }
}
