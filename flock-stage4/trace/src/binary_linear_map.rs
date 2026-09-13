//! Fixed binary-linear programs, with exact coefficient checking at setup.
//!
//! The same XOR network acts on bits or on elements of any characteristic-two
//! field. Coefficient checking expands Boolean basis images exactly; it uses
//! neither randomized fingerprints nor witness-supplied intermediate values.

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryLinearReferenceV0 {
  Zero,
  Input(u32),
  Xor(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryLinearMapLimitsV0 {
  pub inputs: u32,
  pub xors: u32,
  pub outputs: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryLinearValidationLimitsV0 {
  /// Retained coefficient words plus one scratch row, each eight bytes.
  pub coefficient_words: u64,
  /// Total sparse coefficients read, counting duplicates before cancellation.
  pub source_entries: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryLinearMapError {
  SizeLimit,
  Reference,
  CoefficientWordLimit,
  SourceEntryLimit,
  RowCount,
  ColumnOutOfRange(usize),
  CoefficientMismatch(usize),
}

impl fmt::Display for BinaryLinearMapError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "binary-linear map: {self:?}")
  }
}
impl std::error::Error for BinaryLinearMapError {}

/// Immutable, validated straight-line XOR program. This owns a mathematical
/// map, not its authorization: a setup must check its coefficients against
/// the intended approved matrix before using it for root discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryLinearMapV0 {
  inputs: u32,
  xors: Vec<(BinaryLinearReferenceV0, BinaryLinearReferenceV0)>,
  outputs: Vec<BinaryLinearReferenceV0>,
}

impl BinaryLinearMapV0 {
  /// Validate every reference and discard dead operations. All resource
  /// limits apply to the supplied program BEFORE dead-code removal.
  pub fn compile(
    inputs: u32,
    xors: Vec<(BinaryLinearReferenceV0, BinaryLinearReferenceV0)>,
    outputs: Vec<BinaryLinearReferenceV0>,
    limits: BinaryLinearMapLimitsV0,
  ) -> Result<Self, BinaryLinearMapError> {
    use BinaryLinearReferenceV0 as Ref;
    if inputs > limits.inputs
      || xors.len() as u64 > u64::from(limits.xors)
      || outputs.len() as u64 > u64::from(limits.outputs)
    {
      return Err(BinaryLinearMapError::SizeLimit);
    }
    let valid = |reference: Ref, before: usize| match reference {
      Ref::Zero => true,
      Ref::Input(i) => i < inputs,
      Ref::Xor(i) => (i as usize) < before,
    };
    for (i, &(left, right)) in xors.iter().enumerate() {
      if !valid(left, i) || !valid(right, i) {
        return Err(BinaryLinearMapError::Reference);
      }
    }
    if outputs.iter().any(|&r| !valid(r, xors.len())) {
      return Err(BinaryLinearMapError::Reference);
    }
    let mut live = vec![false; xors.len()];
    for &output in &outputs {
      if let Ref::Xor(i) = output {
        live[i as usize] = true;
      }
    }
    for i in (0..xors.len()).rev() {
      if live[i] {
        for r in [xors[i].0, xors[i].1] {
          if let Ref::Xor(child) = r {
            live[child as usize] = true;
          }
        }
      }
    }
    let mut replacements = vec![Ref::Zero; xors.len()];
    let mut retained = Vec::new();
    let remap = |r: Ref, replacements: &[Ref]| match r {
      Ref::Xor(i) => replacements[i as usize],
      _ => r,
    };
    for (i, (left, right)) in xors.into_iter().enumerate() {
      if live[i] {
        replacements[i] = Ref::Xor(
          u32::try_from(retained.len())
            .map_err(|_| BinaryLinearMapError::SizeLimit)?,
        );
        retained
          .push((remap(left, &replacements), remap(right, &replacements)));
      }
    }
    Ok(Self {
      inputs,
      xors: retained,
      outputs: outputs.into_iter().map(|r| remap(r, &replacements)).collect(),
    })
  }

  pub fn inputs(&self) -> u32 {
    self.inputs
  }
  pub fn xors(&self) -> &[(BinaryLinearReferenceV0, BinaryLinearReferenceV0)] {
    &self.xors
  }
  pub fn outputs(&self) -> &[BinaryLinearReferenceV0] {
    &self.outputs
  }

  /// Compare EVERY output coefficient against an exact sparse binary matrix.
  /// Repeated sparse column indices cancel. Bounds are checked before the
  /// coefficient expansion is allocated and while source entries are read.
  pub fn check_rows(
    &self,
    rows: &[Vec<usize>],
    limits: BinaryLinearValidationLimitsV0,
  ) -> Result<(), BinaryLinearMapError> {
    use BinaryLinearMapError as Error;
    if rows.len() != self.outputs.len() {
      return Err(Error::RowCount);
    }
    let words = u64::from(self.inputs).div_ceil(64);
    let total = (self.xors.len() as u64 + 1)
      .checked_mul(words)
      .ok_or(Error::CoefficientWordLimit)?;
    if total > limits.coefficient_words {
      return Err(Error::CoefficientWordLimit);
    }
    let count =
      usize::try_from(total).map_err(|_| Error::CoefficientWordLimit)?;
    let words =
      usize::try_from(words).map_err(|_| Error::CoefficientWordLimit)?;
    let mut coefficients = vec![0u64; count - words];
    for (i, &(left, right)) in self.xors.iter().enumerate() {
      for word in 0..words {
        coefficients[i * words + word] =
          coefficient_word(left, word, words, &coefficients)
            ^ coefficient_word(right, word, words, &coefficients);
      }
    }
    let mut expected = vec![0u64; words];
    let mut remaining = limits.source_entries;
    for (i, (columns, &output)) in rows.iter().zip(&self.outputs).enumerate() {
      expected.fill(0);
      for &column in columns {
        remaining = remaining.checked_sub(1).ok_or(Error::SourceEntryLimit)?;
        if column as u64 >= u64::from(self.inputs) {
          return Err(Error::ColumnOutOfRange(column));
        }
        expected[column / 64] ^= 1u64 << (column % 64);
      }
      for (word, &expected) in expected.iter().enumerate() {
        if coefficient_word(output, word, words, &coefficients) != expected {
          return Err(Error::CoefficientMismatch(i));
        }
      }
    }
    Ok(())
  }

  pub fn digest(&self) -> [u8; 32] {
    fn reference(hash: &mut blake3::Hasher, r: BinaryLinearReferenceV0) {
      use BinaryLinearReferenceV0 as Ref;
      let (tag, i) = match r {
        Ref::Zero => (0, 0),
        Ref::Input(i) => (1, i),
        Ref::Xor(i) => (2, i),
      };
      hash.update(&[tag]);
      hash.update(&i.to_le_bytes());
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/binary-linear-map/v0\0");
    hash.update(&self.inputs.to_le_bytes());
    hash.update(&(self.xors.len() as u64).to_le_bytes());
    for &(left, right) in &self.xors {
      reference(&mut hash, left);
      reference(&mut hash, right);
    }
    hash.update(&(self.outputs.len() as u64).to_le_bytes());
    for &output in &self.outputs {
      reference(&mut hash, output);
    }
    *hash.finalize().as_bytes()
  }
}

fn coefficient_word(
  reference: BinaryLinearReferenceV0,
  word: usize,
  words: usize,
  coefficients: &[u64],
) -> u64 {
  use BinaryLinearReferenceV0 as Ref;
  match reference {
    Ref::Zero => 0,
    Ref::Input(i) => {
      if i as usize / 64 == word {
        1u64 << (i % 64)
      } else {
        0
      }
    },
    Ref::Xor(i) => coefficients[i as usize * words + word],
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use BinaryLinearReferenceV0::{Input, Xor, Zero};

  const SHAPE: BinaryLinearMapLimitsV0 =
    BinaryLinearMapLimitsV0 { inputs: 128, xors: 100, outputs: 10 };
  const CHECK: BinaryLinearValidationLimitsV0 =
    BinaryLinearValidationLimitsV0 {
      coefficient_words: 1000,
      source_entries: 100,
    };

  #[test]
  fn exact_coefficient_check_covers_all_bits_and_duplicate_cancellation() {
    let map = BinaryLinearMapV0::compile(
      128,
      vec![(Input(0), Input(127)), (Xor(0), Input(63)), (Input(9), Input(10))],
      vec![Xor(1), Input(64), Zero, Xor(0)],
      SHAPE,
    )
    .unwrap();
    assert_eq!(map.xors().len(), 2); // Dead node is not a circuit cost.
    let rows = vec![vec![127, 0, 63], vec![64, 5, 5], vec![], vec![0, 127]];
    map.check_rows(&rows, CHECK).unwrap();
    for row in 0..rows.len() {
      for column in 0..128 {
        let mut bad = rows.clone();
        bad[row].push(column);
        assert_eq!(
          map.check_rows(&bad, CHECK),
          Err(BinaryLinearMapError::CoefficientMismatch(row))
        );
      }
    }
    let reordered = BinaryLinearMapV0::compile(
      128,
      map.xors.clone(),
      vec![Input(64), Xor(1), Zero, Xor(0)],
      SHAPE,
    )
    .unwrap();
    assert_ne!(map.digest(), reordered.digest());
  }

  #[test]
  fn references_and_shape_limits_are_checked_even_in_dead_code() {
    for (inputs, pairs, outputs) in [
      (1, vec![(Xor(0), Zero)], vec![]),
      (1, vec![(Input(1), Zero)], vec![]),
      (1, vec![], vec![Xor(0)]),
      (0, vec![], vec![Input(0)]),
    ] {
      assert_eq!(
        BinaryLinearMapV0::compile(inputs, pairs, outputs, SHAPE),
        Err(BinaryLinearMapError::Reference)
      );
    }
    for limits in [
      BinaryLinearMapLimitsV0 { inputs: 0, ..SHAPE },
      BinaryLinearMapLimitsV0 { xors: 0, ..SHAPE },
      BinaryLinearMapLimitsV0 { outputs: 0, ..SHAPE },
    ] {
      assert_eq!(
        BinaryLinearMapV0::compile(
          1,
          vec![(Input(0), Zero)],
          vec![Zero],
          limits
        ),
        Err(BinaryLinearMapError::SizeLimit)
      );
    }
  }

  #[test]
  fn exact_validation_has_separate_memory_entry_and_geometry_bounds() {
    let map = BinaryLinearMapV0::compile(
      65,
      vec![(Input(0), Input(64))],
      vec![Xor(0)],
      SHAPE,
    )
    .unwrap();
    let rows = vec![vec![0, 64, 63, 63]];
    map
      .check_rows(
        &rows,
        BinaryLinearValidationLimitsV0 {
          coefficient_words: 4,
          source_entries: 4,
        },
      )
      .unwrap();
    assert_eq!(
      map.check_rows(
        &rows,
        BinaryLinearValidationLimitsV0 { coefficient_words: 3, ..CHECK }
      ),
      Err(BinaryLinearMapError::CoefficientWordLimit)
    );
    assert_eq!(
      map.check_rows(
        &rows,
        BinaryLinearValidationLimitsV0 { source_entries: 3, ..CHECK }
      ),
      Err(BinaryLinearMapError::SourceEntryLimit)
    );
    assert_eq!(map.check_rows(&[], CHECK), Err(BinaryLinearMapError::RowCount));
    assert_eq!(
      map.check_rows(&[vec![65]], CHECK),
      Err(BinaryLinearMapError::ColumnOutOfRange(65))
    );
    let empty =
      BinaryLinearMapV0::compile(0, vec![], vec![Zero], SHAPE).unwrap();
    empty
      .check_rows(
        &[vec![]],
        BinaryLinearValidationLimitsV0 {
          coefficient_words: 0,
          source_entries: 0,
        },
      )
      .unwrap();
  }
}
