//! Exact sigma evaluations from immutable copy-permutation targets. The
//! coefficient polynomials still live in authenticated key storage; these
//! evaluations are a deterministic view, not another mutable file region.

use crate::{
  FflonkPolynomialSourceV1, FflonkPreprocessingError, FflonkStorageError,
  PlonkCellV1,
};
use ark_bls12_381::Fr;
use ark_ff::{FftField, Field};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

/// Count the low-power window and three coset-scaled high-power windows.
/// This arithmetic also models unsupported domains without allocating them.
pub(crate) fn sigma_power_table_fields(domain_size: u64) -> Option<u64> {
  if !domain_size.is_power_of_two() {
    return None;
  }
  let low = 1u64.checked_shl(domain_size.ilog2().div_ceil(2))?;
  low.checked_add((domain_size / low).checked_mul(3)?)
}

#[derive(Debug)]
pub(crate) struct SigmaEvaluationPowers {
  size: usize,
  low: Vec<Fr>,
  high: [Vec<Fr>; 3],
}

impl SigmaEvaluationPowers {
  pub(crate) fn new(
    domain: &Radix2EvaluationDomain<Fr>,
  ) -> Result<Self, FflonkPreprocessingError> {
    let size = domain.size();
    let size_u64 = u64::try_from(size)
      .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
    // At the Fr domain maximum these windows total only 8 MiB; the current
    // supported FFLONK size-4n prover uses at most 4 MiB at n=2^30.
    if !size.is_power_of_two() || size_u64 > 1u64 << Fr::TWO_ADICITY {
      return Err(FflonkPreprocessingError::UnsupportedDomain {
        domain_size: size_u64,
      });
    }
    let low_size = 1usize
      .checked_shl(size.ilog2().div_ceil(2))
      .ok_or(FflonkPreprocessingError::CountOverflow)?;
    let mut low = Vec::with_capacity(low_size);
    let omega = domain.group_gen();
    let mut step = Fr::ONE;
    for _ in 0..low_size {
      low.push(step);
      step *= omega;
    }
    // step = omega^low_size. Folding the three nonzero cosets into these
    // windows leaves exactly one Fr multiplication per evaluation read.
    let high = [Fr::ONE, Fr::GENERATOR, Fr::GENERATOR.square()].map(|coset| {
      let mut high = Vec::with_capacity(size / low_size);
      let mut value = coset;
      for _ in 0..size / low_size {
        high.push(value);
        value *= step;
      }
      high
    });
    Ok(Self { size, low, high })
  }

  pub(crate) fn heap_bytes(&self) -> usize {
    (self.low.len() + self.high.iter().map(Vec::len).sum::<usize>())
      * size_of::<Fr>()
  }

  pub(crate) fn source<'a>(
    &'a self,
    targets: &'a [PlonkCellV1],
  ) -> SigmaEvaluationSource<'a> {
    SigmaEvaluationSource { powers: self, targets }
  }
}

pub(crate) struct SigmaEvaluationSource<'a> {
  powers: &'a SigmaEvaluationPowers,
  targets: &'a [PlonkCellV1],
}

impl FflonkPolynomialSourceV1 for SigmaEvaluationSource<'_> {
  fn len(&self) -> usize {
    self.targets.len()
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError> {
    if self.targets.len() != self.powers.size {
      return Err(FflonkStorageError::Range);
    }
    let end = start
      .checked_add(output.len())
      .filter(|&end| end <= self.len())
      .ok_or(FflonkStorageError::Range)?;
    let targets = &self.targets[start..end];
    // Validate before changing any output, including hostile index/column
    // tests. The actual key owns a sealed, already-compiled permutation.
    for target in targets {
      if usize::try_from(target.row)
        .ok()
        .is_none_or(|row| row >= self.powers.size)
        || usize::from(target.column) >= self.powers.high.len()
      {
        return Err(FflonkStorageError::Range);
      }
    }
    let low_size = self.powers.low.len();
    for (value, target) in output.iter_mut().zip(targets) {
      let row = usize::try_from(target.row)
        .map_err(|_| FflonkStorageError::CountOverflow)?;
      *value = self.powers.low[row % low_size]
        * self.powers.high[usize::from(target.column)][row / low_size];
    }
    Ok(())
  }
}

#[cfg(test)]
#[path = "permutation_evaluations_tests.rs"]
mod tests;
