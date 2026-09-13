//! Exact layered GF(2) cofactor bases of an approved Shannon diagram.
//!
//! At each coordinate, a remaining function is represented by the pair of
//! coefficient vectors of its two cofactors in the next layer's basis.
//! Gaussian elimination on those pairs is therefore elimination on EXACT
//! functions, not sampled evaluations. Its residual rows define a new basis;
//! the decoder records the XOR of residual rows equal to each source row.
//! Replacing each pair by `low + x * (low + high)` preserves the unique
//! multilinear extension. No coordinate occurs twice on an evaluation path.
//!
//! Lower rank can be outweighed by denser coefficient XORs. Program selection
//! belongs to the approved setup and must be justified by measured cost.

use crate::{F128FixedTableNodeV0 as Node, F128FixedTableV0};
use std::collections::{BTreeMap, HashSet};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128FixedTableBasisLimitsV0 {
  /// Total distinct source cofactor IDs over all layers, including leaves.
  pub state_slots: u64,
  /// CUMULATIVE u64 slots allocated for elimination rows and decoders,
  /// including scratch. Not peak RSS; excludes source DAG and containers.
  pub dense_words: u64,
  /// Word scans, copies and XORs in elimination and sparse extraction.
  pub word_operations: u64,
  /// Total retained sparse coefficient references, including the output.
  pub coefficient_terms: u64,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128FixedTableBasisCensusV0 {
  pub state_slots: u64,
  pub dense_words: u64,
  pub word_operations: u64,
  pub coefficient_terms: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128FixedTableBasisError {
  UnsupportedEncoding,
  StateLimit,
  DenseWordLimit,
  WorkLimit,
  CoefficientTermLimit,
  Allocation,
  IndexOverflow,
}
use F128FixedTableBasisError as Error;

impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "fixed-table cofactor basis: {self:?}")
  }
}
impl std::error::Error for Error {}

/// One basis function, with fixed XOR coefficients into the next layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128FixedTableBasisRowV0 {
  low: Vec<u32>,
  slope: Vec<u32>,
}

impl F128FixedTableBasisRowV0 {
  pub fn low(&self) -> &[u32] {
    &self.low
  }
  pub fn slope(&self) -> &[u32] {
    &self.slope
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128FixedTableBasisLayerV0 {
  coordinate: u32,
  child_rank: u32,
  rows: Vec<F128FixedTableBasisRowV0>,
}

impl F128FixedTableBasisLayerV0 {
  pub fn coordinate(&self) -> u32 {
    self.coordinate
  }
  pub fn child_rank(&self) -> u32 {
    self.child_rank
  }
  pub fn rows(&self) -> &[F128FixedTableBasisRowV0] {
    &self.rows
  }
}

/// Immutable proof-free program derived only from a validated fixed table.
/// No unchecked constructor or witness-selected coefficient API is exposed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128FixedTableBasisV0 {
  source_digest: [u8; 32],
  constants: Vec<[u8; 16]>,
  // Earliest coordinate first, evaluated in reverse.
  layers: Vec<F128FixedTableBasisLayerV0>,
  output: Vec<u32>,
  census: F128FixedTableBasisCensusV0,
}

impl F128FixedTableBasisV0 {
  /// Only the Shannon encoding returned by `F128FixedTableV0::compile` is
  /// supported. A Davio DAG is rejected, never exponentially expanded.
  pub fn compile(
    table: &F128FixedTableV0,
    limits: F128FixedTableBasisLimitsV0,
  ) -> Result<Self, Error> {
    if table.nodes().iter().any(|node| matches!(node, Node::Davio { .. })) {
      return Err(Error::UnsupportedEncoding);
    }
    let mut budget = Budget { limits, used: Default::default() };
    budget.state()?;
    let mut states = vec![vec![table.root()]];
    for &coordinate in table.order() {
      let mut next = HashSet::new();
      for &id in states.last().expect("root state exists") {
        for child in cofactors(table, id, coordinate) {
          if !next.contains(&child) {
            budget.state()?;
            next.insert(child);
          }
        }
      }
      let mut next: Vec<_> = next.into_iter().collect();
      next.sort_unstable();
      states.push(next);
    }
    let leaves = states.last().expect("leaf layer exists");
    let mut eliminate = Eliminate::new(2, leaves.len().min(128));
    let mut decoders = Vec::new();
    for &id in leaves {
      let Node::Constant(value) = table.nodes()[id as usize] else {
        unreachable!("all approved Shannon coordinates have been consumed");
      };
      let mut row = budget.words(2)?;
      budget.work(2)?;
      row[0] = u64::from_le_bytes(value[..8].try_into().expect("eight bytes"));
      row[1] = u64::from_le_bytes(value[8..].try_into().expect("eight bytes"));
      decoders.push(eliminate.insert(row, &mut budget)?);
    }
    let constants = eliminate
      .rows
      .iter()
      .map(|row| {
        (u128::from(row[0]) | (u128::from(row[1]) << 64)).to_le_bytes()
      })
      .collect::<Vec<_>>();
    let mut child_rank = constants.len();
    trim(&mut decoders, child_rank);
    let mut layers = Vec::new();
    for level in (0..table.order().len()).rev() {
      let coordinate = table.order()[level];
      let children = &states[level + 1];
      let words = child_rank.div_ceil(64);
      let mut eliminate =
        Eliminate::new(2 * words, states[level].len().min(2 * child_rank));
      let mut next_decoders = Vec::new();
      for &id in &states[level] {
        let mut row = budget.words(2 * words)?;
        budget.work((2 * words) as u64)?;
        for (side, child) in
          cofactors(table, id, coordinate).into_iter().enumerate()
        {
          let i = children.binary_search(&child).expect("reachable child");
          row[side * words..(side + 1) * words].copy_from_slice(&decoders[i]);
        }
        next_decoders.push(eliminate.insert(row, &mut budget)?);
      }
      let mut rows = Vec::new();
      for pair in &eliminate.rows {
        let low = budget.terms(pair[..words].iter().copied(), child_rank)?;
        budget.work(words as u64)?; // Form the exact low XOR high slope.
        let slope = budget.terms(
          pair[..words].iter().zip(&pair[words..]).map(|(&a, &b)| a ^ b),
          child_rank,
        )?;
        rows.push(F128FixedTableBasisRowV0 { low, slope });
      }
      layers.push(F128FixedTableBasisLayerV0 {
        coordinate,
        child_rank: u32::try_from(child_rank)
          .map_err(|_| Error::IndexOverflow)?,
        rows,
      });
      child_rank = eliminate.rows.len();
      trim(&mut next_decoders, child_rank);
      decoders = next_decoders;
    }
    let output = budget.terms(decoders[0].iter().copied(), child_rank)?;
    layers.reverse();
    Ok(Self {
      source_digest: table.digest(),
      constants,
      layers,
      output,
      census: budget.used,
    })
  }

  pub fn source_digest(&self) -> [u8; 32] {
    self.source_digest
  }
  pub fn constants(&self) -> &[[u8; 16]] {
    &self.constants
  }
  pub fn layers(&self) -> &[F128FixedTableBasisLayerV0] {
    &self.layers
  }
  pub fn output(&self) -> &[u32] {
    &self.output
  }
  pub fn census(&self) -> F128FixedTableBasisCensusV0 {
    self.census
  }
  pub fn digest(&self) -> [u8; 32] {
    fn terms(hash: &mut blake3::Hasher, terms: &[u32]) {
      hash.update(&(terms.len() as u64).to_le_bytes());
      for index in terms {
        hash.update(&index.to_le_bytes());
      }
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/fixed-table-cofactor-basis/v0\0");
    hash.update(&self.source_digest);
    hash.update(&(self.constants.len() as u64).to_le_bytes());
    for value in &self.constants {
      hash.update(value);
    }
    hash.update(&(self.layers.len() as u64).to_le_bytes());
    for layer in &self.layers {
      hash.update(&layer.coordinate.to_le_bytes());
      hash.update(&layer.child_rank.to_le_bytes());
      hash.update(&(layer.rows.len() as u64).to_le_bytes());
      for row in &layer.rows {
        terms(&mut hash, &row.low);
        terms(&mut hash, &row.slope);
      }
    }
    terms(&mut hash, &self.output);
    *hash.finalize().as_bytes()
  }
}

fn cofactors(table: &F128FixedTableV0, id: u32, coordinate: u32) -> [u32; 2] {
  match table.nodes()[id as usize] {
    Node::Branch { coordinate: c, low, high } if c == coordinate => [low, high],
    _ => [id, id],
  }
}

pub(super) fn trim(decoders: &mut [Vec<u64>], rank: usize) {
  for decoder in decoders {
    decoder.truncate(rank.div_ceil(64));
  }
}

pub(super) struct Budget {
  pub(super) limits: F128FixedTableBasisLimitsV0,
  pub(super) used: F128FixedTableBasisCensusV0,
}

fn charge(
  used: &mut u64,
  limit: u64,
  count: u64,
  error: Error,
) -> Result<(), Error> {
  let next = used.checked_add(count).filter(|&n| n <= limit).ok_or(error)?;
  *used = next;
  Ok(())
}

impl Budget {
  pub(super) fn coefficients(&mut self, count: u64) -> Result<(), Error> {
    charge(
      &mut self.used.coefficient_terms,
      self.limits.coefficient_terms,
      count,
      Error::CoefficientTermLimit,
    )
  }
  pub(super) fn state(&mut self) -> Result<(), Error> {
    charge(
      &mut self.used.state_slots,
      self.limits.state_slots,
      1,
      Error::StateLimit,
    )
  }
  pub(super) fn work(&mut self, words: u64) -> Result<(), Error> {
    charge(
      &mut self.used.word_operations,
      self.limits.word_operations,
      words,
      Error::WorkLimit,
    )
  }
  pub(super) fn words(&mut self, words: usize) -> Result<Vec<u64>, Error> {
    charge(
      &mut self.used.dense_words,
      self.limits.dense_words,
      words as u64,
      Error::DenseWordLimit,
    )?;
    let mut row = Vec::new();
    row.try_reserve_exact(words).map_err(|_| Error::Allocation)?;
    row.resize(words, 0);
    Ok(row)
  }
  pub(super) fn terms(
    &mut self,
    words: impl Iterator<Item = u64>,
    rank: usize,
  ) -> Result<Vec<u32>, Error> {
    let mut result = Vec::new();
    for (word, mut bits) in words.enumerate() {
      self.work(1)?;
      while bits != 0 {
        self.work(1)?;
        let bit = word * 64 + bits.trailing_zeros() as usize;
        debug_assert!(bit < rank);
        self.coefficients(1)?;
        result.push(u32::try_from(bit).map_err(|_| Error::IndexOverflow)?);
        bits &= bits - 1;
      }
    }
    Ok(result)
  }
}

struct Eliminate {
  words: usize,
  decoder_words: usize,
  rows: Vec<Vec<u64>>,
  pivots: BTreeMap<usize, usize>,
}

impl Eliminate {
  fn new(words: usize, max_rank: usize) -> Self {
    Self {
      words,
      decoder_words: max_rank.div_ceil(64),
      rows: Vec::new(),
      pivots: BTreeMap::new(),
    }
  }

  fn insert(
    &mut self,
    mut row: Vec<u64>,
    budget: &mut Budget,
  ) -> Result<Vec<u64>, Error> {
    debug_assert_eq!(row.len(), self.words);
    let mut decoder = budget.words(self.decoder_words)?;
    loop {
      let mut pivot = None;
      for (word, &bits) in row.iter().enumerate() {
        budget.work(1)?;
        if bits != 0 {
          pivot = Some(word * 64 + bits.trailing_zeros() as usize);
          break;
        }
      }
      let Some(pivot) = pivot else { break };
      if let Some(&index) = self.pivots.get(&pivot) {
        budget.work(self.words as u64 + 1)?;
        decoder[index / 64] ^= 1 << (index % 64);
        for (dst, &src) in row.iter_mut().zip(&self.rows[index]) {
          *dst ^= src;
        }
      } else {
        budget.work(1)?;
        let index = self.rows.len();
        decoder[index / 64] ^= 1 << (index % 64);
        self.pivots.insert(pivot, index);
        self.rows.push(row);
        break;
      }
    }
    Ok(decoder)
  }
}

#[cfg(test)]
#[path = "fixed_table_basis_tests.rs"]
mod tests;
