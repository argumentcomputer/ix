//! Exact fixed-layout program for the ORIGINAL jagged assertions.
//!
//! Each layout row selects one boundary pair. A shared equality-product DAG
//! evaluates the distinct pairs, then a row Shannon diagram contracts either
//! original equality weight. The combo uses only its approved fixed addresses.
//! No dense pair-space enumeration, random fold, or evaluation advice exists.

use crate::F128JaggedMatrixIdV1;
use std::{
  collections::{BTreeSet, HashMap},
  fmt,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128JaggedDirectLimitsV0 {
  pub runs: u32,
  pub combo_terms: u32,
  pub row_nodes: u32,
  pub equality_nodes: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum F128JaggedRowNodeV0 {
  Pair(u32),
  Branch { coordinate: u32, low: u32, high: u32 },
}

/// Children precede their products. The compiler separates left/right boundary
/// coordinates and interns balanced subproducts, sharing repeated boundaries
/// AND their repeated bit groups. No equality factor is omitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum F128JaggedEqualityNodeV0 {
  Factor { coordinate: u32, complement: bool },
  Multiply { left: u32, right: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128JaggedDirectError {
  Geometry,
  Boundary,
  Coverage,
  ComboAddress,
  Limit(&'static str),
  IndexOverflow,
}
use F128JaggedDirectError as Error;
impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "direct jagged table: {self:?}")
  }
}
impl std::error::Error for Error {}

/// Immutable setup data. Construction checks encoding/geometry, not matrix
/// authorization: the Exec setup owner must supply the real layout and exact
/// combo address order from its approved merged-PCS blueprint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedDirectTableV0 {
  matrix: F128JaggedMatrixIdV1,
  // Strictly increasing exclusive row end, and index of the selected pair.
  runs: Vec<(u64, u32)>,
  pairs: Vec<u64>,
  equality_nodes: Vec<F128JaggedEqualityNodeV0>,
  pair_outputs: Vec<u32>,
  row_nodes: Vec<F128JaggedRowNodeV0>,
  row_root: u32,
  combo: Vec<(u32, u32)>,
}

impl F128JaggedDirectTableV0 {
  pub fn compile(
    matrix: F128JaggedMatrixIdV1,
    bounds: impl IntoIterator<Item = (u64, u64, u32)>,
    combo_addresses: impl IntoIterator<Item = u32>,
    limits: F128JaggedDirectLimitsV0,
  ) -> Result<Self, Error> {
    if matrix.row_variables > 32
      || matrix.column_variables == 0
      || matrix.column_variables > 64
      || !matrix.column_variables.is_multiple_of(2)
    {
      return Err(Error::Geometry);
    }
    let boundary_bits = matrix.column_variables / 2;
    let boundary_limit = 1u64 << (boundary_bits - 1);
    let row_limit = 1u64 << matrix.row_variables;
    let mut raw_runs = Vec::new();
    let mut end = 0u64;
    for (left, right, count) in bounds {
      if raw_runs.len() as u64 >= u64::from(limits.runs) {
        return Err(Error::Limit("runs"));
      }
      if left > right || right > boundary_limit {
        return Err(Error::Boundary);
      }
      end = end.checked_add(u64::from(count)).ok_or(Error::IndexOverflow)?;
      if count == 0 || end > row_limit {
        return Err(Error::Coverage);
      }
      let mut pair = 0u64;
      for bit in 0..boundary_bits {
        pair |= ((left >> bit) & 1) << (2 * bit);
        pair |= ((right >> bit) & 1) << (2 * bit + 1);
      }
      raw_runs.push((end, pair));
    }
    if end != row_limit {
      return Err(Error::Coverage);
    }
    let pairs: Vec<_> = raw_runs
      .iter()
      .map(|&(_, pair)| pair)
      .collect::<BTreeSet<_>>()
      .into_iter()
      .collect();
    let runs: Vec<_> = raw_runs
      .iter()
      .map(|&(end, pair)| {
        let index = pairs.binary_search(&pair).expect("collected pair");
        Ok((end, u32::try_from(index).map_err(|_| Error::IndexOverflow)?))
      })
      .collect::<Result<_, Error>>()?;
    let mut combo = Vec::new();
    for address in combo_addresses {
      if combo.len() as u64 >= u64::from(limits.combo_terms) {
        return Err(Error::Limit("combo terms"));
      }
      if u64::from(address) >= row_limit {
        return Err(Error::ComboAddress);
      }
      let run = runs.partition_point(|&(end, _)| end <= u64::from(address));
      combo.push((address, runs[run].1));
    }
    if combo.is_empty() {
      return Err(Error::ComboAddress);
    }
    let mut result = Self {
      matrix,
      runs,
      pair_outputs: vec![0; pairs.len()],
      pairs,
      equality_nodes: Vec::new(),
      row_nodes: Vec::new(),
      row_root: 0,
      combo,
    };
    let order: Vec<_> = (0..matrix.column_variables)
      .step_by(2)
      .chain((1..matrix.column_variables).step_by(2))
      .collect();
    let mut intern = HashMap::new();
    for index in 0..result.pairs.len() {
      let pair = result.pairs[index];
      let reordered = order
        .iter()
        .enumerate()
        .fold(0, |value, (i, bit)| value | (((pair >> bit) & 1) << i));
      result.pair_outputs[index] = result.compile_equality_product(
        0,
        &order,
        reordered,
        &mut intern,
        limits,
      )?;
    }
    result.row_root = result.compile_rows(
      0,
      matrix.row_variables,
      &mut HashMap::new(),
      limits,
    )?;
    Ok(result)
  }

  fn compile_equality_product(
    &mut self,
    first: u32,
    order: &[u32],
    value: u64,
    intern: &mut HashMap<(u32, u32, u64), u32>,
    limits: F128JaggedDirectLimitsV0,
  ) -> Result<u32, Error> {
    let width = u32::try_from(order.len()).map_err(|_| Error::IndexOverflow)?;
    let key = (first, width, value);
    if let Some(&index) = intern.get(&key) {
      return Ok(index);
    }
    let node = if order.len() == 1 {
      F128JaggedEqualityNodeV0::Factor {
        coordinate: order[0],
        complement: value == 0,
      }
    } else {
      // At most 64 coordinates, so this split is in 1..=32. The mask and
      // shift never use a shift of 64, including maximum-width layouts.
      let split = order.len() / 2;
      let left = self.compile_equality_product(
        first,
        &order[..split],
        value & ((1u64 << split) - 1),
        intern,
        limits,
      )?;
      let right = self.compile_equality_product(
        first + u32::try_from(split).map_err(|_| Error::IndexOverflow)?,
        &order[split..],
        value >> split,
        intern,
        limits,
      )?;
      F128JaggedEqualityNodeV0::Multiply { left, right }
    };
    let index = push_eq(&mut self.equality_nodes, node, limits)?;
    intern.insert(key, index);
    Ok(index)
  }

  fn compile_rows(
    &mut self,
    first: u64,
    bits: u32,
    intern: &mut HashMap<F128JaggedRowNodeV0, u32>,
    limits: F128JaggedDirectLimitsV0,
  ) -> Result<u32, Error> {
    let run = self.runs.partition_point(|&(end, _)| end <= first);
    let node = if self.runs[run].0 >= first + (1u64 << bits) {
      F128JaggedRowNodeV0::Pair(self.runs[run].1)
    } else {
      let coordinate = bits.checked_sub(1).ok_or(Error::Coverage)?;
      let low = self.compile_rows(first, coordinate, intern, limits)?;
      let high = self.compile_rows(
        first + (1u64 << coordinate),
        coordinate,
        intern,
        limits,
      )?;
      if low == high {
        return Ok(low);
      }
      F128JaggedRowNodeV0::Branch { coordinate, low, high }
    };
    if let Some(&index) = intern.get(&node) {
      return Ok(index);
    }
    if self.row_nodes.len() as u64 >= u64::from(limits.row_nodes) {
      return Err(Error::Limit("row nodes"));
    }
    let index =
      u32::try_from(self.row_nodes.len()).map_err(|_| Error::IndexOverflow)?;
    self.row_nodes.push(node);
    intern.insert(node, index);
    Ok(index)
  }

  pub fn matrix(&self) -> F128JaggedMatrixIdV1 {
    self.matrix
  }
  pub fn runs(&self) -> &[(u64, u32)] {
    &self.runs
  }
  pub fn pairs(&self) -> &[u64] {
    &self.pairs
  }
  pub fn equality_nodes(&self) -> &[F128JaggedEqualityNodeV0] {
    &self.equality_nodes
  }
  pub fn pair_outputs(&self) -> &[u32] {
    &self.pair_outputs
  }
  pub fn row_nodes(&self) -> &[F128JaggedRowNodeV0] {
    &self.row_nodes
  }
  pub fn row_root(&self) -> u32 {
    self.row_root
  }
  /// Exact `(fixed row address, pair index)` in approved combo term order.
  pub fn combo(&self) -> &[(u32, u32)] {
    &self.combo
  }

  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/direct-jagged-table/v0\0");
    hash.update(&self.matrix.circuit_digest);
    hash.update(&self.matrix.row_variables.to_le_bytes());
    hash.update(&self.matrix.column_variables.to_le_bytes());
    hash.update(&(self.runs.len() as u64).to_le_bytes());
    for (end, pair) in &self.runs {
      hash.update(&end.to_le_bytes());
      hash.update(&pair.to_le_bytes());
    }
    hash.update(&(self.pairs.len() as u64).to_le_bytes());
    for pair in &self.pairs {
      hash.update(&pair.to_le_bytes());
    }
    hash.update(&(self.equality_nodes.len() as u64).to_le_bytes());
    for node in &self.equality_nodes {
      match node {
        F128JaggedEqualityNodeV0::Factor { coordinate, complement } => {
          hash.update(&[0]);
          hash.update(&coordinate.to_le_bytes());
          hash.update(&[u8::from(*complement)]);
        },
        F128JaggedEqualityNodeV0::Multiply { left, right } => {
          hash.update(&[1]);
          hash.update(&left.to_le_bytes());
          hash.update(&right.to_le_bytes());
        },
      }
    }
    hash.update(&(self.pair_outputs.len() as u64).to_le_bytes());
    for index in &self.pair_outputs {
      hash.update(&index.to_le_bytes());
    }
    hash.update(&(self.row_nodes.len() as u64).to_le_bytes());
    for node in &self.row_nodes {
      match node {
        F128JaggedRowNodeV0::Pair(index) => {
          hash.update(&[0]);
          hash.update(&index.to_le_bytes());
        },
        F128JaggedRowNodeV0::Branch { coordinate, low, high } => {
          hash.update(&[1]);
          hash.update(&coordinate.to_le_bytes());
          hash.update(&low.to_le_bytes());
          hash.update(&high.to_le_bytes());
        },
      }
    }
    hash.update(&self.row_root.to_le_bytes());
    hash.update(&(self.combo.len() as u64).to_le_bytes());
    for (address, pair) in &self.combo {
      hash.update(&address.to_le_bytes());
      hash.update(&pair.to_le_bytes());
    }
    *hash.finalize().as_bytes()
  }
}

fn push_eq(
  nodes: &mut Vec<F128JaggedEqualityNodeV0>,
  node: F128JaggedEqualityNodeV0,
  limits: F128JaggedDirectLimitsV0,
) -> Result<u32, Error> {
  if nodes.len() as u64 >= u64::from(limits.equality_nodes) {
    return Err(Error::Limit("equality nodes"));
  }
  let index = u32::try_from(nodes.len()).map_err(|_| Error::IndexOverflow)?;
  nodes.push(node);
  Ok(index)
}

#[cfg(test)]
#[path = "jagged_direct_tests.rs"]
mod tests;
