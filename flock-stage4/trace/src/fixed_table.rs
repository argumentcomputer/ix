//! Exact, setup-only compression of a fixed sparse F128-valued table.
//!
//! This reduced ordered decision diagram represents the table on the Boolean
//! cube. Replacing each decision by `low + x * (low + high)` evaluates its
//! multilinear extension, not an approximation or a committed-table oracle.
//! Table ownership/authorization belongs to the setup which constructs it.

use std::{collections::HashMap, fmt};

#[path = "fixed_table_davio.rs"]
mod davio;
pub use davio::F128FixedTableDavioLimitsV0;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum F128FixedTableNodeV0 {
  Constant([u8; 16]),
  /// Both children precede this node. Each path follows the approved order
  /// without repeating a coordinate; equal children are reduced away.
  Branch {
    coordinate: u32,
    low: u32,
    high: u32,
  },
  /// Davio decomposition `base + literal * slope`, where `literal` is
  /// `x[coordinate]` or its complement `1+x[coordinate]`. Neither
  /// child depends on this coordinate; the slope is the exact XOR of the
  /// original Shannon cofactors, compiled symbolically rather than hinted.
  Davio {
    coordinate: u32,
    base: u32,
    slope: u32,
    complement: bool,
  },
}

/// Hard bounds for the sparse input and interned DAG, checked during setup.
/// They are not a terminal prover memory-admission model.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128FixedTableLimitsV0 {
  pub entries: usize,
  pub nodes: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128FixedTableError {
  VariableOrder,
  IndexOutOfRange(u64),
  EntryLimit,
  NodeLimit,
  RewriteLimit,
  UnsupportedEncoding,
}

impl fmt::Display for F128FixedTableError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "fixed-table compilation: {self:?}")
  }
}

impl std::error::Error for F128FixedTableError {}

/// Immutable proof-free table program. No constructor from arbitrary nodes
/// is exposed; the DAG is derived from the exact fixed sparse coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128FixedTableV0 {
  order: Vec<u32>,
  nodes: Vec<F128FixedTableNodeV0>,
  root: u32,
  nonzero_entries: usize,
}

impl F128FixedTableV0 {
  /// `order` is a permutation of `0..n` for `n <= 64`, earliest decision
  /// first. Coordinate `i` is bit `i` of each input index (LSB-first).
  /// Unlisted entries are zero. Repeated entries are added by XOR, matching
  /// characteristic-two sparse-matrix semantics, including cancellation.
  pub fn compile(
    order: &[u32],
    entries: impl IntoIterator<Item = (u64, [u8; 16])>,
    limits: F128FixedTableLimitsV0,
  ) -> Result<Self, F128FixedTableError> {
    let variables = order.len();
    if variables > 64 {
      return Err(F128FixedTableError::VariableOrder);
    }
    let mut sorted_order = order.to_vec();
    sorted_order.sort_unstable();
    if !sorted_order
      .iter()
      .copied()
      .eq(0..u32::try_from(variables).expect("at most 64 coordinates"))
    {
      return Err(F128FixedTableError::VariableOrder);
    }
    let mut sparse = Vec::new();
    for (count, (index, value)) in entries.into_iter().enumerate() {
      if count >= limits.entries {
        return Err(F128FixedTableError::EntryLimit);
      }
      if variables < 64 && index >= (1u64 << variables) {
        return Err(F128FixedTableError::IndexOutOfRange(index));
      }
      if value == [0; 16] {
        continue;
      }
      let mut ordered_index = 0;
      for &coordinate in order {
        ordered_index = (ordered_index << 1) | ((index >> coordinate) & 1);
      }
      sparse.push((ordered_index, value));
    }
    sparse.sort_unstable_by_key(|entry| entry.0);
    // Normalize duplicate coefficients in place, avoiding a second full
    // sparse input allocation. This also makes input iteration order inert.
    let (mut read, mut write) = (0, 0);
    while read < sparse.len() {
      let index = sparse[read].0;
      let mut value = [0; 16];
      while read < sparse.len() && sparse[read].0 == index {
        for (dst, src) in value.iter_mut().zip(sparse[read].1) {
          *dst ^= src;
        }
        read += 1;
      }
      if value != [0; 16] {
        sparse[write] = (index, value);
        write += 1;
      }
    }
    sparse.truncate(write);
    let mut compiler = Compiler {
      order,
      nodes: Vec::new(),
      interned: HashMap::new(),
      limit: limits.nodes,
    };
    let root = compiler.subtree(0, &sparse)?;
    Ok(Self {
      order: order.to_vec(),
      nodes: compiler.nodes,
      root,
      nonzero_entries: sparse.len(),
    })
  }

  pub fn order(&self) -> &[u32] {
    &self.order
  }
  pub fn nodes(&self) -> &[F128FixedTableNodeV0] {
    &self.nodes
  }
  pub fn root(&self) -> u32 {
    self.root
  }
  pub fn nonzero_entries(&self) -> usize {
    self.nonzero_entries
  }
  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/fixed-table-dd/v0\0");
    hash.update(
      &u32::try_from(self.order.len())
        .expect("at most 64 coordinates")
        .to_le_bytes(),
    );
    for coordinate in &self.order {
      hash.update(&coordinate.to_le_bytes());
    }
    hash.update(&(self.nonzero_entries as u64).to_le_bytes());
    hash.update(&self.root.to_le_bytes());
    hash.update(&(self.nodes.len() as u64).to_le_bytes());
    for node in &self.nodes {
      match node {
        F128FixedTableNodeV0::Constant(value) => {
          hash.update(&[0]);
          hash.update(value);
        },
        F128FixedTableNodeV0::Branch { coordinate, low, high } => {
          hash.update(&[1]);
          for index in [coordinate, low, high] {
            hash.update(&index.to_le_bytes());
          }
        },
        F128FixedTableNodeV0::Davio { coordinate, base, slope, complement } => {
          hash.update(&[2]);
          hash.update(&[u8::from(*complement)]);
          for index in [coordinate, base, slope] {
            hash.update(&index.to_le_bytes());
          }
        },
      }
    }
    *hash.finalize().as_bytes()
  }
}

struct Compiler<'a> {
  order: &'a [u32],
  nodes: Vec<F128FixedTableNodeV0>,
  interned: HashMap<F128FixedTableNodeV0, u32>,
  limit: u32,
}

impl Compiler<'_> {
  fn intern(
    &mut self,
    node: F128FixedTableNodeV0,
  ) -> Result<u32, F128FixedTableError> {
    if let Some(index) = self.interned.get(&node) {
      return Ok(*index);
    }
    if self.nodes.len() as u64 >= u64::from(self.limit) {
      return Err(F128FixedTableError::NodeLimit);
    }
    let index = u32::try_from(self.nodes.len())
      .map_err(|_| F128FixedTableError::NodeLimit)?;
    self.nodes.push(node);
    self.interned.insert(node, index);
    Ok(index)
  }

  fn subtree(
    &mut self,
    level: usize,
    entries: &[(u64, [u8; 16])],
  ) -> Result<u32, F128FixedTableError> {
    if entries.is_empty() {
      return self.intern(F128FixedTableNodeV0::Constant([0; 16]));
    }
    if level == self.order.len() {
      debug_assert_eq!(entries.len(), 1);
      return self.intern(F128FixedTableNodeV0::Constant(entries[0].1));
    }
    let bit = 1u64 << (self.order.len() - level - 1);
    let middle = entries.partition_point(|entry| entry.0 & bit == 0);
    let low = self.subtree(level + 1, &entries[..middle])?;
    let high = self.subtree(level + 1, &entries[middle..])?;
    if low == high {
      Ok(low)
    } else {
      self.intern(F128FixedTableNodeV0::Branch {
        coordinate: self.order[level],
        low,
        high,
      })
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  const LIMITS: F128FixedTableLimitsV0 =
    F128FixedTableLimitsV0 { entries: 100_000, nodes: 10_000 };

  fn at(table: &F128FixedTableV0, index: u64) -> [u8; 16] {
    let mut values = Vec::new();
    for node in table.nodes() {
      let value = match *node {
        F128FixedTableNodeV0::Constant(value) => value,
        F128FixedTableNodeV0::Branch { coordinate, low, high } => {
          values
            [if index & (1 << coordinate) == 0 { low } else { high } as usize]
        },
        F128FixedTableNodeV0::Davio { coordinate, base, slope, complement } => {
          let mut value: [u8; 16] = values[base as usize];
          if (index & (1 << coordinate) != 0) ^ complement {
            for (dst, src) in value.iter_mut().zip(values[slope as usize]) {
              *dst ^= src;
            }
          }
          value
        },
      };
      values.push(value);
    }
    values[table.root() as usize]
  }

  #[test]
  fn exact_cube_values_and_canonical_duplicate_cancellation() {
    for order in [vec![0, 1, 2, 3], vec![3, 1, 2, 0], vec![3, 2, 1, 0]] {
      let entries = (0u64..16)
        .filter(|i| i % 3 != 0)
        .map(|i| (i, u128::from(17 * i).to_le_bytes()))
        .collect::<Vec<_>>();
      let table =
        F128FixedTableV0::compile(&order, entries.clone(), LIMITS).unwrap();
      let mut shuffled = entries.clone();
      shuffled.extend([(5, [7; 16]), (5, [7; 16]), (0, [0; 16])]);
      shuffled.reverse();
      let same = F128FixedTableV0::compile(&order, shuffled, LIMITS).unwrap();
      assert_eq!(table, same);
      assert_eq!(table.digest(), same.digest());
      let davio = table
        .positive_davio(F128FixedTableDavioLimitsV0 {
          working_nodes: 10_000,
          nodes: 10_000,
          xor_calls: 100_000,
        })
        .unwrap();
      let mixed = table
        .mixed_davio(F128FixedTableDavioLimitsV0 {
          working_nodes: 10_000,
          nodes: 10_000,
          xor_calls: 100_000,
        })
        .unwrap();
      for index in 0..16 {
        let expected = entries
          .iter()
          .find(|entry| entry.0 == index)
          .map_or([0; 16], |entry| entry.1);
        assert_eq!(at(&table, index), expected);
        assert_eq!(at(&davio, index), expected);
        assert_eq!(at(&mixed, index), expected);
      }
      let changed = F128FixedTableV0::compile(
        &order,
        entries.into_iter().chain([(0, [1; 16])]),
        LIMITS,
      )
      .unwrap();
      assert_ne!(table.digest(), changed.digest());
    }
  }

  #[test]
  fn interleaved_diagonal_has_linear_dag_and_exact_skipped_coordinates() {
    let bits = 10;
    let order = (0..bits).rev().flat_map(|i| [i, bits + i]).collect::<Vec<_>>();
    let table = F128FixedTableV0::compile(
      &order,
      (0..1u64 << bits).map(|i| (i | (i << bits), 1u128.to_le_bytes())),
      LIMITS,
    )
    .unwrap();
    assert_eq!(table.nodes().len(), 3 * bits as usize + 2);
    for row in 0..1 << bits {
      for column in [row, row ^ 1, (row + 7) % (1 << bits)] {
        assert_eq!(
          at(&table, row | (column << bits)),
          u128::from(row == column).to_le_bytes()
        );
      }
    }
    // A full constant cube reduces to its sole constant; coordinates which
    // do not affect the table cannot become witness-dependent branches.
    let constant = F128FixedTableV0::compile(
      &[2, 0, 1],
      (0..8).map(|i| (i, [5; 16])),
      LIMITS,
    )
    .unwrap();
    assert_eq!(constant.nodes(), &[F128FixedTableNodeV0::Constant([5; 16])]);
    let scalar =
      F128FixedTableV0::compile(&[], [(0, [9; 16])], LIMITS).unwrap();
    assert_eq!(at(&scalar, 0), [9; 16]);
    let zero = F128FixedTableV0::compile(&[], [], LIMITS).unwrap();
    assert_eq!(at(&zero, 0), [0; 16]);
  }

  #[test]
  fn malformed_shape_and_resource_exhaustion_fail_during_compilation() {
    for order in [vec![0, 0], vec![0, 2], vec![1], (0..65).collect()] {
      assert_eq!(
        F128FixedTableV0::compile(&order, [], LIMITS).unwrap_err(),
        F128FixedTableError::VariableOrder
      );
    }
    for (order, index) in [(vec![], 1), (vec![0, 1], 4)] {
      assert_eq!(
        F128FixedTableV0::compile(&order, [(index, [0; 16])], LIMITS)
          .unwrap_err(),
        F128FixedTableError::IndexOutOfRange(index)
      );
    }
    let too_many = F128FixedTableLimitsV0 { entries: 0, ..LIMITS };
    assert_eq!(
      F128FixedTableV0::compile(&[], [(0, [0; 16])], too_many).unwrap_err(),
      F128FixedTableError::EntryLimit
    );
    let no_nodes = F128FixedTableLimitsV0 { nodes: 0, ..LIMITS };
    assert_eq!(
      F128FixedTableV0::compile(&[], [], no_nodes).unwrap_err(),
      F128FixedTableError::NodeLimit
    );
    let order = (0..64).rev().collect::<Vec<_>>();
    let full_index =
      F128FixedTableV0::compile(&order, [(u64::MAX, [3; 16])], LIMITS).unwrap();
    assert_eq!(at(&full_index, u64::MAX), [3; 16]);
    assert_eq!(at(&full_index, u64::MAX - 1), [0; 16]);
  }

  #[test]
  fn davio_rewrite_is_bounded_and_cannot_reinterpret_an_existing_encoding() {
    let table =
      F128FixedTableV0::compile(&[1, 0], [(0, [7; 16]), (3, [13; 16])], LIMITS)
        .unwrap();
    let limits = F128FixedTableDavioLimitsV0 {
      working_nodes: 100,
      nodes: 100,
      xor_calls: 100,
    };
    let davio = table.positive_davio(limits).unwrap();
    assert_eq!(
      davio.positive_davio(limits).unwrap_err(),
      F128FixedTableError::UnsupportedEncoding
    );
    for limits in [
      F128FixedTableDavioLimitsV0 { working_nodes: 0, ..limits },
      F128FixedTableDavioLimitsV0 { nodes: 0, ..limits },
      F128FixedTableDavioLimitsV0 { xor_calls: 0, ..limits },
    ] {
      assert!(table.positive_davio(limits).is_err());
    }
  }
}
