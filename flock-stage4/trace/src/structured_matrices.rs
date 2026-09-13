//! Exact shared evaluations of fixed Boolean matrices with structured weights.
//!
//! Split each index into low bits and high bits. A fixed low-index block is
//! the bilinear form sum(row_low[i] * column_low[j]) at its nonzero entries.
//! The high-index function is then interpolated at the shared equality-weight
//! coordinates. Identical blocks and high cofactors are shared across matrices.
//! This contracts the ORIGINAL claims; no random fold or unchecked root is
//! introduced. Approval of the source matrices remains the caller's duty.

use crate::{
  F128FixedTableError, F128FixedTableLimitsV0, F128FixedTableNodeV0 as Node,
  F128FixedTableV0, F128MatrixSideV1, F128StaticMatrixIdV1,
};
use std::{
  collections::{BTreeMap, BTreeSet, HashMap},
  fmt,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128StructuredMatricesLimitsV0 {
  pub tables: u32,
  /// Total input coefficients examined, including duplicates that cancel.
  pub source_entries: usize,
  pub blocks: u32,
  pub coefficient_terms: u64,
  pub shared_nodes: u32,
  /// Per-matrix temporary high-index Shannon compiler, not a RAM bound.
  pub temporary_nodes: u32,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128StructuredMatricesCensusV0 {
  pub source_entries: usize,
  pub blocks: u32,
  pub coefficient_terms: u64,
  pub shared_nodes: u32,
  pub maximum_temporary_nodes: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum F128StructuredMatrixNodeV0 {
  Zero,
  Block(u32),
  /// `bit` indexes the high equality-weight point, not a low vector bit.
  Branch {
    column: bool,
    bit: u32,
    low: u32,
    high: u32,
  },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128StructuredMatricesError {
  Geometry,
  MatrixOrder,
  Registry,
  Coordinate,
  Limit(&'static str),
  IndexOverflow,
  Diagram(F128FixedTableError),
}
use F128StructuredMatricesError as Error;
impl fmt::Display for Error {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "structured matrix compilation: {self:?}")
  }
}
impl std::error::Error for Error {}

/// Immutable setup program. Blocks list low `(row | column << low_bits)`
/// pairs, not arbitrary field coefficients or witness-selected addresses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredMatricesV0 {
  low_variables: u32,
  high_variables: u32,
  pairs: Vec<u16>,
  blocks: Vec<Vec<u16>>,
  nodes: Vec<F128StructuredMatrixNodeV0>,
  outputs: Vec<(F128StaticMatrixIdV1, u32)>,
  census: F128StructuredMatricesCensusV0,
}

impl F128StructuredMatricesV0 {
  /// Fixed, ordered matrix IDs and their actual row/column coordinates only.
  /// All matrices share low-vector lengths and prefixes of the same high
  /// points. The circuit must check that wire-sharing premise explicitly.
  /// Currently supports at most six low bits per side, the native RS skip.
  pub fn compile<I, J>(
    low_variables: u32,
    sources: I,
    limits: F128StructuredMatricesLimitsV0,
  ) -> Result<Self, Error>
  where
    I: IntoIterator<Item = (F128StaticMatrixIdV1, J)>,
    J: IntoIterator<Item = (u32, u32)>,
  {
    if low_variables > 6 {
      return Err(Error::Geometry);
    }
    let mut result = Self {
      low_variables,
      high_variables: 0,
      pairs: Vec::new(),
      blocks: Vec::new(),
      nodes: Vec::new(),
      outputs: Vec::new(),
      census: Default::default(),
    };
    let mut block_ids = HashMap::<Vec<u16>, u32>::new();
    let mut node_ids = HashMap::new();
    let mask = (1u32 << low_variables) - 1;
    for (id, entries) in sources {
      if result.outputs.len() as u64 >= u64::from(limits.tables) {
        return Err(Error::Limit("tables"));
      }
      if id.variables < low_variables || id.variables > 32 {
        return Err(Error::Geometry);
      }
      if let Some(&(first, _)) = result.outputs.first()
        && first.registry_digest != id.registry_digest
      {
        return Err(Error::Registry);
      }
      if result.outputs.last().is_some_and(|(last, _)| {
        *last >= id || (last.table == id.table && last.side == id.side)
      }) {
        return Err(Error::MatrixOrder);
      }
      let high_bits = id.variables - low_variables;
      result.high_variables = result.high_variables.max(high_bits);
      let mut blocks = BTreeMap::<u64, Vec<u16>>::new();
      for (row, column) in entries {
        if result.census.source_entries == limits.source_entries {
          return Err(Error::Limit("source entries"));
        }
        result.census.source_entries += 1;
        if u64::from(row) >= (1u64 << id.variables)
          || u64::from(column) >= (1u64 << id.variables)
        {
          return Err(Error::Coordinate);
        }
        let high = u64::from(row >> low_variables)
          | (u64::from(column >> low_variables) << high_bits);
        let low = (row & mask) | ((column & mask) << low_variables);
        blocks
          .entry(high)
          .or_default()
          .push(u16::try_from(low).map_err(|_| Error::IndexOverflow)?);
      }
      let mut high_entries = Vec::new();
      for (high, mut pairs) in blocks {
        pairs.sort_unstable();
        let mut normalized = Vec::new();
        let mut index = 0;
        while index < pairs.len() {
          let first = index;
          while index < pairs.len() && pairs[index] == pairs[first] {
            index += 1;
          }
          if (index - first) % 2 == 1 {
            normalized.push(pairs[first]);
          }
        }
        if normalized.is_empty() {
          continue;
        }
        let block = if let Some(&index) = block_ids.get(&normalized) {
          index
        } else {
          if result.blocks.len() as u64 >= u64::from(limits.blocks) {
            return Err(Error::Limit("blocks"));
          }
          let terms = result
            .census
            .coefficient_terms
            .checked_add(normalized.len() as u64)
            .ok_or(Error::IndexOverflow)?;
          if terms > limits.coefficient_terms {
            return Err(Error::Limit("coefficient terms"));
          }
          result.census.coefficient_terms = terms;
          let index = u32::try_from(result.blocks.len())
            .map_err(|_| Error::IndexOverflow)?;
          block_ids.insert(normalized.clone(), index);
          result.blocks.push(normalized);
          index
        };
        // Unique high index per block: these tags are NEVER XORed as field
        // coefficients. Zero tags represent an absent block. The temporary
        // compiler is Shannon-only and only compares/interns block tags.
        high_entries.push((high, (u128::from(block) + 1).to_le_bytes()));
      }
      let order = (0..high_bits)
        .rev()
        .flat_map(|bit| [bit, high_bits + bit])
        .collect::<Vec<_>>();
      let diagram = F128FixedTableV0::compile(
        &order,
        high_entries,
        F128FixedTableLimitsV0 {
          entries: limits.source_entries,
          nodes: limits.temporary_nodes,
        },
      )
      .map_err(Error::Diagram)?;
      result.census.maximum_temporary_nodes =
        result.census.maximum_temporary_nodes.max(
          u32::try_from(diagram.nodes().len())
            .map_err(|_| Error::IndexOverflow)?,
        );
      let mut translated = Vec::with_capacity(diagram.nodes().len());
      for node in diagram.nodes() {
        let node = match *node {
          Node::Constant(tag) => {
            let tag = u128::from_le_bytes(tag);
            if tag == 0 {
              F128StructuredMatrixNodeV0::Zero
            } else {
              let block =
                u32::try_from(tag - 1).map_err(|_| Error::IndexOverflow)?;
              if block as usize >= result.blocks.len() {
                return Err(Error::Geometry);
              }
              F128StructuredMatrixNodeV0::Block(block)
            }
          },
          Node::Branch { coordinate, low, high } => {
            F128StructuredMatrixNodeV0::Branch {
              column: coordinate >= high_bits,
              bit: if coordinate >= high_bits {
                coordinate - high_bits
              } else {
                coordinate
              },
              low: translated[low as usize],
              high: translated[high as usize],
            }
          },
          Node::Davio { .. } => {
            unreachable!("temporary compiler is Shannon-only")
          },
        };
        let index = if let Some(&index) = node_ids.get(&node) {
          index
        } else {
          if result.nodes.len() as u64 >= u64::from(limits.shared_nodes) {
            return Err(Error::Limit("shared nodes"));
          }
          let index = u32::try_from(result.nodes.len())
            .map_err(|_| Error::IndexOverflow)?;
          result.nodes.push(node);
          node_ids.insert(node, index);
          index
        };
        translated.push(index);
      }
      result.outputs.push((id, translated[diagram.root() as usize]));
    }
    if result.outputs.is_empty() {
      return Err(Error::Geometry);
    }
    result.pairs = result
      .blocks
      .iter()
      .flatten()
      .copied()
      .collect::<BTreeSet<_>>()
      .into_iter()
      .collect();
    result.census.blocks =
      u32::try_from(result.blocks.len()).map_err(|_| Error::IndexOverflow)?;
    result.census.shared_nodes =
      u32::try_from(result.nodes.len()).map_err(|_| Error::IndexOverflow)?;
    Ok(result)
  }

  pub fn low_variables(&self) -> u32 {
    self.low_variables
  }
  pub fn high_variables(&self) -> u32 {
    self.high_variables
  }
  pub fn pairs(&self) -> &[u16] {
    &self.pairs
  }
  pub fn blocks(&self) -> &[Vec<u16>] {
    &self.blocks
  }
  pub fn nodes(&self) -> &[F128StructuredMatrixNodeV0] {
    &self.nodes
  }
  pub fn outputs(&self) -> &[(F128StaticMatrixIdV1, u32)] {
    &self.outputs
  }
  pub fn census(&self) -> F128StructuredMatricesCensusV0 {
    self.census
  }

  pub fn digest(&self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/shared-structured-matrices/v0\0");
    hash.update(&self.low_variables.to_le_bytes());
    hash.update(&self.high_variables.to_le_bytes());
    hash.update(&(self.outputs.len() as u64).to_le_bytes());
    for (id, root) in &self.outputs {
      hash.update(&id.registry_digest);
      hash.update(&id.table.to_le_bytes());
      hash.update(&[match id.side {
        F128MatrixSideV1::A => 0,
        F128MatrixSideV1::B => 1,
      }]);
      hash.update(&id.variables.to_le_bytes());
      hash.update(&root.to_le_bytes());
    }
    hash.update(&(self.pairs.len() as u64).to_le_bytes());
    for pair in &self.pairs {
      hash.update(&pair.to_le_bytes());
    }
    hash.update(&(self.blocks.len() as u64).to_le_bytes());
    for block in &self.blocks {
      hash.update(&(block.len() as u64).to_le_bytes());
      for pair in block {
        hash.update(&pair.to_le_bytes());
      }
    }
    hash.update(&(self.nodes.len() as u64).to_le_bytes());
    for node in &self.nodes {
      match node {
        F128StructuredMatrixNodeV0::Zero => {
          hash.update(&[0]);
        },
        F128StructuredMatrixNodeV0::Block(index) => {
          hash.update(&[1]);
          hash.update(&index.to_le_bytes());
        },
        F128StructuredMatrixNodeV0::Branch { column, bit, low, high } => {
          hash.update(&[2, u8::from(*column)]);
          for x in [bit, low, high] {
            hash.update(&x.to_le_bytes());
          }
        },
      }
    }
    *hash.finalize().as_bytes()
  }
}

#[cfg(test)]
#[path = "structured_matrices_tests.rs"]
mod tests;
