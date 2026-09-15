//! Exact GF(2) cofactor spans for a forest of shared-weight Boolean matrices.
//!
//! Leaves are vectors over the low row/column PAIRS, not field encodings of
//! block IDs. Elimination on those vectors and on pairs of child decoders is
//! elimination on exact polynomial functions. It never samples a field point.
//! At evaluation time the leaf vectors act on constrained low pair products;
//! each high layer uses `low + coordinate * slope`, preserving every original
//! matrix bilinear form and all ordered outputs. Spanning rows may be retained
//! redundantly to bound decoder density; minimum algebraic rank is not a goal.

use crate::{
  F128FixedTableBasisCensusV0, F128FixedTableBasisError as Error,
  F128FixedTableBasisLimitsV0, F128StaticMatrixIdV1, F128StructuredMatricesV0,
  F128StructuredMatrixNodeV0 as Node,
  fixed_table_basis::{Budget, trim},
};
use std::collections::{BTreeMap, BTreeSet};

/// One explicitly evaluated generator, which need not be independent of
/// other generators in its layer. Terms reference the next layer's width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredMatrixSpanRowV0 {
  low: Vec<u32>,
  slope: Vec<u32>,
}
impl F128StructuredMatrixSpanRowV0 {
  pub fn low(&self) -> &[u32] {
    &self.low
  }
  pub fn slope(&self) -> &[u32] {
    &self.slope
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredMatrixSpanLayerV0 {
  coordinate: u32,
  child_width: u32,
  rows: Vec<F128StructuredMatrixSpanRowV0>,
}
impl F128StructuredMatrixSpanLayerV0 {
  pub fn coordinate(&self) -> u32 {
    self.coordinate
  }
  pub fn child_width(&self) -> u32 {
    self.child_width
  }
  pub fn rows(&self) -> &[F128StructuredMatrixSpanRowV0] {
    &self.rows
  }
}

/// An immutable setup-only program. This does not approve the source registry,
/// bind point/value wires, or replace any part of a complete verifier by itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StructuredMatrixSpanV0 {
  source_digest: [u8; 32],
  low_variables: u32,
  high_variables: u32,
  pairs: Vec<u16>,
  leaf_generators: Vec<Vec<u16>>,
  // Earliest global coordinate first; evaluate these layers in reverse.
  layers: Vec<F128StructuredMatrixSpanLayerV0>,
  outputs: Vec<(F128StaticMatrixIdV1, Vec<u32>)>,
  census: F128FixedTableBasisCensusV0,
}

impl F128StructuredMatrixSpanV0 {
  /// The sealed source compiler fixes a common MSB-first interleaved high
  /// order. Smaller matrices omit the leading coordinates, not low inputs.
  /// All limits apply cumulatively across the ENTIRE forest and every leaf.
  pub fn compile(
    source: &F128StructuredMatricesV0,
    limits: F128FixedTableBasisLimitsV0,
  ) -> Result<Self, Error> {
    let mut budget = Budget { limits, used: Default::default() };
    let mut roots = BTreeSet::new();
    for &(_, root) in source.outputs() {
      if !roots.contains(&root) {
        budget.state()?;
        roots.insert(root);
      }
    }
    let mut states = vec![roots.into_iter().collect::<Vec<_>>()];
    let high = source.high_variables();
    let order =
      (0..high).rev().flat_map(|bit| [bit, high + bit]).collect::<Vec<_>>();
    for &coordinate in &order {
      let mut next = BTreeSet::new();
      for &id in states.last().expect("root layer") {
        for child in cofactors(source, id, coordinate) {
          if !next.contains(&child) {
            budget.state()?;
            next.insert(child);
          }
        }
      }
      states.push(next.into_iter().collect::<Vec<_>>());
    }
    let leaves = states.last().expect("leaf layer");
    // Unit low-pair functions avoid dense reconstruction of the source blocks.
    // These are constrained products at evaluation time, not witness hints.
    let pairs = source.pairs().to_vec();
    budget.coefficients(pairs.len() as u64)?;
    let leaf_generators =
      pairs.iter().map(|&pair| vec![pair]).collect::<Vec<_>>();
    let words = pairs.len().div_ceil(64);
    let mut decoders = Vec::with_capacity(leaves.len());
    for &id in leaves {
      let mut row = budget.words(words)?;
      match source.nodes()[id as usize] {
        Node::Zero => {},
        Node::Block(block) => {
          for &pair in &source.blocks()[block as usize] {
            budget.work(1)?;
            let pair = pairs.binary_search(&pair).expect("source pair");
            row[pair / 64] ^= 1 << (pair % 64);
          }
        },
        Node::Branch { .. } => return Err(Error::UnsupportedEncoding),
      }
      decoders.push(row);
    }
    let mut child_width = leaf_generators.len();
    trim(&mut decoders, child_width);
    let mut layers = Vec::with_capacity(order.len());
    for level in (0..order.len()).rev() {
      let coordinate = order[level];
      let children = &states[level + 1];
      let words = child_width.div_ceil(64);
      let mut source_rows = Vec::with_capacity(states[level].len());
      for &id in &states[level] {
        let mut row = budget.words(2 * words)?;
        budget.work((2 * words) as u64)?;
        for (side, child) in
          cofactors(source, id, coordinate).into_iter().enumerate()
        {
          let index = children.binary_search(&child).expect("reachable child");
          row[side * words..(side + 1) * words]
            .copy_from_slice(&decoders[index]);
        }
        source_rows.push(row);
      }
      let (eliminate, mut next_decoders) = eliminate_sparse_first(
        source_rows,
        states[level].len(),
        Some(words),
        &mut budget,
      )?;
      let mut rows = Vec::with_capacity(eliminate.rows.len());
      for pair in &eliminate.rows {
        let low = budget.terms(pair[..words].iter().copied(), child_width)?;
        budget.work(words as u64)?;
        let slope = budget.terms(
          pair[..words].iter().zip(&pair[words..]).map(|(&a, &b)| a ^ b),
          child_width,
        )?;
        rows.push(F128StructuredMatrixSpanRowV0 { low, slope });
      }
      layers.push(F128StructuredMatrixSpanLayerV0 {
        coordinate,
        child_width: u32::try_from(child_width)
          .map_err(|_| Error::IndexOverflow)?,
        rows,
      });
      child_width = eliminate.rows.len();
      trim(&mut next_decoders, child_width);
      decoders = next_decoders;
    }
    let outputs = source
      .outputs()
      .iter()
      .map(|&(id, root)| {
        let index = states[0].binary_search(&root).expect("source output");
        Ok((id, budget.terms(decoders[index].iter().copied(), child_width)?))
      })
      .collect::<Result<Vec<_>, Error>>()?;
    layers.reverse();
    Ok(Self {
      source_digest: source.digest(),
      low_variables: source.low_variables(),
      high_variables: high,
      pairs,
      leaf_generators,
      layers,
      outputs,
      census: budget.used,
    })
  }

  pub fn source_digest(&self) -> [u8; 32] {
    self.source_digest
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
  pub fn leaf_generators(&self) -> &[Vec<u16>] {
    &self.leaf_generators
  }
  pub fn layers(&self) -> &[F128StructuredMatrixSpanLayerV0] {
    &self.layers
  }
  pub fn outputs(&self) -> &[(F128StaticMatrixIdV1, Vec<u32>)] {
    &self.outputs
  }
  pub fn census(&self) -> F128FixedTableBasisCensusV0 {
    self.census
  }

  pub fn digest(&self) -> [u8; 32] {
    fn terms(
      hash: &mut blake3::Hasher,
      terms: impl ExactSizeIterator<Item = u32>,
    ) {
      hash.update(&(terms.len() as u64).to_le_bytes());
      for term in terms {
        hash.update(&term.to_le_bytes());
      }
    }
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/structured-matrix-cofactor-span/v0\0");
    hash.update(&self.source_digest);
    hash.update(&self.low_variables.to_le_bytes());
    hash.update(&self.high_variables.to_le_bytes());
    terms(&mut hash, self.pairs.iter().copied().map(u32::from));
    hash.update(&(self.leaf_generators.len() as u64).to_le_bytes());
    for row in &self.leaf_generators {
      terms(&mut hash, row.iter().copied().map(u32::from));
    }
    hash.update(&(self.layers.len() as u64).to_le_bytes());
    for layer in &self.layers {
      hash.update(&layer.coordinate().to_le_bytes());
      hash.update(&layer.child_width().to_le_bytes());
      hash.update(&(layer.rows().len() as u64).to_le_bytes());
      for row in layer.rows() {
        terms(&mut hash, row.low().iter().copied());
        terms(&mut hash, row.slope().iter().copied());
      }
    }
    hash.update(&(self.outputs.len() as u64).to_le_bytes());
    for (id, output) in &self.outputs {
      hash.update(&id.registry_digest);
      hash.update(&id.table.to_le_bytes());
      hash.update(&[match id.side {
        crate::F128MatrixSideV1::A => 0,
        crate::F128MatrixSideV1::B => 1,
      }]);
      hash.update(&id.variables.to_le_bytes());
      terms(&mut hash, output.iter().copied());
    }
    *hash.finalize().as_bytes()
  }
}

/// Choose exact sparse source rows first to limit elimination fill-in.
/// Stable source indices break all ties. Decoders are returned in SOURCE
/// order, not pivot order; no point assignment influences this choice.
fn eliminate_sparse_first(
  rows: Vec<Vec<u64>>,
  max_width: usize,
  pair_words: Option<usize>,
  budget: &mut Budget,
) -> Result<(OriginalRowSpan, Vec<Vec<u64>>), Error> {
  let words = rows.first().map_or(0, Vec::len);
  let mut decoders = vec![Vec::new(); rows.len()];
  let mut ranked = Vec::with_capacity(rows.len());
  for (index, row) in rows.into_iter().enumerate() {
    budget.work((words + pair_words.unwrap_or(0)) as u64)?;
    let (has_slope, weight) = if let Some(half) = pair_words {
      let low = row[..half]
        .iter()
        .map(|word| u64::from(word.count_ones()))
        .sum::<u64>();
      let slope = row[..half]
        .iter()
        .zip(&row[half..])
        .map(|(a, b)| u64::from((a ^ b).count_ones()))
        .sum::<u64>();
      (slope != 0, low + slope)
    } else {
      (false, row.iter().map(|word| u64::from(word.count_ones())).sum::<u64>())
    };
    ranked.push((has_slope, weight, index, row));
  }
  ranked.sort_unstable_by_key(|(slope, weight, index, _)| {
    (*slope, *weight, *index)
  });
  let mut eliminate = OriginalRowSpan::new(words, max_width);
  for (_, _, index, row) in ranked {
    decoders[index] = eliminate.insert(row, budget)?;
  }
  Ok((eliminate, decoders))
}

/// Echelon residuals are only an independence test. The retained evaluation
/// span uses ORIGINAL rows. Each residual carries its exact decoder in that
/// span, so dependent source rows still receive complete checked decoders.
/// A dense dependent decoder instead gets an explicitly evaluated original
/// row. This is an overcomplete span, never an unchecked value shortcut.
struct OriginalRowSpan {
  words: usize,
  decoder_words: usize,
  rows: Vec<Vec<u64>>,
  residuals: Vec<Vec<u64>>,
  residual_decoders: Vec<Vec<u64>>,
  pivots: BTreeMap<usize, usize>,
}

impl OriginalRowSpan {
  fn new(words: usize, max_width: usize) -> Self {
    Self {
      words,
      decoder_words: max_width.div_ceil(64),
      rows: Vec::new(),
      residuals: Vec::new(),
      residual_decoders: Vec::new(),
      pivots: BTreeMap::new(),
    }
  }

  fn insert(
    &mut self,
    original: Vec<u64>,
    budget: &mut Budget,
  ) -> Result<Vec<u64>, Error> {
    let mut row = budget.words(self.words)?;
    budget.work(self.words as u64)?;
    row.copy_from_slice(&original);
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
      let Some(pivot) = pivot else {
        budget.work(self.decoder_words as u64)?;
        let terms = decoder.iter().map(|word| word.count_ones()).sum::<u32>();
        if terms > 8 {
          let index = self.rows.len();
          let mut direct = budget.words(self.decoder_words)?;
          budget.work(1)?;
          direct[index / 64] = 1 << (index % 64);
          self.rows.push(original);
          return Ok(direct);
        }
        return Ok(decoder);
      };
      if let Some(&index) = self.pivots.get(&pivot) {
        budget.work((self.words + self.decoder_words) as u64)?;
        for (dst, &src) in row.iter_mut().zip(&self.residuals[index]) {
          *dst ^= src;
        }
        for (dst, &src) in
          decoder.iter_mut().zip(&self.residual_decoders[index])
        {
          *dst ^= src;
        }
      } else {
        let index = self.rows.len();
        let mut source_decoder = budget.words(self.decoder_words)?;
        budget.work(2)?;
        source_decoder[index / 64] = 1 << (index % 64);
        decoder[index / 64] ^= 1 << (index % 64);
        self.pivots.insert(pivot, self.residuals.len());
        self.rows.push(original);
        self.residuals.push(row);
        self.residual_decoders.push(decoder);
        return Ok(source_decoder);
      }
    }
  }
}

fn cofactors(
  source: &F128StructuredMatricesV0,
  id: u32,
  coordinate: u32,
) -> [u32; 2] {
  match source.nodes()[id as usize] {
    Node::Branch { column, bit, low, high }
      if bit + if column { source.high_variables() } else { 0 }
        == coordinate =>
    {
      [low, high]
    },
    _ => [id, id],
  }
}

#[cfg(test)]
#[path = "structured_matrix_span_tests.rs"]
mod tests;
