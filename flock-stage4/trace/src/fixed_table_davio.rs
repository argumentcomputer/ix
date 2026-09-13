//! Exact cofactor-XOR rewriting of the setup-owned Shannon diagram. The
//! bounded working BDD is never a witness; its canonical XOR operation is
//! evaluated structurally and can only add fixed table-program nodes.

use super::{
  Compiler, F128FixedTableError as Error, F128FixedTableNodeV0 as Node,
  F128FixedTableV0,
};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128FixedTableDavioLimitsV0 {
  /// Maximum retained original and intermediate Shannon nodes.
  pub working_nodes: u32,
  /// Maximum emitted Davio nodes.
  pub nodes: u32,
  /// Hard bound on recursive XOR calls, including cache hits.
  pub xor_calls: u64,
}

impl F128FixedTableV0 {
  /// Preserve the exact multilinear polynomial while exposing cofactor
  /// cancellation before field arithmetization. For example, equality on a
  /// Boolean bit pair is `1 + row + column` in characteristic two.
  /// This accepts only the Shannon encoding returned by `compile`.
  pub fn positive_davio(
    &self,
    limits: F128FixedTableDavioLimitsV0,
  ) -> Result<Self, Error> {
    self.rewrite_davio(limits, false)
  }

  /// Pick the cofactor with smaller deterministic unfolded-node weight as
  /// the base at each decision. A zero base always wins. This keeps sparse
  /// prefixes sparse; it is a bounded heuristic, not a promise of a smaller
  /// circuit. The chosen polarity is part of the emitted program's identity.
  pub fn mixed_davio(
    &self,
    limits: F128FixedTableDavioLimitsV0,
  ) -> Result<Self, Error> {
    self.rewrite_davio(limits, true)
  }

  fn rewrite_davio(
    &self,
    limits: F128FixedTableDavioLimitsV0,
    mixed: bool,
  ) -> Result<Self, Error> {
    if self.nodes.len() as u64 > u64::from(limits.working_nodes) {
      return Err(Error::NodeLimit);
    }
    if self.nodes.iter().any(|node| matches!(node, Node::Davio { .. })) {
      return Err(Error::UnsupportedEncoding);
    }
    let mut levels = vec![0; self.order.len()];
    for (level, &coordinate) in self.order.iter().enumerate() {
      levels[coordinate as usize] = level;
    }
    let source = Compiler {
      order: &self.order,
      nodes: self.nodes.clone(),
      interned: self
        .nodes
        .iter()
        .copied()
        .enumerate()
        .map(|(i, node)| {
          Ok((node, u32::try_from(i).map_err(|_| Error::NodeLimit)?))
        })
        .collect::<Result<_, Error>>()?,
      limit: limits.working_nodes,
    };
    let target = Compiler {
      order: &self.order,
      nodes: Vec::new(),
      interned: HashMap::new(),
      limit: limits.nodes,
    };
    let mut rewrite = Rewrite {
      source,
      target,
      levels,
      xor_cache: HashMap::new(),
      converted: HashMap::new(),
      remaining_calls: limits.xor_calls,
      mixed,
      weights: HashMap::new(),
    };
    let root = rewrite.convert(self.root)?;
    Ok(Self {
      order: self.order.clone(),
      nodes: rewrite.target.nodes,
      root,
      nonzero_entries: self.nonzero_entries,
    })
  }
}

struct Rewrite<'a> {
  source: Compiler<'a>,
  target: Compiler<'a>,
  levels: Vec<usize>,
  xor_cache: HashMap<(u32, u32), u32>,
  converted: HashMap<u32, u32>,
  remaining_calls: u64,
  mixed: bool,
  weights: HashMap<u32, u64>,
}

impl Rewrite<'_> {
  fn weight(&mut self, id: u32) -> u64 {
    if let Some(&weight) = self.weights.get(&id) {
      return weight;
    }
    let weight = match self.source.nodes[id as usize] {
      Node::Constant(value) => u64::from(value != [0; 16]),
      Node::Branch { low, high, .. } => {
        self.weight(low).saturating_add(self.weight(high)).saturating_add(1)
      },
      Node::Davio { .. } => unreachable!("source is a Shannon diagram"),
    };
    self.weights.insert(id, weight);
    weight
  }
  fn zero(&mut self) -> Result<u32, Error> {
    self.source.intern(Node::Constant([0; 16]))
  }

  fn level(&self, id: u32) -> usize {
    match self.source.nodes[id as usize] {
      Node::Constant(_) => self.levels.len(),
      Node::Branch { coordinate, .. } => self.levels[coordinate as usize],
      Node::Davio { .. } => unreachable!("source is a Shannon diagram"),
    }
  }

  fn cofactors(&self, id: u32, level: usize) -> (u32, u32) {
    if self.level(id) == level {
      let Node::Branch { low, high, .. } = self.source.nodes[id as usize]
      else {
        unreachable!("a constant cannot be the next XOR coordinate");
      };
      (low, high)
    } else {
      (id, id)
    }
  }

  fn xor(&mut self, left: u32, right: u32) -> Result<u32, Error> {
    self.remaining_calls =
      self.remaining_calls.checked_sub(1).ok_or(Error::RewriteLimit)?;
    if left == right {
      return self.zero();
    }
    let pair = (left.min(right), left.max(right));
    if let Some(&id) = self.xor_cache.get(&pair) {
      return Ok(id);
    }
    let l = self.source.nodes[left as usize];
    let r = self.source.nodes[right as usize];
    let zero = Node::Constant([0; 16]);
    if l == zero {
      return Ok(right);
    }
    if r == zero {
      return Ok(left);
    }
    let result = if let (Node::Constant(a), Node::Constant(b)) = (l, r) {
      self
        .source
        .intern(Node::Constant(core::array::from_fn(|i| a[i] ^ b[i])))?
    } else {
      let level = self.level(left).min(self.level(right));
      let (l0, l1) = self.cofactors(left, level);
      let (r0, r1) = self.cofactors(right, level);
      let low = self.xor(l0, r0)?;
      let high = self.xor(l1, r1)?;
      if low == high {
        low
      } else {
        self.source.intern(Node::Branch {
          coordinate: self.source.order[level],
          low,
          high,
        })?
      }
    };
    self.xor_cache.insert(pair, result);
    Ok(result)
  }

  fn convert(&mut self, id: u32) -> Result<u32, Error> {
    if let Some(&converted) = self.converted.get(&id) {
      return Ok(converted);
    }
    let converted = match self.source.nodes[id as usize] {
      Node::Constant(value) => self.target.intern(Node::Constant(value))?,
      Node::Branch { coordinate, low, high } => {
        let delta = self.xor(low, high)?;
        let complement = self.mixed && self.weight(high) < self.weight(low);
        let base = self.convert(if complement { high } else { low })?;
        if self.source.nodes[delta as usize] == Node::Constant([0; 16]) {
          base
        } else {
          let slope = self.convert(delta)?;
          self.target.intern(Node::Davio {
            coordinate,
            base,
            slope,
            complement,
          })?
        }
      },
      Node::Davio { .. } => unreachable!("source is a Shannon diagram"),
    };
    self.converted.insert(id, converted);
    Ok(converted)
  }
}
