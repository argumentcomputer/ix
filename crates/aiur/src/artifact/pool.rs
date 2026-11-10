//! The shared pools of a version 2 artifact: polynomial nodes and table rows.
//!
//! A node pool lists distinct polynomial nodes; an operator's operands are
//! earlier nodes, named by their distance back, so the pool is acyclic by
//! construction and is read in one forward pass. A polynomial is the index
//! of its root node. A row pool lists distinct fixed-table rows, and a table
//! is a list of row indices.
//!
//! Writers build canonical pools ([`Interner`], [`RowInterner`]): every
//! entry once, in first-reference order, nodes in the order a left-to-right
//! post-order walk of the roots, taken in writing order, first completes
//! them. Readers ([`Nodes`], [`Rows`]) check safety only: references point
//! back and in range, constants and row values lie below the modulus, and
//! pools and expanded sizes are bounded. They accept non-canonical pools.
use rustc_hash::FxHashMap;

use crate::{
  ixon::{Reader, Writer},
  trace::Polynomial,
};

/// The most entries a pool may hold.
pub(super) const MAX_POOL_ENTRIES: usize = 1 << 28;
/// The most polynomial nodes the polynomials read from one node pool may
/// expand to, counting a shared node once per occurrence. The largest
/// compiled program expands to about 7 million.
pub(super) const MAX_EXPANDED_NODES: u64 = 1 << 28;
/// The most row entries the tables read from one row pool may expand to,
/// counting each row reference as its length and at least 1.
pub(super) const MAX_EXPANDED_ROWS: u64 = 1 << 28;

/// One pool node. Operands are indices of earlier nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Node {
  Const(u64),
  Var(usize),
  Add(usize, usize),
  Sub(usize, usize),
  Mul(usize, usize),
}

/// Builds the canonical node pool of the polynomials interned into it.
#[derive(Debug, Default)]
pub(super) struct Interner {
  nodes: Vec<Node>,
  index: FxHashMap<Node, usize>,
}

impl Interner {
  fn node(&mut self, node: Node) -> usize {
    let next = self.nodes.len();
    *self.index.entry(node).or_insert_with(|| {
      self.nodes.push(node);
      next
    })
  }

  /// The index of `polynomial`'s root, adding the nodes not yet present.
  /// Walks the tree without recursion.
  pub(super) fn intern(&mut self, polynomial: &Polynomial) -> usize {
    let mut pending = vec![(polynomial, false)];
    let mut done: Vec<usize> = Vec::new();
    while let Some((p, expanded)) = pending.pop() {
      let node = match p {
        Polynomial::Const(value) => Node::Const(*value),
        Polynomial::Var(var) => Node::Var(*var),
        Polynomial::Add(xs) | Polynomial::Sub(xs) | Polynomial::Mul(xs) => {
          if !expanded {
            pending.push((p, true));
            pending.push((&xs[1], false));
            pending.push((&xs[0], false));
            continue;
          }
          let (Some(b), Some(a)) = (done.pop(), done.pop()) else {
            unreachable!("both operands precede their node");
          };
          match p {
            Polynomial::Add(_) => Node::Add(a, b),
            Polynomial::Sub(_) => Node::Sub(a, b),
            _ => Node::Mul(a, b),
          }
        },
      };
      done.push(self.node(node));
    }
    done.pop().expect("a polynomial has a root")
  }

  /// `nodes = list(node)`, operands as distances back.
  pub(super) fn put(&self, w: &mut Writer) {
    w.usize(self.nodes.len());
    for (index, &node) in self.nodes.iter().enumerate() {
      match node {
        Node::Const(value) => {
          w.u8(0);
          w.nat(value);
        },
        Node::Var(var) => {
          w.u8(1);
          w.usize(var);
        },
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          w.u8(match node {
            Node::Add(..) => 2,
            Node::Sub(..) => 3,
            _ => 4,
          });
          w.usize(index - a);
          w.usize(index - b);
        },
      }
    }
  }
}

/// A node pool read from an artifact, from which polynomials are expanded.
#[derive(Debug)]
pub(super) struct Nodes {
  nodes: Vec<Node>,
  /// Each node's expanded size, saturating at `u64::MAX`.
  sizes: Vec<u64>,
  expanded: u64,
}

impl Nodes {
  /// Read a pool. Constants must lie below `modulus` when one is given.
  pub(super) fn read(
    r: &mut Reader<'_>,
    modulus: Option<u64>,
  ) -> Result<Self, String> {
    let count = pool_count(r, "polynomial node")?;
    let mut nodes = Vec::with_capacity(count);
    let mut sizes: Vec<u64> = Vec::with_capacity(count);
    for index in 0..count {
      let node = match r.tag("polynomial node", 5)? {
        0 => {
          let value = r.nat()?;
          if let Some(modulus) = modulus
            && value >= modulus
          {
            return Err(r.error(format!(
              "field element {value} is not below the modulus {modulus}"
            )));
          }
          Node::Const(value)
        },
        1 => Node::Var(r.usize()?),
        tag => {
          let a = operand(r, index)?;
          let b = operand(r, index)?;
          match tag {
            2 => Node::Add(a, b),
            3 => Node::Sub(a, b),
            _ => Node::Mul(a, b),
          }
        },
      };
      let size = match node {
        Node::Const(_) | Node::Var(_) => 1,
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          sizes[a].saturating_add(sizes[b]).saturating_add(1)
        },
      };
      nodes.push(node);
      sizes.push(size);
    }
    Ok(Self { nodes, sizes, expanded: 0 })
  }

  /// `nat(root)`: the polynomial rooted at an index of the pool.
  pub(super) fn poly(
    &mut self,
    r: &mut Reader<'_>,
  ) -> Result<Polynomial, String> {
    let root = r.usize()?;
    let Some(&size) = self.sizes.get(root) else {
      return Err(r.error(format!(
        "polynomial root {root} is not one of the {} pool nodes",
        self.nodes.len()
      )));
    };
    self.expanded = self.expanded.saturating_add(size);
    if self.expanded > MAX_EXPANDED_NODES {
      return Err(r.error(format!(
        "polynomials expand to more than {MAX_EXPANDED_NODES} nodes"
      )));
    }
    Ok(self.build(root))
  }

  /// The tree rooted at `root`, built without recursion.
  fn build(&self, root: usize) -> Polynomial {
    let mut pending = vec![(root, false)];
    let mut built: Vec<Polynomial> = Vec::new();
    while let Some((index, expanded)) = pending.pop() {
      let node = self.nodes[index];
      let polynomial = match node {
        Node::Const(value) => Polynomial::Const(value),
        Node::Var(var) => Polynomial::Var(var),
        Node::Add(a, b) | Node::Sub(a, b) | Node::Mul(a, b) => {
          if !expanded {
            pending.push((index, true));
            pending.push((b, false));
            pending.push((a, false));
            continue;
          }
          let (Some(right), Some(left)) = (built.pop(), built.pop()) else {
            unreachable!("both operands precede their node");
          };
          let operands = Box::new([left, right]);
          match node {
            Node::Add(..) => Polynomial::Add(operands),
            Node::Sub(..) => Polynomial::Sub(operands),
            _ => Polynomial::Mul(operands),
          }
        },
      };
      built.push(polynomial);
    }
    built.pop().expect("a polynomial has a root")
  }
}

/// An operand of node `index`: a distance back to an earlier node.
fn operand(r: &mut Reader<'_>, index: usize) -> Result<usize, String> {
  let distance = r.usize()?;
  if distance == 0 || distance > index {
    return Err(r.error(format!(
      "polynomial node {index} refers {distance} nodes back, not to an earlier node"
    )));
  }
  Ok(index - distance)
}

fn pool_count(r: &mut Reader<'_>, what: &str) -> Result<usize, String> {
  let count = r.count()?;
  if count > MAX_POOL_ENTRIES {
    return Err(r.error(format!(
      "{count} {what} entries exceed the pool limit {MAX_POOL_ENTRIES}"
    )));
  }
  Ok(count)
}

/// Builds the canonical row pool of a program's tables.
#[derive(Debug, Default)]
pub(super) struct RowInterner<'a> {
  rows: Vec<&'a [u64]>,
  index: FxHashMap<&'a [u64], usize>,
}

impl<'a> RowInterner<'a> {
  pub(super) fn intern(&mut self, row: &'a [u64]) -> usize {
    let next = self.rows.len();
    *self.index.entry(row).or_insert_with(|| {
      self.rows.push(row);
      next
    })
  }

  /// `rows = list(nats)`.
  pub(super) fn put(&self, w: &mut Writer) {
    w.list(&self.rows, |w, row| w.nats(row));
  }
}

/// A row pool read from an artifact, from which tables are expanded.
#[derive(Debug)]
pub(super) struct Rows {
  rows: Vec<Vec<u64>>,
  expanded: u64,
}

impl Rows {
  /// Read a pool whose values must lie below `modulus`.
  pub(super) fn read(r: &mut Reader<'_>, modulus: u64) -> Result<Self, String> {
    let count = pool_count(r, "table row")?;
    let mut rows = Vec::with_capacity(count);
    for _ in 0..count {
      let row = r.nats()?;
      if let Some(value) = row.iter().find(|&&value| value >= modulus) {
        return Err(r.error(format!(
          "table value {value} is not below the modulus {modulus}"
        )));
      }
      rows.push(row);
    }
    Ok(Self { rows, expanded: 0 })
  }

  /// `nats(row)`: a table's rows as indices into the pool.
  pub(super) fn table(
    &mut self,
    r: &mut Reader<'_>,
  ) -> Result<Vec<Vec<u64>>, String> {
    r.list(|r| {
      let index = r.usize()?;
      let Some(row) = self.rows.get(index) else {
        return Err(r.error(format!(
          "table row {index} is not one of the {} pool rows",
          self.rows.len()
        )));
      };
      let size = u64::try_from(row.len()).unwrap_or(u64::MAX).max(1);
      self.expanded = self.expanded.saturating_add(size);
      if self.expanded > MAX_EXPANDED_ROWS {
        return Err(r.error(format!(
          "tables expand to more than {MAX_EXPANDED_ROWS} row entries"
        )));
      }
      Ok(row.clone())
    })
  }
}
