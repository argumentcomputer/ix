//! Shared polynomial nodes: the node pool of an encoded program.
//!
//! A pool is a list of nodes in which every operand names an earlier node,
//! so it is acyclic by construction and is read in one forward pass. A
//! polynomial is the index of its root node. Equal subexpressions are stored
//! once and referenced wherever they occur; [`Polynomial`] trees are expanded
//! from the pool on demand.
//!
//! [`Interner`] builds the canonical pool of a sequence of polynomials: nodes
//! appear in the order a left-to-right post-order walk of the roots, in the
//! order they are interned, first completes them, and no node occurs twice.
//! [`Pool`] reads a pool back and, in canonical mode, rejects any pool the
//! interner would not have produced for the same roots, so a canonical
//! encoding is unique.
use rustc_hash::FxHashMap;

use crate::trace::Polynomial;

/// The most polynomial nodes the polynomials read from one pool may expand
/// to, counting shared nodes once per occurrence. Bounds the memory an
/// encoding can request; the largest compiled program expands to about
/// 7 million nodes.
pub const MAX_EXPANDED_NODES: u64 = 1 << 28;

/// One pool node. Operands are indices of earlier nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Node {
  Const(u64),
  Var(usize),
  Add(usize, usize),
  Sub(usize, usize),
  Mul(usize, usize),
}

impl Node {
  pub fn tag(self) -> u8 {
    match self {
      Self::Const(_) => 0,
      Self::Var(_) => 1,
      Self::Add(..) => 2,
      Self::Sub(..) => 3,
      Self::Mul(..) => 4,
    }
  }

  /// The node with tag `tag` and words `a`, `b`; a leaf's `b` is ignored.
  pub fn from_parts(tag: u8, a: usize, b: usize) -> Result<Self, String> {
    Ok(match tag {
      0 => Self::Const(a as u64),
      1 => Self::Var(a),
      2 => Self::Add(a, b),
      3 => Self::Sub(a, b),
      4 => Self::Mul(a, b),
      other => return Err(format!("invalid polynomial node tag {other}")),
    })
  }

  pub fn operands(self) -> Option<(usize, usize)> {
    match self {
      Self::Add(a, b) | Self::Sub(a, b) | Self::Mul(a, b) => Some((a, b)),
      Self::Const(_) | Self::Var(_) => None,
    }
  }
}

/// Builds the canonical pool of the polynomials interned into it.
#[derive(Debug, Default)]
pub struct Interner {
  nodes: Vec<Node>,
  index: FxHashMap<Node, usize>,
  modulus: Option<u64>,
}

impl Interner {
  /// An interner that rejects constants not below `modulus`.
  pub fn with_modulus(modulus: u64) -> Self {
    Self { modulus: Some(modulus), ..Self::default() }
  }

  pub fn nodes(&self) -> &[Node] {
    &self.nodes
  }

  fn node(&mut self, node: Node) -> usize {
    let next = self.nodes.len();
    *self.index.entry(node).or_insert_with(|| {
      self.nodes.push(node);
      next
    })
  }

  /// The index of `polynomial`'s root, adding the nodes not yet present.
  /// Walks the tree without recursion.
  pub fn intern(&mut self, polynomial: &Polynomial) -> Result<usize, String> {
    let mut pending = vec![(polynomial, false)];
    let mut done: Vec<usize> = Vec::new();
    while let Some((p, expanded)) = pending.pop() {
      let node = match p {
        Polynomial::Const(value) => {
          if let Some(modulus) = self.modulus
            && *value >= modulus
          {
            return Err(format!(
              "noncanonical field element {value} for modulus {modulus}"
            ));
          }
          Node::Const(*value)
        },
        Polynomial::Var(index) => Node::Var(*index),
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
    Ok(done.pop().expect("a polynomial has a root"))
  }
}

/// Tracks the canonical order of a pool as its roots are read.
#[derive(Debug)]
struct Order {
  visited: Vec<bool>,
  /// How many nodes the roots read so far reach.
  reached: usize,
  seen: FxHashMap<Node, usize>,
}

/// A pool read from an encoding, from which polynomials are expanded.
#[derive(Debug)]
pub struct Pool {
  nodes: Vec<Node>,
  /// Each node's expanded size, saturating at `u64::MAX`.
  sizes: Vec<u64>,
  expanded: u64,
  modulus: u64,
  order: Option<Order>,
}

impl Pool {
  /// An empty pool whose constants must be below `modulus`. A canonical
  /// pool must also be exactly what [`Interner`] builds for the roots read
  /// from it ([`Pool::finish`]).
  pub fn new(modulus: u64, canonical: bool) -> Self {
    Self {
      nodes: Vec::new(),
      sizes: Vec::new(),
      expanded: 0,
      modulus,
      order: canonical.then(|| Order {
        visited: Vec::new(),
        reached: 0,
        seen: FxHashMap::default(),
      }),
    }
  }

  pub fn len(&self) -> usize {
    self.nodes.len()
  }

  pub fn is_empty(&self) -> bool {
    self.nodes.is_empty()
  }

  /// Appends `node`, whose operands must name earlier nodes.
  pub fn push(&mut self, node: Node) -> Result<(), String> {
    let index = self.nodes.len();
    let size = match node {
      Node::Const(value) if value >= self.modulus => {
        return Err(format!(
          "noncanonical field element {value} for modulus {}",
          self.modulus
        ));
      },
      Node::Const(_) | Node::Var(_) => 1,
      _ => {
        let (a, b) = node.operands().expect("an operator node");
        if a >= index || b >= index {
          return Err(format!(
            "polynomial node {index} references a later node"
          ));
        }
        self.sizes[a].saturating_add(self.sizes[b]).saturating_add(1)
      },
    };
    if let Some(order) = &mut self.order {
      if order.seen.insert(node, index).is_some() {
        return Err(format!("polynomial node {index} repeats an earlier node"));
      }
      order.visited.push(false);
    }
    self.nodes.push(node);
    self.sizes.push(size);
    Ok(())
  }

  /// The polynomial rooted at node `root`, built without recursion.
  pub fn expand(&mut self, root: usize) -> Result<Polynomial, String> {
    let Some(&size) = self.sizes.get(root) else {
      return Err(format!("polynomial root {root} is not a pool node"));
    };
    self.expanded = self.expanded.saturating_add(size);
    if self.expanded > MAX_EXPANDED_NODES {
      return Err(format!(
        "polynomials expand to more than {MAX_EXPANDED_NODES} nodes"
      ));
    }
    if let Some(order) = &mut self.order {
      reach(&self.nodes, order, root)?;
    }
    Ok(self.build(root))
  }

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
          let children = Box::new([left, right]);
          match node {
            Node::Add(..) => Polynomial::Add(children),
            Node::Sub(..) => Polynomial::Sub(children),
            _ => Polynomial::Mul(children),
          }
        },
      };
      built.push(polynomial);
    }
    built.pop().expect("a polynomial has a root")
  }

  /// Checks, for a canonical pool, that the roots read reached every node.
  pub fn finish(&self) -> Result<(), String> {
    match &self.order {
      Some(order) if order.reached != self.nodes.len() => Err(format!(
        "polynomial node {} is unreferenced or out of order",
        order.reached
      )),
      _ => Ok(()),
    }
  }
}

/// Visits the nodes `root` reaches that no earlier root reached, in
/// post-order, and checks that they are the next nodes of the pool: the
/// order [`Interner`] assigns.
fn reach(nodes: &[Node], order: &mut Order, root: usize) -> Result<(), String> {
  let mut pending = vec![(root, false)];
  while let Some((index, expanded)) = pending.pop() {
    if order.visited[index] {
      continue;
    }
    if !expanded && let Some((a, b)) = nodes[index].operands() {
      pending.push((index, true));
      pending.push((b, false));
      pending.push((a, false));
      continue;
    }
    if index != order.reached {
      return Err(format!(
        "polynomial node {index} is out of canonical order (expected {})",
        order.reached
      ));
    }
    order.visited[index] = true;
    order.reached += 1;
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn var(i: usize) -> Polynomial {
    Polynomial::Var(i)
  }
  fn add(a: Polynomial, b: Polynomial) -> Polynomial {
    Polynomial::Add(Box::new([a, b]))
  }
  fn mul(a: Polynomial, b: Polynomial) -> Polynomial {
    Polynomial::Mul(Box::new([a, b]))
  }

  fn read(nodes: &[Node], roots: &[usize]) -> Result<Vec<Polynomial>, String> {
    let mut pool = Pool::new(7, true);
    for &node in nodes {
      pool.push(node)?;
    }
    let polys =
      roots.iter().map(|&r| pool.expand(r)).collect::<Result<Vec<_>, _>>()?;
    pool.finish()?;
    Ok(polys)
  }

  #[test]
  fn interning_shares_subexpressions() {
    let shared = add(var(0), var(1));
    let polys = [mul(shared.clone(), shared.clone()), shared.clone(), var(1)];
    let mut interner = Interner::with_modulus(7);
    let roots: Vec<usize> =
      polys.iter().map(|p| interner.intern(p).unwrap()).collect();
    assert_eq!(
      interner.nodes(),
      [Node::Var(0), Node::Var(1), Node::Add(0, 1), Node::Mul(2, 2)]
    );
    assert_eq!(roots, [3, 2, 1]);
    assert_eq!(read(interner.nodes(), &roots).unwrap(), polys);
    assert!(Interner::with_modulus(7).intern(&Polynomial::Const(7)).is_err());
  }

  #[test]
  fn canonical_pools_are_unique() {
    use Node::*;
    let ok = [Var(0), Var(1), Add(0, 1)];
    assert!(read(&ok, &[2]).is_ok());
    // Out of post-order, a repeated node, an unreferenced node, a forward
    // reference and a noncanonical constant.
    assert!(read(&[Var(1), Var(0), Add(0, 1)], &[2]).is_ok());
    assert!(read(&[Var(1), Var(0), Add(1, 0)], &[2]).is_err());
    assert!(read(&[Var(0), Var(0), Add(0, 1)], &[2]).is_err());
    assert!(read(&[Var(0), Var(1), Var(2)], &[1]).is_err());
    assert!(read(&ok, &[2, 0]).is_ok());
    assert!(read(&ok, &[0, 2]).is_ok());
    assert!(read(&ok, &[1, 2]).is_err());
    assert!(read(&[Add(1, 2), Var(0), Var(1)], &[0]).is_err());
    assert!(read(&[Const(7)], &[0]).is_err());
    assert!(read(&ok, &[3]).is_err());
    // A non-canonical pool is still read when canonicity is not required.
    let mut pool = Pool::new(7, false);
    for node in [Var(1), Var(0), Add(0, 1), Var(5)] {
      pool.push(node).unwrap();
    }
    assert_eq!(pool.expand(2).unwrap(), add(var(1), var(0)));
    pool.finish().unwrap();
  }

  #[test]
  fn expansion_is_bounded() {
    let mut pool = Pool::new(7, false);
    pool.push(Node::Var(0)).unwrap();
    for i in 0..40 {
      pool.push(Node::Add(i, i)).unwrap();
    }
    assert!(pool.expand(10).is_ok());
    let error = pool.expand(40).unwrap_err();
    assert!(error.contains("expand"), "{error}");
  }
}
