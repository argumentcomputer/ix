//! Aggregating a `.ixc` catalog's member roots into one statement
//! (`Aggr.catalogPlan`, `ix aggregate --ixc`). A catalog's members may come
//! from different Lean toolchains, so their aggregate roots state their
//! typing under different role bindings:
//!
//! 1. the members are grouped by the literal class of their binding, the
//!    groups in the order of their first member; a member without a class
//!    (an incomplete binding) is a group of its own;
//! 2. each group is folded left to right with the cross-binding structural
//!    pair (`ix_aggr` shape 15) into one `CheckEnv` claim under its class;
//! 3. the groups' claims are folded left to right with the catalog join
//!    (shape 16) into a `Catalog` claim. A catalog of one class has that
//!    class's claim as its root.
//!
//! Which members a catalog has, and each member's claim, are the caller's:
//! `Ix.Cli.CatalogAggregate.catalogMembers` derives them from the verified
//! catalog, and the caller accepts the root only after recomputing it. The
//! circuit checks every fold again.

use std::{
  path::{Path, PathBuf},
  sync::Arc,
};

use ix_common::address::Address;
use ixon::{Claim, merkle::node_hash};

use crate::{
  backend::{Backend, ChildProof, ExtraNode},
  protocol::{CATALOG_SHAPE, CROSS_BINDING_SHAPE, ChildKind},
  statement::CanonicalTree,
  store::{
    claim_wrapper_bytes, decode_wrapper, load_cached_claim,
    persist_cached_claim, persist_claim_wrapper, read_store,
  },
};

/// One catalog member, as the plan sees it (`Aggr.CatalogMember`).
pub struct Member {
  pub label: String,
  /// The unconditional `CheckEnv` claim the member's aggregate root states,
  /// validating the member's binding.
  pub claim: Claim,
  /// The member's role binding section, whose hash the claim's context
  /// names. A cross-binding join reads the literal class from it.
  pub binding_section: Vec<u8>,
  /// The literal class of a complete binding.
  pub literal_class: Option<Address>,
}

/// A node of the plan: a member's root, or a join of two earlier nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
  Member(usize),
  /// Shape 15: two nodes whose bindings have the literal class `class`.
  CrossBinding {
    class: Address,
    left: usize,
    right: usize,
  },
  /// Shape 16: two nodes of different classes, or catalogs.
  CatalogJoin {
    left: usize,
    right: usize,
  },
}

impl Node {
  pub fn children(&self) -> Option<[usize; 2]> {
    match *self {
      Node::Member(_) => None,
      Node::CrossBinding { left, right, .. }
      | Node::CatalogJoin { left, right } => Some([left, right]),
    }
  }
}

/// A node's statement: its claim, and for a `Catalog` claim the canonical
/// tree over its members' claim digests.
pub struct NodeStatement {
  pub claim: Claim,
  pub claim_bytes: Vec<u8>,
  pub members: Option<Arc<CanonicalTree>>,
}

impl NodeStatement {
  fn new(claim: Claim, members: Option<Arc<CanonicalTree>>) -> Self {
    let mut claim_bytes = Vec::new();
    claim.put(&mut claim_bytes);
    Self { claim, claim_bytes, members }
  }

  /// The member statements of one side of a catalog join
  /// (`CatalogTrees.part`): a claim's own digest, or a catalog's members.
  fn part(&self) -> Vec<Address> {
    match &self.members {
      Some(tree) => tree.leaves.to_vec(),
      None => vec![Address::hash(&self.claim_bytes)],
    }
  }
}

/// The plan: its nodes in proving order (the members first, by index),
/// each node's statement, and the root node.
pub struct Plan {
  pub nodes: Vec<Node>,
  pub statements: Vec<NodeStatement>,
  pub root: usize,
}

/// What proving one join takes besides its children's proofs
/// (`CatalogPlan.advice`).
pub struct NodeAdvice {
  pub shape: u8,
  /// Channel 4: the children's claims, then the binding section of each
  /// member child of a cross-binding join.
  pub preimages: Vec<Vec<u8>>,
  /// Channel 5: the members trees of catalog children and of the output.
  pub trees: Vec<Arc<CanonicalTree>>,
}

/// Whether a claim may be a catalog member (`CatalogTrees.isMember`): an
/// unconditional `CheckEnv` claim that validates its binding or names a
/// literal class.
pub fn is_member(claim: &Claim) -> bool {
  matches!(
    claim,
    Claim::CheckEnv { ctx, assumptions: None, .. } if !ctx.binding_assumed
  )
}

/// The cross-binding join of two unconditional `CheckEnv` claims whose
/// bindings have the literal class `class` (`Aggr.crossBindingClaim`).
pub fn cross_binding_claim(
  class: &Address,
  left: &Claim,
  right: &Claim,
) -> Result<Claim, String> {
  let unconditional = |claim: &Claim| match claim {
    Claim::CheckEnv { ctx, root, assumptions: None } => {
      Ok((ctx.clone(), root.clone()))
    },
    _ => Err(format!(
      "catalog plan: not an unconditional CheckEnv claim: {claim:?}"
    )),
  };
  let (lctx, lroot) = unconditional(left)?;
  let (rctx, rroot) = unconditional(right)?;
  if lctx.spec != rctx.spec || lctx.axioms != rctx.axioms {
    return Err(
      "catalog plan: members differ in specification digest or axioms".into(),
    );
  }
  if lctx.binding_assumed || rctx.binding_assumed {
    return Err("catalog plan: a member assumes its binding".into());
  }
  let mut ctx = lctx;
  ctx.binding = class.clone();
  ctx.binding_assumed = false;
  ctx.literal_class = true;
  Ok(Claim::CheckEnv {
    ctx,
    root: node_hash(&lroot, &rroot),
    assumptions: None,
  })
}

/// The catalog join of two statements (`CatalogTrees.join`): the canonical
/// tree over the union of both sides' member statements.
fn catalog_join(
  left: &NodeStatement,
  right: &NodeStatement,
) -> Result<Arc<CanonicalTree>, String> {
  let mut leaves = left.part();
  leaves.extend(right.part());
  leaves.sort_unstable();
  leaves.dedup();
  CanonicalTree::from_sorted(leaves)?
    .ok_or_else(|| "catalog join: no member statements".into())
}

/// Plans the joins of `members`, in their order (`Aggr.catalogPlan`).
pub fn plan(members: &[Member]) -> Result<Plan, String> {
  if members.is_empty() {
    return Err("catalog plan: a catalog has at least one member".into());
  }
  let mut nodes = Vec::new();
  let mut statements = Vec::new();
  let mut classes: Vec<(Option<Address>, Vec<usize>)> = Vec::new();
  for (index, member) in members.iter().enumerate() {
    if !is_member(&member.claim) {
      return Err(format!(
        "catalog plan: member {}'s claim is not an unconditional CheckEnv claim that validates its binding: {:?}",
        member.label, member.claim
      ));
    }
    nodes.push(Node::Member(index));
    statements.push(NodeStatement::new(member.claim.clone(), None));
    let group = member.literal_class.as_ref().and_then(|class| {
      classes.iter().position(|(c, _)| c.as_ref() == Some(class))
    });
    match group {
      Some(group) => classes[group].1.push(index),
      None => classes.push((member.literal_class.clone(), vec![index])),
    }
  }
  let mut tops = Vec::with_capacity(classes.len());
  for (class, indices) in &classes {
    let mut acc = indices[0];
    for &index in &indices[1..] {
      let class = class.as_ref().ok_or(
        "catalog plan: an incomplete binding cannot use a cross-binding join",
      )?;
      let claim = cross_binding_claim(
        class,
        &statements[acc].claim,
        &statements[index].claim,
      )?;
      nodes.push(Node::CrossBinding {
        class: class.clone(),
        left: acc,
        right: index,
      });
      statements.push(NodeStatement::new(claim, None));
      acc = nodes.len() - 1;
    }
    tops.push(acc);
  }
  let mut root = tops[0];
  for &top in &tops[1..] {
    let tree = catalog_join(&statements[root], &statements[top])?;
    let claim = Claim::Catalog { members: tree.root.clone() };
    nodes.push(Node::CatalogJoin { left: root, right: top });
    statements.push(NodeStatement::new(claim, Some(tree)));
    root = nodes.len() - 1;
  }
  Ok(Plan { nodes, statements, root })
}

impl Plan {
  /// The advice of node `index`; `None` for a member.
  pub fn advice(&self, members: &[Member], index: usize) -> Option<NodeAdvice> {
    let claim_bytes = |j: usize| self.statements[j].claim_bytes.clone();
    let binding_section = |j: usize| match self.nodes[j] {
      Node::Member(m) => vec![members[m].binding_section.clone()],
      _ => Vec::new(),
    };
    let members_tree =
      |j: usize| self.statements[j].members.iter().cloned().collect::<Vec<_>>();
    match self.nodes[index] {
      Node::Member(_) => None,
      Node::CrossBinding { left, right, .. } => {
        let mut preimages = vec![claim_bytes(left), claim_bytes(right)];
        preimages.extend(binding_section(left));
        preimages.extend(binding_section(right));
        Some(NodeAdvice {
          shape: CROSS_BINDING_SHAPE,
          preimages,
          trees: Vec::new(),
        })
      },
      Node::CatalogJoin { left, right } => {
        let mut trees = members_tree(left);
        trees.extend(members_tree(right));
        trees.extend(members_tree(index));
        Some(NodeAdvice {
          shape: CATALOG_SHAPE,
          preimages: vec![claim_bytes(left), claim_bytes(right)],
          trees,
        })
      },
    }
  }
}

pub struct Config {
  pub use_cache: bool,
  pub write_outputs: bool,
  /// The content-addressed store; `None` is `~/.ix/store`.
  pub store_dir: Option<PathBuf>,
  /// The aggregate cache; `None` is `AIUR_LANES_CACHE_DIR/aggregate`, or
  /// `~/.ix/cache/aggregate`.
  pub cache_dir: Option<PathBuf>,
}

/// A proven node.
struct Proven<P> {
  proof: P,
  claims_bytes: Vec<u8>,
  address: Address,
}

fn child_proof<'s, P>(
  plan: &'s Plan,
  proven: &'s [Option<Proven<P>>],
  index: usize,
) -> Result<ChildProof<'s, P>, String> {
  let node = proven[index]
    .as_ref()
    .ok_or_else(|| format!("node {index} has no proof"))?;
  Ok(ChildProof {
    kind: ChildKind::Aggr,
    claim_bytes: &plan.statements[index].claim_bytes,
    claims_bytes: &node.claims_bytes,
    proof: &node.proof,
  })
}

/// The member root proofs `root_hexes` name, one per member, each bound to
/// its member by claim and verified natively.
fn member_roots<B: Backend>(
  backend: &B,
  store_dir: &Path,
  members: &[Member],
  root_hexes: &[String],
) -> Result<Vec<Proven<B::Proof>>, String> {
  let mut roots = Vec::with_capacity(root_hexes.len());
  for hex in root_hexes {
    let address = Address::from_hex(hex).ok_or_else(|| {
      format!("aggregate proof: expected a 64-character hex address, got {hex}")
    })?;
    let bytes = read_store(store_dir, &address)?;
    if Address::hash(&bytes) != address {
      return Err(format!("{hex}: the store object has another digest"));
    }
    let wrapper = decode_wrapper(&bytes).map_err(|e| format!("{hex}: {e}"))?;
    roots.push((address, wrapper));
  }
  for (address, wrapper) in &roots {
    if !members.iter().any(|m| m.claim == wrapper.claim) {
      return Err(format!(
        "aggregate root {} states no member's claim: {:?}",
        address.hex(),
        wrapper.claim
      ));
    }
  }
  members
    .iter()
    .map(|member| {
      let mut matching =
        roots.iter().filter(|(_, wrapper)| wrapper.claim == member.claim);
      let (address, wrapper) = match (matching.next(), matching.next()) {
        (Some(root), None) => root,
        (None, _) => {
          return Err(format!(
            "no aggregate root states member {}'s claim {:?}",
            member.label, member.claim
          ));
        },
        (Some(_), Some(_)) => {
          return Err(format!(
            "several aggregate roots state member {}'s claim",
            member.label
          ));
        },
      };
      let proof = backend.decode_proof(&wrapper.proof).map_err(|e| {
        format!("member root {} does not decode: {e}", address.hex())
      })?;
      let mut claim_bytes = Vec::new();
      member.claim.put(&mut claim_bytes);
      let outer = backend.outer_claim(ChildKind::Aggr, &claim_bytes);
      backend.verify(ChildKind::Aggr, &outer, &proof).map_err(|e| {
        format!("member root {} does not verify: {e}", address.hex())
      })?;
      Ok(Proven {
        proof,
        claims_bytes: backend.claims_bytes(&outer),
        address: address.clone(),
      })
    })
    .collect()
}

/// `ix aggregate --ixc`: proves every join of `members`' plan on one lane,
/// bottom up, from the member roots `root_hexes`, reusing and publishing
/// joins through the aggregate cache, and returns the address of the
/// root's proof wrapper. With `expected_root`, the plan's root claim must
/// serialize to it before anything is proven. A catalog of one member has
/// that member's root as its root.
pub fn run<B: Backend>(
  cfg: &Config,
  backend: &B,
  members: &[Member],
  root_hexes: &[String],
  expected_root: Option<&[u8]>,
) -> Result<String, String> {
  let plan = plan(members)?;
  let root_bytes = &plan.statements[plan.root].claim_bytes;
  if expected_root.is_some_and(|expected| expected != root_bytes.as_slice()) {
    return Err(
      "the controller's catalog plan reaches another root claim than the caller's"
        .into(),
    );
  }
  let home = || {
    std::env::var_os("HOME")
      .map(PathBuf::from)
      .ok_or_else(|| "no HOME environment variable".to_string())
  };
  let store_dir = match &cfg.store_dir {
    Some(dir) => dir.clone(),
    None => home()?.join(".ix").join("store"),
  };
  let cache_path = match &cfg.cache_dir {
    Some(dir) => dir.clone(),
    None => match std::env::var_os("AIUR_LANES_CACHE_DIR") {
      Some(dir) => PathBuf::from(dir).join("aggregate"),
      None => home()?.join(".ix").join("cache").join("aggregate"),
    },
  };
  let cache_dir = cfg.use_cache.then_some(cache_path.as_path());
  let mut proven: Vec<Option<Proven<B::Proof>>> =
    plan.nodes.iter().map(|_| None).collect();
  for (index, root) in member_roots(backend, &store_dir, members, root_hexes)?
    .into_iter()
    .enumerate()
  {
    proven[index] = Some(root);
  }
  let lanes = backend.lanes(1)?;
  let lane = &lanes[0];
  for index in 0..plan.nodes.len() {
    let Some(advice) = plan.advice(members, index) else { continue };
    let [left, right] =
      plan.nodes[index].children().ok_or("a catalog join has no children")?;
    let output = &plan.statements[index];
    let outer = backend.outer_claim(ChildKind::Aggr, &output.claim_bytes);
    let key = backend.cache_key(&outer);
    let label = format!("catalog node {index} (shape {})", advice.shape);
    let cached = load_cached_claim(
      &store_dir,
      cache_dir,
      &label,
      &key,
      &output.claim,
      &outer,
      |bytes| backend.decode_proof(bytes),
      |outer, proof| backend.verify(ChildKind::Aggr, outer, proof),
    );
    let node = match cached {
      Some((proof, address)) => {
        Proven { proof, claims_bytes: backend.claims_bytes(&outer), address }
      },
      None => {
        let child = |j: usize| child_proof(&plan, &proven, j);
        let trees: Vec<&CanonicalTree> =
          advice.trees.iter().map(Arc::as_ref).collect();
        let started = std::time::Instant::now();
        let (_pool, reservation) = crate::aggregate::reservation()?;
        let binding = backend.bind(&reservation);
        let proof = backend.prove_extra(
          lane,
          ExtraNode::Catalog {
            shape: advice.shape,
            children: [child(left)?, child(right)?],
            output: &output.claim_bytes,
            preimages: &advice.preimages,
            trees: &trees,
          },
          &reservation,
        )?;
        drop(binding);
        backend
          .verify(ChildKind::Aggr, &outer, &proof)
          .map_err(|e| format!("{label}: the proof fails: {e}"))?;
        let address = match persist_cached_claim(
          &store_dir,
          cache_dir,
          cfg.write_outputs,
          &label,
          &key,
          &output.claim,
          &output.claim_bytes,
          || backend.encode_proof(&proof),
        )? {
          Some(address) => address,
          None if cfg.write_outputs => persist_claim_wrapper(
            &store_dir,
            &output.claim,
            &output.claim_bytes,
            backend.encode_proof(&proof),
          )?,
          None => Address::hash(&claim_wrapper_bytes(
            &output.claim,
            backend.encode_proof(&proof),
          )?),
        };
        eprintln!(
          "[aggregate] {label} proved in {} ms: {}",
          started.elapsed().as_millis(),
          address.hex()
        );
        Proven { proof, claims_bytes: backend.claims_bytes(&outer), address }
      },
    };
    proven[index] = Some(node);
  }
  let root = proven[plan.root].as_ref().ok_or("the root has no proof")?;
  Ok(root.address.hex())
}

#[cfg(test)]
mod tests {
  use super::*;
  use ixon::ClaimContext;

  fn address(label: &str) -> Address {
    Address::hash(label.as_bytes())
  }

  fn member(label: &str, binding: &str, class: Option<&str>) -> Member {
    let ctx = ClaimContext {
      spec: address("spec"),
      binding: address(binding),
      axioms: None,
      binding_assumed: false,
      literal_class: false,
    };
    Member {
      label: label.into(),
      claim: Claim::CheckEnv { ctx, root: address(label), assumptions: None },
      binding_section: binding.as_bytes().to_vec(),
      literal_class: class.map(address),
    }
  }

  /// Members of one class fold first, in order, and the classes then join
  /// into a catalog over every class's claim.
  #[test]
  fn classes_fold_then_join() {
    let members = [
      member("a", "b1", Some("k1")),
      member("b", "b2", Some("k2")),
      member("c", "b3", Some("k1")),
      member("d", "b4", None),
    ];
    let plan = plan(&members).unwrap();
    assert_eq!(
      plan.nodes[4..],
      [
        Node::CrossBinding { class: address("k1"), left: 0, right: 2 },
        Node::CatalogJoin { left: 4, right: 1 },
        Node::CatalogJoin { left: 5, right: 3 },
      ]
    );
    assert_eq!(plan.root, 6);
    let Claim::CheckEnv { ctx, root, assumptions: None } =
      &plan.statements[4].claim
    else {
      panic!("a cross-binding join states a CheckEnv claim");
    };
    assert!(ctx.literal_class && !ctx.binding_assumed);
    assert_eq!(ctx.binding, address("k1"));
    assert_eq!(*root, node_hash(&address("a"), &address("c")));
    let members_tree = plan.statements[6].members.as_ref().unwrap();
    let mut expected: Vec<Address> = [4, 1, 3]
      .iter()
      .map(|&j| Address::hash(&plan.statements[j].claim_bytes))
      .collect();
    expected.sort_unstable();
    assert_eq!(members_tree.leaves.to_vec(), expected);
    let cross = plan.advice(&members, 4).unwrap();
    assert_eq!(cross.shape, CROSS_BINDING_SHAPE);
    assert_eq!(cross.preimages.len(), 4);
    assert_eq!(cross.preimages[2], b"b1");
    let join = plan.advice(&members, 6).unwrap();
    assert_eq!(join.shape, CATALOG_SHAPE);
    assert_eq!(join.trees.len(), 2);
    assert!(plan.advice(&members, 0).is_none());
  }

  #[test]
  fn assumed_members_are_rejected() {
    let mut m = member("a", "b1", Some("k1"));
    if let Claim::CheckEnv { ctx, .. } = &mut m.claim {
      ctx.binding_assumed = true;
    }
    assert!(plan(&[m]).is_err());
  }
}
