use super::{
  super::{CELL_DOMAIN, MemoryDepth},
  *,
};
use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  hash::{
    CHUNK_END, CHUNK_START, IV, PARENT, ROOT, pack_bytes, pack_params, pack8,
  },
  ixby::memory_log::PermutationSlots,
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

#[derive(Clone)]
pub struct LeafWires {
  pub address: Wire,
  pub old: [Wire; 2],
  pub new: [Wire; 2],
}
pub struct ParentWires {
  pub enabled: Wire,
  /// Low u64 is the level; high u64 is the node index at that level.
  pub position: Wire,
  pub old_children: [[Wire; 2]; 2],
  pub new_children: [[Wire; 2]; 2],
}
pub struct FrontierWires {
  pub enabled: Wire,
  pub position: Wire,
  pub hash: [Wire; 2],
}
pub struct MultiProofWires {
  pub leaves: Vec<LeafWires>,
  pub parents: Vec<ParentWires>,
  pub frontier: Vec<FrontierWires>,
  pub switches: Vec<Wire>,
}
impl MultiProofWires {
  pub fn inputs(b: &mut impl CircuitEmitter, capacity: MultiCapacity) -> Self {
    let leaves = (0..capacity.leaves)
      .map(|_| LeafWires {
        address: b.input(),
        old: std::array::from_fn(|_| b.input()),
        new: std::array::from_fn(|_| b.input()),
      })
      .collect();
    let frontier = (0..capacity.frontier())
      .map(|_| FrontierWires {
        enabled: b.input(),
        position: b.input(),
        hash: std::array::from_fn(|_| b.input()),
      })
      .collect();
    let parents = (0..capacity.parents)
      .map(|_| ParentWires {
        enabled: b.input(),
        position: b.input(),
        old_children: std::array::from_fn(|_| {
          std::array::from_fn(|_| b.input())
        }),
        new_children: std::array::from_fn(|_| {
          std::array::from_fn(|_| b.input())
        }),
      })
      .collect();
    let switches = (0..capacity.plan().switches()).map(|_| b.input()).collect();
    Self { leaves, parents, frontier, switches }
  }
}
pub struct MultiMemorySlots {
  depth: MemoryDepth,
  gates: [(SlotId, MultiGate); 4],
  compression: Blake3CompressionSlots,
  permutation: PermutationSlots,
  zero: Wire,
  one: Wire,
  root_position: Wire,
  iv: [Wire; 2],
  domain: [Wire; 2],
  leaf_params: Wire,
  parent_params: Wire,
  residual: Wire,
}
impl MultiMemorySlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
  ) -> Result<Self> {
    let compression =
      Blake3CompressionSlots::declare(b, nu, Blake3Backend::LegacyOptionF)?;
    Self::sharing_compression(b, nu, depth, &compression)
  }
  /// Sharing requires the same emitter and row domain.
  pub fn sharing_compression(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    let gates = MultiKind::ALL
      .into_iter()
      .map(|kind| {
        let gate = MultiGate::new(nu, depth, kind)?;
        Ok((b.slot(gate.clone()), gate))
      })
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .ok()
      .unwrap();
    Ok(Self {
      depth,
      gates,
      compression: compression.clone(),
      permutation: PermutationSlots::declare(b, CLAIM_WORDS)?,
      zero: b.fixed_public_input(F128::ZERO),
      one: b.fixed_public_input(F128::ONE),
      root_position: b.fixed_public_input(F128::new(depth.bits() as u64, 0)),
      iv: pack8(&IV).map(|w| b.fixed_public_input(w)),
      domain: [pack_bytes(&CELL_DOMAIN[..16]), pack_bytes(&CELL_DOMAIN[16..])]
        .map(|w| b.fixed_public_input(w)),
      leaf_params: b.fixed_public_input(pack_params(
        0,
        64,
        CHUNK_START | CHUNK_END | ROOT,
      )),
      parent_params: b.fixed_public_input(pack_params(0, 64, PARENT | ROOT)),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn depth(&self) -> MemoryDepth {
    self.depth
  }
  pub fn gates(&self) -> impl Iterator<Item = (SlotId, &MultiGate)> {
    self.gates.iter().map(|(s, g)| (*s, g))
  }
  pub fn compression(&self) -> &Blake3CompressionSlots {
    &self.compression
  }
  pub fn permutation(&self) -> &PermutationSlots {
    &self.permutation
  }
  fn gate(
    &self,
    b: &mut impl CircuitEmitter,
    kind: MultiKind,
    input: &[Wire],
  ) -> Vec<Wire> {
    let mut out = b.gate(self.gates[kind as usize].0, input);
    b.connect(out.pop().unwrap(), self.residual);
    out
  }
  fn hash(
    &self,
    b: &mut impl CircuitEmitter,
    left: [Wire; 2],
    right: [Wire; 2],
    params: Wire,
  ) -> [Wire; 2] {
    let out = self.compression.compress(
      b,
      [self.iv[0], self.iv[1], left[0], left[1], right[0], right[1], params],
    );
    [out[0], out[1]]
  }
  /// Every leaf is the caller's actual old/new cell. Unchanged frontier
  /// hashes are private, but the complete tree must reach the expected roots.
  pub fn check(
    &self,
    b: &mut impl CircuitEmitter,
    [initial_root, final_root]: [[Wire; 2]; 2],
    proof: &MultiProofWires,
  ) {
    let MultiProofWires { leaves, parents, frontier, switches } = proof;
    let capacity = MultiCapacity::new(leaves.len(), parents.len()).unwrap();
    assert_eq!(frontier.len(), capacity.frontier());
    let plan = capacity.plan();
    assert_eq!(switches.len(), plan.switches());
    let mut supplied = Vec::new();
    let mut requested = Vec::new();
    for leaf in leaves {
      let old = self.hash(b, self.domain, leaf.old, self.leaf_params);
      let new = self.hash(b, self.domain, leaf.new, self.leaf_params);
      let input =
        [leaf.address].into_iter().chain(old).chain(new).collect::<Vec<_>>();
      supplied.push(self.gate(b, MultiKind::Leaf, &input));
    }
    for node in frontier {
      supplied.push(self.gate(
        b,
        MultiKind::Frontier,
        &[node.enabled, node.position, node.hash[0], node.hash[1]],
      ));
    }
    for node in parents {
      let old = self.hash(
        b,
        node.old_children[0],
        node.old_children[1],
        self.parent_params,
      );
      let new = self.hash(
        b,
        node.new_children[0],
        node.new_children[1],
        self.parent_params,
      );
      let input = [node.enabled, node.position]
        .into_iter()
        .chain(node.old_children.into_iter().flatten())
        .chain(node.new_children.into_iter().flatten())
        .chain(old)
        .chain(new)
        .collect::<Vec<_>>();
      let out = self.gate(b, MultiKind::Parent, &input);
      supplied.push(out[..CLAIM_WORDS].to_vec());
      requested.push(out[CLAIM_WORDS..2 * CLAIM_WORDS].to_vec());
      requested.push(out[2 * CLAIM_WORDS..].to_vec());
    }
    requested.push(
      [self.one, self.root_position]
        .into_iter()
        .chain(initial_root)
        .chain(final_root)
        .collect(),
    );
    let pad = vec![self.zero; CLAIM_WORDS];
    supplied.resize(plan.lanes(), pad.clone());
    requested.resize(plan.lanes(), pad);
    let actual = self.permutation.permute(b, plan, &supplied, switches);
    for (a, r) in actual.iter().zip(&requested) {
      self.gate(
        b,
        MultiKind::Equal,
        &a.iter().chain(r).copied().collect::<Vec<_>>(),
      );
    }
  }
}
