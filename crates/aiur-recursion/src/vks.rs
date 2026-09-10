//! The recursion verifying-key allowlist: a Merkle tree over the digests of
//! every recursion program a proof may pass through, whose root is a public
//! input of the final proof.
//!
//! SP1's `RecursionVks` is tied to the RISC-V machine's shape catalogue
//! (it sizes its tree by it); this is the same structure over the Aiur
//! pipeline's programs. The tree has a fixed height, [`VK_TREE_HEIGHT`],
//! because every compose program bakes in the length of the Merkle paths it
//! verifies: a taller tree would be a different program.

use std::collections::BTreeMap;

use anyhow::{Result, anyhow};
use slop_algebra::{AbstractField, PrimeField32};
use sp1_hypercube::{
  HashableKey, MachineVerifyingKey, MerkleProof, verify_merkle_proof,
};
use sp1_primitives::{SP1Field, SP1GlobalContext};
use sp1_recursion_circuit::basefold::merkle_tree::MerkleTree;
use sp1_recursion_executor::DIGEST_SIZE;

/// Height of the allowlist tree: room for 256 programs. A machine's shape
/// catalogue is a handful of area classes (see `aiur_hypercube::shape`) and
/// the rest of the pipeline is a program per compose arity, so this is
/// generous; it must not change, since the compose programs depend on it.
pub const VK_TREE_HEIGHT: usize = 8;

pub type Digest = [SP1Field; DIGEST_SIZE];

/// The allowlist of one pipeline.
pub struct AiurVks {
  root: Digest,
  map: BTreeMap<Digest, usize>,
  tree: MerkleTree<SP1GlobalContext>,
}

impl AiurVks {
  /// Commit to `digests` (deduplicated, in lexicographic order, padded to
  /// the tree's capacity with distinct placeholders).
  pub fn new(digests: impl IntoIterator<Item = Digest>) -> Result<Self> {
    let capacity = 1usize << VK_TREE_HEIGHT;
    let digests: Vec<Digest> = digests
      .into_iter()
      .collect::<std::collections::BTreeSet<_>>()
      .into_iter()
      .collect();
    if digests.len() > capacity {
      return Err(anyhow!(
        "{} recursion vks exceed the allowlist capacity {capacity}",
        digests.len()
      ));
    }
    let map: BTreeMap<Digest, usize> =
      digests.iter().copied().enumerate().map(|(i, d)| (d, i)).collect();
    let mut leaves = digests;
    for i in leaves.len()..capacity {
      leaves.push([SP1Field::from_canonical_usize(i); DIGEST_SIZE]);
    }
    let (root, tree) = MerkleTree::<SP1GlobalContext>::commit(leaves);
    assert_eq!(tree.height, VK_TREE_HEIGHT);
    Ok(Self { root, map, tree })
  }

  pub fn root(&self) -> Digest {
    self.root
  }

  pub fn num_keys(&self) -> usize {
    self.map.len()
  }

  pub fn contains(&self, vk: &MachineVerifyingKey<SP1GlobalContext>) -> bool {
    self.map.contains_key(&vk.hash_koalabear())
  }

  /// The allowlist opening of `vk`: its digest and Merkle path.
  pub fn open(
    &self,
    vk: &MachineVerifyingKey<SP1GlobalContext>,
  ) -> Result<(Digest, MerkleProof<SP1GlobalContext>)> {
    let digest = vk.hash_koalabear();
    let index = *self.map.get(&digest).ok_or_else(|| {
      anyhow!(
        "recursion vk {:?} is not in the allowlist: the program proven \
         differs from the one the allowlist was built from",
        digest.map(|x| x.as_canonical_u32())
      )
    })?;
    let (value, proof) = self.tree.open(index);
    verify_merkle_proof(&proof, value, self.root)
      .map_err(|e| anyhow!("allowlist opening does not verify: {e:?}"))?;
    Ok((value, proof))
  }
}
