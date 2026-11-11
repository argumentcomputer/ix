use crate::statement::{CanonicalTree, ShardSet, SubjectTree, merge_sorted};
use ix_common::address::Address;
use ixon::shard::ShardInfo;
use ixon::{Axiom, Constant, ConstantInfo, Expr};
use std::sync::Arc;

mod lanes;
mod plan;
mod prepare;
mod scheduler;

fn addr(label: &str) -> Address {
  Address::hash(label.as_bytes())
}

/// A claim context for statements built without an environment.
pub(crate) fn ctx() -> ixon::ClaimContext {
  ixon::ClaimContext {
    spec: ixon::proof::spec_digest(),
    binding: addr("test-binding"),
    axioms: None,
    binding_assumed: false,
    literal_class: false,
  }
}

#[test]
fn sorted_merge_is_a_set_union() {
  let a = addr("a");
  let b = addr("b");
  let c = addr("c");
  let mut left = vec![a.clone(), c.clone()];
  let mut right = vec![b.clone(), c.clone()];
  left.sort_unstable();
  right.sort_unstable();
  let merged = merge_sorted(&left, &right);
  assert_eq!(merged.len(), 3);
  assert!(merged.windows(2).all(|window| window[0] < window[1]));
}

#[test]
fn cached_canonical_path_matches_root() {
  let mut leaves: Vec<Address> =
    (0..17).map(|index| addr(&format!("leaf-{index}"))).collect();
  leaves.sort_unstable();
  let tree = CanonicalTree::from_sorted(leaves.clone()).unwrap().unwrap();
  for leaf in leaves {
    let path = tree.merkle_proof(&leaf).expect("member path");
    assert!(ixon::merkle::verify_merkle_proof(&tree.root, &leaf, &path));
  }
}

#[test]
fn structural_path_uses_cached_child_roots() {
  let mut left_leaves = vec![addr("a"), addr("b")];
  let mut right_leaves = vec![addr("c"), addr("d")];
  left_leaves.sort_unstable();
  right_leaves.sort_unstable();
  let left =
    SubjectTree::canonical(left_leaves.clone(), ShardSet::singleton(0, 2))
      .unwrap();
  let right =
    SubjectTree::canonical(right_leaves.clone(), ShardSet::singleton(1, 2))
      .unwrap();
  let joined = SubjectTree::structural(left, right);
  for leaf in left_leaves.iter().chain(&right_leaves) {
    let owner = usize::from(right_leaves.contains(leaf));
    let path = joined.merkle_proof(leaf, owner).expect("member path");
    assert!(ixon::merkle::verify_merkle_proof(&joined.root, leaf, &path));
  }
}

/// Pinned encodings of the word identity: the identity blob, both outer
/// claims, their serialized claim lists and their aggregate-cache keys.
#[test]
fn word_identity_has_stable_test_vectors() {
  use crate::{
    Identity,
    protocol::{ChildKind, WordIdentity},
  };
  let words = WordIdentity::new(0, b"ixvm-vk", 3, b"aggr-vk", 5, vec![7; 40]);
  assert_eq!(
    hex(&words.allowed),
    "61354e65068e0ba95abf72bf4b240ab30c1017addae4a68a21968671ae1fc39a\
     0300000000000000\
     7a5bd2e82c761a0f6dcd467e1e50246760055d4f83a9612124ae702cbe1ed0f0\
     0500000000000000"
  );
  let claim_digest: [u64; 8] = [
    2220387823, 1153400518, 375520072, 2758343986, 2009813318, 2070912879,
    1014261555, 2685601472,
  ];
  let allowed_digest: [u64; 8] = [
    2334286298, 4229521692, 1751805623, 313404058, 276664792, 774388594,
    1694600667, 448945970,
  ];
  let ixvm: Vec<u64> = [0, 3].into_iter().chain(claim_digest).collect();
  let aggr: Vec<u64> =
    [0, 5].into_iter().chain(allowed_digest).chain(claim_digest).collect();
  for (kind, outer, claims, key) in [
    (
      ChildKind::Ixvm,
      &ixvm,
      "39eb1475a036be33bc87d2d1b7fbdbc9cd3187708bc1080d6a8e8afc7706454e",
      "0a8ef1ce295fdde5d4194290d936666072055d0286aff6f53750ab146319cf74",
    ),
    (
      ChildKind::Aggr,
      &aggr,
      "9a76a486563ff1e22fe365d4b9bbda12623b6128ee198e8d72dd941e9080e240",
      "42dae1b84f1abe701e28567ce8dac2bfb950c3a984c9ce167d7477c25adba4f2",
    ),
  ] {
    assert_eq!(&words.outer_claim(kind, b"claim bytes"), outer);
    assert_eq!(
      blake3::hash(&words.claims_bytes(outer)).to_hex().as_str(),
      claims
    );
    assert_eq!(words.cache_key(outer).hex(), key);
  }
  // The cache-key layout of the earlier aggregate cache, kept unchanged.
  assert_eq!(
    words_cache_key(b"vk", &[1, 2, 3]),
    "86ed059157e2915fe0a83f1afd58f31f7553659ad778669f6b795e1473e7afe0"
  );
}

fn words_cache_key(aggr_key: &[u8], outer: &[u64]) -> String {
  use crate::{Identity, protocol::WordIdentity};
  WordIdentity::new(0, b"", 0, aggr_key, 0, vec![7; 40])
    .cache_key(&outer.to_vec())
    .hex()
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn store_axiom(env: &ixon::Env, typ: Arc<Expr>, refs: Vec<Address>) -> Address {
  let constant = Constant {
    info: ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ }),
    sharing: Vec::new(),
    refs,
    univs: Vec::new(),
  };
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let address = Address::hash(&bytes);
  env.store_const(address.clone(), constant);
  address
}

fn shard(id: u32, block: Address) -> ShardInfo {
  ShardInfo {
    id,
    blocks: vec![block],
    heartbeats: 0,
    own_size: 0,
    foreign_blocks: Vec::new(),
    cross_ingress: 0,
    assumption_root: None,
    measured_peak_bytes: 0,
  }
}
