//! The `ix_aggr` advice of the formal recursive verifier as ordered byte
//! streams (`Ix.Aggr.Protocol` channels):
//!
//! | Channel | Key | Payload |
//! |---|---|---|
//! | 0 | child slot | the child's raw proof |
//! | 1 | child kind | the verifying key of that kind |
//! | 2 | child slot, or 2 | the child's serialized claims, or the output claim |
//! | 3 | 0 | the identity blob |
//! | 4 | packed digest | a claim preimage |
//! | 5 | tree root | a serialized canonical tree |
//! | 6 | 0, or a candidate | the shape byte, or a structural path |
//!
//! Streams keep the order in which they are first added, and adding a key
//! again replaces its payload in place: the advice layout, and therefore the
//! trace and the proof, depend on that order. A witness is checked again by
//! the circuit; nothing here is trusted.

use std::borrow::Cow;

use ix_common::address::Address;
use rustc_hash::FxHashMap;

use crate::{
  advice::{advice_trees, path_payload},
  protocol::{ChildKind, discharge_shape_code},
  statement::{CanonicalTree, Statement, merge_optional_sets},
};

/// One stream: channel, key words and payload.
pub type Entry<'a> = (u64, Vec<u64>, Cow<'a, [u8]>);

#[derive(Default)]
pub struct Streams<'a> {
  entries: Vec<Entry<'a>>,
  position: FxHashMap<(u64, Vec<u64>), usize>,
}

/// A 32-byte address as a key: one word per byte.
pub fn address_key(address: &Address) -> Vec<u64> {
  address.as_bytes().iter().map(|&byte| u64::from(byte)).collect()
}

/// The packed Blake3 digest of `bytes` as a key: eight little-endian `u32`
/// words (`MultiStark.digestGs`).
pub fn digest_key(bytes: &[u8]) -> Vec<u64> {
  blake3::hash(bytes)
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| u64::from(u32::from_le_bytes(*word)))
    .collect()
}

impl<'a> Streams<'a> {
  pub fn extend(
    &mut self,
    channel: u64,
    key: Vec<u64>,
    payload: impl Into<Cow<'a, [u8]>>,
  ) {
    let payload = payload.into();
    match self.position.get(&(channel, key.clone())) {
      Some(&at) => self.entries[at].2 = payload,
      None => {
        self.position.insert((channel, key.clone()), self.entries.len());
        self.entries.push((channel, key, payload));
      },
    }
  }

  pub fn entries(&self) -> &[Entry<'a>] {
    &self.entries
  }

  /// The verifying key of one child kind.
  pub fn vk(&mut self, kind: ChildKind, key: &'a [u8]) {
    self.extend(1, vec![u64::from(kind.code())], key);
  }

  /// One child slot's proof transport and claims.
  pub fn child(
    &mut self,
    slot: u64,
    proof: impl Into<Cow<'a, [u8]>>,
    claims: impl Into<Cow<'a, [u8]>>,
  ) {
    self.extend(0, vec![slot], proof);
    self.extend(2, vec![slot], claims);
  }

  /// The identity blob and the shape byte.
  pub fn identity(&mut self, allowed: &'a [u8], shape: u8) {
    self.extend(3, vec![0], allowed);
    self.extend(6, vec![0], vec![shape]);
  }

  /// A pair fold's output claim.
  pub fn output_claim(&mut self, bytes: &'a [u8]) {
    self.extend(2, vec![2], bytes);
  }

  /// A preimage keyed by its packed digest.
  pub fn preimage(&mut self, bytes: &'a [u8]) {
    self.extend(4, digest_key(bytes), bytes);
  }
}

/// The verifying keys and identity blob every node binds.
#[derive(Clone, Copy)]
pub struct Keys<'a> {
  pub allowed: &'a [u8],
  pub ixvm: &'a [u8],
  pub aggr: &'a [u8],
}

impl<'a> Keys<'a> {
  fn key(&self, kind: ChildKind) -> &'a [u8] {
    match kind {
      ChildKind::Ixvm => self.ixvm,
      ChildKind::Aggr => self.aggr,
    }
  }
}

/// A proven child of a wrap or pair.
#[derive(Clone, Copy)]
pub struct Child<'a> {
  pub kind: ChildKind,
  pub statement: &'a Statement,
  /// The raw proof, without its backend prefix.
  pub proof: &'a [u8],
  /// The serialized claim list of the child's outer claim.
  pub claims: &'a [u8],
}

impl<'a> Child<'a> {
  pub fn transport(&self) -> Transport<'a> {
    Transport { kind: self.kind, proof: self.proof, claims: self.claims }
  }
}

/// What a parent's advice carries for one child proof: its kind, its raw
/// proof and the serialized claim list of its outer claim.
#[derive(Clone, Copy)]
pub struct Transport<'a> {
  pub kind: ChildKind,
  /// The raw proof, without its backend prefix.
  pub proof: &'a [u8],
  pub claims: &'a [u8],
}

fn child<'a>(
  streams: &mut Streams<'a>,
  keys: Keys<'a>,
  slot: u64,
  c: Transport<'a>,
) {
  streams.vk(c.kind, keys.key(c.kind));
  streams.child(slot, c.proof, c.claims);
}

/// Shape 0 or 1: one child, passed through.
pub fn wrap<'a>(keys: Keys<'a>, shape: u8, left: Transport<'a>) -> Streams<'a> {
  let mut streams = Streams::default();
  streams.identity(keys.allowed, shape);
  child(&mut streams, keys, 0, left);
  streams
}

/// Shapes 2 to 9: two children folded into `output`. A structural fold
/// carries, for each candidate assumption of either child, its Merkle path
/// into the output subjects when the output discharges it.
pub fn pair<'a>(
  keys: Keys<'a>,
  shape: u8,
  left: Child<'a>,
  right: Child<'a>,
  output: &'a Statement,
  structural: bool,
  owner_by_address: &FxHashMap<Address, usize>,
) -> Result<Streams<'a>, String> {
  let mut streams = Streams::default();
  streams.identity(keys.allowed, shape);
  child(&mut streams, keys, 0, left.transport());
  child(&mut streams, keys, 1, right.transport());
  streams.output_claim(&output.claim_bytes);
  streams.preimage(&left.statement.claim_bytes);
  streams.preimage(&right.statement.claim_bytes);
  for tree in advice_trees(left.statement, right.statement, output, structural)?
  {
    streams.extend(5, address_key(&tree.root), tree.serialized());
  }
  if structural {
    let candidates = merge_optional_sets(
      left.statement.assumptions.as_deref(),
      right.statement.assumptions.as_deref(),
    );
    for candidate in candidates {
      let owner = owner_by_address.get(&candidate).ok_or_else(|| {
        format!("aggregate assumption {} has no owning shard", candidate.hex())
      })?;
      let path = output.subjects.merkle_proof(&candidate, *owner);
      streams.extend(6, address_key(&candidate), path_payload(path.as_ref())?);
    }
  }
  Ok(streams)
}

/// Shapes 13 and 14 (`FormalAdvice.streamsDischarge`): the child that assumes its role
/// binding in slot 0, the IxVM proof of the `Binding` claim in slot 1, the
/// output claim, and the preimages of both children's claims. The IxVM key
/// is added again after the child's; for an IxVM child that replaces its
/// own entry in place.
pub fn discharge<'a>(
  keys: Keys<'a>,
  child_proof: Transport<'a>,
  child_claim: &'a [u8],
  binding: Transport<'a>,
  binding_claim: &'a [u8],
  output: &'a [u8],
) -> Result<Streams<'a>, String> {
  if binding.kind != ChildKind::Ixvm {
    return Err("a binding proof is an IxVM proof".into());
  }
  let mut streams = Streams::default();
  streams.identity(keys.allowed, discharge_shape_code(child_proof.kind));
  child(&mut streams, keys, 0, child_proof);
  child(&mut streams, keys, 1, binding);
  streams.output_claim(output);
  streams.preimage(child_claim);
  streams.preimage(binding_claim);
  Ok(streams)
}

/// Shapes 15 and 16 (`FormalAdvice.streamsCatalog`): both children,
/// the output claim, then the node's preimages and trees in the order
/// [`crate::catalog::Plan::advice`] lists them.
pub fn catalog<'a>(
  keys: Keys<'a>,
  shape: u8,
  children: [Transport<'a>; 2],
  output: &'a [u8],
  preimages: &'a [Vec<u8>],
  trees: &[&'a CanonicalTree],
) -> Streams<'a> {
  let mut streams = Streams::default();
  streams.identity(keys.allowed, shape);
  for (slot, c) in (0u64..).zip(children) {
    child(&mut streams, keys, slot, c);
  }
  streams.output_claim(output);
  for preimage in preimages {
    streams.preimage(preimage);
  }
  for tree in trees {
    streams.extend(5, address_key(&tree.root), tree.serialized());
  }
  streams
}

#[cfg(test)]
mod tests {
  use super::*;

  /// A repeated key keeps its first position and takes the last payload.
  #[test]
  fn repeated_keys_replace_in_place() {
    let mut streams = Streams::default();
    streams.extend(1, vec![1], vec![1]);
    streams.extend(0, vec![0], vec![2]);
    streams.extend(1, vec![1], vec![3]);
    streams.extend(1, vec![0], vec![4]);
    let entries: Vec<_> = streams
      .entries()
      .iter()
      .map(|(c, k, p)| (*c, k.clone(), p.to_vec()))
      .collect();
    assert_eq!(
      entries,
      vec![(1, vec![1], vec![3]), (0, vec![0], vec![2]), (1, vec![0], vec![4])]
    );
  }

  #[test]
  fn keys_widen_bytes_and_digest_words() {
    let address = Address::hash(b"key");
    let key = address_key(&address);
    assert_eq!(key.len(), 32);
    assert_eq!(key[0], u64::from(address.as_bytes()[0]));
    let digest = digest_key(b"preimage");
    assert_eq!(digest.len(), 8);
    let hash = blake3::hash(b"preimage");
    assert_eq!(
      digest[1],
      u64::from(u32::from_le_bytes(hash.as_bytes()[4..8].try_into().unwrap()))
    );
  }

  /// Equal assumption trees on both children and the output are one tree
  /// stream, at the position of its first use.
  #[test]
  fn repeated_trees_are_one_stream() {
    use crate::statement::{CanonicalTree, ShardSet, SubjectTree};
    let address = |label: &str| Address::hash(label.as_bytes());
    let (a, b, c) = (address("a"), address("b"), address("c"));
    let owners: FxHashMap<Address, usize> =
      [(a.clone(), 0), (b.clone(), 1), (c.clone(), 2)].into_iter().collect();
    let statement = |leaf: &Address, shard: usize| {
      Statement::new(
        crate::tests::ctx(),
        SubjectTree::canonical(
          vec![leaf.clone()],
          ShardSet::singleton(shard, 3),
        )
        .unwrap(),
        CanonicalTree::from_sorted(vec![c.clone()]).unwrap(),
      )
    };
    let (left, right) = (statement(&a, 0), statement(&b, 1));
    let c_root = left.assumptions.as_ref().unwrap().root.clone();
    let keys = Keys { allowed: b"allowed", ixvm: b"ixvm", aggr: b"aggr" };
    let child = |statement| Child {
      kind: ChildKind::Aggr,
      statement,
      proof: b"proof",
      claims: b"claims",
    };
    for structural in [false, true] {
      let output = Statement::join(&left, &right, structural, &owners).unwrap();
      assert_eq!(
        output.assumptions.as_ref().map(|t| t.root.clone()),
        Some(c_root.clone())
      );
      let streams = pair(
        keys,
        5,
        child(&left),
        child(&right),
        &output,
        structural,
        &owners,
      )
      .unwrap();
      let trees: Vec<Vec<u64>> = streams
        .entries()
        .iter()
        .filter(|(channel, _, _)| *channel == 5)
        .map(|(_, key, _)| key.clone())
        .collect();
      let root = |statement: &Statement| {
        address_key(&statement.subjects.canonical_tree().unwrap().root)
      };
      let assumptions = address_key(&left.assumptions.as_ref().unwrap().root);
      if structural {
        assert_eq!(trees, vec![assumptions]);
      } else {
        assert_eq!(
          trees,
          vec![root(&left), assumptions, root(&right), root(&output)]
        );
      }
      let keys: Vec<u64> =
        streams.entries().iter().filter(|e| e.0 == 1).map(|e| e.1[0]).collect();
      assert_eq!(keys, vec![1]);
    }
  }
}
