use super::*;
use crate::{hash::pack_bytes, ixby::ixbf_decode::stream::witness::Tree};
#[derive(Clone, Debug)]
pub struct CommitmentBridgeAdvice {
  pub private: Vec<F128>,
  pub statement: CommitmentBridgeStatement,
}
/// Native hashing and source trees supply only advice; the circuit checks both.
pub struct CommitmentBridgeWitness<'a> {
  raw: &'a [u8],
  raw_tree: Tree<'a>,
  parent: [F128; 2],
  raw_hash: [F128; 2],
  prefixed_tree: Tree<'static>,
  message_len: usize,
  hash: [F128; 2],
  index: u64,
}
fn digest(bytes: &[u8]) -> [F128; 2] {
  let h = blake3::hash(bytes);
  [pack_bytes(&h.as_bytes()[..16]), pack_bytes(&h.as_bytes()[16..])]
}
impl<'a> CommitmentBridgeWitness<'a> {
  pub fn new(
    domain: ArtifactDomain,
    raw: &'a [u8],
    parent: [F128; 2],
  ) -> Result<Self> {
    ensure!(raw.len() <= 1 << 24, "commitment raw capacity");
    let mut message = domain.prefix().to_vec();
    for v in parent {
      message.extend(v.lo.to_le_bytes());
      message.extend(v.hi.to_le_bytes());
    }
    message.extend(raw);
    let hash = digest(&message);
    Ok(Self {
      raw,
      raw_tree: Tree::new(raw),
      parent,
      raw_hash: digest(raw),
      message_len: message.len(),
      prefixed_tree: Tree::owned(message),
      hash,
      index: 0,
    })
  }
  pub fn digest(&self) -> [F128; 2] {
    self.hash
  }
  pub fn next_batch(&mut self) -> Result<Option<CommitmentBridgeAdvice>> {
    let end = self.message_len.div_ceil(1024) as u64;
    if self.index == end {
      return Ok(None);
    }
    let i = self.index;
    let last = self.raw.len().saturating_sub(1) as u64 >> 10;
    let mut private = [F128::new(self.raw.len() as u64, 0)]
      .into_iter()
      .chain(self.raw_hash)
      .chain(self.parent)
      .chain(self.hash)
      .chain([F128::new(i, 0)])
      .collect::<Vec<_>>();
    let mut expected = private.clone();
    expected.push(F128::new(i + 1, 0));
    for index in [i.saturating_sub(1), i.min(last), last] {
      private.extend(self.raw_tree.advice(index as usize, RAW_DEPTH));
    }
    let tree = &self.prefixed_tree;
    private.extend(&tree.advice(i as usize, PREFIXED_DEPTH)[64..]);
    private.extend(tree.advice(end as usize - 1, PREFIXED_DEPTH));
    self.index += 1;
    Ok(Some(CommitmentBridgeAdvice {
      private,
      statement: CommitmentBridgeStatement::from_words(&expected)?,
    }))
  }
}
