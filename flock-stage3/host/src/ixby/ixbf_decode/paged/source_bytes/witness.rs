use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{SparseMemory, multi::MultiAdvice},
    ixbf_decode::{source::last_index, stream::witness::Tree},
  },
};

#[derive(Clone, Debug)]
pub struct SourceBytesAdvice {
  pub private: Vec<F128>,
  pub statement: SourceBytesStatement,
}
/// Native hashing, memory edits and routing here are untrusted witness advice.
pub struct SourceBytesWitness<'a> {
  bank: SourceBank,
  bytes: &'a [u8],
  tree: Tree<'a>,
  digest: [F128; 2],
  cursor: u64,
}
impl<'a> SourceBytesWitness<'a> {
  pub fn new(bank: SourceBank, bytes: &'a [u8]) -> Result<Self> {
    ensure!(bytes.len() <= 1 << (SOURCE_DEPTH + 10), "source bytes length");
    let hash = blake3::hash(bytes);
    Ok(Self {
      bank,
      bytes,
      tree: Tree::new(bytes),
      digest: [
        pack_bytes(&hash.as_bytes()[..16]),
        pack_bytes(&hash.as_bytes()[16..]),
      ],
      cursor: 0,
    })
  }
  pub fn cursor(&self) -> u64 {
    self.cursor
  }
  pub fn next_batch(
    &mut self,
    memory: &mut SparseMemory,
  ) -> Result<Option<SourceBytesAdvice>> {
    ensure!(memory.depth().bits() == MEMORY_DEPTH, "source bytes memory depth");
    let last = last_index(self.bytes.len() as u64);
    let first = self.cursor;
    if first > last {
      return Ok(None);
    }
    let end = (first + 2).min(last + 1);
    let address = self.bank.address() + first * 32;
    let updates = (0..CELLS)
      .map(|i| {
        let at = first as usize * 1024 + i * 32;
        let mut cell = [0; 32];
        if at < self.bytes.len() {
          let n = 32.min(self.bytes.len() - at);
          cell[..n].copy_from_slice(&self.bytes[at..at + n]);
        }
        (address + i as u64, [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])])
      })
      .collect::<Vec<_>>();
    for &(address, _) in &updates {
      ensure!(
        memory.value(address)? == [F128::ZERO; 2],
        "source bytes destination not zero"
      );
    }
    let update = memory.replace_many(updates)?;
    let tree = MultiAdvice::new(capacity(), &update)?;
    let mut statement = vec![F128::new(self.bytes.len() as u64, 0)];
    statement.extend(self.digest);
    statement.push(F128::new(first, 0));
    statement.extend(update.initial_root);
    let mut private = statement.clone();
    private.extend(update.final_root);
    statement.push(F128::new(end, 0));
    statement.extend(update.final_root);
    for index in [first, (first + 1).min(last), last] {
      private.extend(self.tree.advice(index as usize, SOURCE_DEPTH));
    }
    private.extend(&tree.private[4 + 5 * CELLS..]);
    self.cursor = end;
    Ok(Some(SourceBytesAdvice {
      private,
      statement: SourceBytesStatement::from_words(&statement)?,
    }))
  }
}
