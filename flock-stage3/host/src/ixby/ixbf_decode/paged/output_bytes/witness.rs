use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::SparseMemory,
    ixbf_decode::stream::witness::Tree,
    memory_log::{AccessAdvice, MemoryBatch},
  },
};
use flock_prover::circuit::builder::GateType;
#[derive(Clone, Debug)]
pub struct OutputBytesAdvice {
  pub private: Vec<F128>,
  pub statement: OutputBytesStatement,
  pub steps: usize,
}
pub struct OutputBytesWitness<'a> {
  bytes: &'a [u8],
  tree: Tree<'a>,
  digest: [F128; 2],
  value: [F128; 2],
  header: u64,
  index: u64,
  end: u64,
  gate: OutputBytesGate,
}
impl<'a> OutputBytesWitness<'a> {
  pub fn new(bytes: &'a [u8], value: [F128; 2]) -> Result<Self> {
    ensure!(
      bytes.len() >= 15 && bytes.len() <= 1 << 24,
      "output source capacity"
    );
    let mut prefix = [0u8; 32];
    let n = bytes.len().min(32);
    prefix[..n].copy_from_slice(&bytes[..n]);
    let mut header = Vec::new();
    OutputBytesGate::new(3, OutputBytesOp::Header)?.eval(
      &[
        F128::new(bytes.len() as u64, 0),
        value[0],
        value[1],
        pack_bytes(&prefix[..16]),
        pack_bytes(&prefix[16..]),
        F128::ZERO,
      ],
      &(),
      &mut header,
    );
    ensure!(header[2] == F128::ZERO, "output header or Bytes value rejected");
    let hash = blake3::hash(bytes);
    Ok(Self {
      bytes,
      tree: Tree::new(bytes),
      digest: [
        pack_bytes(&hash.as_bytes()[..16]),
        pack_bytes(&hash.as_bytes()[16..]),
      ],
      value,
      header: header[0].lo,
      end: header[1].lo,
      index: 0,
      gate: OutputBytesGate::new(3, OutputBytesOp::Step)?,
    })
  }
  pub fn done(&self) -> bool {
    self.index == self.end
  }
  pub fn index(&self) -> u64 {
    self.index
  }
  pub fn next_batch(
    &mut self,
    memory: &mut SparseMemory,
  ) -> Result<Option<OutputBytesAdvice>> {
    if self.done() {
      return Ok(None);
    }
    ensure!(memory.depth().bits() == 40, "output memory depth");
    let root = memory.root();
    let initial = self.index;
    let shared = [F128::new(self.bytes.len() as u64, 0)]
      .into_iter()
      .chain(self.digest)
      .chain(root)
      .chain(self.value)
      .collect::<Vec<_>>();
    let first = (self.header + initial * 32) >> 10;
    let last = (self.bytes.len() - 1) as u64 >> 10;
    let mut private = shared.clone();
    private.push(F128::new(initial, 0));
    private.push(F128::new(first, 0));
    for chunk in [0, first, (first + 1).min(last), last] {
      private.extend(self.tree.advice(chunk as usize, SOURCE_DEPTH));
    }
    let mut log = MemoryBatch::new(memory);
    let mut steps = 0;
    for step in 0..STEPS {
      let enabled =
        !self.done() && (self.header + self.index * 32) >> 10 == first;
      let offset = self.index * 32;
      let take = if enabled {
        self.value[1].hi.saturating_sub(offset).min(32)
      } else {
        0
      };
      let pointer = self.value[1].lo + offset;
      let addresses = [
        if take > 0 { pointer >> 5 } else { 0 },
        if take > 0 && (pointer & 31) + take > 32 {
          (pointer >> 5) + 1
        } else {
          0
        },
      ];
      let replies = addresses
        .map(|address| log.value(address))
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
      let mut input = self.value.to_vec();
      input.extend([
        F128::new(self.header, 0),
        F128::new(self.bytes.len() as u64, 0),
        F128::new(self.index, 0),
        F128::new(enabled as u64, 0),
      ]);
      input.extend(replies.iter().flatten());
      let mut out = Vec::new();
      self.gate.eval(&input, &(), &mut out);
      ensure!(out[7] == F128::ZERO, "output row rejected");
      let records = (0..2)
        .map(|i| AccessAdvice {
          address: out[3 + i].lo,
          write: false,
          value: replies[i],
        })
        .collect::<Vec<_>>();
      ensure!(log.fits_shared(&records, capacity()), "output memory quota");
      for record in records {
        ensure!(
          log.read(record.address)? == record.value,
          "output memory reply"
        );
      }
      if step > 0 {
        private.push(F128::new(enabled as u64, 0));
      } else {
        ensure!(enabled, "output batch progress");
      }
      private.extend(&input[6..]);
      self.index = out[0].lo;
      steps += enabled as usize;
    }
    let (log, tree) = log.finish_shared(capacity())?;
    ensure!(
      log.initial_root == root && log.final_root == root,
      "output read-only memory"
    );
    private.extend(&tree.private[4..]);
    private.extend(log.switches);
    let words = shared
      .into_iter()
      .chain([F128::new(initial, 0), F128::new(self.index, 0)])
      .collect::<Vec<_>>();
    Ok(Some(OutputBytesAdvice {
      private,
      statement: OutputBytesStatement::from_words(&words)?,
      steps,
    }))
  }
}
