//! Bounded-batch advice generation. Retains original bytes and a BLAKE3 tree,
//! not an AST or a complete parser trace. Native hashing/decoding here is
//! untrusted and is never used to admit proofs.
use crate::{
  hash::pack_bytes,
  ixby::ixbf_decode::{
    dispatch::{DispatchConfig, DispatchEvaluator},
    source::{SourceCapacity, last_index},
  },
};
use anyhow::{Result, ensure};
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root};
use flock_prover::field::F128;

fn words(bytes: &[u8]) -> Vec<F128> {
  assert_eq!(bytes.len() % 16, 0);
  bytes.as_chunks::<16>().0.iter().map(|w| pack_bytes(w)).collect()
}

struct Tree<'a> {
  bytes: &'a [u8],
  levels: Vec<Vec<[u8; 32]>>,
}
impl<'a> Tree<'a> {
  fn new(bytes: &'a [u8]) -> Self {
    let mut leaves: Vec<_> = bytes
      .chunks(1024)
      .enumerate()
      .map(|(index, chunk)| {
        blake3::Hasher::new()
          .set_input_offset((index as u64) * 1024)
          .update(chunk)
          .finalize_non_root()
      })
      .collect();
    if leaves.is_empty() {
      leaves.push([0; 32]);
    }
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 1 {
      levels.push(
        levels
          .last()
          .unwrap()
          .chunks(2)
          .map(|pair| {
            if pair.len() == 1 {
              pair[0]
            } else {
              merge_subtrees_non_root(&pair[0], &pair[1], Mode::Hash)
            }
          })
          .collect(),
      );
    }
    Self { bytes, levels }
  }
  fn advice(&self, index: usize, depth: usize) -> Vec<F128> {
    let at = index * 1024;
    let end = (at + 1024).min(self.bytes.len());
    let mut chunk = [0; 1024];
    chunk[..end - at].copy_from_slice(&self.bytes[at..end]);
    let mut out = words(&chunk);
    for level in 0..depth {
      let sibling = self
        .levels
        .get(level)
        .and_then(|nodes| nodes.get((index >> level) ^ 1));
      out.extend(sibling.map(|cv| words(cv)).unwrap_or(vec![F128::ZERO; 2]));
    }
    out
  }
}

pub struct BatchAdvice {
  pub first_chunk: u64,
  pub steps: usize,
  pub initial: [F128; 30],
  pub final_state: [F128; 30],
  pub events: [usize; 18],
  /// length, digest, initial state, first chunk, actual step count, followed
  /// by first/next/final proofs (64 byte words + two words per tree level).
  pub private: Vec<F128>,
  /// Exact length, original digest, all initial and final state words.
  pub statement: Vec<F128>,
}

pub struct BatchWitness<'a> {
  evaluator: DispatchEvaluator,
  capacity: SourceCapacity,
  tree: Tree<'a>,
  root: [F128; 2],
  state: [F128; 30],
}
impl<'a> BatchWitness<'a> {
  pub fn new(
    config: DispatchConfig,
    depth: usize,
    bytes: &'a [u8],
    context: [F128; 15],
  ) -> Result<Self> {
    let capacity = SourceCapacity::new(depth, config.window_bytes())?;
    ensure!(
      capacity.admits_length(bytes.len().try_into()?),
      "stream source length capacity"
    );
    let evaluator = DispatchEvaluator::new(config)?;
    let state = evaluator.initialize(bytes.len() as u64, context)?;
    Ok(Self {
      evaluator,
      capacity,
      tree: Tree::new(bytes),
      root: words(blake3::hash(bytes).as_bytes()).try_into().unwrap(),
      state,
    })
  }
  pub fn state(&self) -> &[F128; 30] {
    &self.state
  }
  pub fn root(&self) -> [F128; 2] {
    self.root
  }
  pub fn done(&self) -> bool {
    self.state[1].lo as u8 == 20 && self.state[28..] == [F128::ZERO; 2]
  }
  pub fn next_batch(
    &mut self,
    maximum_steps: usize,
  ) -> Result<Option<BatchAdvice>> {
    ensure!(maximum_steps > 0, "zero parser batch capacity");
    if self.done() {
      return Ok(None);
    }
    let length = self.tree.bytes.len() as u64;
    let initial = self.state;
    let last = last_index(length);
    let first = (self.evaluator.request(&self.state)?[4].lo >> 10).min(last);
    let mut events = [0; 18];
    let mut steps = 0;
    while steps < maximum_steps && !self.done() {
      let req = self.evaluator.request(&self.state)?;
      if req[5].lo != 0 && (req[4].lo >> 10).min(last) != first {
        break;
      }
      let at: usize = req[4].lo.try_into()?;
      ensure!(at <= self.tree.bytes.len(), "parser source cursor");
      let take = (req[5].lo as usize).min(self.tree.bytes.len() - at);
      let mut window = vec![0; self.capacity.window_bytes()];
      window[..take].copy_from_slice(&self.tree.bytes[at..at + take]);
      let next = self.evaluator.step(&self.state, &words(&window))?;
      if next.committed {
        events[next.tag as usize] += 1;
      }
      self.state = next.state;
      steps += 1;
    }
    ensure!(
      steps > 0 && self.state != initial,
      "parser batch made no progress"
    );
    let mut statement = vec![F128::new(length, 0)];
    statement.extend(self.root);
    statement.extend(initial);
    let mut private = statement.clone();
    statement.extend(self.state);
    private.extend([F128::new(first, 0), F128::new(steps as u64, 0)]);
    for index in [first, (first + 1).min(last), last] {
      private.extend(self.tree.advice(index as usize, self.capacity.depth()));
    }
    Ok(Some(BatchAdvice {
      first_chunk: first,
      steps,
      initial,
      final_state: self.state,
      events,
      private,
      statement,
    }))
  }
}
