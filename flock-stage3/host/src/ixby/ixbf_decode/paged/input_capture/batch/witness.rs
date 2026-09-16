use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::SparseMemory,
    ixbf_decode::{
      dispatch::DispatchEvaluator,
      paged::input_capture::{
        GRAMMAR_INDICES, InputCaptureGate, REPLIES, RESOLVED, STATE_WORDS,
      },
      source::last_index,
      stream::witness::Tree,
    },
    memory_log::{AccessAdvice, MemoryBatch},
    paged_code::{CONSTRUCTORS, FUNCTIONS},
  },
};
use anyhow::Context;
use flock_prover::circuit::builder::GateType;
#[derive(Clone, Debug)]
pub struct InputCaptureAdvice {
  pub private: Vec<F128>,
  pub statement: InputCaptureStatement,
  pub steps: usize,
}
pub struct InputCaptureWitness<'a> {
  bytes: &'a [u8],
  tree: Tree<'a>,
  digest: [F128; 2],
  decoder: DispatchEvaluator,
  capture: InputCaptureGate,
  parser: [F128; 30],
  state: [F128; STATE_WORDS],
}
impl<'a> InputCaptureWitness<'a> {
  pub fn new(bytes: &'a [u8], context: [F128; 15]) -> Result<Self> {
    ensure!(bytes.len() <= 1 << (DEPTH + 10), "input capture source capacity");
    let decoder = DispatchEvaluator::new(config())?;
    let parser = decoder.initialize(bytes.len() as u64, context)?;
    let hash = blake3::hash(bytes);
    Ok(Self {
      bytes,
      tree: Tree::new(bytes),
      digest: [
        pack_bytes(&hash.as_bytes()[..16]),
        pack_bytes(&hash.as_bytes()[16..]),
      ],
      decoder,
      capture: InputCaptureGate::new(3)?,
      parser,
      state: [F128::ZERO; STATE_WORDS],
    })
  }
  pub fn parser(&self) -> &[F128; 30] {
    &self.parser
  }
  pub fn state(&self) -> &[F128; STATE_WORDS] {
    &self.state
  }
  pub fn done(&self) -> bool {
    self.parser[1].lo as u8 == 20
      && self.parser[28..] == [F128::ZERO; 2]
      && [self.state[0], self.state[2], self.state[3]] == [F128::ZERO; 3]
  }
  pub fn next_batch(
    &mut self,
    memory: &mut SparseMemory,
  ) -> Result<Option<InputCaptureAdvice>> {
    if self.done() {
      return Ok(None);
    }
    ensure!(memory.depth().bits() == 40, "input capture memory depth");
    let initial = self.parser;
    let initial_capture = self.state;
    let initial_root = memory.root();
    let last = last_index(self.bytes.len() as u64);
    let first = (self.decoder.request(&self.parser)?[4].lo >> 10).min(last);
    let mut memory = MemoryBatch::new(memory);
    let mut steps = 0;
    let mut hints = Vec::new();
    while steps < STEPS && !self.done() {
      let req = self.decoder.request(&self.parser)?;
      if req[5].lo != 0 && (req[4].lo >> 10).min(last) != first {
        break;
      }
      let at: usize = req[4].lo.try_into()?;
      ensure!(at <= self.bytes.len(), "input capture source cursor");
      let take = (req[5].lo as usize).min(self.bytes.len() - at);
      let mut window = vec![0; config().window_bytes()];
      window[..take].copy_from_slice(&self.bytes[at..at + take]);
      let words = window
        .as_chunks::<16>()
        .0
        .iter()
        .map(|v| pack_bytes(v))
        .collect::<Vec<_>>();
      let event = self.decoder.step(&self.parser, &words)?;
      let mut input = GRAMMAR_INDICES.map(|i| self.parser[i]).to_vec();
      input.extend([
        event.next,
        F128::new(event.tag as u64, 0),
        F128::new(u64::from(event.committed), 0),
      ]);
      input.extend(event.fields);
      input.extend([event.natural_magnitude[0], event.payload_range]);
      input.extend(self.state);
      assert_eq!(input.len(), RESOLVED);
      input.extend([F128::ZERO; 9]);
      let mut addresses = [0u64; 3];
      if self.parser[1].lo as u8 == 0 {
        addresses[0] = FUNCTIONS + self.parser[24].lo;
      } else if self.parser[1].lo as u8 == 19 {
        if event.fields[0] == F128::ONE {
          let mut resolved = None;
          for i in 0..self.parser[2].lo {
            let a = CONSTRUCTORS + 3 * i;
            let x = memory.value(a)?;
            let y = memory.value(a + 1)?;
            if [x[0], x[1], y[0], y[1]] == event.fields[1..5] {
              resolved = Some(i);
              break;
            }
          }
          let i = resolved.context("input constructor ID not declared")?;
          input[RESOLVED] = F128::new(i, 0);
          addresses = std::array::from_fn(|j| CONSTRUCTORS + 3 * i + j as u64);
        } else if event.fields[0] == F128::new(2, 0) {
          addresses[0] = FUNCTIONS + event.fields[1].lo;
        }
      }
      for (i, address) in addresses.into_iter().enumerate() {
        input[REPLIES + 2 * i..REPLIES + 2 * i + 2]
          .copy_from_slice(&memory.value(address)?);
      }
      let mut out = Vec::new();
      self.capture.eval(&input, &(), &mut out);
      let pop = out[STATE_WORDS + 3 * 4].lo;
      if pop != 0 {
        input[REPLIES + 6..REPLIES + 8].copy_from_slice(&memory.value(pop)?);
        out.clear();
        self.capture.eval(&input, &(), &mut out);
      }
      ensure!(
        out.last() == Some(&F128::ZERO),
        "input capture row rejected at byte {} phase {}",
        self.parser[0].lo,
        self.parser[1].lo as u8
      );
      let records = out[STATE_WORDS..STATE_WORDS + 24]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|r| AccessAdvice {
          address: r[0].lo,
          write: r[1] == F128::ONE,
          value: [r[2], r[3]],
        })
        .collect::<Vec<_>>();
      if !memory.fits_shared(&records, capacity()) {
        break;
      }
      for r in records {
        if r.write {
          memory.write(r.address, r.value)?;
        } else {
          ensure!(
            memory.read(r.address)? == r.value,
            "input capture native read"
          );
        }
      }
      self.parser = event.state;
      self.state.copy_from_slice(&out[..STATE_WORDS]);
      hints.extend(&input[RESOLVED..]);
      steps += 1;
    }
    ensure!(steps > 0, "input capture batch cannot make progress");
    for _ in steps..STEPS {
      hints.extend([F128::ZERO; 9]);
      for _ in 0..6 {
        ensure!(
          memory.read(0)? == [F128::ZERO; 2],
          "input capture padding cell"
        );
      }
    }
    let (memory, tree) = memory.finish_shared(capacity())?;
    ensure!(
      memory.initial_root == initial_root,
      "input capture initial memory"
    );
    let mut statement = vec![F128::new(self.bytes.len() as u64, 0)];
    statement.extend(self.digest);
    statement.extend(initial);
    statement.extend(initial_capture);
    statement.extend(initial_root);
    let mut private = statement.clone();
    private.extend([F128::new(first, 0), F128::new(steps as u64, 0)]);
    for index in [first, (first + 1).min(last), last] {
      private.extend(self.tree.advice(index as usize, DEPTH));
    }
    private.extend(hints);
    private.extend(memory.final_root);
    private.extend(&tree.private[4..]);
    private.extend(memory.switches);
    statement.extend(self.parser);
    statement.extend(self.state);
    statement.extend(memory.final_root);
    Ok(Some(InputCaptureAdvice {
      private,
      statement: InputCaptureStatement::from_words(&statement)?,
      steps,
    }))
  }
}
