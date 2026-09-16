use super::*;
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::SparseMemory,
    ixbf_decode::{
      dispatch::DispatchEvaluator,
      paged::code_capture::{CodeCaptureGate, GRAMMAR_INDICES},
      source::last_index,
      stream::witness::Tree,
    },
    memory_log::{AccessAdvice, MemoryBatch},
    paged_code::{CodeGate, CodeGateKind},
  },
};
use anyhow::Context;
use flock_prover::circuit::builder::GateType;
#[derive(Clone, Debug)]
pub struct CodeCaptureAdvice {
  pub private: Vec<F128>,
  pub statement: CodeCaptureStatement,
  pub steps: usize,
}
pub struct CodeCaptureWitness<'a> {
  bytes: &'a [u8],
  tree: Tree<'a>,
  digest: [F128; 2],
  decoder: DispatchEvaluator,
  capture: CodeCaptureGate,
  header: CodeGate,
  parser: [F128; 30],
  state: [F128; 7],
}
fn eval<G: GateType<Hint = ()>>(g: &G, input: &[F128]) -> Result<Vec<F128>> {
  let mut out = Vec::new();
  g.eval(input, &(), &mut out);
  ensure!(out.pop() == Some(F128::ZERO), "code capture native row rejected");
  Ok(out)
}
impl<'a> CodeCaptureWitness<'a> {
  pub fn new(bytes: &'a [u8]) -> Result<Self> {
    ensure!(bytes.len() <= 1 << (DEPTH + 10), "code capture source capacity");
    let decoder = DispatchEvaluator::new(config())?;
    let parser = decoder.initialize(bytes.len() as u64, [F128::ZERO; 15])?;
    let hash = blake3::hash(bytes);
    Ok(Self {
      bytes,
      tree: Tree::new(bytes),
      digest: [
        pack_bytes(&hash.as_bytes()[..16]),
        pack_bytes(&hash.as_bytes()[16..]),
      ],
      decoder,
      capture: CodeCaptureGate::new(3)?,
      header: CodeGate::new(3, CodeGateKind::Block)?,
      parser,
      state: [F128::ZERO; 7],
    })
  }
  pub fn parser(&self) -> &[F128; 30] {
    &self.parser
  }
  pub fn state(&self) -> &[F128; 7] {
    &self.state
  }
  pub fn done(&self) -> bool {
    self.parser[1].lo as u8 == 20
      && self.parser[28..] == [F128::ZERO; 2]
      && self.state == [F128::ZERO; 7]
  }
  pub fn next_batch(
    &mut self,
    memory: &mut SparseMemory,
  ) -> Result<Option<CodeCaptureAdvice>> {
    if self.done() {
      return Ok(None);
    }
    ensure!(memory.depth().bits() == 40, "code capture memory depth");
    let initial = self.parser;
    let initial_capture = self.state;
    let initial_root = memory.root();
    let last = last_index(self.bytes.len() as u64);
    let first = (self.decoder.request(&self.parser)?[4].lo >> 10).min(last);
    let mut memory = MemoryBatch::new(memory);
    let mut steps = 0;
    while steps < STEPS && !self.done() {
      let req = self.decoder.request(&self.parser)?;
      if req[5].lo != 0 && (req[4].lo >> 10).min(last) != first {
        break;
      }
      let at: usize = req[4].lo.try_into()?;
      ensure!(at <= self.bytes.len(), "code capture source cursor");
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
        event.state[1],
        F128::new(event.tag as u64, 0),
        F128::new(u64::from(event.committed), 0),
      ]);
      input.extend(event.fields);
      input.extend([event.natural_magnitude[0], event.payload_range]);
      input.extend(self.state);
      let out = eval(&self.capture, &input)
        .with_context(|| format!("capture at byte {}", self.parser[0].lo))?;
      eval(&self.header, &[out[19], out[20], out[21], F128::ZERO])?;
      let records = out[7..19]
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
      for record in records {
        if record.write {
          memory.write(record.address, record.value)?;
        } else {
          ensure!(
            memory.read(record.address)? == record.value,
            "code capture native null read"
          );
        }
      }
      self.parser = event.state;
      self.state = out[..7].try_into().unwrap();
      steps += 1;
    }
    ensure!(steps > 0, "code capture batch cannot make progress");
    for _ in steps..STEPS {
      for _ in 0..3 {
        ensure!(
          memory.read(0)? == [F128::ZERO; 2],
          "code capture padding cell"
        );
      }
    }
    let (memory, tree) = memory.finish_shared(capacity())?;
    ensure!(memory.initial_root == initial_root, "code capture initial root");
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
    private.extend(memory.final_root);
    private.extend(&tree.private[4..]);
    private.extend(memory.switches);
    statement.extend(self.parser);
    statement.extend(self.state);
    statement.extend(memory.final_root);
    Ok(Some(CodeCaptureAdvice {
      private,
      statement: CodeCaptureStatement::from_words(&statement)?,
      steps,
    }))
  }
}
