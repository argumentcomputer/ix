use super::*;
use crate::ixby::{
  auth_memory::SparseMemory,
  memory_log::{AccessAdvice, MemoryBatch},
  paged_code::{CONSTRUCTORS, FUNCTIONS, block_address},
};
use flock_prover::circuit::builder::GateType;
#[derive(Clone, Debug)]
pub struct ReferenceAdvice {
  pub private: Vec<F128>,
  pub statement: ReferenceStatement,
  pub steps: usize,
}
pub struct ReferenceWitness {
  context: [F128; 3],
  state: [F128; 3],
  gate: ReferenceGate,
}
impl ReferenceWitness {
  pub fn new(context: [F128; 3]) -> Result<Self> {
    let mut words = [F128::ZERO; PUBLIC_WORDS];
    words[..3].copy_from_slice(&context);
    ReferenceStatement::from_words(&words)?;
    Ok(Self { context, state: [F128::ZERO; 3], gate: ReferenceGate::new(3)? })
  }
  pub fn state(&self) -> &[F128; 3] {
    &self.state
  }
  pub fn done(&self) -> bool {
    self.state[0].lo as u8 == 3
  }
  fn row(&self, memory: &MemoryBatch<'_>) -> Result<(Vec<F128>, Vec<F128>)> {
    let mut input =
      self.context.into_iter().chain(self.state).collect::<Vec<_>>();
    input.push(F128::ONE);
    let c = self.state[0].lo;
    let f = (c >> 8) as u16;
    let block = (c >> 24) as u8;
    let alt = (c >> 32) as u8;
    let mut addresses = [0u64; 4];
    match c as u8 {
      0 => {
        addresses[0] = FUNCTIONS + u64::from(f);
        let decl = memory.value(addresses[0])?;
        addresses[1] = block_address(f, (decl[0].lo >> 8) as u8);
      },
      1 => {
        addresses[0] = block_address(f, block);
        let h = memory.value(addresses[0])?[0];
        let inst = (h.lo >> 8) as u8;
        let op = (h.lo >> 16) as u8;
        if inst == 2 || (inst == 0 && matches!(op, 4 | 5)) {
          addresses[1] = FUNCTIONS + u64::from(h.hi as u16);
        } else if inst == 0 && op == 2 {
          addresses[1] = CONSTRUCTORS + 3 * u64::from(h.hi as u16) + 2;
        }
        if matches!(inst, 0 | 6 | 7) {
          addresses[2] = block_address(f, (h.hi >> 16) as u8);
        }
        if matches!(inst, 6 | 7) {
          addresses[3] = block_address(f, (h.hi >> 24) as u8);
        }
      },
      2 => {
        addresses[0] = block_address(f, block) + 128 + u64::from(alt);
        let a = memory.value(addresses[0])?[0].lo;
        addresses[1] = CONSTRUCTORS + 3 * u64::from(a as u8) + 2;
        addresses[2] = block_address(f, (a >> 8) as u8);
      },
      3 => {},
      _ => anyhow::bail!("native reference phase"),
    }
    for address in addresses {
      input.extend(memory.value(address)?);
    }
    let mut out = Vec::new();
    self.gate.eval(&input, &(), &mut out);
    ensure!(
      out.last() == Some(&F128::ZERO),
      "reference row rejected at state {:?}",
      self.state
    );
    for (i, address) in addresses.into_iter().enumerate() {
      ensure!(
        out[3 + 4 * i] == F128::new(address, 0),
        "native reference address mismatch"
      );
    }
    Ok((input, out))
  }
  pub fn next_batch(
    &mut self,
    memory: &mut SparseMemory,
  ) -> Result<Option<ReferenceAdvice>> {
    if self.done() {
      return Ok(None);
    }
    ensure!(memory.depth().bits() == 40, "reference memory depth");
    let root = memory.root();
    let initial = self.state;
    let mut private =
      self.context.into_iter().chain(root).chain(initial).collect::<Vec<_>>();
    let mut log = MemoryBatch::new(memory);
    let mut steps = 0;
    while steps < STEPS && !self.done() {
      let (input, out) = self.row(&log)?;
      let records = out[3..19]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|r| AccessAdvice {
          address: r[0].lo,
          write: false,
          value: [r[2], r[3]],
        })
        .collect::<Vec<_>>();
      if !log.fits_shared(&records, capacity()) {
        break;
      }
      for r in records {
        ensure!(log.read(r.address)? == r.value, "reference read value");
      }
      self.state.copy_from_slice(&out[..3]);
      private.extend(&input[6..]);
      steps += 1;
    }
    ensure!(steps > 0, "reference batch cannot make progress");
    for _ in steps..STEPS {
      private.extend([F128::ZERO; 9]);
      for _ in 0..4 {
        ensure!(log.read(0)? == [F128::ZERO; 2], "reference padding cell");
      }
    }
    let (log, tree) = log.finish_shared(capacity())?;
    ensure!(
      log.initial_root == root && log.final_root == root,
      "reference read-only memory"
    );
    private.extend(&tree.private[4..]);
    private.extend(log.switches);
    let words = self
      .context
      .into_iter()
      .chain(root)
      .chain(initial)
      .chain(self.state)
      .collect::<Vec<_>>();
    Ok(Some(ReferenceAdvice {
      private,
      statement: ReferenceStatement::from_words(&words)?,
      steps,
    }))
  }
}
