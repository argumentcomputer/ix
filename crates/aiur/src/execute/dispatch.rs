//! Prepare the interpreter's next action once, including skipped instructions
//! and fixed host calls. Original PCs remain the keys for errors and trace replay.
use crate::{
  bytecode::{CheckedProgram, Instruction},
  field::FieldBackend,
  hints::HintSite,
  host::{MapCalls, RegisterHint, RegisterMap},
};
use std::sync::Arc;

pub(crate) struct Dispatch<F> {
  pub(crate) pc: usize,
  pub(crate) next: usize,
  pub(crate) instructions: u64,
  pub(crate) action: Action<F>,
}

pub(crate) enum Action<F> {
  Bytecode { memory_type: usize, branch: usize },
  Return { plan: usize },
  Map { function: usize, call: Arc<RegisterMap<F>> },
  Hint { call: Arc<RegisterHint<F>> },
}

pub(crate) fn prepare<B: FieldBackend>(
  program: &CheckedProgram<B>,
  hints: &[Vec<Option<HintSite<B::Element>>>],
  maps: Option<&[MapCalls<B::Element>]>,
) -> Vec<Vec<Dispatch<B::Element>>> {
  program
    .steps
    .iter()
    .enumerate()
    .map(|(function, steps)| {
      // Different entries into a skipped prefix can have different
      // instruction counts. Keep each reachable entry, not just each
      // eventual operation, and resolve its successors to dense indices.
      let code = &program.execution_functions[function].code;
      let returns = &program.returns[function];
      let mut reachable = vec![false; steps.len()];
      let mut pending = vec![0];
      while let Some(pc) = pending.pop() {
        if std::mem::replace(&mut reachable[pc], true) {
          continue;
        }
        let step = &steps[pc];
        if returns[step.pc].is_some() {
          continue;
        }
        match &code[step.pc] {
          Instruction::Ret { .. } | Instruction::Fail { .. } => (),
          Instruction::Jump { target } => pending.push(*target),
          Instruction::Branch { tests, otherwise } => {
            if !tests.is_empty() {
              pending.push(*otherwise);
            }
            pending.push(step.pc + 1);
          },
          _ => pending.push(step.pc + 1),
        }
      }
      let pcs: Vec<_> = reachable
        .iter()
        .enumerate()
        .filter_map(|(pc, &reachable)| reachable.then_some(pc))
        .collect();
      let mut entries = vec![usize::MAX; steps.len()];
      for (index, &pc) in pcs.iter().enumerate() {
        entries[pc] = index;
      }
      pcs
        .iter()
        .map(|&pc| {
          let step = &steps[pc];
          if let Some(ret) = &returns[step.pc] {
            return Dispatch {
              pc: ret.pc,
              next: usize::MAX,
              instructions: step.skipped + ret.instructions,
              action: Action::Return { plan: step.pc },
            };
          }
          let action =
            match &program.execution_functions[function].code[step.pc] {
              Instruction::Call { function: callee, .. } => {
                maps.and_then(|maps| maps[function][step.pc].as_ref()).map(
                  |call| Action::Map { function: *callee, call: call.clone() },
                )
              },
              Instruction::Hint { .. } => hints[function][step.pc]
                .as_ref()
                .and_then(|site| site.registers.as_ref())
                .map(|call| Action::Hint { call: call.clone() }),
              _ => None,
            }
            .unwrap_or(Action::Bytecode {
              memory_type: step.memory_type,
              branch: match &code[step.pc] {
                Instruction::Branch { otherwise, .. } => entries[*otherwise],
                Instruction::Jump { target } => entries[*target],
                _ => usize::MAX,
              },
            });
          Dispatch {
            pc: step.pc,
            next: entries.get(step.pc + 1).copied().unwrap_or(usize::MAX),
            instructions: step.skipped + 1,
            action,
          }
        })
        .collect()
    })
    .collect()
}
