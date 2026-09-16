//! Untrusted native loading of the complete original program and input.
//! This supplies advice and an expected memory root for execution experiments;
//! it does not prove admission of that root from the original source bytes.
use super::{HEAP_COUNT, NativeMachine, STATE_WORDS, initial_state};
use crate::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    ixbf::{self, DecodeLimits, ValueKind},
    paged_code::{PackedProgram, scalar, small},
    paged_frame::{FrameState, HEAP, LOCALS},
    paged_value::INPUT_BYTES,
  },
};
use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use std::collections::BTreeMap;

pub struct NativeImage {
  pub memory: SparseMemory,
  pub state: [F128; STATE_WORDS],
  pub parameters: [F128; 3],
  pub cell_count: usize,
}
impl NativeImage {
  /// Decode without replacing, normalizing or reserializing either source.
  /// Physical capacities can reject otherwise valid functional programs.
  pub fn load(
    program: &[u8],
    input: &[u8],
    loader: DecodeLimits,
  ) -> Result<Self> {
    let artifact = ixbf::decode_program(program, loader)?;
    let input = ixbf::decode_input(&artifact, input, loader)?;
    let limits = artifact.limits();
    let budget = small(artifact.max_steps(), u64::MAX)?;
    let parameters = [
      F128::new(
        small(&limits.locals, u64::MAX)?,
        small(&limits.continuations, u64::MAX)?,
      ),
      F128::new(budget, 0),
      F128::new(
        small(&limits.nat_bits, u64::MAX)?,
        small(&limits.byte_array_bytes, u64::MAX)?,
      ),
    ];
    ensure!(parameters[2].lo >= 128, "paged Nat128 semantic limit");
    let mut cells = PackedProgram::from_artifact(&artifact)?.cells;
    ensure!(
      input.source().len().div_ceil(32) as u64 <= 1 << 36,
      "paged input byte bank capacity"
    );
    for (i, bytes) in input.source().chunks(32).enumerate() {
      let mut cell = [0u8; 32];
      cell[..bytes.len()].copy_from_slice(bytes);
      cells.push((
        INPUT_BYTES + i as u64,
        [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])],
      ));
    }
    let constructors = artifact
      .constructors()
      .iter()
      .enumerate()
      .map(|(i, decl)| (&decl.id, i))
      .collect::<BTreeMap<_, _>>();
    let forest = input.values();
    let mut destinations = vec![None; forest.nodes().len()];
    for (index, &root) in forest.roots().iter().enumerate() {
      destinations[root] = Some(LOCALS + index as u64);
    }
    let mut heap = 0u64;
    // Reserve each field vector at its parent's preorder event. The streaming
    // input circuit uses this same allocation order and then fills its children.
    for (index, node) in forest.nodes().iter().enumerate() {
      let value = match &node.kind {
        ValueKind::Scalar(value) => scalar(input.source(), INPUT_BYTES, value)?,
        ValueKind::Erased => [F128::new(5, 0), F128::ZERO],
        ValueKind::Constructor(_) | ValueKind::PartialApplication(_) => {
          let (tag, reference) = match &node.kind {
            ValueKind::Constructor(id) => (
              7,
              *constructors.get(id).context("input constructor declaration")?,
            ),
            ValueKind::PartialApplication(function) => (9, *function),
            _ => unreachable!(),
          };
          let count = node.children.len() as u64;
          ensure!(
            count <= 64 && heap + count <= 1 << 36,
            "paged input heap capacity"
          );
          let pointer = if count == 0 { 0 } else { HEAP + heap };
          for &child in &node.children {
            ensure!(
              child > index && child < destinations.len(),
              "input value preorder"
            );
            ensure!(destinations[child].is_none(), "duplicate input parent");
            destinations[child] = Some(HEAP + heap);
            heap += 1;
          }
          [F128::new(tag, reference as u64), F128::new(pointer, count)]
        },
      };
      cells
        .push((destinations[index].context("input value destination")?, value));
    }
    let entry = artifact.entry();
    let function = &artifact.functions()[entry];
    let arity = small(&function.arity, 64)? as u8;
    ensure!(forest.roots().len() == arity as usize, "input entry arity");
    let mut state = initial_state(
      FrameState::eval(entry as u16, function.entry as u8, arity, 0).words(),
      budget,
    );
    state[HEAP_COUNT] = F128::new(heap, 0);
    let cell_count = cells.len();
    let memory = SparseMemory::from_cells(MemoryDepth::new(40)?, cells)?;
    Ok(Self { memory, state, parameters, cell_count })
  }
  pub fn machine(&self) -> Result<NativeMachine> {
    NativeMachine::new(self.state, 0, self.parameters)
  }
}
