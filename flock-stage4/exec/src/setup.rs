//! Proof-free ownership boundary for the complete root-conditional replay.
//! This is a typed verifier-topology compiler, not FFLONK preprocessing and
//! not a terminal acceptance key. It accepts no guest, statement, or proof.

use crate::{
  ExecReplayWitness,
  blueprint::{
    self, BooleanBlueprint, FoldBlueprint, MainBlueprint, PcsBlueprint,
  },
  native::compile_exec_binding,
  replay::Stage4TranscriptOpV1 as Op,
};
use anyhow::Result;
use ix_stage4_trace::{ExecBindingV0, ExecCommitmentsV0, F128WiringTraceV1};
use ixby_flock::ixby::exec::CompiledExec;

/// Distinct component identities of one fixed replay compiler output. These
/// are diagnostics, not signatures or independent authorization to use a key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExecReplayIdentitiesV0 {
  pub exec_setup: [u8; 32],
  pub binding: [u8; 32],
  pub wiring: [u8; 32],
  pub boolean: [u8; 32],
  pub merged_pcs: [u8; 32],
  pub multipoint: [u8; 32],
  pub inner_ligerito: [u8; 32],
  pub main_operations: [u8; 32],
  pub main_hash: [u8; 32],
  pub accumulator_operations: [u8; 32],
  pub accumulator_hash: [u8; 32],
  pub matrices: [u8; 32],
  pub structure: [u8; 32],
  pub jagged: [u8; 32],
}

impl ExecReplayIdentitiesV0 {
  pub fn digest(self) -> [u8; 32] {
    let mut hash = blake3::Hasher::new();
    hash.update(b"IxBy/Stage4/compiled-replay/v0\0");
    for component in [
      self.exec_setup,
      self.binding,
      self.wiring,
      self.boolean,
      self.merged_pcs,
      self.multipoint,
      self.inner_ligerito,
      self.main_operations,
      self.main_hash,
      self.accumulator_operations,
      self.accumulator_hash,
      self.matrices,
      self.structure,
      self.jagged,
    ] {
      hash.update(&component);
    }
    *hash.finalize().as_bytes()
  }
}

/// Immutable, setup-borrowed topology. Private fields prevent constructing it
/// from a prover-selected export or replacing one phase after compilation.
pub struct CompiledExecReplay<'a> {
  pub(crate) setup: &'a CompiledExec,
  pub(crate) binding: ExecBindingV0,
  pub(crate) wiring: F128WiringTraceV1,
  pub(crate) boolean: BooleanBlueprint,
  pub(crate) pcs: PcsBlueprint,
  pub(crate) main: MainBlueprint,
  pub(crate) folds: FoldBlueprint,
  identities: ExecReplayIdentitiesV0,
}

impl<'a> CompiledExecReplay<'a> {
  pub fn exec_setup(&self) -> &'a CompiledExec {
    self.setup
  }
  pub fn identities(&self) -> ExecReplayIdentitiesV0 {
    self.identities
  }
  pub fn binding(&self) -> &ExecBindingV0 {
    &self.binding
  }
  pub fn replay(
    &self,
    commitments: ExecCommitmentsV0,
    proof_bytes: &[u8],
  ) -> Result<ExecReplayWitness<'a>> {
    crate::native::replay_compiled(self, commitments, proof_bytes)
  }
}

/// Compile once before witnesses exist. The only input is the already-owned
/// generic interpreter/protocol configuration and its fixed public template.
pub fn compile_exec_replay(
  setup: &CompiledExec,
) -> Result<CompiledExecReplay<'_>> {
  let binding = compile_exec_binding(setup)?;
  let wiring = blueprint::compile_wiring(setup)?;
  let boolean = blueprint::compile_boolean(setup)?;
  let pcs = blueprint::compile_pcs(setup, &wiring, &boolean)?;
  let main = blueprint::compile_transcript(setup, &boolean, &pcs)?;
  let folds = blueprint::compile_folds(setup, &wiring, &boolean, &pcs)?;
  let identities = ExecReplayIdentitiesV0 {
    exec_setup: setup.identities().digest(),
    binding: binding.topology_digest(),
    wiring: wiring.topology_digest(),
    boolean: boolean.trace.topology_digest(),
    merged_pcs: pcs.frontend.topology_digest(),
    multipoint: pcs.multipoint.topology_digest(),
    inner_ligerito: main.inner.topology_digest(),
    main_operations: operations_digest(&main.operations),
    main_hash: main.hash.topology_digest(),
    accumulator_operations: operations_digest(&folds.operations),
    accumulator_hash: folds.hash.topology_digest(),
    matrices: folds.matrices.topology_digest(),
    structure: folds.structure.topology_digest(),
    jagged: folds.jagged.topology_digest(),
  };
  Ok(CompiledExecReplay {
    setup,
    binding,
    wiring,
    boolean,
    pcs,
    main,
    folds,
    identities,
  })
}

fn operations_digest(ops: &[Op]) -> [u8; 32] {
  fn length(hash: &mut blake3::Hasher, n: u64) {
    hash.update(&n.to_le_bytes());
  }
  fn bytes(hash: &mut blake3::Hasher, data: &[u8]) {
    length(hash, data.len() as u64);
    hash.update(data);
  }
  fn walk(hash: &mut blake3::Hasher, ops: &[Op]) {
    length(hash, ops.len() as u64);
    for op in ops {
      let tag = match op {
        Op::Label(_) => 0,
        Op::ObserveScalar => 1,
        Op::ObserveSlice(_) => 2,
        Op::ObserveBytes(_) => 3,
        Op::SqueezeScalar => 4,
        Op::SqueezeSlice(_) => 5,
        Op::Forked { .. } => 6,
        Op::Merge { .. } => 7,
        Op::Pow { .. } => 8,
        Op::LegacyPow { .. } => 9,
      };
      hash.update(&[tag]);
      match op {
        Op::Label(label) => bytes(hash, label),
        Op::ObserveSlice(count)
        | Op::ObserveBytes(count)
        | Op::SqueezeSlice(count) => length(hash, *count),
        Op::Forked { label, ops } => {
          bytes(hash, label);
          walk(hash, ops);
        },
        Op::Merge { fork } => length(hash, *fork),
        Op::Pow { bits } | Op::LegacyPow { bits } => {
          hash.update(&bits.to_le_bytes());
        },
        _ => {},
      }
    }
  }
  let mut hash = blake3::Hasher::new();
  hash.update(b"IxBy/Stage4/operation-tree/v0\0");
  walk(&mut hash, ops);
  *hash.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::collections::BTreeSet;

  #[test]
  fn compiled_identity_binds_each_distinct_component_in_order() {
    let original = ExecReplayIdentitiesV0 {
      exec_setup: [0; 32],
      binding: [0; 32],
      wiring: [0; 32],
      boolean: [0; 32],
      merged_pcs: [0; 32],
      multipoint: [0; 32],
      inner_ligerito: [0; 32],
      main_operations: [0; 32],
      main_hash: [0; 32],
      accumulator_operations: [0; 32],
      accumulator_hash: [0; 32],
      matrices: [0; 32],
      structure: [0; 32],
      jagged: [0; 32],
    };
    let mut digests = BTreeSet::from([original.digest()]);
    for index in 0..14 {
      let mut changed = original;
      let components = [
        &mut changed.exec_setup,
        &mut changed.binding,
        &mut changed.wiring,
        &mut changed.boolean,
        &mut changed.merged_pcs,
        &mut changed.multipoint,
        &mut changed.inner_ligerito,
        &mut changed.main_operations,
        &mut changed.main_hash,
        &mut changed.accumulator_operations,
        &mut changed.accumulator_hash,
        &mut changed.matrices,
        &mut changed.structure,
        &mut changed.jagged,
      ];
      components[index][31] = 1;
      assert!(digests.insert(changed.digest()), "component {index}");
    }
    assert_eq!(digests.len(), 15);
  }

  #[test]
  fn operation_identity_binds_kinds_lengths_labels_and_tree_boundaries() {
    let operations = [
      Op::Label(vec![]),
      Op::Label(vec![0]),
      Op::Label(vec![0, 0]),
      Op::ObserveScalar,
      Op::ObserveSlice(1),
      Op::ObserveSlice(2),
      Op::ObserveBytes(1),
      Op::ObserveBytes(2),
      Op::SqueezeScalar,
      Op::SqueezeSlice(1),
      Op::SqueezeSlice(2),
      Op::Forked { label: vec![], ops: vec![] },
      Op::Forked { label: vec![0], ops: vec![] },
      Op::Forked { label: vec![], ops: vec![Op::ObserveScalar] },
      Op::Merge { fork: 0 },
      Op::Merge { fork: 1 },
      Op::Pow { bits: 0 },
      Op::Pow { bits: 1 },
      Op::LegacyPow { bits: 0 },
      Op::LegacyPow { bits: 1 },
    ];
    let mut digests = BTreeSet::from([operations_digest(&[])]);
    for op in operations {
      assert!(digests.insert(operations_digest(&[op])));
    }
    // Same labels and leaves with different length framing, ordering, or
    // nesting must not share an identity. This tests encoding, not validity
    // of these deliberately minimal transcript fragments.
    for ops in [
      vec![Op::Label(vec![]), Op::Label(vec![0])],
      vec![Op::Label(vec![0]), Op::Label(vec![])],
      vec![Op::Forked { label: vec![], ops: vec![] }, Op::ObserveScalar],
      vec![Op::ObserveScalar, Op::Forked { label: vec![], ops: vec![] }],
      vec![Op::Pow { bits: 0 }, Op::SqueezeScalar],
      vec![Op::Pow { bits: 0 }, Op::SqueezeSlice(1)],
      vec![Op::Forked {
        label: vec![],
        ops: vec![Op::Forked { label: vec![], ops: vec![] }],
      }],
      vec![
        Op::Forked { label: vec![], ops: vec![] },
        Op::Forked { label: vec![], ops: vec![] },
      ],
    ] {
      assert!(digests.insert(operations_digest(&ops)));
    }
    assert_eq!(digests.len(), 29);
  }
}
