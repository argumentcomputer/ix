use super::*;
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{LeafWires, MultiMemorySlots, MultiProofWires},
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::PermutationSlots,
    paged_code,
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::SlotId;
pub(super) struct Emission {
  pub gates: [(SlotId, ConstructorIdGate); 2],
  pub permutation: PermutationSlots,
  pub tree: MultiMemorySlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let tree =
    MultiMemorySlots::declare(&mut b, NU, MemoryDepth::new(40).unwrap())
      .unwrap();
  let gates = [ConstructorIdKind::Source, ConstructorIdKind::Audit].map(|k| {
    let g = ConstructorIdGate::new(NU, k).unwrap();
    (b.slot(g.clone()), g)
  });
  let permutation = PermutationSlots::declare(&mut b, 5).unwrap();
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::ONE);
  let count = b.input();
  let root: [_; 2] = std::array::from_fn(|_| b.input());
  for w in [count].into_iter().chain(root) {
    b.publish(w);
  }
  // Leaves have fixed addresses and exactly the same old/new value wires.
  let mut leaves = Vec::new();
  let mut records = Vec::new();
  for i in 0..CONSTRUCTORS {
    let index = b.fixed_public_input(F128::new(i as u64, 0));
    let values: [_; 4] = std::array::from_fn(|_| b.input());
    for half in 0..2 {
      let address = b.fixed_public_input(F128::new(
        paged_code::CONSTRUCTORS + 3 * i as u64 + half as u64,
        0,
      ));
      let value = [values[2 * half], values[2 * half + 1]];
      leaves.push(LeafWires { address, old: value, new: value });
    }
    let out = b.gate(
      gates[0].0,
      &[count, index].into_iter().chain(values).collect::<Vec<_>>(),
    );
    b.connect(out[5], zero);
    records.push(out[..5].to_vec());
  }
  let switches = (0..plan().switches()).map(|_| b.input()).collect::<Vec<_>>();
  let ordered = permutation.permute(&mut b, plan(), &records, &switches);
  let mut previous = vec![zero; 5];
  for (i, record) in ordered.into_iter().enumerate() {
    let out = b.gate(
      gates[1].0,
      &previous
        .into_iter()
        .chain(record.clone())
        .chain([if i == 0 { one } else { zero }])
        .collect::<Vec<_>>(),
    );
    b.connect(out[0], zero);
    previous = record;
  }
  let mut proof = MultiProofWires {
    leaves,
    frontier: (0..capacity().frontier())
      .map(|_| crate::ixby::auth_memory::multi::FrontierWires {
        enabled: b.input(),
        position: b.input(),
        hash: std::array::from_fn(|_| b.input()),
      })
      .collect(),
    parents: (0..PARENTS)
      .map(|_| crate::ixby::auth_memory::multi::ParentWires {
        enabled: b.input(),
        position: b.input(),
        old_children: std::array::from_fn(|_| {
          std::array::from_fn(|_| b.input())
        }),
        new_children: std::array::from_fn(|_| {
          std::array::from_fn(|_| b.input())
        }),
      })
      .collect(),
    switches: Vec::new(),
  };
  proof.switches =
    (0..capacity().plan().switches()).map(|_| b.input()).collect();
  tree.check(&mut b, [root, root], &proof);
  let (inputs, public) = b.finish();
  Emission { gates, permutation, tree, inputs, public }
}
