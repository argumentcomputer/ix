use super::*;
use crate::ixby::{
  auth_memory::{SparseMemory, multi::MultiAdvice},
  paged_code,
};
#[derive(Clone, Debug)]
pub struct ConstructorIdsAdvice {
  pub private: Vec<F128>,
  pub statement: ConstructorIdsStatement,
}
impl ConstructorIdsAdvice {
  /// Native advice only: all addresses, declared flags, comparisons and tree
  /// bindings are separately constrained by the compiled fixed circuit.
  pub fn new(memory: &mut SparseMemory, count: usize) -> Result<Self> {
    ensure!(
      memory.depth().bits() == 40 && count <= CONSTRUCTORS,
      "constructor IDs native capacities"
    );
    let root = memory.root();
    let statement = ConstructorIdsStatement::from_words(&[
      F128::new(count as u64, 0),
      root[0],
      root[1],
    ])?;
    let mut private = statement.words().to_vec();
    let mut updates = Vec::new();
    let mut ids = Vec::new();
    for i in 0..CONSTRUCTORS {
      let a = paged_code::CONSTRUCTORS + 3 * i as u64;
      let first = memory.value(a)?;
      let second = memory.value(a + 1)?;
      let id = [first[0], first[1], second[0], second[1]];
      private.extend(id);
      ids.push(id.map(|v| u128::from(v.lo) | (u128::from(v.hi) << 64)));
      updates.extend([(a, first), (a + 1, second)]);
    }
    let mut order = (0..CONSTRUCTORS).collect::<Vec<_>>();
    order.sort_by_key(|&i| (i >= count, ids[i]));
    let mut destination = vec![0; CONSTRUCTORS];
    for (to, from) in order.into_iter().enumerate() {
      destination[from] = to;
    }
    private.extend(plan().route(&destination)?);
    let update = memory.replace_many(updates)?;
    ensure!(
      update.initial_root == root && update.final_root == root,
      "constructor IDs read-only update"
    );
    let tree = MultiAdvice::new(capacity(), &update)?;
    private.extend(&tree.private[4 + 5 * CELLS..]);
    Ok(Self { private, statement })
  }
}
