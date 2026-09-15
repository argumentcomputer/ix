//! Independent original-wire encodings shared with header registry tests.
pub(super) use super::super::registry::fixtures::{
  Fixture, Function, Spec, base, encode, word,
};

pub(super) fn let_op(operation: &[u8]) -> Spec {
  let mut spec = base();
  let mut instruction = vec![0];
  instruction.extend(operation);
  instruction.push(1);
  spec.functions[0].blocks = vec![(0, instruction), (1, vec![1, 2])];
  spec
}
pub(super) fn call(op: u8, args: usize, arity: u128) -> Spec {
  let mut operation = vec![op, 1, args as u8];
  operation.extend(vec![2; args]);
  let mut spec = let_op(&operation);
  spec.functions.push(Function {
    arity,
    entry: 0,
    blocks: vec![(arity, vec![1, 2])],
  });
  spec
}
pub(super) fn alternatives(entries: &[(u8, u8)]) -> Spec {
  let mut spec = base();
  spec.constructors = vec![[1, 2, 3, 4, 0], [1, 2, 3, 5, 1]];
  let mut instruction = vec![5, 2, entries.len() as u8];
  for (ctor, target) in entries {
    instruction.extend([*ctor, *target]);
  }
  spec.functions[0].blocks = vec![(0, instruction), (1, vec![1, 2])];
  spec
}
pub(super) fn corpus() -> Vec<(&'static str, Spec)> {
  let mut out = vec![];
  for (name, spec) in [
    "return",
    "constructor",
    "owners",
    "changed",
    "forward-tail",
    "utf8",
    "nat4096",
    "wide-headers",
  ]
  .into_iter()
  .zip(super::super::registry::fixtures::corpus())
  {
    out.push((name, spec));
  }
  out.push(("copy", let_op(&[0, 2])));
  out.push(("primitive", let_op(&[1, 8, 1, 2])));
  let mut construct = let_op(&[2, 0, 1, 2]);
  construct.constructors = vec![[1, 2, 3, 4, 1]];
  out.push(("construct", construct));
  out.push(("project", let_op(&[3, 2, 0])));
  out.push(("closure", call(4, 1, 2)));
  out.push(("call", call(5, 1, 1)));
  out.push(("self-call", let_op(&[6, 0])));
  out.push(("apply", let_op(&[7, 2, 1, 2])));
  let mut tail_self = base();
  tail_self.functions[0].blocks[0].1 = vec![3, 0];
  out.push(("tail-self", tail_self));
  let mut tail_apply = base();
  tail_apply.functions[0].blocks[0].1 = vec![4, 2, 1, 2];
  out.push(("tail-apply", tail_apply));
  out.push(("alternatives", alternatives(&[(0, 0), (1, 1)])));
  let mut reset = alternatives(&[(0, 0)]);
  reset.functions[0].blocks[1] = (0, vec![5, 2, 1, 0, 1]);
  out.push(("alternative-reset", reset));
  let mut case_nat = base();
  case_nat.functions[0].blocks = vec![(0, vec![6, 2, 0, 1]), (1, vec![1, 2])];
  out.push(("case-nat", case_nat));
  let mut branch = base();
  branch.functions[0].blocks = vec![(0, vec![7, 2, 0, 1]), (0, vec![1, 2])];
  out.push(("branch", branch));
  let mut owned = base();
  owned.functions[0].blocks.push((0, vec![1, 2]));
  owned.functions.push(Function {
    arity: 2,
    entry: 0,
    blocks: vec![(2, vec![7, 2, 0, 1]), (2, vec![1, 2])],
  });
  out.push(("owned-target", owned));
  let mut wide = let_op(&[0, 2]);
  wide.wide_limits = true;
  wide.functions[0].arity = u128::MAX - 1;
  wide.functions[0].blocks[0].0 = u128::MAX - 1;
  wide.functions[0].blocks[1].0 = u128::MAX;
  out.push(("wide-successor", wide));
  out
}

/// Every negative remains a complete canonical grammar and passes header
/// registration. The native structural validator rejects its references.
pub(super) fn invalid() -> Vec<(&'static str, Spec)> {
  let mut out = vec![
    ("call-arity", call(5, 1, 2)),
    ("saturated-closure", call(4, 1, 1)),
    ("oversaturated-closure", call(4, 2, 1)),
  ];
  let mut construct = let_op(&[2, 0, 1, 2]);
  construct.constructors = vec![[1, 2, 3, 4, 0]];
  out.push(("constructor-arity", construct));
  out.push(("self-arity", let_op(&[6, 1, 2])));
  let mut tail = base();
  tail.functions.push(tail.functions[0].clone());
  tail.functions[0].blocks[0].1 = vec![2, 1, 1, 2];
  out.push(("tail-arity", tail));
  let mut tail_self = base();
  tail_self.functions[0].blocks[0].1 = vec![3, 1, 2];
  out.push(("tail-self-arity", tail_self));
  let mut frame = let_op(&[0, 2]);
  frame.functions[0].blocks[1].0 = 0;
  out.push(("let-frame", frame));
  out.push(("duplicate-alternative", alternatives(&[(0, 0), (0, 0)])));
  out.push(("case-frame", alternatives(&[(1, 0)])));
  let mut nat = base();
  nat.functions[0].blocks = vec![(0, vec![6, 2, 0, 1]), (0, vec![1, 2])];
  out.push(("nat-successor-frame", nat));
  let mut nat_zero = base();
  nat_zero.functions[0].blocks = vec![(0, vec![6, 2, 1, 1]), (1, vec![1, 2])];
  out.push(("nat-zero-frame", nat_zero));
  let mut branch = base();
  branch.functions[0].blocks = vec![(0, vec![7, 2, 0, 1]), (1, vec![1, 2])];
  out.push(("branch-frame", branch));
  let mut dead = call(5, 1, 2);
  dead.functions[0].blocks[1].0 = 0;
  dead.functions[0].entry = 1;
  out.push(("dead-call", dead));
  let mut wide = call(5, 1, 1u128 << 100);
  wide.wide_limits = true;
  out.push(("wide-call-arity", wide));
  out
}
