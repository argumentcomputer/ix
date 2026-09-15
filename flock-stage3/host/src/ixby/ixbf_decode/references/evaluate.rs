//! Independent integer witness preparation; never called by a verifier.
use super::{
  super::grammar::{self, Phase},
  *,
};
use flock_prover::field::F128;

fn request(cap: RegistryCapacity, x: &[u128], bad: &mut bool) -> Vec<u128> {
  let phase = x[1] & 255;
  let commit = x[COMMITTED] & 1 != 0;
  let tag = x[TAG];
  let instruction = x[STATE];
  let f = &x[FIELDS..STATE];
  *bad |= x[COMMITTED] > 1 || tag > 17;
  *bad |= (tag != 15 && tag != 17 && !commit) || (tag == 17 && commit);
  *bad |= x[1] >> 40 != 0
    || phase > Phase::Done as u128
    || phase == Phase::Value as u128;
  *bad |= instruction > 7 || x[STATE + 2] >> cap.constructors() != 0;
  let active = |p: Phase| commit && phase == p as u128;
  let block = active(Phase::Block);
  let op = active(Phase::Operation);
  let tail_index = active(Phase::FunctionIndex);
  let count = active(Phase::OperandCount);
  let target = active(Phase::Target);
  let alternative = active(Phase::Alternative);
  for (enable, expected) in [
    (block, 5),
    (op, 12),
    (tail_index, 2),
    (count, 1),
    (target, 2),
    (alternative, 6),
  ] {
    *bad |= enable && tag != expected;
  }
  *bad |= (block && f[1] > 7) || (op && (instruction != 0 || f[0] > 7));
  *bad |= tail_index && instruction != 2;
  *bad |= count && ![0, 2, 3, 4].contains(&instruction);
  *bad |= alternative && instruction != 5;
  let targets = (x[1] >> 32) & 255;
  *bad |= target
    && (![0, 6, 7].contains(&instruction) || !(1..=2).contains(&targets));
  *bad |= target && instruction == 0 && targets != 1;

  let construct = op && f[0] == 2;
  let closure = op && f[0] == 4;
  let call = op && f[0] == 5;
  let self_call = op && f[0] == 6;
  let tail_call = count && instruction == 2;
  let tail_self = count && instruction == 3;
  let function = closure || call || self_call || tail_call || tail_self;
  let needs_owner = self_call || tail_self || target || alternative;
  let owner = x[grammar::FUNCTION_INDEX].wrapping_sub(1);
  *bad |= needs_owner && x[grammar::FUNCTION_INDEX] == 0;
  let mut out = x[STATE..STATE + STATE_WORDS].to_vec();
  if block {
    out = vec![f[1], 0, 0];
  }
  if tail_index {
    out[1] = f[0];
  }
  if alternative {
    let selected =
      usize::try_from(f[0]).ok().filter(|i| *i < cap.constructors());
    if let Some(index) = selected {
      let bit = 1u128 << index;
      *bad |= x[STATE + 2] & bit != 0;
      out[2] |= bit;
    } else {
      *bad = true;
    }
  }
  let mut facts = [0; FACTS];
  facts[CTOR_ENABLE] = u128::from(construct || alternative);
  facts[CTOR_INDEX] = if construct {
    f[2]
  } else if alternative {
    f[0]
  } else {
    0
  };
  facts[FUNCTION_ENABLE] = u128::from(function);
  facts[FUNCTION_INDEX] = if closure || call {
    f[2]
  } else if self_call || tail_self {
    owner
  } else if tail_call {
    x[STATE + 1]
  } else {
    0
  };
  facts[BLOCK_ENABLE] = u128::from(target || alternative);
  facts[BLOCK_OWNER] = if target || alternative { owner } else { 0 };
  facts[BLOCK_INDEX] = if target {
    f[0]
  } else if alternative {
    f[1]
  } else {
    0
  };
  facts[PARTIAL] = u128::from(closure);
  facts[ARGUMENTS] = if construct || closure || call || self_call {
    f[3]
  } else if tail_call || tail_self {
    f[0]
  } else {
    0
  };
  facts[CONSTRUCT] = u128::from(construct);
  facts[LOCALS] = if target || alternative { x[grammar::LOCALS] } else { 0 };
  facts[ADD_ONE] = u128::from(
    target && (instruction == 0 || (instruction == 6 && targets == 1)),
  );
  facts[ADD_CTOR] = u128::from(alternative);
  facts[LOCAL_LIMIT] =
    if target || alternative { x[grammar::LIMITS + 3] } else { 0 };
  out.extend(facts);
  out
}

fn check(x: &[u128], bad: &mut bool) {
  for i in [
    CTOR_ENABLE,
    FUNCTION_ENABLE,
    BLOCK_ENABLE,
    PARTIAL,
    CONSTRUCT,
    ADD_ONE,
    ADD_CTOR,
  ] {
    *bad |= x[i] > 1;
  }
  let enabled = |i: usize| x[i] & 1 != 0;
  let ctor = enabled(CTOR_ENABLE);
  let function = enabled(FUNCTION_ENABLE);
  let block = enabled(BLOCK_ENABLE);
  let partial = enabled(PARTIAL);
  let construct = enabled(CONSTRUCT);
  let add_one = enabled(ADD_ONE);
  let add_ctor = enabled(ADD_CTOR);
  *bad |= ctor != (construct || add_ctor) || (construct && add_ctor);
  *bad |= construct && function || partial && !function;
  *bad |= add_ctor && !block || add_one && (!block || add_ctor);
  for (on, indices) in [
    (ctor, vec![CTOR_INDEX]),
    (function, vec![FUNCTION_INDEX, PARTIAL]),
    (
      block,
      vec![BLOCK_OWNER, BLOCK_INDEX, LOCALS, ADD_ONE, ADD_CTOR, LOCAL_LIMIT],
    ),
    (construct || function, vec![ARGUMENTS]),
  ] {
    *bad |= !on && indices.into_iter().any(|i| x[i] != 0);
  }
  for (on, start) in [(ctor, CTOR), (function, FUNCTION), (block, BLOCK)] {
    *bad |= !on && x[start..start + 5].iter().any(|v| *v != 0);
  }
  *bad |= x[FUNCTION + 3..FUNCTION + 5].iter().any(|v| *v != 0);
  *bad |= x[BLOCK + 2..BLOCK + 5].iter().any(|v| *v != 0);
  *bad |= construct && x[ARGUMENTS] != x[CTOR + 4];
  *bad |= function
    && if partial {
      x[ARGUMENTS] >= x[FUNCTION]
    } else {
      x[ARGUMENTS] != x[FUNCTION]
    };
  let extra =
    if add_one { 1 } else { 0 } ^ if add_ctor { x[CTOR + 4] } else { 0 };
  let sum = x[LOCALS].checked_add(extra);
  *bad |= block
    && (sum.is_none() || sum != Some(x[BLOCK]) || x[BLOCK] > x[LOCAL_LIMIT]);
}

pub(super) fn evaluate(
  cap: RegistryCapacity,
  op: ReferenceOp,
  input: &[F128],
) -> Vec<F128> {
  let x: Vec<_> =
    input.iter().map(|w| u128::from(w.lo) | (u128::from(w.hi) << 64)).collect();
  let mut bad = false;
  let mut out = match op {
    ReferenceOp::Request => request(cap, &x, &mut bad),
    ReferenceOp::Check => {
      check(&x, &mut bad);
      Vec::new()
    },
  };
  out.push(u128::from(bad));
  out.into_iter().map(|n| F128::new(n as u64, (n >> 64) as u64)).collect()
}
