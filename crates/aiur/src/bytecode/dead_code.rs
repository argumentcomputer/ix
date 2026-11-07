//! Execution liveness after validation. The original bytecode and circuit stay
//! intact. Empty copies stand in for omitted instructions so PCs, hint sites,
//! error locations, and logical instruction counts retain their meanings.
use super::{Function, Instruction};

fn contains(live: &[u64], register: usize) -> bool {
  live.get(register / 64).is_some_and(|word| word & (1 << (register % 64)) != 0)
}

fn set(live: &mut [u64], register: usize, value: bool) {
  // Unreachable instructions may contain arbitrary register indices.
  if let Some(word) = live.get_mut(register / 64) {
    let bit = 1 << (register % 64);
    if value {
      *word |= bit;
    } else {
      *word &= !bit;
    }
  }
}

fn reads(live: &mut [u64], registers: &[usize]) {
  for &register in registers {
    set(live, register, true);
  }
}

fn writes(live: &mut [u64], registers: &[usize]) {
  for &register in registers {
    set(live, register, false);
  }
}

fn nop() -> Instruction {
  Instruction::Copy { dest: vec![], source: vec![] }
}

pub(super) fn eliminate<F>(function: &mut Function, inverses: &[Option<F>]) {
  let empty = vec![0u64; function.registers.div_ceil(64)];
  let mut before = vec![empty.clone(); function.code.len() + 1];
  // Validated intra-function control flow is forward-only. Union successor
  // liveness before processing each instruction, including both branch arms.
  for pc in (0..function.code.len()).rev() {
    use Instruction::*;
    let mut live = match &function.code[pc] {
      Ret { .. } | Fail { .. } => empty.clone(),
      Jump { target } => before.get(*target).unwrap_or(&empty).clone(),
      _ => before[pc + 1].clone(),
    };
    if let Branch { tests, otherwise } = &function.code[pc]
      && !tests.is_empty()
      && let Some(other) = before.get(*otherwise)
    {
      for (live, other) in live.iter_mut().zip(other) {
        *live |= other;
      }
    }
    let op = &mut function.code[pc];
    match op {
      Literal { dest, .. } => {
        if contains(&live, *dest) {
          set(&mut live, *dest, false);
        } else {
          *op = nop();
        }
      },
      Copy { dest, source } if dest.len() == source.len() => {
        // Copies read all sources before writing. For duplicate
        // destinations only the last assignment is observable.
        let mut kept = Vec::new();
        for (&d, &s) in dest.iter().zip(source.iter()).rev() {
          if contains(&live, d) {
            set(&mut live, d, false);
            kept.push((d, s));
          }
        }
        kept.reverse();
        (*dest, *source) = kept.into_iter().unzip();
        reads(&mut live, source);
      },
      Copy { dest, source } => {
        // Malformed unreachable copies must not panic the linker.
        writes(&mut live, dest);
        reads(&mut live, source);
      },
      Neg { dest, source } => {
        if contains(&live, *dest) {
          set(&mut live, *dest, false);
          set(&mut live, *source, true);
        } else {
          *op = nop();
        }
      },
      Binary { dest, operator, left, right } => {
        // Division can fail even if unused. Only a cached, nonzero
        // constant denominator makes it safe to discard.
        let may_fail = matches!(operator, super::Binary::Div)
          && inverses.get(pc).is_none_or(Option::is_none);
        if contains(&live, *dest) || may_fail {
          set(&mut live, *dest, false);
          reads(&mut live, &[*left, *right]);
        } else {
          *op = nop();
        }
      },
      AssertEq { runtime_check: false, .. } => *op = nop(),
      AssertEq { left, right, .. } => {
        reads(&mut live, left);
        reads(&mut live, right);
      },
      Guard { tests, .. } | Branch { tests, .. } => {
        for (register, _) in tests {
          set(&mut live, *register, true);
        }
      },
      Call { args, dest, .. } => {
        writes(&mut live, dest);
        reads(&mut live, args);
      },
      Store { value, dest, .. } => {
        set(&mut live, *dest, false);
        reads(&mut live, value);
      },
      Load { pointer, dest, .. } => {
        writes(&mut live, dest);
        set(&mut live, *pointer, true);
      },
      Hint { key, dest, .. } => {
        writes(&mut live, dest);
        reads(&mut live, key);
      },
      Ret { value } => reads(&mut live, value),
      Jump { .. } | Fail { .. } => {},
    }
    before[pc] = live;
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    bytecode::{Program, Type},
    hints::HintChannels,
  };
  use serde_json::{Value, json};

  fn program(code: Value, registers: usize) -> Program {
    serde_json::from_value(json!({
        "version": 2, "modulus": 65537, "enums": [], "tables": [], "maps": [],
        "functions": [{"name": "root", "params": [{"kind": "field"}],
            "result": {"kind": "field"}, "registers": registers, "code": code}],
        "entries": [{"name": "root", "function": 0,
            "inputs": [{"kind": "field"}], "output": {"kind": "field"}}]
    }))
    .unwrap()
  }

  #[test]
  fn dead_arithmetic_is_removed_but_query_hint_and_rom_effects_remain() {
    let mut source = program(
      json!([
          {"op": "literal", "dest": 1, "value": 9},
          {"op": "binary", "operator": "mul", "dest": 2, "left": 0, "right": 0},
          {"op": "literal", "dest": 3, "value": 256},
          {"op": "binary", "operator": "div", "dest": 4, "left": 2, "right": 3},
          {"op": "assert_eq", "left": [4], "right": [1], "runtime_check": false},
          {"op": "call", "function": 1, "args": [0], "dest": [5]},
          {"op": "hint", "channel": "identity", "type": {"kind": "field"},
              "key_type": {"kind": "field"}, "key": [0], "dest": [6]},
          {"op": "store", "type": {"kind": "field"}, "value": [6], "dest": 7},
          {"op": "load", "type": {"kind": "field"}, "pointer": 7, "dest": [8]},
          {"op": "call", "function": 2, "args": [8], "dest": [9]},
          {"op": "assert_eq", "left": [5], "right": [9], "runtime_check": false},
          {"op": "ret", "value": [0]}
      ]),
      10,
    );
    source.functions.push(
      serde_json::from_value(json!({
          "name": "identity", "params": [{"kind": "field"}],
          "result": {"kind": "field"}, "registers": 1,
          "code": [{"op": "ret", "value": [0]}]
      }))
      .unwrap(),
    );
    source.tables = serde_json::from_value(json!([
            {"name": "input", "type": {"kind": "tuple", "items": [{"kind": "field"}]}, "rows": [[3], [48]]},
            {"name": "output", "type": {"kind": "field"}, "rows": [[3], [48]]}
        ])).unwrap();
    source.maps = serde_json::from_value(json!([
        {"name": "table_identity", "params": [{"kind": "field"}],
            "result": {"kind": "field"}, "input": 0, "output": 1}
    ]))
    .unwrap();
    let deferred = source.clone().check().unwrap();
    for op in &mut source.functions[0].code {
      if let Instruction::AssertEq { runtime_check, .. } = op {
        *runtime_check = true;
      }
    }
    let checked = source.check().unwrap();
    assert!(deferred.execution_functions[0].code.iter().all(|op| !matches!(
      op,
      Instruction::Binary { .. } | Instruction::AssertEq { .. }
    )));
    assert!(deferred.program.functions[0].code.iter().any(|op| matches!(
      op,
      Instruction::AssertEq { runtime_check: false, .. }
    )));
    let mut channels = HintChannels::new();
    channels
      .insert("identity", Type::Field, Type::Field, |input, output| {
        output.copy_from_slice(input);
        Ok(())
      })
      .unwrap();
    let deferred = deferred.prepare_hint_channels(&[], &channels).unwrap();
    let checked = checked.prepare_hint_channels(&[], &channels).unwrap();
    let actual = deferred.execute("root", vec![48]).unwrap();
    let expected = checked.execute("root", vec![48]).unwrap();
    assert_eq!(actual.output, expected.output);
    assert_eq!(actual.queries, expected.queries);
    assert_eq!(actual.instructions, expected.instructions);
    assert_eq!(
      serde_json::to_value(&actual.memory).unwrap(),
      serde_json::to_value(&expected.memory).unwrap()
    );
    assert_eq!(actual.queries.len(), 3);
    assert_eq!(actual.memory.get(0).unwrap().multiplicity, 2);
    assert_eq!(deferred.execute("root", vec![3]).unwrap().output, [3]);
    assert_eq!(checked.execute("root", vec![3]).unwrap_err().instruction, 4);
  }

  #[test]
  fn deferred_assertions_do_not_hide_division_errors() {
    let source = program(
      json!([
          {"op": "literal", "dest": 1, "value": 1},
          {"op": "binary", "operator": "div", "dest": 2, "left": 1, "right": 0},
          {"op": "assert_eq", "left": [2], "right": [1], "runtime_check": false},
          {"op": "ret", "value": [0]}
      ]),
      3,
    );
    let checked = source.clone().check().unwrap();
    assert_eq!(checked.execute("root", vec![2]).unwrap().output, [2]);
    assert_eq!(checked.execute("root", vec![0]).unwrap_err().instruction, 1);
    // A provably nonzero denominator permits removal, including its inputs.
    let mut constant = source.clone();
    if let Instruction::Binary { right, .. } =
      &mut constant.functions[0].code[1]
    {
      *right = 1;
    }
    let checked = constant.check().unwrap();
    assert!(
      checked.execution_functions[0]
        .code
        .iter()
        .all(|op| !matches!(op, Instruction::Binary { .. }))
    );
    assert_eq!(checked.execute("root", vec![0]).unwrap().output, [0]);
    // A constant zero denominator still fails even though the result is dead.
    let mut zero = source;
    if let Instruction::Literal { value, .. } = &mut zero.functions[0].code[0] {
      *value = 0;
    }
    if let Instruction::Binary { right, .. } = &mut zero.functions[0].code[1] {
      *right = 1;
    }
    assert_eq!(
      zero.check().unwrap().execute("root", vec![2]).unwrap_err().instruction,
      1
    );
  }

  #[test]
  fn both_branch_successors_and_legacy_assertions_are_live() {
    let source = program(
            json!([
                {"op": "literal", "dest": 1, "value": 7},
                {"op": "literal", "dest": 2, "value": 13},
                {"op": "binary", "operator": "mul", "dest": 3, "left": 1, "right": 2},
                {"op": "assert_eq", "left": [3], "right": [0], "runtime_check": false},
                {"op": "branch", "tests": [[0, 0]], "otherwise": 7},
                {"op": "copy", "dest": [3], "source": [1]},
                {"op": "jump", "target": 8},
                {"op": "copy", "dest": [3, 3], "source": [1, 2]},
                {"op": "ret", "value": [3]}
            ]),
            4,
        )
        .check()
        .unwrap();
    assert_eq!(source.execute("root", vec![0]).unwrap().output, [7]);
    assert_eq!(source.execute("root", vec![5]).unwrap().output, [13]);
    assert!(!matches!(
      source.execution_functions[0].code[2],
      Instruction::Binary { .. }
    ));

    let legacy = program(
      json!([
          {"op": "literal", "dest": 1, "value": 4},
          {"op": "binary", "operator": "mul", "dest": 2, "left": 0, "right": 0},
          {"op": "assert_eq", "left": [2], "right": [1]},
          {"op": "ret", "value": [0]}
      ]),
      3,
    )
    .check()
    .unwrap();
    assert_eq!(legacy.execute("root", vec![2]).unwrap().output, [2]);
    assert_eq!(legacy.execute("root", vec![3]).unwrap_err().instruction, 2);
  }
}
