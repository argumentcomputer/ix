//! Independent, straightforward crypto-v0 encoder for constraint tests. It
//! performs NO admission and can serialize malformed operands/declarations.
//! Golden and pure Lean vectors pin its byte order and tags separately.

use super::ProgramCapacities;
use crate::ixby::value::{
  BOOL_TAG, ERASED_TAG, EXT_TAG, FIELD_TAG, ValueWords, WORD32_TAG,
};
use flock_prover::field::F128;

#[derive(Clone, Debug)]
pub(crate) enum Value {
  Bool(u8),
  Word(u32),
  Field(u64),
  Ext(u64, u64),
  Erased,
}

impl Value {
  pub(crate) fn words(&self) -> ValueWords {
    let (tag, lo, hi) = match *self {
      Self::Bool(x) => (BOOL_TAG, u64::from(x), 0),
      Self::Word(x) => (WORD32_TAG, u64::from(x), 0),
      Self::Field(x) => (FIELD_TAG, x, 0),
      Self::Ext(x, y) => (EXT_TAG, x, y),
      Self::Erased => (ERASED_TAG, 0, 0),
    };
    [F128::new(tag, 0), F128::new(lo, hi)]
  }
  fn scalar(&self, bytes: &mut Vec<u8>) {
    match *self {
      Self::Bool(x) => bytes.extend([0, x]),
      Self::Word(x) => {
        bytes.push(1);
        bytes.extend(x.to_le_bytes());
      },
      Self::Field(x) => {
        bytes.push(2);
        bytes.extend(x.to_le_bytes());
      },
      Self::Ext(x, y) => {
        bytes.push(3);
        bytes.extend(x.to_le_bytes());
        bytes.extend(y.to_le_bytes());
      },
      Self::Erased => panic!("erased is a value/operand, not a scalar"),
    }
  }
}

#[derive(Clone, Debug)]
pub(crate) enum Operand {
  Local(u32),
  Literal(Value),
}

impl Operand {
  fn encode(&self, bytes: &mut Vec<u8>) {
    match self {
      Self::Local(index) => {
        bytes.push(0);
        bytes.extend(index.to_le_bytes());
      },
      Self::Literal(Value::Erased) => bytes.push(2),
      Self::Literal(value) => {
        bytes.push(1);
        value.scalar(bytes);
      },
    }
  }
  fn words(&self) -> [F128; 3] {
    match self {
      Self::Local(index) => [meta(1, *index, 0, 0), F128::ZERO, F128::ZERO],
      Self::Literal(value) => {
        let [tag, payload] = value.words();
        [meta(2, 0, 0, 0), tag, payload]
      },
    }
  }
}

#[derive(Clone, Debug)]
pub(crate) enum Instruction {
  Copy(Operand, u32),
  Primitive(u8, Vec<Operand>, u32),
  Call(Option<u32>, Vec<Operand>, u32),
  Ret(Operand),
  Tail(Option<u32>, Vec<Operand>),
  Branch(Operand, u32, u32),
}

fn vector(bytes: &mut Vec<u8>, operands: &[Operand]) {
  bytes.extend((operands.len() as u32).to_le_bytes());
  for operand in operands {
    operand.encode(bytes);
  }
}

impl Instruction {
  fn encode(&self, bytes: &mut Vec<u8>) {
    match self {
      Self::Copy(operand, target) => {
        bytes.extend([0, 0]);
        operand.encode(bytes);
        bytes.extend(target.to_le_bytes());
      },
      Self::Primitive(op, operands, target) => {
        bytes.extend([0, 1, *op]);
        vector(bytes, operands);
        bytes.extend(target.to_le_bytes());
      },
      Self::Call(callee, operands, target) => {
        bytes.extend([0, if callee.is_some() { 5 } else { 6 }]);
        if let Some(callee) = callee {
          bytes.extend(callee.to_le_bytes());
        }
        vector(bytes, operands);
        bytes.extend(target.to_le_bytes());
      },
      Self::Ret(operand) => {
        bytes.push(1);
        operand.encode(bytes);
      },
      Self::Tail(callee, operands) => {
        bytes.push(if callee.is_some() { 2 } else { 3 });
        if let Some(callee) = callee {
          bytes.extend(callee.to_le_bytes());
        }
        vector(bytes, operands);
      },
      Self::Branch(operand, yes, no) => {
        bytes.push(6);
        operand.encode(bytes);
        bytes.extend(yes.to_le_bytes());
        bytes.extend(no.to_le_bytes());
      },
    }
  }
  fn words(
    &self,
    locals: u32,
    function: u32,
    operand_capacity: usize,
  ) -> Vec<F128> {
    let (kind, target, alternative, callee, primitive, operands) = match self {
      Self::Copy(operand, target) => {
        (1, *target, 0, 0, 0, vec![operand.clone()])
      },
      Self::Primitive(primitive, operands, target) => {
        (2, *target, 0, 0, u32::from(*primitive), operands.clone())
      },
      Self::Call(callee, operands, target) => {
        (3, *target, 0, callee.unwrap_or(function), 0, operands.clone())
      },
      Self::Ret(operand) => (4, 0, 0, 0, 0, vec![operand.clone()]),
      Self::Tail(callee, operands) => {
        (5, 0, 0, callee.unwrap_or(function), 0, operands.clone())
      },
      Self::Branch(operand, yes, no) => {
        (6, *yes, *no, 0, 0, vec![operand.clone()])
      },
    };
    let mut result = vec![
      meta(locals, kind, target, alternative),
      meta(callee, primitive, operands.len() as u32, 0),
    ];
    for operand in operands {
      result.extend(operand.words());
    }
    result.resize(2 + 3 * operand_capacity, F128::ZERO);
    result
  }
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionImage {
  pub arity: u32,
  pub entry: u32,
  pub blocks: Vec<(u32, Instruction)>,
}

pub(crate) fn program(entry: u32, functions: &[FunctionImage]) -> Vec<u8> {
  let mut bytes = b"IXBY\0\0\0\0".to_vec();
  bytes.extend(entry.to_le_bytes());
  bytes.extend(0u32.to_le_bytes());
  bytes.extend((functions.len() as u32).to_le_bytes());
  for function in functions {
    bytes.extend(function.arity.to_le_bytes());
    bytes.extend(function.entry.to_le_bytes());
    bytes.extend((function.blocks.len() as u32).to_le_bytes());
    for (locals, instruction) in &function.blocks {
      bytes.extend(locals.to_le_bytes());
      instruction.encode(&mut bytes);
    }
  }
  bytes
}

pub(crate) fn program_table(
  capacity: ProgramCapacities,
  entry: u32,
  functions: &[FunctionImage],
) -> Vec<F128> {
  let layout = capacity.layout();
  let mut words = vec![F128::ZERO; layout.words()];
  words[0] = meta(entry, functions.len() as u32, 0, 0);
  for (index, function) in functions.iter().enumerate() {
    words[layout.function_word(index)] =
      meta(function.arity, function.entry, function.blocks.len() as u32, 0);
    for (block, (locals, instruction)) in function.blocks.iter().enumerate() {
      let start = layout.block_word(index, block);
      words[start..start + layout.block_words()].copy_from_slice(
        &instruction.words(*locals, index as u32, capacity.operands),
      );
    }
  }
  words
}

pub(crate) fn input(values: &[Value]) -> Vec<u8> {
  let mut bytes = b"IXBI\0\0\0\0".to_vec();
  bytes.extend((values.len() as u32).to_le_bytes());
  for value in values {
    if matches!(value, Value::Erased) {
      bytes.push(3);
    } else {
      bytes.push(0);
      value.scalar(&mut bytes);
    }
  }
  bytes
}

pub(crate) fn advice(capacity: usize, bytes: &[u8]) -> Vec<F128> {
  assert!(bytes.len() <= capacity);
  let mut words = vec![F128::ZERO; 1 + capacity.div_ceil(16)];
  words[0] = F128::new(bytes.len() as u64, 0);
  for (index, byte) in bytes.iter().enumerate() {
    let word = &mut words[1 + index / 16];
    if index % 16 < 8 {
      word.lo |= u64::from(*byte) << (8 * (index % 8));
    } else {
      word.hi |= u64::from(*byte) << (8 * (index % 8));
    }
  }
  words
}

pub(crate) fn meta(a: u32, b: u32, c: u32, d: u32) -> F128 {
  F128::new(
    u64::from(a) | (u64::from(b) << 32),
    u64::from(c) | (u64::from(d) << 32),
  )
}

pub(crate) fn output(value: &Value) -> Vec<u8> {
  let mut bytes = b"IXBO\0\0\0\0".to_vec();
  if matches!(value, Value::Erased) {
    bytes.push(3);
  } else {
    bytes.push(0);
    value.scalar(&mut bytes);
  }
  bytes
}
