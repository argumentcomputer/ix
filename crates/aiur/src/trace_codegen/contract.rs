//! Versioned bytecode identity shared with `Aiur.TraceContract`.

use super::*;
use crate::bytecode::{Ctrl, Op};

struct Encoder(blake3::Hasher);
impl Encoder {
  fn byte(&mut self, value: u8) {
    self.0.update(&[value]);
  }
  fn word(&mut self, value: u64) {
    self.0.update(&value.to_le_bytes());
  }
  fn index(&mut self, value: usize) {
    self.word(value.try_into().expect("64-bit index"));
  }
  fn indices(&mut self, values: &[usize]) {
    self.index(values.len());
    for &value in values {
      self.index(value);
    }
  }
  fn string(&mut self, value: &str) {
    self.index(value.len());
    self.0.update(value.as_bytes());
  }
  fn unary(&mut self, tag: u8, a: usize) {
    self.byte(tag);
    self.index(a);
  }
  fn binary(&mut self, tag: u8, a: usize, b: usize) {
    self.unary(tag, a);
    self.index(b);
  }
  fn operation(&mut self, op: &Op) {
    match op {
      Op::Const(g) => {
        self.byte(0);
        self.word(g.as_canonical_u64());
      },
      Op::Add(a, b) => self.binary(1, *a, *b),
      Op::Sub(a, b) => self.binary(2, *a, *b),
      Op::Mul(a, b) => self.binary(3, *a, *b),
      Op::EqZero(a) => self.unary(4, *a),
      Op::Call(f, args, n, u) => {
        self.unary(5, *f);
        self.indices(args);
        self.index(*n);
        self.byte(u8::from(*u));
      },
      Op::Store(xs) => {
        self.byte(6);
        self.indices(xs);
      },
      Op::Load(n, p) => self.binary(7, *n, *p),
      Op::AssertEq(a, b, msg) => {
        self.byte(8);
        self.indices(a);
        self.indices(b);
        self.byte(u8::from(msg.is_some()));
        if let Some(msg) = msg {
          self.string(msg);
        }
      },
      Op::IOGetInfo(c, key) => {
        self.unary(9, *c);
        self.indices(key);
      },
      Op::IOSetInfo(c, key, i, n) => {
        self.unary(10, *c);
        self.indices(key);
        self.index(*i);
        self.index(*n);
      },
      Op::IORead(c, i, n) => {
        self.binary(11, *c, *i);
        self.index(*n);
      },
      Op::IOWrite(c, xs) => {
        self.unary(12, *c);
        self.indices(xs);
      },
      Op::U8BitDecomposition(a) => self.unary(13, *a),
      Op::U8ShiftLeft(a) => self.unary(14, *a),
      Op::U8ShiftRight(a) => self.unary(15, *a),
      Op::U8Xor(a, b) => self.binary(16, *a, *b),
      Op::U8Add(a, b) => self.binary(17, *a, *b),
      Op::U8Mul(a, b) => self.binary(18, *a, *b),
      Op::U8Sub(a, b) => self.binary(19, *a, *b),
      Op::U8And(a, b) => self.binary(20, *a, *b),
      Op::U8Or(a, b) => self.binary(21, *a, *b),
      Op::U8LessThan(a, b) => self.binary(22, *a, *b),
      Op::U32LessThan(a, b) => self.binary(23, *a, *b),
      Op::U8XorSplit7(a, b) => self.binary(24, *a, *b),
      Op::U8XorSplit4(a, b) => self.binary(25, *a, *b),
      Op::Debug(msg, args) => {
        self.byte(26);
        self.string(msg);
        self.byte(u8::from(args.is_some()));
        if let Some(args) = args {
          self.indices(args);
        }
      },
      Op::U8RangeCheck(a, b) => self.binary(27, *a, *b),
      Op::UnconstrainedBigUintDivMod(a, b) => self.binary(28, *a, *b),
      Op::UnconstrainedGToBytes(a) => self.unary(29, *a),
      Op::UnconstrainedGInverse(a) => self.unary(30, *a),
      Op::UnconstrainedU32Add(a, b) => {
        self.byte(31);
        self.indices(a);
        self.indices(b);
      },
      Op::UnconstrainedU32Add3(a, b, c) => {
        self.byte(32);
        self.indices(a);
        self.indices(b);
        self.indices(c);
      },
      Op::U32ToField(a) => {
        self.byte(33);
        self.indices(a);
      },
    }
  }
  fn arms(
    &mut self,
    arms: &crate::FxIndexMap<G, Block>,
    fallback: &Option<Box<Block>>,
  ) {
    self.index(arms.len());
    for (value, block) in arms {
      self.word(value.as_canonical_u64());
      self.block(block);
    }
    self.byte(u8::from(fallback.is_some()));
    if let Some(block) = fallback {
      self.block(block);
    }
  }
  fn block(&mut self, block: &Block) {
    self.index(block.ops.len());
    for op in &block.ops {
      self.operation(op);
    }
    match &block.ctrl {
      Ctrl::Match(d, arms, fallback) => {
        self.unary(0, *d);
        self.arms(arms, fallback);
      },
      Ctrl::Return(s, xs) => {
        self.unary(1, *s);
        self.indices(xs);
      },
      Ctrl::Yield(s, xs) => {
        self.unary(2, *s);
        self.indices(xs);
      },
      Ctrl::MatchContinue(d, arms, fallback, n, aux, lookup, continuation) => {
        self.unary(3, *d);
        self.arms(arms, fallback);
        self.index(*n);
        self.index(*aux);
        self.index(*lookup);
        self.block(continuation);
      },
    }
  }
  fn layout(&mut self, l: &FunctionLayout) {
    self.index(l.input_size);
    self.index(l.selectors);
    self.index(l.auxiliaries);
    self.index(l.lookups);
  }
}

/// Grouping is validated separately so one writer can populate singleton or
/// merged circuits without changing its function-library identity.
pub fn fingerprint(top: &Toplevel) -> [u8; 32] {
  let mut e = Encoder(blake3::Hasher::new());
  e.0.update(b"aiur-trace-library-v1/seed-v2/writer-v2\0");
  e.index(top.functions.len());
  for function in &top.functions {
    e.layout(&function.layout);
    e.byte(u8::from(function.entry));
    e.byte(u8::from(function.constrained));
    e.block(&function.body);
  }
  e.indices(&top.memory_sizes);
  *e.0.finalize().as_bytes()
}

pub(super) fn validate_grouping(top: &Toplevel) -> bool {
  let mut seen = vec![false; top.functions.len()];
  for circuit in &top.circuits {
    let mut layout = FunctionLayout {
      input_size: 0,
      selectors: 0,
      auxiliaries: 0,
      lookups: 0,
    };
    if circuit.members.is_empty() {
      return false;
    }
    for &member in &circuit.members {
      let Some(function) = top.functions.get(member) else {
        return false;
      };
      if !function.constrained || std::mem::replace(&mut seen[member], true) {
        return false;
      }
      let l = function.layout;
      layout.input_size = layout.input_size.max(l.input_size);
      let Some(selectors) = layout.selectors.checked_add(l.selectors) else {
        return false;
      };
      layout.selectors = selectors;
      layout.auxiliaries = layout.auxiliaries.max(l.auxiliaries);
      layout.lookups = layout.lookups.max(l.lookups);
    }
    if layout != circuit.layout {
      return false;
    }
  }
  seen.iter().zip(&top.functions).all(|(&seen, f)| seen == f.constrained)
}
