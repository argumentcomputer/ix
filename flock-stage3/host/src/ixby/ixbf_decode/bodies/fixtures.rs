//! Native syntax and a separate canonical encoder provide complete expected
//! records/ranges. No fixture controls the circuit's parsing or insertion.
use super::{
  super::{
    references,
    registry::{RegistryOp, fixtures as program},
  },
  *,
};
use crate::ixby::ixbf::{self, Instruction, Operand, Operation, Scalar};
use flock_prover::field::F128;
use num_bigint::BigUint;
pub(in crate::ixby::ixbf_decode) use program::{
  Function, Spec, base, nat, word,
};
pub(in crate::ixby::ixbf_decode) struct Fixture {
  pub name: String,
  pub source: program::Fixture,
  pub bank: Vec<F128>,
  pub prove: bool,
}
fn wide(v: &BigUint) -> F128 {
  let b = v.to_bytes_le();
  assert!(b.len() <= 16);
  let mut full = [0; 16];
  full[..b.len()].copy_from_slice(&b);
  crate::hash::pack_bytes(&full)
}
fn big(bytes: &mut Vec<u8>, v: &BigUint) {
  let digits = v.to_radix_le(128);
  for (i, digit) in digits.iter().enumerate() {
    bytes.push(*digit | if i + 1 < digits.len() { 128 } else { 0 });
  }
}
struct BlockEncoder {
  capacity: BodyCapacity,
  start: usize,
  bytes: Vec<u8>,
  record: Vec<F128>,
}
impl BlockEncoder {
  fn at(&self) -> usize {
    self.start + self.bytes.len()
  }
  fn count(&mut self, n: usize) {
    nat(&mut self.bytes, n as u128);
  }
  fn operand(&mut self, o: &Operand<'_>) {
    let c = self.capacity;
    let start = self.at();
    let mut r = vec![F128::ZERO; c.operand_words()];
    r[0] = F128::ONE;
    match o {
      Operand::Erased => {
        self.bytes.push(2);
        r[O_KIND] = word(2);
      },
      Operand::Local(v) => {
        self.bytes.push(0);
        big(&mut self.bytes, v);
        r[O_LOCAL] = wide(v);
      },
      Operand::Literal(s) => {
        self.bytes.push(1);
        r[O_KIND] = F128::ONE;
        let tag = match s {
          Scalar::Nat(v) => {
            self.bytes.push(0);
            let start = self.at();
            big(&mut self.bytes, v);
            r[O_PAYLOAD] = F128::new(start as u64, (self.at() - start) as u64);
            let bytes = v.to_bytes_le();
            assert!(bytes.len() <= 16 * c.natural.magnitude_words());
            let mut padded = vec![0; 16 * c.natural.magnitude_words()];
            padded[..bytes.len()].copy_from_slice(&bytes);
            for (out, b) in
              r[O_MAGNITUDE..].iter_mut().zip(padded.as_chunks::<16>().0)
            {
              *out = crate::hash::pack_bytes(b);
            }
            0
          },
          Scalar::String(s) => {
            self.bytes.push(1);
            self.count(s.len());
            r[O_PAYLOAD] = F128::new(self.at() as u64, s.len() as u64);
            self.bytes.extend(s.as_bytes());
            1
          },
          Scalar::Bool(v) => {
            self.bytes.extend([2, u8::from(*v)]);
            r[O_FIXED] = word(u128::from(*v));
            2
          },
          Scalar::Word32(v) => {
            self.bytes.push(3);
            self.bytes.extend(v.to_le_bytes());
            r[O_FIXED] = word(*v as u128);
            3
          },
          Scalar::Goldilocks(v) => {
            self.bytes.push(4);
            self.bytes.extend(v.to_le_bytes());
            r[O_FIXED] = word(*v as u128);
            4
          },
          Scalar::Extension(v) => {
            self.bytes.push(5);
            for v in v {
              self.bytes.extend(v.to_le_bytes());
            }
            r[O_FIXED] = F128::new(v[0], v[1]);
            5
          },
          Scalar::Bytes(v) => {
            self.bytes.push(6);
            self.count(v.len());
            r[O_PAYLOAD] = F128::new(self.at() as u64, v.len() as u64);
            self.bytes.extend(*v);
            6
          },
        };
        r[O_SCALAR] = word(tag);
      },
    }
    r[O_SPAN] = F128::new(start as u64, self.at() as u64);
    let index = self.record[OPERANDS].lo as usize;
    assert!(index < c.operands);
    let at = HEADER_WORDS + index * c.operand_words();
    self.record[at..at + c.operand_words()].copy_from_slice(&r);
    self.record[OPERANDS].lo += 1;
  }
  fn operands(&mut self, args: &[Operand<'_>]) {
    self.record[ARGUMENTS] = word(args.len() as u128);
    self.count(args.len());
    for arg in args {
      self.operand(arg);
    }
  }
  fn operation(&mut self, op: &Operation<'_>) {
    let tag = match op {
      Operation::Copy(_) => 0,
      Operation::Primitive(_, _) => 1,
      Operation::Construct(_, _) => 2,
      Operation::Project(_, _) => 3,
      Operation::Closure(_, _) => 4,
      Operation::Call(_, _) => 5,
      Operation::CallSelf(_) => 6,
      Operation::Apply(_, _) => 7,
    };
    self.record[OPERATION] = word(tag);
    self.bytes.push(tag as u8);
    match op {
      Operation::Copy(o) => self.operand(o),
      Operation::Primitive(p, args) => {
        self.record[PRIMITIVE] = word(p.opcode() as u128);
        self.bytes.push(p.opcode());
        self.operands(args);
      },
      Operation::Construct(index, args)
      | Operation::Closure(index, args)
      | Operation::Call(index, args) => {
        self.record[REFERENCE] = word(*index as u128);
        self.count(*index);
        self.operands(args);
      },
      Operation::Project(o, field) => {
        self.operand(o);
        big(&mut self.bytes, field);
        self.record[PROJECTION] = wide(field);
      },
      Operation::CallSelf(args) => self.operands(args),
      Operation::Apply(o, args) => {
        self.operand(o);
        self.operands(args);
      },
    }
  }
  fn instruction(&mut self, i: &Instruction<'_>) {
    let tag = match i {
      Instruction::Let(_, _) => 0,
      Instruction::Return(_) => 1,
      Instruction::TailCall(_, _) => 2,
      Instruction::TailCallSelf(_) => 3,
      Instruction::TailApply(_, _) => 4,
      Instruction::CaseConstructor(_, _) => 5,
      Instruction::CaseNat(_, _, _) => 6,
      Instruction::Branch(_, _, _) => 7,
    };
    self.record[INSTRUCTION] = word(tag);
    self.bytes.push(tag as u8);
    self.record[HEADER_END] = word(self.at() as u128);
    match i {
      Instruction::Let(op, target) => {
        self.operation(op);
        self.record[TARGET0] = word(*target as u128);
        self.count(*target);
      },
      Instruction::Return(o) => self.operand(o),
      Instruction::TailCall(index, args) => {
        self.record[REFERENCE] = word(*index as u128);
        self.count(*index);
        self.operands(args);
      },
      Instruction::TailCallSelf(args) => self.operands(args),
      Instruction::TailApply(o, args) => {
        self.operand(o);
        self.operands(args);
      },
      Instruction::CaseConstructor(o, alts) => {
        self.operand(o);
        self.count(alts.len());
        self.record[ALTERNATIVES] = word(alts.len() as u128);
        for (i, alt) in alts.iter().enumerate() {
          let start = self.at();
          self.count(alt.constructor);
          self.count(alt.target);
          let end = self.at();
          let at = self.capacity.alternatives() + i * ALT_WORDS;
          self.record[at..at + ALT_WORDS].copy_from_slice(&[
            F128::ONE,
            word(alt.constructor as u128),
            word(alt.target as u128),
            F128::new(start as u64, end as u64),
          ]);
        }
      },
      Instruction::CaseNat(o, first, second)
      | Instruction::Branch(o, first, second) => {
        self.operand(o);
        self.record[TARGET0] = word(*first as u128);
        self.record[TARGET1] = word(*second as u128);
        self.count(*first);
        self.count(*second);
      },
    }
  }
}
pub(in crate::ixby::ixbf_decode) fn encode(
  c: BodyCapacity,
  name: &str,
  spec: &Spec,
  prove: bool,
) -> Fixture {
  let source = program::encode(spec);
  let artifact =
    ixbf::decode_program(&source.bytes, ixbf::DecodeLimits::default())
      .unwrap_or_else(|e| panic!("{name}: {e:#}"));
  assert_eq!(artifact.encode(), source.bytes);
  let mut bank = vec![F128::ZERO; c.finished_words()];
  for (f, function) in artifact.functions().iter().enumerate() {
    let header = source
      .headers
      .iter()
      .find(|h| h.kind == RegistryOp::Function && h.index == f)
      .unwrap();
    let end = function.blocks.last().unwrap().encoded.end;
    bank[f * FUNCTION_WORDS..(f + 1) * FUNCTION_WORDS].copy_from_slice(&[
      F128::ONE,
      wide(&function.arity),
      word(function.entry as u128),
      word(function.blocks.len() as u128),
      F128::new(header.span.lo, end as u64),
    ]);
    for (i, block) in function.blocks.iter().enumerate() {
      let mut encoder = BlockEncoder {
        capacity: c,
        start: block.encoded.start,
        bytes: vec![],
        record: vec![F128::ZERO; c.block_words()],
      };
      encoder.record[0] = F128::ONE;
      encoder.record[LOCALS] = wide(&block.locals);
      big(&mut encoder.bytes, &block.locals);
      encoder.instruction(&block.instruction);
      encoder.record[SPAN] =
        F128::new(block.encoded.start as u64, encoder.at() as u64);
      assert_eq!(
        encoder.bytes,
        source.bytes[block.encoded.clone()],
        "exact body encoding {name} {f}/{i}"
      );
      let at = c.registry.functions() * FUNCTION_WORDS
        + (f * c.registry.blocks_per_function() + i) * c.block_words();
      bank[at..at + c.block_words()].copy_from_slice(&encoder.record);
    }
  }
  Fixture { name: name.to_owned(), source, bank, prove }
}
impl Fixture {
  pub(in crate::ixby::ixbf_decode) fn queries(
    &self,
    c: BodyCapacity,
  ) -> [F128; 13] {
    let mut q = [F128::ZERO; 13];
    for f in 0..c.registry.functions() {
      if self.bank[f * FUNCTION_WORDS] != F128::ZERO {
        q[..2].copy_from_slice(&[F128::ONE, word(f as u128)]);
      }
    }
    let mut literal = false;
    for f in 0..c.registry.functions() {
      for block in 0..c.registry.blocks_per_function() {
        let at = c.registry.functions() * FUNCTION_WORDS
          + (f * c.registry.blocks_per_function() + block) * c.block_words();
        let r = &self.bank[at..at + c.block_words()];
        if r[0] == F128::ZERO {
          continue;
        }
        q[2..5].copy_from_slice(&[
          F128::ONE,
          word(f as u128),
          word(block as u128),
        ]);
        for i in 0..c.operands {
          let o = HEADER_WORDS + i * c.operand_words();
          if r[o] == F128::ONE {
            let is_literal = r[o + O_KIND] == F128::ONE;
            if is_literal || !literal {
              q[5..9].copy_from_slice(&[
                F128::ONE,
                word(f as u128),
                word(block as u128),
                word(i as u128),
              ]);
              literal = is_literal;
            }
          }
        }
        for i in 0..c.registry.constructors() {
          if r[c.alternatives() + i * ALT_WORDS] == F128::ONE {
            q[9..13].copy_from_slice(&[
              F128::ONE,
              word(f as u128),
              word(block as u128),
              word(i as u128),
            ]);
          }
        }
      }
    }
    q
  }
  pub(in crate::ixby::ixbf_decode) fn results(
    &self,
    c: BodyCapacity,
    q: &[F128; 13],
  ) -> Vec<F128> {
    let mut out = Vec::new();
    for (kind, offset, width) in [
      (BodyOp::ReadFunction, 0, FUNCTION_WORDS),
      (BodyOp::ReadBlock, 2, HEADER_WORDS),
      (BodyOp::ReadOperand, 5, c.operand_words()),
      (BodyOp::ReadAlternative, 9, ALT_WORDS),
    ] {
      if q[offset] == F128::ZERO {
        out.extend(vec![F128::ZERO; width]);
        continue;
      }
      let owner = q[offset + 1].lo as usize;
      let at = if kind == BodyOp::ReadFunction {
        owner * FUNCTION_WORDS
      } else {
        let block = q[offset + 2].lo as usize;
        let at = c.registry.functions() * FUNCTION_WORDS
          + (owner * c.registry.blocks_per_function() + block)
            * c.block_words();
        match kind {
          BodyOp::ReadBlock => at,
          BodyOp::ReadOperand => {
            at + HEADER_WORDS + q[offset + 3].lo as usize * c.operand_words()
          },
          _ => at + c.alternatives() + q[offset + 3].lo as usize * ALT_WORDS,
        }
      };
      out.extend(&self.bank[at..at + width]);
    }
    out
  }
}
fn let_op(operation: &[u8], locals: u128) -> Spec {
  let mut spec = base();
  spec.functions[0].arity = locals;
  let mut instruction = vec![0];
  instruction.extend(operation);
  instruction.push(1);
  spec.functions[0].blocks =
    vec![(locals, instruction), (locals + 1, vec![1, 2])];
  spec
}
pub(in crate::ixby::ixbf_decode) fn corpus(c: BodyCapacity) -> Vec<Fixture> {
  let mut specs: Vec<_> = references::test_programs()
    .into_iter()
    .map(|(name, spec)| (name.to_owned(), spec, true))
    .collect();
  for p in ixbf::Primitive::ALL {
    let mut op = vec![1, p.opcode(), p.arity() as u8];
    op.extend(vec![2; p.arity()]);
    specs.push((
      format!("primitive-{}", p.opcode()),
      let_op(&op, 0),
      p.opcode() == 42,
    ));
  }
  let mut scalars = vec![
    ("zero", vec![0, 0]),
    ("bool", vec![2, 1]),
    ("word", vec![3, 255, 0, 0, 128]),
    ("empty-string", vec![1, 0]),
    ("empty-bytes", vec![6, 0]),
  ];
  let mut gold = vec![4];
  gold.extend(0xffff_ffff_0000_0000u64.to_le_bytes());
  scalars.push(("gold", gold));
  let mut ext = vec![5];
  ext.extend(0xffff_ffff_0000_0000u64.to_le_bytes());
  ext.extend(7u64.to_le_bytes());
  scalars.push(("extension", ext));
  let mut bytes = vec![6];
  nat(&mut bytes, 800);
  bytes.extend((0..800).map(|v| v as u8));
  scalars.push(("bytes", bytes));
  for (name, scalar) in scalars {
    let mut spec = base();
    let mut ins = vec![1, 1];
    ins.extend(scalar);
    spec.functions[0].blocks[0].1 = ins;
    specs.push((name.to_owned(), spec, true));
  }
  let mut project = vec![3, 2];
  nat(&mut project, u128::MAX);
  specs.push(("wide-projection".to_owned(), let_op(&project, 0), true));
  specs.push((
    "ordered-mixed".to_owned(),
    let_op(&[1, 42, 3, 0, 0, 1, 0, 255, 1, 2], 1),
    true,
  ));
  specs.push((
    "ordered-apply".to_owned(),
    let_op(&[7, 0, 0, 2, 1, 1, 3, b'a', b'b', b'c', 1, 6, 2, 255, 128], 1),
    true,
  ));
  specs
    .into_iter()
    .map(|(name, spec, prove)| encode(c, &name, &spec, prove))
    .collect()
}
