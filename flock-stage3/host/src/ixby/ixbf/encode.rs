use super::{
  FORMAT_VERSION, PROGRAM_SEMANTICS_VERSION, SEMANTICS_VERSION, model::*,
};
use num_bigint::BigUint;

struct Writer(Vec<u8>);

impl Writer {
  fn header(magic: &[u8; 4]) -> Self {
    let mut value = Self(Vec::new());
    value.0.extend_from_slice(magic);
    value.0.extend_from_slice(&FORMAT_VERSION.to_le_bytes());
    let semantics = if magic == b"IXBF" {
      PROGRAM_SEMANTICS_VERSION
    } else {
      SEMANTICS_VERSION
    };
    value.0.extend_from_slice(&semantics.to_le_bytes());
    value
  }
  fn byte(&mut self, value: u8) {
    self.0.push(value);
  }
  fn natural(&mut self, value: &BigUint) {
    let digits = value.to_radix_le(128);
    for (index, digit) in digits.iter().enumerate() {
      self.byte(digit | if index + 1 < digits.len() { 128 } else { 0 });
    }
  }
  fn count(&mut self, value: usize) {
    self.natural(&BigUint::from(value));
  }
  fn bytes(&mut self, value: &[u8]) {
    self.count(value.len());
    self.0.extend_from_slice(value);
  }
  fn scalar(&mut self, value: &Scalar<'_>) {
    match value {
      Scalar::Nat(value) => {
        self.byte(0);
        self.natural(value);
      },
      Scalar::String(value) => {
        self.byte(1);
        self.bytes(value.as_bytes());
      },
      Scalar::Bool(value) => {
        self.byte(2);
        self.byte(u8::from(*value));
      },
      Scalar::Word32(value) => {
        self.byte(3);
        self.0.extend_from_slice(&value.to_le_bytes());
      },
      Scalar::Goldilocks(value) => {
        self.byte(4);
        self.0.extend_from_slice(&value.to_le_bytes());
      },
      Scalar::Extension(value) => {
        self.byte(5);
        for coefficient in value {
          self.0.extend_from_slice(&coefficient.to_le_bytes());
        }
      },
      Scalar::Bytes(value) => {
        self.byte(6);
        self.bytes(value);
      },
    }
  }
  fn constructor_id(&mut self, id: &ConstructorId) {
    self.0.extend_from_slice(&id.block);
    self.natural(&id.member);
    self.natural(&id.tag);
  }
  fn operand(&mut self, value: &Operand<'_>) {
    match value {
      Operand::Local(value) => {
        self.byte(0);
        self.natural(value);
      },
      Operand::Literal(value) => {
        self.byte(1);
        self.scalar(value);
      },
      Operand::Erased => self.byte(2),
    }
  }
  fn operands(&mut self, values: &[Operand<'_>]) {
    self.count(values.len());
    for value in values {
      self.operand(value);
    }
  }
  fn operation(&mut self, value: &Operation<'_>) {
    match value {
      Operation::Copy(value) => {
        self.byte(0);
        self.operand(value);
      },
      Operation::Primitive(primitive, args) => {
        self.byte(1);
        self.byte(primitive.opcode());
        self.operands(args);
      },
      Operation::Construct(constructor, args) => {
        self.byte(2);
        self.count(*constructor);
        self.operands(args);
      },
      Operation::Project(value, field) => {
        self.byte(3);
        self.operand(value);
        self.natural(field);
      },
      Operation::Closure(function, args) => {
        self.byte(4);
        self.count(*function);
        self.operands(args);
      },
      Operation::Call(function, args) => {
        self.byte(5);
        self.count(*function);
        self.operands(args);
      },
      Operation::CallSelf(args) => {
        self.byte(6);
        self.operands(args);
      },
      Operation::Apply(value, args) => {
        self.byte(7);
        self.operand(value);
        self.operands(args);
      },
    }
  }
  fn instruction(&mut self, instruction: &Instruction<'_>) {
    match instruction {
      Instruction::Let(op, next) => {
        self.byte(0);
        self.operation(op);
        self.count(*next);
      },
      Instruction::Return(value) => {
        self.byte(1);
        self.operand(value);
      },
      Instruction::TailCall(function, args) => {
        self.byte(2);
        self.count(*function);
        self.operands(args);
      },
      Instruction::TailCallSelf(args) => {
        self.byte(3);
        self.operands(args);
      },
      Instruction::TailApply(value, args) => {
        self.byte(4);
        self.operand(value);
        self.operands(args);
      },
      Instruction::CaseConstructor(value, alternatives) => {
        self.byte(5);
        self.operand(value);
        self.count(alternatives.len());
        for alternative in alternatives {
          self.count(alternative.constructor);
          self.count(alternative.target);
        }
      },
      Instruction::CaseNat(value, zero, successor) => {
        self.byte(6);
        self.operand(value);
        self.count(*zero);
        self.count(*successor);
      },
      Instruction::Branch(value, yes, no) => {
        self.byte(7);
        self.operand(value);
        self.count(*yes);
        self.count(*no);
      },
    }
  }
  fn forest(&mut self, forest: &ValueForest<'_>) {
    // The sealed decoder-owned arena is already a complete preorder traversal.
    // Iteration keeps both encoding and destruction independent of tree depth.
    for node in &forest.nodes {
      match &node.kind {
        ValueKind::Scalar(value) => {
          self.byte(0);
          self.scalar(value);
        },
        ValueKind::Constructor(id) => {
          self.byte(1);
          self.constructor_id(id);
          self.count(node.children.len());
        },
        ValueKind::PartialApplication(function) => {
          self.byte(2);
          self.count(*function);
          self.count(node.children.len());
        },
        ValueKind::Erased => self.byte(3),
      }
    }
  }
}

pub(super) fn program(artifact: &Artifact<'_>) -> Vec<u8> {
  let mut writer = Writer::header(b"IXBF");
  let limits = &artifact.limits;
  for value in [
    &limits.functions,
    &limits.constructors,
    &limits.blocks,
    &limits.locals,
    &limits.operands,
    &limits.continuations,
    &limits.input_nodes,
    &limits.nat_bits,
    &limits.string_bytes,
    &limits.byte_array_bytes,
    &artifact.max_steps,
  ] {
    writer.natural(value);
  }
  writer.count(artifact.entry);
  writer.count(artifact.constructors.len());
  for constructor in &artifact.constructors {
    writer.constructor_id(&constructor.id);
    writer.natural(&constructor.fields);
  }
  writer.count(artifact.functions.len());
  for function in &artifact.functions {
    writer.natural(&function.arity);
    writer.count(function.entry);
    writer.count(function.blocks.len());
    for block in &function.blocks {
      writer.natural(&block.locals);
      writer.instruction(&block.instruction);
    }
  }
  writer.0
}

pub(super) fn input(input: &Input<'_>) -> Vec<u8> {
  let mut writer = Writer::header(b"IXFI");
  writer.count(input.values.roots.len());
  writer.forest(&input.values);
  writer.0
}

pub(super) fn output(output: &Output<'_>) -> Vec<u8> {
  let mut writer = Writer::header(b"IXFO");
  writer.forest(&output.values);
  writer.0
}
