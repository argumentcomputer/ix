use super::{Artifact, Instruction, Operand, Operation, Primitive, Scalar};
use num_bigint::BigUint;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrimitiveInventory {
  pub primitive: Primitive,
  pub sites: usize,
  /// Opcode-name correspondence only, not admission or a refinement proof.
  pub native_opcode: Option<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScalarInventory {
  pub kind: &'static str,
  pub literals: usize,
  pub maximum_bytes: usize,
  pub maximum_bits: u64,
}

/// Whole-image facts, not dynamic heap/stack maxima or a prover-cost estimate.
/// Large natural metadata is retained exactly instead of rounded or truncated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Inventory {
  pub program_bytes: usize,
  pub functions: usize,
  pub blocks: usize,
  pub constructors: usize,
  pub maximum_function_blocks: usize,
  pub maximum_function_arity: BigUint,
  pub maximum_frame_locals: BigUint,
  pub maximum_constructor_fields: BigUint,
  pub maximum_operand_vector: usize,
  pub instructions: [usize; 8],
  pub operations: [usize; 8],
  pub primitives: Vec<PrimitiveInventory>,
  pub scalars: Vec<ScalarInventory>,
}

struct Census {
  result: Inventory,
  primitive_counts: [usize; 45],
}

impl Census {
  fn operand(&mut self, operand: &Operand<'_>) {
    if let Operand::Literal(value) = operand {
      let (kind, bytes, bits) = match value {
        Scalar::Nat(value) => (0, 0, value.bits()),
        Scalar::String(value) => (1, value.len(), 0),
        Scalar::Bool(_) => (2, 1, 1),
        Scalar::Word32(_) => (3, 4, 32),
        Scalar::Goldilocks(_) => (4, 8, 64),
        Scalar::Extension(_) => (5, 16, 128),
        Scalar::Bytes(value) => (6, value.len(), 0),
      };
      let entry = &mut self.result.scalars[kind];
      entry.literals += 1;
      entry.maximum_bytes = entry.maximum_bytes.max(bytes);
      entry.maximum_bits = entry.maximum_bits.max(bits);
    }
  }

  fn operands(&mut self, operands: &[Operand<'_>]) {
    self.result.maximum_operand_vector =
      self.result.maximum_operand_vector.max(operands.len());
    for operand in operands {
      self.operand(operand);
    }
  }

  fn operation(&mut self, operation: &Operation<'_>) {
    let kind = match operation {
      Operation::Copy(value) => {
        self.operand(value);
        0
      },
      Operation::Primitive(primitive, args) => {
        self.primitive_counts[usize::from(primitive.opcode())] += 1;
        self.operands(args);
        1
      },
      Operation::Construct(_, args) => {
        self.operands(args);
        2
      },
      Operation::Project(value, _) => {
        self.operand(value);
        3
      },
      Operation::Closure(_, args) => {
        self.operands(args);
        4
      },
      Operation::Call(_, args) => {
        self.operands(args);
        5
      },
      Operation::CallSelf(args) => {
        self.operands(args);
        6
      },
      Operation::Apply(value, args) => {
        self.operand(value);
        self.operands(args);
        7
      },
    };
    self.result.operations[kind] += 1;
  }

  fn instruction(&mut self, instruction: &Instruction<'_>) {
    let kind = match instruction {
      Instruction::Let(operation, _) => {
        self.operation(operation);
        0
      },
      Instruction::Return(value) => {
        self.operand(value);
        1
      },
      Instruction::TailCall(_, args) => {
        self.operands(args);
        2
      },
      Instruction::TailCallSelf(args) => {
        self.operands(args);
        3
      },
      Instruction::TailApply(value, args) => {
        self.operand(value);
        self.operands(args);
        4
      },
      Instruction::CaseConstructor(value, _) => {
        self.operand(value);
        5
      },
      Instruction::CaseNat(value, _, _) => {
        self.operand(value);
        6
      },
      Instruction::Branch(value, _, _) => {
        self.operand(value);
        7
      },
    };
    self.result.instructions[kind] += 1;
  }
}

impl Artifact<'_> {
  pub fn inventory(&self) -> Inventory {
    let mut census = Census {
      result: Inventory {
        program_bytes: self.source().len(),
        functions: self.functions().len(),
        blocks: 0,
        constructors: self.constructors().len(),
        maximum_function_blocks: 0,
        maximum_function_arity: BigUint::default(),
        maximum_frame_locals: BigUint::default(),
        maximum_constructor_fields: self
          .constructors()
          .iter()
          .map(|c| &c.fields)
          .max()
          .cloned()
          .unwrap_or_default(),
        maximum_operand_vector: 0,
        instructions: [0; 8],
        operations: [0; 8],
        primitives: Vec::new(),
        scalars: [
          "Nat",
          "String",
          "Bool",
          "Word32",
          "Goldilocks",
          "Extension",
          "Bytes",
        ]
        .map(|kind| ScalarInventory {
          kind,
          literals: 0,
          maximum_bytes: 0,
          maximum_bits: 0,
        })
        .to_vec(),
      },
      primitive_counts: [0; 45],
    };
    for function in self.functions() {
      census.result.blocks += function.blocks.len();
      census.result.maximum_function_blocks =
        census.result.maximum_function_blocks.max(function.blocks.len());
      census.result.maximum_function_arity =
        census.result.maximum_function_arity.max(function.arity.clone());
      for block in &function.blocks {
        census.result.maximum_frame_locals =
          census.result.maximum_frame_locals.max(block.locals.clone());
        census.instruction(&block.instruction);
      }
    }
    census.result.primitives = Primitive::ALL
      .into_iter()
      .filter_map(|primitive| {
        let sites = census.primitive_counts[usize::from(primitive.opcode())];
        (sites != 0).then_some(PrimitiveInventory {
          primitive,
          sites,
          native_opcode: primitive.native_opcode(),
        })
      })
      .collect();
    census.result
  }
}
