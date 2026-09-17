use super::{
  FORMAT_VERSION, PROGRAM_SEMANTICS_VERSION, SEMANTICS_VERSION, model::*,
  primitive::Primitive,
};
use anyhow::{Context, Result, bail, ensure};
use num_bigint::BigUint;
use std::collections::BTreeMap;

/// Host allocation/parse budgets; none of these is a proving admission.
/// `syntax_nodes` additionally bounds decoded program objects, independently
/// of both file size and the program's self-declared execution limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodeLimits {
  pub bytes: usize,
  pub integer_bytes: usize,
  pub syntax_nodes: usize,
  pub value_nodes: usize,
  pub value_depth: usize,
}

impl Default for DecodeLimits {
  fn default() -> Self {
    Self {
      bytes: 64 * 1024 * 1024,
      integer_bytes: 8192,
      syntax_nodes: 1_048_576,
      value_nodes: 1_048_576,
      value_depth: 1024,
    }
  }
}

struct Reader<'a> {
  bytes: &'a [u8],
  offset: usize,
  loader: DecodeLimits,
  syntax_remaining: usize,
}

fn index(value: &BigUint) -> Result<usize> {
  let words = value.to_u64_digits();
  let value = match words.as_slice() {
    [] => 0,
    [value] => *value,
    _ => bail!("functional binary index cannot name a host array element"),
  };
  usize::try_from(value).context("functional binary index width")
}

impl<'a> Reader<'a> {
  fn new(bytes: &'a [u8], loader: DecodeLimits) -> Result<Self> {
    ensure!(bytes.len() <= loader.bytes, "functional binary file byte limit");
    Ok(Self { bytes, offset: 0, loader, syntax_remaining: loader.syntax_nodes })
  }

  fn take(&mut self, count: usize) -> Result<&'a [u8]> {
    let end = self
      .offset
      .checked_add(count)
      .context("functional binary offset overflow")?;
    let bytes = self.bytes.get(self.offset..end).with_context(|| {
      format!("truncated functional binary at byte {}", self.offset)
    })?;
    self.offset = end;
    Ok(bytes)
  }

  fn byte(&mut self) -> Result<u8> {
    Ok(self.take(1)?[0])
  }

  fn fixed<const N: usize>(&mut self) -> Result<[u8; N]> {
    Ok(self.take(N)?.try_into().expect("exact checked slice length"))
  }

  fn natural(&mut self) -> Result<BigUint> {
    let start = self.offset;
    for i in 0..self.loader.integer_bytes {
      let byte = self.byte()?;
      if byte < 128 {
        ensure!(
          i == 0 || byte != 0,
          "non-minimal functional LEB128 at byte {start}"
        );
        let digits: Vec<_> =
          self.bytes[start..self.offset].iter().map(|b| b & 127).collect();
        return BigUint::from_radix_le(&digits, 128)
          .context("functional LEB128 digits");
      }
    }
    bail!("functional binary integer byte limit at byte {start}")
  }

  fn bounded_natural(&mut self, bound: &BigUint) -> Result<BigUint> {
    let value = self.natural()?;
    ensure!(&value <= bound, "functional binary semantic count limit");
    Ok(value)
  }

  fn count(&mut self, bound: &BigUint) -> Result<usize> {
    let value = self.bounded_natural(bound)?;
    // Every vector element is at least one byte. Check before iterating or
    // allocating; a huge declared count never becomes a Vec capacity.
    ensure!(
      value <= BigUint::from(self.bytes.len() - self.offset),
      "functional binary count exceeds remaining bytes"
    );
    index(&value)
  }

  fn index(&mut self) -> Result<usize> {
    index(&self.natural()?)
  }

  fn syntax_node(&mut self) -> Result<()> {
    self.syntax_remaining = self
      .syntax_remaining
      .checked_sub(1)
      .context("functional binary syntax node limit")?;
    Ok(())
  }

  fn header(&mut self, magic: &[u8; 4]) -> Result<()> {
    ensure!(self.take(4)? == magic, "wrong functional binary domain");
    ensure!(
      u32::from_le_bytes(self.fixed()?) == FORMAT_VERSION,
      "unsupported functional binary format version"
    );
    let semantics = u32::from_le_bytes(self.fixed()?);
    ensure!(
      semantics
        == if magic == b"IXBF" {
          PROGRAM_SEMANTICS_VERSION
        } else {
          SEMANTICS_VERSION
        },
      "unsupported functional binary semantics version"
    );
    Ok(())
  }

  fn finish(self) -> Result<()> {
    ensure!(
      self.offset == self.bytes.len(),
      "trailing functional binary bytes"
    );
    Ok(())
  }

  fn field(&mut self) -> Result<u64> {
    let value = u64::from_le_bytes(self.fixed()?);
    ensure!(
      value < 0xffff_ffff_0000_0001,
      "non-canonical Goldilocks coefficient"
    );
    Ok(value)
  }

  fn scalar(&mut self, limits: &Limits) -> Result<Scalar<'a>> {
    let value = match self.byte()? {
      0 => Scalar::Nat(self.natural()?),
      1 => {
        let count = self.count(&limits.string_bytes)?;
        Scalar::String(
          std::str::from_utf8(self.take(count)?)
            .context("invalid functional UTF-8")?,
        )
      },
      2 => Scalar::Bool(match self.byte()? {
        0 => false,
        1 => true,
        _ => bail!("non-canonical functional Boolean"),
      }),
      3 => Scalar::Word32(u32::from_le_bytes(self.fixed()?)),
      4 => Scalar::Goldilocks(self.field()?),
      5 => Scalar::Extension([self.field()?, self.field()?]),
      6 => {
        let count = self.count(&limits.byte_array_bytes)?;
        Scalar::Bytes(self.take(count)?)
      },
      tag => bail!("invalid functional scalar tag {tag}"),
    };
    super::validate::scalar(limits, &value)?;
    Ok(value)
  }

  fn constructor_id(&mut self) -> Result<ConstructorId> {
    Ok(ConstructorId {
      block: self.fixed()?,
      member: self.natural()?,
      tag: self.natural()?,
    })
  }

  fn operand(&mut self, limits: &Limits) -> Result<Operand<'a>> {
    self.syntax_node()?;
    Ok(match self.byte()? {
      0 => Operand::Local(self.natural()?),
      1 => Operand::Literal(self.scalar(limits)?),
      2 => Operand::Erased,
      tag => bail!("invalid functional operand tag {tag}"),
    })
  }

  fn operands(&mut self, limits: &Limits) -> Result<Vec<Operand<'a>>> {
    let count = self.count(&limits.operands)?;
    ensure!(count <= self.syntax_remaining, "functional operand syntax budget");
    let mut operands = Vec::new();
    for _ in 0..count {
      operands.push(self.operand(limits)?);
    }
    Ok(operands)
  }

  fn operation(&mut self, limits: &Limits) -> Result<Operation<'a>> {
    self.syntax_node()?;
    Ok(match self.byte()? {
      0 => Operation::Copy(self.operand(limits)?),
      1 => {
        let primitive = Primitive::from_opcode(self.byte()?)
          .context("invalid functional primitive opcode")?;
        Operation::Primitive(primitive, self.operands(limits)?)
      },
      2 => Operation::Construct(self.index()?, self.operands(limits)?),
      3 => Operation::Project(self.operand(limits)?, self.natural()?),
      4 => Operation::Closure(self.index()?, self.operands(limits)?),
      5 => Operation::Call(self.index()?, self.operands(limits)?),
      6 => Operation::CallSelf(self.operands(limits)?),
      7 => Operation::Apply(self.operand(limits)?, self.operands(limits)?),
      tag => bail!("invalid functional operation tag {tag}"),
    })
  }

  fn instruction(&mut self, limits: &Limits) -> Result<Instruction<'a>> {
    self.syntax_node()?;
    Ok(match self.byte()? {
      0 => Instruction::Let(self.operation(limits)?, self.index()?),
      1 => Instruction::Return(self.operand(limits)?),
      2 => Instruction::TailCall(self.index()?, self.operands(limits)?),
      3 => Instruction::TailCallSelf(self.operands(limits)?),
      4 => {
        Instruction::TailApply(self.operand(limits)?, self.operands(limits)?)
      },
      5 => {
        let value = self.operand(limits)?;
        let count = self.count(&limits.constructors)?;
        ensure!(
          count <= self.syntax_remaining,
          "functional alternative syntax budget"
        );
        let mut alternatives = Vec::new();
        for _ in 0..count {
          self.syntax_node()?;
          alternatives.push(Alternative {
            constructor: self.index()?,
            target: self.index()?,
          });
        }
        Instruction::CaseConstructor(value, alternatives)
      },
      6 => Instruction::CaseNat(
        self.operand(limits)?,
        self.index()?,
        self.index()?,
      ),
      7 => {
        Instruction::Branch(self.operand(limits)?, self.index()?, self.index()?)
      },
      tag => bail!("invalid functional instruction tag {tag}"),
    })
  }

  fn function(&mut self, limits: &Limits) -> Result<Function<'a>> {
    self.syntax_node()?;
    let arity = self.bounded_natural(&limits.operands)?;
    let entry = self.index()?;
    let count = self.count(&limits.blocks)?;
    ensure!(count <= self.syntax_remaining, "functional block syntax budget");
    let mut blocks = Vec::new();
    for _ in 0..count {
      self.syntax_node()?;
      let start = self.offset;
      let locals = self.bounded_natural(&limits.locals)?;
      let instruction = self.instruction(limits)?;
      blocks.push(Block { locals, instruction, encoded: start..self.offset });
    }
    Ok(Function { arity, entry, blocks })
  }

  fn forest(
    &mut self,
    artifact: &Artifact<'_>,
    roots: usize,
  ) -> Result<ValueForest<'a>> {
    struct Frame {
      parent: Option<usize>,
      remaining: usize,
      depth: usize,
    }
    let mut pending = vec![Frame { parent: None, remaining: roots, depth: 1 }];
    let mut forest =
      ValueForest { nodes: Vec::new(), roots: Vec::new(), depth: 0 };
    let semantic_budget =
      index(&artifact.limits.input_nodes).unwrap_or(usize::MAX);
    let budget = self.loader.value_nodes.min(semantic_budget);
    while let Some(frame) = pending.last_mut() {
      if frame.remaining == 0 {
        pending.pop();
        continue;
      }
      ensure!(
        frame.depth <= self.loader.value_depth,
        "functional value depth limit"
      );
      ensure!(forest.nodes.len() < budget, "functional value node limit");
      let parent = frame.parent;
      let depth = frame.depth;
      frame.remaining -= 1;
      let (kind, children) = match self.byte()? {
        0 => (ValueKind::Scalar(self.scalar(&artifact.limits)?), 0),
        1 => {
          let id = self.constructor_id()?;
          let count = self.count(&artifact.limits.operands)?;
          let declaration = artifact
            .constructor_indices
            .get(&id)
            .and_then(|index| artifact.constructors.get(*index))
            .context("unknown functional value constructor identity")?;
          ensure!(
            declaration.fields == BigUint::from(count),
            "functional constructor value arity"
          );
          (ValueKind::Constructor(id), count)
        },
        2 => {
          let function = self.index()?;
          let count = self.count(&artifact.limits.operands)?;
          let callee = artifact
            .functions
            .get(function)
            .context("functional PAP function index")?;
          ensure!(
            BigUint::from(count) < callee.arity,
            "functional PAP must be undersaturated"
          );
          (ValueKind::PartialApplication(function), count)
        },
        3 => (ValueKind::Erased, 0),
        4 => {
          let count = self.count(&artifact.limits.input_nodes)?;
          ensure!(count < 1usize << 32, "functional array length");
          (ValueKind::Array, count)
        },
        tag => bail!("invalid functional value tag {tag}"),
      };
      let node = forest.nodes.len();
      forest.nodes.push(ValueNode { kind, children: Vec::new() });
      if let Some(parent) = parent {
        forest.nodes[parent].children.push(node);
      } else {
        forest.roots.push(node);
      }
      forest.depth = forest.depth.max(depth);
      ensure!(
        children <= budget - forest.nodes.len(),
        "functional child node budget"
      );
      if children != 0 {
        pending.push(Frame {
          parent: Some(node),
          remaining: children,
          depth: depth
            .checked_add(1)
            .context("functional value depth overflow")?,
        });
      }
    }
    Ok(forest)
  }
}

pub(super) fn program(
  bytes: &[u8],
  loader: DecodeLimits,
) -> Result<Artifact<'_>> {
  let mut reader = Reader::new(bytes, loader)?;
  reader.header(b"IXBF")?;
  let limits = Limits {
    functions: reader.natural()?,
    constructors: reader.natural()?,
    blocks: reader.natural()?,
    locals: reader.natural()?,
    operands: reader.natural()?,
    continuations: reader.natural()?,
    input_nodes: reader.natural()?,
    nat_bits: reader.natural()?,
    string_bytes: reader.natural()?,
    byte_array_bytes: reader.natural()?,
  };
  let max_steps = reader.natural()?;
  let entry = reader.index()?;
  let count = reader.count(&limits.constructors)?;
  ensure!(
    count <= reader.syntax_remaining,
    "functional constructor syntax budget"
  );
  let mut constructors = Vec::new();
  for _ in 0..count {
    reader.syntax_node()?;
    constructors.push(ConstructorDeclaration {
      id: reader.constructor_id()?,
      fields: reader.bounded_natural(&limits.operands)?,
    });
  }
  let count = reader.count(&limits.functions)?;
  ensure!(
    count <= reader.syntax_remaining,
    "functional function syntax budget"
  );
  let mut functions = Vec::new();
  for _ in 0..count {
    functions.push(reader.function(&limits)?);
  }
  reader.finish()?;
  let mut artifact = Artifact {
    source: bytes,
    limits,
    max_steps,
    entry,
    constructors,
    constructor_indices: BTreeMap::new(),
    functions,
  };
  super::validate::program(&mut artifact)?;
  ensure!(
    artifact.encode() == bytes,
    "functional program re-encoding mismatch"
  );
  Ok(artifact)
}

pub(super) fn input<'a>(
  artifact: &Artifact<'_>,
  bytes: &'a [u8],
  loader: DecodeLimits,
) -> Result<Input<'a>> {
  let mut reader = Reader::new(bytes, loader)?;
  reader.header(b"IXFI")?;
  let count = reader.count(&artifact.limits.operands)?;
  ensure!(
    BigUint::from(count) == artifact.functions[artifact.entry].arity,
    "functional input entry arity"
  );
  let values = reader.forest(artifact, count)?;
  reader.finish()?;
  let input = Input { source: bytes, values };
  ensure!(input.encode() == bytes, "functional input re-encoding mismatch");
  Ok(input)
}

pub(super) fn output<'a>(
  artifact: &Artifact<'_>,
  bytes: &'a [u8],
  loader: DecodeLimits,
) -> Result<Output<'a>> {
  let mut reader = Reader::new(bytes, loader)?;
  reader.header(b"IXFO")?;
  let values = reader.forest(artifact, 1)?;
  reader.finish()?;
  let output = Output { source: bytes, values };
  ensure!(output.encode() == bytes, "functional output re-encoding mismatch");
  Ok(output)
}
