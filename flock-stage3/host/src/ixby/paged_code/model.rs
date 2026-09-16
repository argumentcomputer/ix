use crate::{
  hash::pack_bytes,
  ixby::{ixbf::*, paged_value::PROGRAM_BYTES},
};
use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use num_bigint::BigUint;

pub const FUNCTIONS: u64 = 1 << 36;
pub const BLOCKS: u64 = 2 << 36;
pub const CONSTRUCTORS: u64 = 3 << 36;
pub fn block_address(function: u16, block: u8) -> u64 {
  assert!(function < 1024);
  BLOCKS + (u64::from(function) << 16) + (u64::from(block) << 8)
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Header {
  pub locals: u8,
  pub instruction: u8,
  pub operation: u8,
  pub primitive: u8,
  pub operands: u8,
  pub arguments: u8,
  pub alternatives: u8,
  pub reference: u16,
  pub target: u8,
  pub other_target: u8,
  pub projection: u16,
}
impl Header {
  pub fn words(self) -> [F128; 2] {
    [
      F128::new(
        u64::from(self.locals)
          | u64::from(self.instruction) << 8
          | u64::from(self.operation) << 16
          | u64::from(self.primitive) << 24
          | u64::from(self.operands) << 32
          | u64::from(self.arguments) << 40
          | u64::from(self.alternatives) << 48,
        u64::from(self.reference)
          | u64::from(self.target) << 16
          | u64::from(self.other_target) << 24
          | u64::from(self.projection) << 32,
      ),
      F128::ZERO,
    ]
  }
}
fn small(n: &BigUint, maximum: u64) -> Result<u64> {
  let digits = n.to_u64_digits();
  ensure!(
    digits.len() <= 1 && digits.first().copied().unwrap_or(0) <= maximum,
    "paged physical integer capacity"
  );
  Ok(digits.first().copied().unwrap_or(0))
}
fn magnitude(n: &BigUint) -> Result<F128> {
  let digits = n.to_u64_digits();
  ensure!(digits.len() <= 2, "paged physical Nat128 capacity");
  Ok(F128::new(
    digits.first().copied().unwrap_or(0),
    digits.get(1).copied().unwrap_or(0),
  ))
}
fn source_range(source: &[u8], slice: &[u8]) -> Result<F128> {
  if slice.is_empty() {
    return Ok(F128::ZERO);
  }
  let offset = (slice.as_ptr() as usize)
    .checked_sub(source.as_ptr() as usize)
    .context("literal source range")?;
  ensure!(
    source.get(offset..offset + slice.len()) == Some(slice),
    "literal does not belong to original source"
  );
  Ok(F128::new((PROGRAM_BYTES << 5) + offset as u64, slice.len() as u64))
}
fn operand(source: &[u8], value: &Operand<'_>) -> Result<[F128; 2]> {
  let (tag, payload) = match value {
    Operand::Local(index) => (0, F128::new(small(index, 127)?, 0)),
    Operand::Erased => (5, F128::ZERO),
    Operand::Literal(value) => match value {
      Scalar::Nat(n) => (8, magnitude(n)?),
      Scalar::Bool(v) => (1, F128::new(u64::from(*v), 0)),
      Scalar::Word32(v) => (2, F128::new(u64::from(*v), 0)),
      Scalar::Goldilocks(v) => (3, F128::new(*v, 0)),
      Scalar::Extension(v) => (4, F128::new(v[0], v[1])),
      Scalar::Bytes(v) => (6, source_range(source, v)?),
      Scalar::String(v) => (10, source_range(source, v.as_bytes())?),
    },
  };
  Ok([F128::new(tag, 0), payload])
}
fn operands<'a>(
  header: &mut Header,
  values: &'a [Operand<'a>],
) -> Result<Vec<&'a Operand<'a>>> {
  ensure!(values.len() <= 64, "paged argument capacity");
  header.arguments = values.len() as u8;
  Ok(values.iter().collect())
}
fn function_index(index: usize) -> Result<u16> {
  ensure!(index < 1024, "paged function index");
  Ok(index as u16)
}
fn target(index: usize) -> Result<u8> {
  index.try_into().context("paged block index")
}
fn block<'a>(
  value: &'a Block<'a>,
) -> Result<(Header, Vec<&'a Operand<'a>>, Vec<Alternative>)> {
  let mut h =
    Header { locals: small(&value.locals, 128)? as u8, ..Header::default() };
  let mut alts = Vec::new();
  let values = match &value.instruction {
    Instruction::Let(op, next) => {
      h.target = target(*next)?;
      match op {
        Operation::Copy(v) => vec![v],
        Operation::Primitive(prim, args) => {
          h.operation = 1;
          h.primitive = prim.opcode();
          operands(&mut h, args)?
        },
        Operation::Construct(index, args) => {
          h.operation = 2;
          ensure!(*index < 256, "paged constructor index");
          h.reference = *index as u16;
          operands(&mut h, args)?
        },
        Operation::Project(v, field) => {
          h.operation = 3;
          h.projection = small(field, u16::MAX as u64)? as u16;
          vec![v]
        },
        Operation::Closure(index, args) => {
          h.operation = 4;
          h.reference = function_index(*index)?;
          operands(&mut h, args)?
        },
        Operation::Call(index, args) => {
          h.operation = 5;
          h.reference = function_index(*index)?;
          operands(&mut h, args)?
        },
        Operation::CallSelf(args) => {
          h.operation = 6;
          operands(&mut h, args)?
        },
        Operation::Apply(v, args) => {
          h.operation = 7;
          let mut values = operands(&mut h, args)?;
          values.insert(0, v);
          values
        },
      }
    },
    Instruction::Return(v) => {
      h.instruction = 1;
      vec![v]
    },
    Instruction::TailCall(index, args) => {
      h.instruction = 2;
      h.reference = function_index(*index)?;
      operands(&mut h, args)?
    },
    Instruction::TailCallSelf(args) => {
      h.instruction = 3;
      operands(&mut h, args)?
    },
    Instruction::TailApply(v, args) => {
      h.instruction = 4;
      let mut values = operands(&mut h, args)?;
      values.insert(0, v);
      values
    },
    Instruction::CaseConstructor(v, alternatives) => {
      h.instruction = 5;
      ensure!(alternatives.len() <= 128, "paged alternative capacity");
      h.alternatives = alternatives.len() as u8;
      alts.clone_from(alternatives);
      vec![v]
    },
    Instruction::CaseNat(v, yes, no) => {
      h.instruction = 6;
      h.target = target(*yes)?;
      h.other_target = target(*no)?;
      vec![v]
    },
    Instruction::Branch(v, yes, no) => {
      h.instruction = 7;
      h.target = target(*yes)?;
      h.other_target = target(*no)?;
      vec![v]
    },
  };
  h.operands = values.len() as u8;
  Ok((h, values, alts))
}

/// Native advice only. The source bytes remain intact, and byte literals use
/// offsets into their original byte bank rather than new host-supplied hashes.
pub struct PackedProgram {
  pub cells: Vec<(u64, [F128; 2])>,
}
impl PackedProgram {
  pub fn from_artifact(artifact: &Artifact<'_>) -> Result<Self> {
    ensure!(
      artifact.functions().len() <= 1024
        && artifact.constructors().len() <= 256,
      "paged declaration capacities"
    );
    let mut cells = Vec::new();
    for (index, function) in artifact.functions().iter().enumerate() {
      ensure!(function.blocks.len() <= 256, "paged function block capacity");
      let arity = small(&function.arity, 64)?;
      cells.push((
        FUNCTIONS + index as u64,
        [
          F128::new(
            arity
              | u64::from(target(function.entry)?) << 8
              | (function.blocks.len() as u64) << 16,
            0,
          ),
          F128::ZERO,
        ],
      ));
      for (at, value) in function.blocks.iter().enumerate() {
        let address = block_address(index as u16, at as u8);
        let (header, values, alternatives) = block(value)?;
        cells.push((address, header.words()));
        for (i, value) in values.into_iter().enumerate() {
          cells
            .push((address + 1 + i as u64, operand(artifact.source(), value)?));
        }
        for (i, alternative) in alternatives.into_iter().enumerate() {
          ensure!(
            alternative.constructor < 256,
            "paged alternative constructor index"
          );
          cells.push((
            address + 128 + i as u64,
            [
              F128::new(
                alternative.constructor as u64
                  | u64::from(target(alternative.target)?) << 8,
                0,
              ),
              F128::ZERO,
            ],
          ));
        }
      }
    }
    for (index, decl) in artifact.constructors().iter().enumerate() {
      let address = CONSTRUCTORS + 3 * index as u64;
      cells.push((
        address,
        [pack_bytes(&decl.id.block[..16]), pack_bytes(&decl.id.block[16..])],
      ));
      cells.push((
        address + 1,
        [magnitude(&decl.id.member)?, magnitude(&decl.id.tag)?],
      ));
      cells.push((
        address + 2,
        [F128::new(small(&decl.fields, 64)?, 0), F128::ZERO],
      ));
    }
    for (i, bytes) in artifact.source().chunks(32).enumerate() {
      let mut cell = [0u8; 32];
      cell[..bytes.len()].copy_from_slice(bytes);
      cells.push((
        PROGRAM_BYTES + i as u64,
        [pack_bytes(&cell[..16]), pack_bytes(&cell[16..])],
      ));
    }
    Ok(Self { cells })
  }
}
