use super::model::*;
use anyhow::{Context, Result, ensure};
use num_bigint::BigUint;
use std::collections::BTreeSet;

pub(super) fn scalar(limits: &Limits, value: &Scalar<'_>) -> Result<()> {
  match value {
    Scalar::Nat(value) => ensure!(
      BigUint::from(value.bits()) <= limits.nat_bits,
      "functional Nat bit limit"
    ),
    Scalar::String(value) => ensure!(
      BigUint::from(value.len()) <= limits.string_bytes,
      "functional UTF-8 byte limit"
    ),
    Scalar::Bytes(value) => ensure!(
      BigUint::from(value.len()) <= limits.byte_array_bytes,
      "functional byte-array limit"
    ),
    _ => {},
  }
  Ok(())
}

fn operand(
  limits: &Limits,
  locals: &BigUint,
  value: &Operand<'_>,
) -> Result<()> {
  match value {
    Operand::Local(slot) => {
      ensure!(slot < locals, "functional local reference")
    },
    Operand::Literal(value) => scalar(limits, value)?,
    Operand::Erased => {},
  }
  Ok(())
}

fn operands(
  limits: &Limits,
  locals: &BigUint,
  values: &[Operand<'_>],
) -> Result<()> {
  ensure!(
    BigUint::from(values.len()) <= limits.operands,
    "functional operand count limit"
  );
  for value in values {
    operand(limits, locals, value)?;
  }
  Ok(())
}

fn target(
  function: &Function<'_>,
  block: usize,
  locals: &BigUint,
) -> Result<()> {
  let block =
    function.blocks.get(block).context("functional target block index")?;
  ensure!(&block.locals == locals, "functional successor local-frame contract");
  Ok(())
}

fn direct_call(
  artifact: &Artifact<'_>,
  locals: &BigUint,
  callee: usize,
  args: &[Operand<'_>],
) -> Result<()> {
  operands(&artifact.limits, locals, args)?;
  let callee =
    artifact.functions.get(callee).context("functional call function index")?;
  ensure!(
    BigUint::from(args.len()) == callee.arity,
    "functional direct-call arity"
  );
  Ok(())
}

fn operation(
  artifact: &Artifact<'_>,
  function: usize,
  locals: &BigUint,
  op: &Operation<'_>,
) -> Result<()> {
  match op {
    Operation::Copy(value) | Operation::Project(value, _) => {
      operand(&artifact.limits, locals, value)?
    },
    Operation::Primitive(primitive, args) => {
      operands(&artifact.limits, locals, args)?;
      ensure!(args.len() == primitive.arity(), "functional primitive arity");
    },
    Operation::Construct(constructor, args) => {
      operands(&artifact.limits, locals, args)?;
      let declaration = artifact
        .constructors
        .get(*constructor)
        .context("functional constructor index")?;
      ensure!(
        BigUint::from(args.len()) == declaration.fields,
        "functional construction arity"
      );
    },
    Operation::Closure(callee, args) => {
      operands(&artifact.limits, locals, args)?;
      let callee = artifact
        .functions
        .get(*callee)
        .context("functional closure function index")?;
      ensure!(
        BigUint::from(args.len()) < callee.arity,
        "functional closure must be undersaturated"
      );
    },
    Operation::Call(callee, args) => {
      direct_call(artifact, locals, *callee, args)?
    },
    Operation::CallSelf(args) => direct_call(artifact, locals, function, args)?,
    Operation::Apply(value, args) => {
      operand(&artifact.limits, locals, value)?;
      operands(&artifact.limits, locals, args)?;
    },
  }
  Ok(())
}

fn instruction(
  artifact: &Artifact<'_>,
  self_index: usize,
  function: &Function<'_>,
  block: &Block<'_>,
) -> Result<()> {
  ensure!(
    block.locals <= artifact.limits.locals,
    "functional local-frame limit"
  );
  let locals = &block.locals;
  match &block.instruction {
    Instruction::Let(op, next) => {
      operation(artifact, self_index, locals, op)?;
      target(function, *next, &(locals + 1u8))?;
    },
    Instruction::Return(value) => operand(&artifact.limits, locals, value)?,
    Instruction::TailCall(callee, args) => {
      direct_call(artifact, locals, *callee, args)?
    },
    Instruction::TailCallSelf(args) => {
      direct_call(artifact, locals, self_index, args)?
    },
    Instruction::TailApply(value, args) => {
      operand(&artifact.limits, locals, value)?;
      operands(&artifact.limits, locals, args)?;
    },
    Instruction::CaseConstructor(value, alternatives) => {
      operand(&artifact.limits, locals, value)?;
      ensure!(
        BigUint::from(alternatives.len()) <= artifact.limits.constructors,
        "functional constructor alternative limit"
      );
      let mut seen = BTreeSet::new();
      for alternative in alternatives {
        ensure!(
          seen.insert(alternative.constructor),
          "duplicate functional case alternative"
        );
        let declaration = artifact
          .constructors
          .get(alternative.constructor)
          .context("functional case constructor index")?;
        target(function, alternative.target, &(locals + &declaration.fields))?;
      }
    },
    Instruction::CaseNat(value, zero, successor) => {
      operand(&artifact.limits, locals, value)?;
      target(function, *zero, locals)?;
      target(function, *successor, &(locals + 1u8))?;
    },
    Instruction::Branch(value, yes, no) => {
      operand(&artifact.limits, locals, value)?;
      target(function, *yes, locals)?;
      target(function, *no, locals)?;
    },
  }
  Ok(())
}

/// Mirrors structural `Ix.Ixby.validateProgram`, not dynamic typing,
/// termination, source reflection, or satisfaction of a Flock circuit.
pub(super) fn program(artifact: &mut Artifact<'_>) -> Result<()> {
  ensure!(
    BigUint::from(artifact.functions.len()) <= artifact.limits.functions,
    "functional function limit"
  );
  ensure!(
    BigUint::from(artifact.constructors.len()) <= artifact.limits.constructors,
    "functional constructor limit"
  );
  for (index, declaration) in artifact.constructors.iter().enumerate() {
    ensure!(
      declaration.fields <= artifact.limits.operands,
      "functional constructor field limit"
    );
    ensure!(
      artifact
        .constructor_indices
        .insert(declaration.id.clone(), index)
        .is_none(),
      "duplicate functional constructor identity"
    );
  }
  for (function_index, function) in artifact.functions.iter().enumerate() {
    ensure!(
      function.arity <= artifact.limits.operands,
      "functional function operand limit"
    );
    ensure!(
      function.arity <= artifact.limits.locals,
      "functional function local limit"
    );
    ensure!(
      BigUint::from(function.blocks.len()) <= artifact.limits.blocks,
      "functional block limit"
    );
    target(function, function.entry, &function.arity).with_context(|| {
      format!("functional entry frame of function {function_index}")
    })?;
    for (block_index, block) in function.blocks.iter().enumerate() {
      instruction(artifact, function_index, function, block).with_context(
        || format!("functional function {function_index} block {block_index}"),
      )?;
    }
  }
  ensure!(
    artifact.entry < artifact.functions.len(),
    "functional program entry function"
  );
  Ok(())
}
