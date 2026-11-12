//! Wide field data uses the ordinary package structure with a versioned scalar
//! encoding. Decoding validates transport values, not the primality of the
//! modulus or the program's execution semantics.
use super::{
  Digest, PACKAGE_MAGIC, Reader, WIDE_FORMAT_VERSION, Writer, header, program,
  put_program, put_trace, trace,
};
use crate::{
  bytecode::{Instruction, Program},
  field_word::FieldWord,
  trace::{Action, Polynomial, TraceArtifact},
};
use std::path::Path;

/// A package whose moduli and field constants can occupy up to four limbs.
/// Prepare `program` with a matching `FieldBackend<Word = FieldWord>` to execute
/// native field elements. The companion trace remains transport data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WidePackage {
  pub program: Program<FieldWord>,
  pub trace: Option<TraceArtifact<FieldWord>>,
}

impl WidePackage {
  /// Read versions 1, 2 or 3, preserving every field bit. Narrow encodings
  /// are promoted without reduction; version 3 field words are canonical.
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    let mut r = Reader::new(bytes);
    let format = header(&mut r, PACKAGE_MAGIC)?;
    let package = Self {
      program: program(&mut r, format)?,
      trace: r.option(|r| trace(r, format))?,
    };
    r.finish()?;
    package.validate()?;
    Ok(package)
  }

  /// Emit version 3 after checking the modulus and every field constant.
  /// Structural counts, indices and semantic versions remain TagN u64.
  pub fn encode(&self) -> Result<Vec<u8>, String> {
    self.validate()?;
    let mut w = Writer::new();
    w.raw(PACKAGE_MAGIC);
    w.nat(WIDE_FORMAT_VERSION);
    put_program(&mut w, &self.program);
    w.option(self.trace.as_ref(), put_trace);
    Ok(w.into_bytes())
  }

  pub fn load(path: &Path) -> Result<(Self, Digest), String> {
    let (bytes, digest) = super::read(path)?;
    Ok((Self::decode(&bytes)?, digest))
  }

  pub fn validate(&self) -> Result<(), String> {
    let modulus = self.program.modulus;
    modulus.validate_modulus()?;
    for function in &self.program.functions {
      for instruction in &function.code {
        match instruction {
          Instruction::Literal { value, .. } => {
            value.validate_field(modulus)?
          },
          Instruction::Guard { tests, .. }
          | Instruction::Branch { tests, .. } => {
            for &(_, value) in tests {
              value.validate_field(modulus)?;
            }
          },
          _ => {},
        }
      }
    }
    for table in &self.program.tables {
      for &value in table.rows.iter().flatten() {
        value.validate_field(modulus)?;
      }
    }
    let Some(trace) = &self.trace else { return Ok(()) };
    if trace.modulus != modulus {
      return Err("program and trace field moduli differ".into());
    }
    for function in &trace.functions {
      for step in &function.steps {
        validate_poly(&step.guard, modulus)?;
        match &step.action {
          Action::Assign { values, .. } | Action::Store { values, .. } => {
            validate_polys(values, modulus)?;
          },
          Action::Inverse { value, .. } => validate_poly(value, modulus)?,
          Action::Choose { tests, .. } => {
            for test in tests {
              validate_polys(test, modulus)?;
            }
          },
          Action::Failure { differences, .. } => {
            validate_polys(differences, modulus)?
          },
          Action::Call { args, .. } => validate_polys(args, modulus)?,
          Action::Load { address, .. } => validate_poly(address, modulus)?,
          Action::Hint { key, .. } => validate_polys(key, modulus)?,
        }
      }
      for write in &function.writes {
        validate_poly(&write.guard, modulus)?;
      }
    }
    for chip in &trace.chips {
      validate_polys(&chip.output, modulus)?;
      validate_polys(&chip.constraints, modulus)?;
      for send in &chip.sends {
        validate_polys(&send.args, modulus)?;
        validate_poly(&send.enable, modulus)?;
      }
      for memory in &chip.memory {
        validate_poly(&memory.address, modulus)?;
        validate_polys(&memory.values, modulus)?;
        validate_poly(&memory.enable, modulus)?;
      }
    }
    for group in &trace.groups {
      validate_poly(&group.activation, modulus)?;
      validate_polys(&group.constraints, modulus)?;
      validate_polys(&group.receive, modulus)?;
      for send in &group.sends {
        validate_poly(&send.enable, modulus)?;
        validate_polys(&send.args, modulus)?;
      }
      for member in &group.members {
        for write in &member.writes {
          validate_poly(&write.value, modulus)?;
        }
      }
    }
    Ok(())
  }
}

fn validate_polys(
  polynomials: &[Polynomial<FieldWord>],
  modulus: FieldWord,
) -> Result<(), String> {
  for polynomial in polynomials {
    validate_poly(polynomial, modulus)?;
  }
  Ok(())
}

fn validate_poly(
  polynomial: &Polynomial<FieldWord>,
  modulus: FieldWord,
) -> Result<(), String> {
  let mut pending = vec![polynomial];
  while let Some(polynomial) = pending.pop() {
    match polynomial {
      Polynomial::Const(value) => value.validate_field(modulus)?,
      Polynomial::Var(_) => {},
      Polynomial::Add(operands)
      | Polynomial::Sub(operands)
      | Polynomial::Mul(operands) => {
        pending.extend(operands.iter());
      },
    }
  }
  Ok(())
}
