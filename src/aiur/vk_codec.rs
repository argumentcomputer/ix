//! (De)serialization of the verifier's key: `System<AiurCircuit>`.
//!
//! The verifier needs the system's per-circuit AIR (symbolic constraints +
//! lookups + widths), the shared preprocessed commitment, the preprocessed
//! index map, and the commitment parameters — i.e. everything in
//! [`System<AiurCircuit>`] except the prover-only preprocessed traces (the
//! large gadget tables in each `LookupAir.preprocessed`, which are
//! `#[serde(skip)]`-ed and reconstructed/committed separately).
//!
//! This uses serde (`#[derive(Serialize, Deserialize)]` on `System`, `Circuit`,
//! `LookupAir`, `Lookup`, `SymbolicExpression`, `SymbolicVariable`, `Entry`,
//! `CommitmentParameters`, and the Ix `AiurCircuit`/`Constraints`/`Memory`)
//! with the **same bincode config the proof uses**
//! (`standard().with_little_endian().with_fixed_int_encoding()`), so the wire
//! format matches `Proof`'s and can be re-implemented in Aiur the same way.

// The codec is exercised by tests today and wired to the FFI / Aiur port next.
#![allow(dead_code)]

use bincode::{
  config::{Configuration, Fixint, LittleEndian, standard},
  serde::{decode_from_slice, encode_to_vec},
};
use multi_stark::system::System;

use crate::aiur::synthesis::{AiurCircuit, AiurSystem};

/// The bincode configuration shared with `multi_stark::prover::Proof`.
fn serde_config() -> Configuration<LittleEndian, Fixint> {
  standard().with_little_endian().with_fixed_int_encoding()
}

/// Serialize the verifying key `System<AiurCircuit>` (preprocessed traces are
/// skipped — see the module docs).
pub(crate) fn to_bytes(
  system: &System<AiurCircuit>,
) -> Result<Vec<u8>, String> {
  encode_to_vec(system, serde_config()).map_err(|e| e.to_string())
}

/// Deserialize a `System<AiurCircuit>` from [`to_bytes`] output, requiring that
/// every byte is consumed.
pub(crate) fn from_bytes(bytes: &[u8]) -> Result<System<AiurCircuit>, String> {
  let (system, consumed) =
    decode_from_slice(bytes, serde_config()).map_err(|e| e.to_string())?;
  if consumed != bytes.len() {
    return Err(format!(
      "trailing data: consumed {consumed} of {}",
      bytes.len()
    ));
  }
  Ok(system)
}

/// Convenience: serialize the verifying key of a built [`AiurSystem`].
pub(crate) fn aiur_system_to_bytes(
  sys: &AiurSystem,
) -> Result<Vec<u8>, String> {
  to_bytes(&sys.system)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::aiur::gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2};
  use multi_stark::{lookup::LookupAir, types::CommitmentParameters};

  /// Build a small real `System<AiurCircuit>` from the two byte gadgets and
  /// check the verifying-key codec round-trips (re-encoding is byte-identical).
  #[test]
  fn system_vk_round_trips() {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let (system, _key) = System::new(
      cp,
      [
        LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups()),
        LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups()),
      ],
    );
    let bytes = to_bytes(&system).expect("encode");
    let back = from_bytes(&bytes).expect("decode");
    let reencoded = to_bytes(&back).expect("re-encode");
    assert_eq!(bytes, reencoded, "verifying-key codec round-trip mismatch");
  }

  #[test]
  fn rejects_trailing_bytes() {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let (system, _key) =
      System::new(cp, [LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups())]);
    let mut bytes = to_bytes(&system).expect("encode");
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "should reject trailing data");
  }
}

// ════════════════════════════════════════════════════════════════════════════
// Manual deserializer — a hand-written reader matching the exact bincode bytes
// `to_bytes` produces, decoding straight into the real `System<AiurCircuit>`.
// This is the reference re-implemented in Aiur (the verifier reads its key from
// this stream); `manual_matches_serde` proves it agrees with serde.
//
// bincode `standard().little_endian().fixed_int` layout:
//   enum tag : u32 (4 bytes LE)       Option : 1 byte (0 = None / 1 = Some)
//   usize / u64 / G : 8 bytes LE      Vec : u64 length, then elements
//   struct : fields in declaration order      Range<usize> : start, end (u64)
//   MerkleCap : Vec<[u64; 4]>         PhantomData : 0 bytes
// ════════════════════════════════════════════════════════════════════════════

use multi_stark::{
  builder::symbolic::{Entry, SymbolicExpression, SymbolicVariable},
  lookup::{Lookup, LookupAir},
  p3_field::PrimeCharacteristicRing,
  system::Circuit,
  types::{Commitment, CommitmentParameters, Val},
};

use crate::aiur::{constraints::Constraints, memory::Memory};

type Expr = SymbolicExpression<Val>;

struct R<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> R<'a> {
  fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self.pos.checked_add(n).ok_or("length overflow")?;
    if end > self.buf.len() {
      return Err(format!("eof: need {n} at offset {}", self.pos));
    }
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }
  fn u8(&mut self) -> Result<u8, String> {
    Ok(self.take(1)?[0])
  }
  fn u32(&mut self) -> Result<u32, String> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
  fn usize(&mut self) -> Result<usize, String> {
    usize::try_from(self.u64()?).map_err(|e| format!("usize overflow: {e}"))
  }
  fn g(&mut self) -> Result<Val, String> {
    Ok(Val::from_u64(self.u64()?))
  }
  fn entry(&mut self) -> Result<Entry, String> {
    Ok(match self.u32()? {
      0 => Entry::Preprocessed { offset: self.usize()? },
      1 => Entry::Main { offset: self.usize()? },
      2 => Entry::Stage2 { offset: self.usize()? },
      3 => Entry::Public,
      4 => Entry::Stage2Public,
      5 => Entry::Challenge,
      t => return Err(format!("bad Entry tag {t}")),
    })
  }
  fn expr(&mut self) -> Result<Expr, String> {
    Ok(match self.u32()? {
      0 => SymbolicExpression::Variable(SymbolicVariable::new(
        self.entry()?,
        self.usize()?,
      )),
      1 => SymbolicExpression::IsFirstRow,
      2 => SymbolicExpression::IsLastRow,
      3 => SymbolicExpression::IsTransition,
      4 => SymbolicExpression::Constant(self.g()?),
      5 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        SymbolicExpression::Add { x, y, degree_multiple: self.usize()? }
      },
      6 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        SymbolicExpression::Sub { x, y, degree_multiple: self.usize()? }
      },
      7 => {
        let x = Box::new(self.expr()?);
        SymbolicExpression::Neg { x, degree_multiple: self.usize()? }
      },
      8 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        SymbolicExpression::Mul { x, y, degree_multiple: self.usize()? }
      },
      t => return Err(format!("bad SymbolicExpression tag {t}")),
    })
  }
  fn vec<T>(
    &mut self,
    mut f: impl FnMut(&mut Self) -> Result<T, String>,
  ) -> Result<Vec<T>, String> {
    let n = self.usize()?;
    let mut v = Vec::with_capacity(n.min(1 << 16));
    for _ in 0..n {
      v.push(f(self)?);
    }
    Ok(v)
  }
  fn lookup(&mut self) -> Result<Lookup<Expr>, String> {
    Ok(Lookup { multiplicity: self.expr()?, args: self.vec(Self::expr)? })
  }
  fn aircircuit(&mut self) -> Result<AiurCircuit, String> {
    Ok(match self.u32()? {
      0 => AiurCircuit::Function(Constraints {
        zeros: self.vec(Self::expr)?,
        selectors: self.usize()?..self.usize()?,
        width: self.usize()?,
      }),
      1 => AiurCircuit::Memory(Memory { width: self.usize()? }),
      2 => AiurCircuit::Bytes1,
      3 => AiurCircuit::Bytes2,
      t => return Err(format!("bad AiurCircuit tag {t}")),
    })
  }
  fn circuit(&mut self) -> Result<Circuit<AiurCircuit>, String> {
    // LookupAir: inner_air, lookups (preprocessed is `#[serde(skip)]` -> None).
    let air = LookupAir {
      inner_air: self.aircircuit()?,
      lookups: self.vec(Self::lookup)?,
      preprocessed: None,
    };
    Ok(Circuit {
      air,
      constraint_count: self.usize()?,
      max_constraint_degree: self.usize()?,
      preprocessed_height: self.usize()?,
      preprocessed_width: self.usize()?,
      stage_1_width: self.usize()?,
      stage_2_width: self.usize()?,
    })
  }
  fn commitment(&mut self) -> Result<Commitment, String> {
    let caps = self.vec(|r| Ok([r.u64()?, r.u64()?, r.u64()?, r.u64()?]))?;
    Ok(Commitment::from(caps))
  }
  fn option<T>(
    &mut self,
    f: impl FnOnce(&mut Self) -> Result<T, String>,
  ) -> Result<Option<T>, String> {
    match self.u8()? {
      0 => Ok(None),
      1 => Ok(Some(f(self)?)),
      t => Err(format!("bad Option tag {t}")),
    }
  }
}

/// Hand-written deserializer of the verifying-key `System<AiurCircuit>`,
/// matching serde/bincode byte-for-byte (the Aiur port mirrors this).
pub(crate) fn manual_deserialize(
  bytes: &[u8],
) -> Result<System<AiurCircuit>, String> {
  let mut r = R { buf: bytes, pos: 0 };
  let commitment_parameters =
    CommitmentParameters { log_blowup: r.usize()?, cap_height: r.usize()? };
  let circuits = r.vec(R::circuit)?;
  let preprocessed_commit = r.option(R::commitment)?;
  let preprocessed_indices = r.vec(|r| r.option(R::usize))?;
  if r.pos != bytes.len() {
    return Err(format!(
      "trailing data: consumed {} of {}",
      r.pos,
      bytes.len()
    ));
  }
  Ok(System {
    commitment_parameters,
    circuits,
    preprocessed_commit,
    preprocessed_indices,
  })
}

#[cfg(test)]
mod manual_tests {
  use super::*;
  use crate::aiur::gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2};
  use multi_stark::{lookup::LookupAir, types::CommitmentParameters};

  /// The manual deserializer agrees with serde: decoding serde's bytes and
  /// re-encoding with serde reproduces them byte-for-byte.
  #[test]
  fn manual_matches_serde() {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let (system, _key) = System::new(
      cp,
      [
        LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups()),
        LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups()),
      ],
    );
    let bytes = to_bytes(&system).expect("serde encode");
    let manual = manual_deserialize(&bytes).expect("manual decode");
    let reencoded = to_bytes(&manual).expect("serde re-encode");
    assert_eq!(bytes, reencoded, "manual deserializer disagrees with serde");
  }

  #[test]
  fn manual_rejects_trailing() {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let (system, _key) =
      System::new(cp, [LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups())]);
    let mut bytes = to_bytes(&system).expect("encode");
    bytes.push(0);
    assert!(manual_deserialize(&bytes).is_err());
  }
}
