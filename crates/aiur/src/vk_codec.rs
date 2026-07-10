//! (De)serialization of the verifier's key: `System<AiurCircuit>`.
//!
//! The verifier needs the system's per-circuit AIR (symbolic constraints +
//! lookups + widths), the shared preprocessed commitment, the preprocessed
//! index map, and the commitment + FRI parameters (which seed the config's
//! challenger) — i.e. everything in [`System<AiurCircuit>`] except the
//! prover-only preprocessed traces (the large gadget tables in each
//! `LookupAir.preprocessed`), which are reconstructed/committed separately
//! and so are *not* serialized.
//!
//! This is a **hand-written, serde-free** codec. `multi-stark` does not derive
//! `serde` on its types, and we do not want to fork it just to add the derives,
//! so the encoder and decoder are written by hand against the public fields of
//! `System`, `Circuit`, `LookupAir`, `Lookup`, `SymbolicExpression`,
//! `SymbolicVariable`, `Entry`, `CommitmentParameters`, `FriParameters` and
//! the Ix `AiurCircuit`/`Constraints`/`Memory`. The wire format mirrors the
//! `bincode standard().little_endian().fixed_int` layout the proof uses, so the
//! Aiur port (`Ix/MultiStark/SystemDeserialize.lean`) can read it the same way.
//!
//! Wire format:
//!   enum tag : u32 (4 bytes LE)       Option : 1 byte (0 = None / 1 = Some)
//!   usize / u64 : 8 bytes LE          Vec : u64 length, then elements
//!   struct : fields in declaration order      Range<usize> : start, end (u64)
//!   Goldilocks `G` : canonical u64, 8 bytes LE (the Lean side reduces mod p on
//!                    read; canonical and raw representations agree there)
//!   MerkleCap : Vec<[u64; 4]>         PhantomData : 0 bytes
//!
//! Goldilocks note: bincode/serde would write Goldilocks' *raw* internal `u64`,
//! but that field is `pub(crate)` inside `p3_goldilocks` and unreachable here.
//! We instead write `as_canonical_u64()` (the reduced value) and read it back
//! with `from_u64`. The constants that appear in a verifying key are canonical,
//! and the Lean reader reduces mod p regardless, so the two representations are
//! interchangeable.

// The codec is exercised by tests and wired to the FFI / Aiur port.
#![allow(dead_code)]

use multi_stark::{
  builder::symbolic::{Entry, SymbolicExpression, SymbolicVariable},
  lookup::{Lookup, LookupAir},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::Matrix,
  system::{Circuit, System},
  types::{Commitment, CommitmentParameters, FriParameters, Val},
};

use crate::{
  constraints::Constraints,
  memory::Memory,
  synthesis::{AiurCircuit, AiurConfig, AiurSystem},
};

type Expr = SymbolicExpression<Val>;

// ════════════════════════════════════════════════════════════════════════════
// Encoder — System<AiurCircuit> -> bytes
// ════════════════════════════════════════════════════════════════════════════

struct W {
  buf: Vec<u8>,
}

impl W {
  fn u8(&mut self, v: u8) {
    self.buf.push(v);
  }
  fn u32(&mut self, v: u32) {
    self.buf.extend_from_slice(&v.to_le_bytes());
  }
  fn u64(&mut self, v: u64) {
    self.buf.extend_from_slice(&v.to_le_bytes());
  }
  fn usize(&mut self, v: usize) {
    self.u64(v as u64);
  }
  fn g(&mut self, v: Val) {
    // Goldilocks' raw repr is unreachable; the canonical value round-trips.
    self.u64(v.as_canonical_u64());
  }
  fn entry(&mut self, e: &Entry) {
    match *e {
      Entry::Preprocessed { offset } => {
        self.u32(0);
        self.usize(offset);
      },
      Entry::Main { offset } => {
        self.u32(1);
        self.usize(offset);
      },
      Entry::Stage2 { offset } => {
        self.u32(2);
        self.usize(offset);
      },
      Entry::Public => self.u32(3),
      Entry::Stage2Public => self.u32(4),
      Entry::Challenge => self.u32(5),
    }
  }
  fn expr(&mut self, e: &Expr) {
    match e {
      SymbolicExpression::Variable(v) => {
        self.u32(0);
        self.entry(&v.entry);
        self.usize(v.index);
      },
      SymbolicExpression::IsFirstRow => self.u32(1),
      SymbolicExpression::IsLastRow => self.u32(2),
      SymbolicExpression::IsTransition => self.u32(3),
      SymbolicExpression::Constant(c) => {
        self.u32(4);
        self.g(*c);
      },
      SymbolicExpression::Add { x, y, degree_multiple } => {
        self.u32(5);
        self.expr(x);
        self.expr(y);
        self.usize(*degree_multiple);
      },
      SymbolicExpression::Sub { x, y, degree_multiple } => {
        self.u32(6);
        self.expr(x);
        self.expr(y);
        self.usize(*degree_multiple);
      },
      SymbolicExpression::Neg { x, degree_multiple } => {
        self.u32(7);
        self.expr(x);
        self.usize(*degree_multiple);
      },
      SymbolicExpression::Mul { x, y, degree_multiple } => {
        self.u32(8);
        self.expr(x);
        self.expr(y);
        self.usize(*degree_multiple);
      },
    }
  }
  fn vec<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Self, &T)) {
    self.usize(items.len());
    for item in items {
      f(self, item);
    }
  }
  fn lookup(&mut self, l: &Lookup<Expr>) {
    self.expr(&l.multiplicity);
    self.vec(&l.args, Self::expr);
  }
  fn aircircuit(&mut self, c: &AiurCircuit) {
    match c {
      AiurCircuit::Function(Constraints { zeros, selectors, width }) => {
        self.u32(0);
        self.vec(zeros, Self::expr);
        self.usize(selectors.start);
        self.usize(selectors.end);
        self.usize(*width);
      },
      AiurCircuit::Memory(Memory { width }) => {
        self.u32(1);
        self.usize(*width);
      },
      AiurCircuit::Bytes1 => self.u32(2),
      AiurCircuit::Bytes2 => self.u32(3),
    }
  }
  fn circuit(&mut self, c: &Circuit<AiurCircuit, Val>) {
    // LookupAir: inner_air, lookups (preprocessed is not serialized).
    self.aircircuit(&c.air.inner_air);
    self.vec(&c.air.lookups, Self::lookup);
    self.usize(c.constraint_count);
    self.usize(c.max_constraint_degree);
    self.usize(c.preprocessed_height);
    self.usize(c.preprocessed_width);
    self.usize(c.stage_1_width);
    self.usize(c.stage_2_width);
  }
  fn commitment(&mut self, c: &Commitment) {
    // MerkleCap: Vec<[u8; 32]> Blake3 digests (raw bytes).
    self.vec(c.roots(), |w, digest: &[u8; 32]| {
      for &byte in digest {
        w.u8(byte);
      }
    });
  }
  fn option<T>(&mut self, o: &Option<T>, f: impl FnOnce(&mut Self, &T)) {
    match o {
      None => self.u8(0),
      Some(v) => {
        self.u8(1);
        f(self, v);
      },
    }
  }
}

/// Serialize the verifying key `System<AiurCircuit>` (preprocessed traces are
/// skipped — see the module docs). The config's construction parameters are
/// passed alongside because [`AiurConfig`] doesn't expose them back; they are
/// written first so the decoder can rebuild the config.
pub(crate) fn to_bytes(
  system: &System<AiurConfig, AiurCircuit>,
  commitment_parameters: CommitmentParameters,
  fri_parameters: FriParameters,
) -> Vec<u8> {
  let mut w = W { buf: Vec::new() };
  w.usize(commitment_parameters.log_blowup);
  w.usize(commitment_parameters.cap_height);
  w.usize(fri_parameters.log_final_poly_len);
  w.usize(fri_parameters.max_log_arity);
  w.usize(fri_parameters.num_queries);
  w.usize(fri_parameters.commit_proof_of_work_bits);
  w.usize(fri_parameters.query_proof_of_work_bits);
  w.vec(&system.circuits, W::circuit);
  w.option(&system.preprocessed_commit, W::commitment);
  w.vec(&system.preprocessed_indices, |w, idx| {
    w.option(idx, |w, &i| w.usize(i))
  });
  w.buf
}

/// Convenience: serialize the verifying key of a built [`AiurSystem`].
pub fn aiur_system_to_bytes(sys: &AiurSystem) -> Result<Vec<u8>, String> {
  Ok(to_bytes(&sys.system, sys.commitment_parameters, sys.fri_parameters))
}

// ════════════════════════════════════════════════════════════════════════════
// Decoder — bytes -> System<AiurCircuit>
//
// A hand-written reader matching the bytes `to_bytes` produces, decoding
// straight into the real `System<AiurCircuit>`. This is the reference
// re-implemented in Aiur (`Ix/MultiStark/SystemDeserialize.lean`).
// ════════════════════════════════════════════════════════════════════════════

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
  fn circuit(&mut self) -> Result<Circuit<AiurCircuit, Val>, String> {
    // LookupAir: inner_air, lookups. The preprocessed trace is not in the
    // wire format, but it is NOT prover-only: `LookupAir::eval` dispatches on
    // `preprocessed.is_some()`, so a verifier with `None` here would evaluate
    // the gadget circuits' preprocessed-column expressions against nothing
    // and panic. The gadget tables are deterministic functions of the inner
    // air, so `LookupAir::new` regenerates them.
    let inner_air = self.aircircuit()?;
    let lookups = self.vec(Self::lookup)?;
    let air = LookupAir::new(inner_air, lookups);
    let circuit = Circuit {
      air,
      constraint_count: self.usize()?,
      max_constraint_degree: self.usize()?,
      preprocessed_height: self.usize()?,
      preprocessed_width: self.usize()?,
      stage_1_width: self.usize()?,
      stage_2_width: self.usize()?,
    };
    // The serialized dimensions must describe the regenerated table.
    let (height, width) = circuit
      .air
      .preprocessed
      .as_ref()
      .map_or((0, 0), |m| (m.height(), m.width()));
    if (height, width)
      != (circuit.preprocessed_height, circuit.preprocessed_width)
    {
      return Err(format!(
        "preprocessed trace is {height}x{width}, but the vk declares {}x{}",
        circuit.preprocessed_height, circuit.preprocessed_width
      ));
    }
    Ok(circuit)
  }
  fn commitment(&mut self) -> Result<Commitment, String> {
    let caps = self.vec(|r| {
      let mut d = [0u8; 32];
      for b in d.iter_mut() {
        *b = r.u8()?;
      }
      Ok(d)
    })?;
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

/// Deserialize a `System<AiurCircuit>` from [`to_bytes`] output, requiring that
/// every byte is consumed. Also returns the config's construction parameters,
/// which the `System` itself doesn't expose.
pub(crate) fn from_bytes(
  bytes: &[u8],
) -> Result<
  (System<AiurConfig, AiurCircuit>, CommitmentParameters, FriParameters),
  String,
> {
  let mut r = R { buf: bytes, pos: 0 };
  let commitment_parameters =
    CommitmentParameters { log_blowup: r.usize()?, cap_height: r.usize()? };
  let fri_parameters = FriParameters {
    log_final_poly_len: r.usize()?,
    max_log_arity: r.usize()?,
    num_queries: r.usize()?,
    commit_proof_of_work_bits: r.usize()?,
    query_proof_of_work_bits: r.usize()?,
  };
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
  let system = System {
    config: AiurConfig::new(commitment_parameters, fri_parameters),
    circuits,
    preprocessed_commit,
    preprocessed_indices,
  };
  Ok((system, commitment_parameters, fri_parameters))
}

/// A decoded Aiur verifying key: the `System` alone, without the prover-side
/// `Toplevel`/`ProverKey` that a full [`AiurSystem`] carries.
///
/// This is the entrypoint for standalone verifiers (e.g. a zkVM guest that
/// re-verifies an Aiur proof in-circuit): decode the bytes produced by
/// [`aiur_system_to_bytes`], then [`verify`](Self::verify) a `(claim, proof)`
/// pair against it. Keeps `AiurCircuit` out of the public API. The wire
/// format carries the commitment and FRI parameters, so verification needs
/// no further configuration; consumers binding the statement to specific
/// parameters can cross-check [`fri_parameters`](Self::fri_parameters).
pub struct AiurVerifyingKey {
  system: System<AiurConfig, AiurCircuit>,
  commitment_parameters: CommitmentParameters,
  fri_parameters: FriParameters,
}

impl AiurVerifyingKey {
  /// Decode a verifying key serialized by [`aiur_system_to_bytes`].
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    from_bytes(bytes).map(|(system, commitment_parameters, fri_parameters)| {
      Self { system, commitment_parameters, fri_parameters }
    })
  }

  /// Serialize back to the [`aiur_system_to_bytes`] wire format.
  pub fn to_bytes(&self) -> Vec<u8> {
    to_bytes(&self.system, self.commitment_parameters, self.fri_parameters)
  }

  /// The FRI parameters serialized inside the verifying key (the ones
  /// [`verify`](Self::verify) uses).
  pub fn fri_parameters(&self) -> FriParameters {
    self.fri_parameters
  }

  /// The commitment parameters serialized inside the verifying key.
  pub fn commitment_parameters(&self) -> CommitmentParameters {
    self.commitment_parameters
  }

  /// Number of circuits in the system (diagnostics: a valid proof carries
  /// one stage-1/stage-2 opening set per circuit).
  pub fn num_circuits(&self) -> usize {
    self.system.circuits.len()
  }

  pub fn verify(
    &self,
    claim: &[Val],
    proof: &crate::synthesis::AiurProof,
  ) -> Result<
    (),
    multi_stark::verifier::VerificationError<multi_stark::types::PcsError>,
  > {
    self.system.verify(claim, proof)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2};
  use multi_stark::{lookup::LookupAir, types::CommitmentParameters};

  fn test_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    (cp, fp)
  }

  /// Build a small real `System<AiurCircuit>` from the two byte gadgets and
  /// check the verifying-key codec round-trips: decode(encode(x)) re-encodes to
  /// the same bytes (a serialization fixpoint).
  #[test]
  fn system_vk_round_trips() {
    let (cp, fp) = test_parameters();
    let (system, _key) = System::new(
      AiurConfig::new(cp, fp),
      [
        LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups()),
        LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups()),
      ],
    );
    let bytes = to_bytes(&system, cp, fp);
    let (back, back_cp, back_fp) = from_bytes(&bytes).expect("decode");
    let reencoded = to_bytes(&back, back_cp, back_fp);
    assert_eq!(bytes, reencoded, "verifying-key codec round-trip mismatch");
  }

  #[test]
  fn rejects_trailing_bytes() {
    let (cp, fp) = test_parameters();
    let (system, _key) = System::new(
      AiurConfig::new(cp, fp),
      [LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups())],
    );
    let mut bytes = to_bytes(&system, cp, fp);
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "should reject trailing data");
  }
}
