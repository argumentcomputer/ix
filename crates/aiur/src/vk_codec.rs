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
//! `serde` on its types, so the encoder and decoder are written by hand against
//! the public fields of `System`, `Circuit`, `LookupAir`, `Lookup`,
//! `SymbolicExpression`, `SymbolicVariable`, `Entry`, `CommitmentParameters`,
//! `FriParameters` and the Ix `AiurCircuit`/`Constraints`/`Memory`. The Aiur
//! port (`Ix/MultiStark/SystemDeserialize.lean`) reads the same bytes
//! in-circuit; the two must stay mirror images.
//!
//! # Split-streams wire format (v2)
//!
//! The recursive verifier hashes every vk byte (digest binding) and reads them
//! with fixed-size `io_read` chunks, so the format optimizes for (a) few bytes
//! and (b) fixed-width fields only — no varints. Each field class lives in its
//! own per-circuit byte segment with a single width:
//!
//! ```text
//! GLOBAL HEADER
//!   7 x u16 LE   commitment + FRI parameters (log_blowup, cap_height,
//!                log_final_poly_len, max_log_arity, num_queries,
//!                commit_proof_of_work_bits, query_proof_of_work_bits)
//!   u16          circuit count
//! PER-CIRCUIT RECORDS (circuit count times; each record is a contiguous
//!                      byte range — a future Merkle leaf)
//!   5 x u32 LE   segment lengths: TAGS, IDX, C2, C8, META
//!   TAGS   1 byte per node: low nibble = kind, high nibble = aux
//!   IDX    2 bytes per Variable: column index (u16 LE)
//!   C2     2 bytes per small constant (canonical value < 2^16, u16 LE)
//!   C8     8 bytes per large constant (canonical u64 LE)
//!   META   4 bytes per count/metadata field (u32 LE)
//! TRAILER
//!   u8           preprocessed commit flag (0 = None / 1 = Some)
//!   [u16 + 32-byte digests]   MerkleCap, if flag = 1
//!   u16 x circuit count       preprocessed indices (0xFFFF = None)
//! ```
//!
//! TAGS byte: kind 0 = Variable, 1 = IsFirstRow, 2 = IsLastRow,
//! 3 = IsTransition, 4 = Constant, 5 = Add, 6 = Sub, 7 = Neg, 8 = Mul.
//! Aux for Variable = entry kind (0 = Preprocessed, 1 = Main, 2 = Stage2,
//! 3 = Public, 4 = Stage2Public, 5 = Challenge) + 8 * rotation offset (the
//! rotation is only 0/1: current or next row). Aux for Constant = size class
//! (0 -> C2, 1 -> C8). A record's first TAGS byte is the `AiurCircuit`
//! variant tag (0 = Function, 1 = Memory, 2 = Bytes1, 3 = Bytes2), then
//! expression nodes in preorder.
//!
//! Record content order (defines each segment's fill order):
//! aircircuit tag; [Function: zeros count (META), zero exprs, selectors
//! start/end + width (META) | Memory: width (META)]; lookups count (META);
//! per lookup: multiplicity expr, args count (META), arg exprs; then the 6
//! circuit metadata fields (constraint_count, max_constraint_degree,
//! preprocessed_height, preprocessed_width, stage_1_width, stage_2_width)
//! (META).
//!
//! `degree_multiple` is NOT serialized: it is fully derivable (variables by
//! entry kind, add/sub = max of children, mul = sum, neg = child) and the
//! decoder recomputes it via the library's own `degree_multiple()` on the
//! reconstructed children. Dropping it, the u32 enum tags, and the u64
//! fixed-width scaffolding shrinks the kernel vk ~7x, which directly cuts the
//! recursive verifier's dominant blake3 cost.
//!
//! Goldilocks note: constants are written as `as_canonical_u64()` (the raw
//! internal repr is `pub(crate)` in `p3_goldilocks`) and read back with
//! `from_u64`; verifying-key constants are canonical so the round-trip is
//! exact, and the Lean reader reduces mod p regardless.

// The codec is exercised by tests and wired to the FFI / Aiur port.
#![allow(dead_code)]

use multi_stark::{
  builder::symbolic::{Entry, SymbolicExpression, SymbolicVariable},
  lookup::{Lookup, LookupAir},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  system::{Circuit, System},
  types::{Commitment, CommitmentParameters, FriParameters, Val},
};

use crate::{
  constraints::Constraints,
  memory::Memory,
  synthesis::{AiurCircuit, AiurConfig, AiurSystem},
};

type Expr = SymbolicExpression<Val>;

/// Sentinel for `None` in the preprocessed-index trailer.
const NO_PREP_INDEX: u16 = u16::MAX;

// ════════════════════════════════════════════════════════════════════════════
// Encoder — System<AiurCircuit> -> bytes
// ════════════════════════════════════════════════════════════════════════════

/// One circuit's five segments, filled in record-content order.
#[derive(Default)]
struct RecordBufs {
  tags: Vec<u8>,
  idx: Vec<u8>,
  c2: Vec<u8>,
  c8: Vec<u8>,
  meta: Vec<u8>,
}

impl RecordBufs {
  fn tag(&mut self, kind: u8, aux: u8) {
    debug_assert!(kind < 16 && aux < 16);
    self.tags.push(kind | (aux << 4));
  }
  fn index_u16(&mut self, v: usize) {
    let v = u16::try_from(v).expect("variable column index exceeds u16");
    self.idx.extend_from_slice(&v.to_le_bytes());
  }
  fn meta_u32(&mut self, v: usize) {
    let v = u32::try_from(v).expect("vk metadata field exceeds u32");
    self.meta.extend_from_slice(&v.to_le_bytes());
  }
  fn constant(&mut self, v: Val) {
    let c = v.as_canonical_u64();
    if c < (1 << 16) {
      self.c2.extend_from_slice(&(c as u16).to_le_bytes());
      self.tag(4, 0);
    } else {
      self.c8.extend_from_slice(&c.to_le_bytes());
      self.tag(4, 1);
    }
  }
  fn variable(&mut self, v: &SymbolicVariable<Val>) {
    let (kind, offset) = match v.entry {
      Entry::Preprocessed { offset } => (0u8, offset),
      Entry::Main { offset } => (1, offset),
      Entry::Stage2 { offset } => (2, offset),
      Entry::Public => (3, 0),
      Entry::Stage2Public => (4, 0),
      Entry::Challenge => (5, 0),
    };
    assert!(offset <= 1, "rotation offset {offset} not in {{0, 1}}");
    self.tag(0, kind + 8 * offset as u8);
    self.index_u16(v.index);
  }
  fn expr(&mut self, e: &Expr) {
    match e {
      SymbolicExpression::Variable(v) => self.variable(v),
      SymbolicExpression::IsFirstRow => self.tag(1, 0),
      SymbolicExpression::IsLastRow => self.tag(2, 0),
      SymbolicExpression::IsTransition => self.tag(3, 0),
      SymbolicExpression::Constant(c) => self.constant(*c),
      SymbolicExpression::Add { x, y, .. } => {
        self.tag(5, 0);
        self.expr(x);
        self.expr(y);
      },
      SymbolicExpression::Sub { x, y, .. } => {
        self.tag(6, 0);
        self.expr(x);
        self.expr(y);
      },
      SymbolicExpression::Neg { x, .. } => {
        self.tag(7, 0);
        self.expr(x);
      },
      SymbolicExpression::Mul { x, y, .. } => {
        self.tag(8, 0);
        self.expr(x);
        self.expr(y);
      },
    }
  }
  fn circuit(&mut self, c: &Circuit<AiurCircuit, Val>) {
    match &c.air.inner_air {
      AiurCircuit::Function(Constraints { zeros, selectors, width }) => {
        self.tag(0, 0);
        self.meta_u32(zeros.len());
        for z in zeros {
          self.expr(z);
        }
        self.meta_u32(selectors.start);
        self.meta_u32(selectors.end);
        self.meta_u32(*width);
      },
      AiurCircuit::Memory(Memory { width }) => {
        self.tag(1, 0);
        self.meta_u32(*width);
      },
      AiurCircuit::Bytes1 => self.tag(2, 0),
      AiurCircuit::Bytes2 => self.tag(3, 0),
    }
    self.meta_u32(c.air.lookups.len());
    for l in &c.air.lookups {
      self.expr(&l.multiplicity);
      self.meta_u32(l.args.len());
      for a in &l.args {
        self.expr(a);
      }
    }
    self.meta_u32(c.constraint_count);
    self.meta_u32(c.max_constraint_degree);
    self.meta_u32(c.preprocessed_height);
    self.meta_u32(c.preprocessed_width);
    self.meta_u32(c.stage_1_width);
    self.meta_u32(c.stage_2_width);
  }
}

fn push_u16(buf: &mut Vec<u8>, v: usize) {
  let v = u16::try_from(v).expect("vk header field exceeds u16");
  buf.extend_from_slice(&v.to_le_bytes());
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
  let mut buf = Vec::new();
  push_u16(&mut buf, commitment_parameters.log_blowup);
  push_u16(&mut buf, commitment_parameters.cap_height);
  push_u16(&mut buf, fri_parameters.log_final_poly_len);
  push_u16(&mut buf, fri_parameters.max_log_arity);
  push_u16(&mut buf, fri_parameters.num_queries);
  push_u16(&mut buf, fri_parameters.commit_proof_of_work_bits);
  push_u16(&mut buf, fri_parameters.query_proof_of_work_bits);
  push_u16(&mut buf, system.circuits.len());
  for c in &system.circuits {
    let mut r = RecordBufs::default();
    r.circuit(c);
    for seg in [&r.tags, &r.idx, &r.c2, &r.c8, &r.meta] {
      let len = u32::try_from(seg.len()).expect("vk segment exceeds u32");
      buf.extend_from_slice(&len.to_le_bytes());
    }
    for seg in [&r.tags, &r.idx, &r.c2, &r.c8, &r.meta] {
      buf.extend_from_slice(seg);
    }
  }
  match &system.preprocessed_commit {
    None => buf.push(0),
    Some(c) => {
      buf.push(1);
      push_u16(&mut buf, c.roots().len());
      for digest in c.roots() {
        buf.extend_from_slice(digest);
      }
    },
  }
  for idx in &system.preprocessed_indices {
    match idx {
      None => buf.extend_from_slice(&NO_PREP_INDEX.to_le_bytes()),
      Some(i) => {
        let v = u16::try_from(*i).expect("preprocessed index exceeds u16");
        assert!(v != NO_PREP_INDEX, "preprocessed index collides with sentinel");
        buf.extend_from_slice(&v.to_le_bytes());
      },
    }
  }
  buf
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
// `degree_multiple` is recomputed from the reconstructed children.
// ════════════════════════════════════════════════════════════════════════════

/// Cursor over one byte region.
struct Seg<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Seg<'a> {
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
  fn u16(&mut self) -> Result<u16, String> {
    Ok(u16::from_le_bytes(self.take(2)?.try_into().unwrap()))
  }
  fn u32(&mut self) -> Result<u32, String> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
  fn done(&self, what: &str) -> Result<(), String> {
    if self.pos != self.buf.len() {
      return Err(format!(
        "{what}: consumed {} of {} bytes",
        self.pos,
        self.buf.len()
      ));
    }
    Ok(())
  }
}

/// One record's five segment cursors.
struct RecordReader<'a> {
  tags: Seg<'a>,
  idx: Seg<'a>,
  c2: Seg<'a>,
  c8: Seg<'a>,
  meta: Seg<'a>,
}

impl<'a> RecordReader<'a> {
  fn meta_usize(&mut self) -> Result<usize, String> {
    Ok(self.meta.u32()? as usize)
  }
  fn expr(&mut self) -> Result<Expr, String> {
    let byte = self.tags.u8()?;
    let (kind, aux) = (byte & 0xF, byte >> 4);
    Ok(match kind {
      0 => {
        let offset = (aux >> 3) as usize;
        let entry = match aux & 0x7 {
          0 => Entry::Preprocessed { offset },
          1 => Entry::Main { offset },
          2 => Entry::Stage2 { offset },
          3 => Entry::Public,
          4 => Entry::Stage2Public,
          5 => Entry::Challenge,
          k => return Err(format!("bad entry kind {k}")),
        };
        let index = self.idx.u16()? as usize;
        SymbolicExpression::Variable(SymbolicVariable::new(entry, index))
      },
      1 => SymbolicExpression::IsFirstRow,
      2 => SymbolicExpression::IsLastRow,
      3 => SymbolicExpression::IsTransition,
      4 => {
        let c = match aux {
          0 => self.c2.u16()? as u64,
          1 => self.c8.u64()?,
          a => return Err(format!("bad constant size class {a}")),
        };
        SymbolicExpression::Constant(Val::from_u64(c))
      },
      5 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        let degree_multiple = x.degree_multiple().max(y.degree_multiple());
        SymbolicExpression::Add { x, y, degree_multiple }
      },
      6 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        let degree_multiple = x.degree_multiple().max(y.degree_multiple());
        SymbolicExpression::Sub { x, y, degree_multiple }
      },
      7 => {
        let x = Box::new(self.expr()?);
        let degree_multiple = x.degree_multiple();
        SymbolicExpression::Neg { x, degree_multiple }
      },
      8 => {
        let x = Box::new(self.expr()?);
        let y = Box::new(self.expr()?);
        let degree_multiple = x.degree_multiple() + y.degree_multiple();
        SymbolicExpression::Mul { x, y, degree_multiple }
      },
      t => return Err(format!("bad expr kind {t}")),
    })
  }
  fn circuit(&mut self) -> Result<Circuit<AiurCircuit, Val>, String> {
    let inner_air = match self.tags.u8()? {
      0 => {
        let n = self.meta_usize()?;
        let mut zeros = Vec::with_capacity(n.min(1 << 16));
        for _ in 0..n {
          zeros.push(self.expr()?);
        }
        let start = self.meta_usize()?;
        let end = self.meta_usize()?;
        let width = self.meta_usize()?;
        AiurCircuit::Function(Constraints { zeros, selectors: start..end, width })
      },
      1 => AiurCircuit::Memory(Memory { width: self.meta_usize()? }),
      2 => AiurCircuit::Bytes1,
      3 => AiurCircuit::Bytes2,
      t => return Err(format!("bad aircircuit tag {t}")),
    };
    let n = self.meta_usize()?;
    let mut lookups = Vec::with_capacity(n.min(1 << 16));
    for _ in 0..n {
      let multiplicity = self.expr()?;
      let a = self.meta_usize()?;
      let mut args = Vec::with_capacity(a.min(1 << 16));
      for _ in 0..a {
        args.push(self.expr()?);
      }
      lookups.push(Lookup { multiplicity, args });
    }
    let air = LookupAir { inner_air, lookups, preprocessed: None };
    let c = Circuit {
      air,
      constraint_count: self.meta_usize()?,
      max_constraint_degree: self.meta_usize()?,
      preprocessed_height: self.meta_usize()?,
      preprocessed_width: self.meta_usize()?,
      stage_1_width: self.meta_usize()?,
      stage_2_width: self.meta_usize()?,
    };
    self.tags.done("TAGS segment")?;
    self.idx.done("IDX segment")?;
    self.c2.done("C2 segment")?;
    self.c8.done("C8 segment")?;
    self.meta.done("META segment")?;
    Ok(c)
  }
}

/// Deserialize a `System<AiurCircuit>` from [`to_bytes`] output, requiring that
/// every byte (globally and within each record segment) is consumed. Also
/// returns the config's construction parameters, which the `System` itself
/// doesn't expose.
pub(crate) fn from_bytes(
  bytes: &[u8],
) -> Result<
  (System<AiurConfig, AiurCircuit>, CommitmentParameters, FriParameters),
  String,
> {
  let mut r = Seg { buf: bytes, pos: 0 };
  let commitment_parameters = CommitmentParameters {
    log_blowup: r.u16()? as usize,
    cap_height: r.u16()? as usize,
  };
  let fri_parameters = FriParameters {
    log_final_poly_len: r.u16()? as usize,
    max_log_arity: r.u16()? as usize,
    num_queries: r.u16()? as usize,
    commit_proof_of_work_bits: r.u16()? as usize,
    query_proof_of_work_bits: r.u16()? as usize,
  };
  let n_circuits = r.u16()? as usize;
  let mut circuits = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    let lens: [usize; 5] = [
      r.u32()? as usize,
      r.u32()? as usize,
      r.u32()? as usize,
      r.u32()? as usize,
      r.u32()? as usize,
    ];
    let tags = Seg { buf: r.take(lens[0])?, pos: 0 };
    let idx = Seg { buf: r.take(lens[1])?, pos: 0 };
    let c2 = Seg { buf: r.take(lens[2])?, pos: 0 };
    let c8 = Seg { buf: r.take(lens[3])?, pos: 0 };
    let meta = Seg { buf: r.take(lens[4])?, pos: 0 };
    let mut rec = RecordReader { tags, idx, c2, c8, meta };
    circuits.push(rec.circuit()?);
  }
  let preprocessed_commit = match r.u8()? {
    0 => None,
    1 => {
      let n = r.u16()? as usize;
      let mut caps = Vec::with_capacity(n.min(1 << 16));
      for _ in 0..n {
        let mut d = [0u8; 32];
        d.copy_from_slice(r.take(32)?);
        caps.push(d);
      }
      Some(Commitment::from(caps))
    },
    t => return Err(format!("bad Option tag {t}")),
  };
  let mut preprocessed_indices = Vec::with_capacity(n_circuits);
  for _ in 0..n_circuits {
    let v = r.u16()?;
    preprocessed_indices
      .push(if v == NO_PREP_INDEX { None } else { Some(v as usize) });
  }
  r.done("vk")?;
  let system = System {
    config: AiurConfig::new(commitment_parameters, fri_parameters),
    circuits,
    preprocessed_commit,
    preprocessed_indices,
  };
  Ok((system, commitment_parameters, fri_parameters))
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

  fn test_system() -> (System<AiurConfig, AiurCircuit>, CommitmentParameters, FriParameters)
  {
    let (cp, fp) = test_parameters();
    let (system, _key) = System::new(
      AiurConfig::new(cp, fp),
      [
        LookupAir::new(AiurCircuit::Bytes1, Bytes1.lookups()),
        LookupAir::new(AiurCircuit::Bytes2, Bytes2.lookups()),
      ],
    );
    (system, cp, fp)
  }

  /// Structural equality of expressions INCLUDING the recomputed
  /// `degree_multiple` — validates the decoder's degree reconstruction
  /// node by node.
  fn expr_eq(a: &Expr, b: &Expr) -> bool {
    use SymbolicExpression as E;
    if a.degree_multiple() != b.degree_multiple() {
      return false;
    }
    match (a, b) {
      (E::Variable(u), E::Variable(v)) => u.entry == v.entry && u.index == v.index,
      (E::IsFirstRow, E::IsFirstRow)
      | (E::IsLastRow, E::IsLastRow)
      | (E::IsTransition, E::IsTransition) => true,
      (E::Constant(c), E::Constant(d)) => c == d,
      (E::Add { x: ax, y: ay, .. }, E::Add { x: bx, y: by, .. })
      | (E::Sub { x: ax, y: ay, .. }, E::Sub { x: bx, y: by, .. })
      | (E::Mul { x: ax, y: ay, .. }, E::Mul { x: bx, y: by, .. }) => {
        expr_eq(ax, bx) && expr_eq(ay, by)
      },
      (E::Neg { x: ax, .. }, E::Neg { x: bx, .. }) => expr_eq(ax, bx),
      _ => false,
    }
  }

  /// Round-trip: decode(encode(x)) re-encodes to the same bytes AND every
  /// expression (with its recomputed degrees) matches the original.
  #[test]
  fn system_vk_round_trips() {
    let (system, cp, fp) = test_system();
    let bytes = to_bytes(&system, cp, fp);
    let (back, back_cp, back_fp) = from_bytes(&bytes).expect("decode");
    let reencoded = to_bytes(&back, back_cp, back_fp);
    assert_eq!(bytes, reencoded, "verifying-key codec round-trip mismatch");
    assert_eq!(system.circuits.len(), back.circuits.len());
    for (a, b) in system.circuits.iter().zip(&back.circuits) {
      assert_eq!(a.air.lookups.len(), b.air.lookups.len());
      for (la, lb) in a.air.lookups.iter().zip(&b.air.lookups) {
        assert!(
          expr_eq(&la.multiplicity, &lb.multiplicity),
          "lookup multiplicity mismatch (degree recomputation?)"
        );
        assert_eq!(la.args.len(), lb.args.len());
        for (ea, eb) in la.args.iter().zip(&lb.args) {
          assert!(expr_eq(ea, eb), "lookup arg mismatch");
        }
      }
      if let (AiurCircuit::Function(fa), AiurCircuit::Function(fb)) =
        (&a.air.inner_air, &b.air.inner_air)
      {
        assert_eq!(fa.zeros.len(), fb.zeros.len());
        for (ea, eb) in fa.zeros.iter().zip(&fb.zeros) {
          assert!(expr_eq(ea, eb), "constraint mismatch");
        }
      }
    }
  }

  #[test]
  fn rejects_trailing_bytes() {
    let (system, cp, fp) = test_system();
    let mut bytes = to_bytes(&system, cp, fp);
    bytes.push(0);
    assert!(from_bytes(&bytes).is_err(), "should reject trailing data");
  }

  /// A tampered segment length must be rejected (the record readers enforce
  /// exact per-segment consumption).
  #[test]
  fn rejects_bad_segment_length() {
    let (system, cp, fp) = test_system();
    let mut bytes = to_bytes(&system, cp, fp);
    // First record header starts right after the 16-byte global header;
    // bump the TAGS segment length by one.
    let tags_len = u32::from_le_bytes(bytes[16..20].try_into().unwrap());
    bytes[16..20].copy_from_slice(&(tags_len + 1).to_le_bytes());
    assert!(from_bytes(&bytes).is_err(), "should reject bad segment length");
  }
}
