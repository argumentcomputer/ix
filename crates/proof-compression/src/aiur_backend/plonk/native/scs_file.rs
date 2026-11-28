//! Full parser and validator for Lean's `ix-aiur-scs-v1` (`ixscs001`) sparse
//! R1CS format (`Aiur/Aiur/Plonk/Scs.lean`, `MultiStark/Examples/PlonkExport.lean`).
//!
//! Gates and hints remain in their compact packed representations (26 bytes per
//! gate, 9 bytes per wire) so multi-million-gate constraint systems stay memory
//! bounded. While the `ix-aiur-scs-v1` wire format can parse non-empty
//! `outputs` headers (e.g. legacy 18-word BN254 or 22-word BLS12-381 deferred
//! pairing accumulators), native PLONK-SCS (`setup`, `prepare_to_dir`,
//! `NativeProver::open`, `prove`) does not synthesize in-circuit pairing
//! constraints for deferred `scs.outputs` and rejects any circuit with
//! `!scs.outputs.is_empty()` fail-closed (requiring self-contained
//! `outputs == 0` circuits).

use crate::aiur_backend::plonk::{
  MAX_PUBLIC_INPUTS,
  scs::{INPUTS_FORMAT, Inputs, Table},
};
use crate::kzg::curve::KzgCurve;
use ark_ff::{BigInt, BigInteger, PrimeField};
use sha2::{Digest, Sha256};
use std::path::Path;

/// Magic header for `ix-aiur-scs-v1` binary files.
pub const MAGIC: &[u8; 8] = b"ixscs001";
/// Byte size of one packed gate record (`a, b, c, sel, alpha, beta, omega, qC`).
pub const GATE_BYTES: usize = 26;
/// Byte size of one packed wire hint record (`kind, x, y`).
pub const HINT_BYTES: usize = 9;

/// Selector bitmasks in `PackedGate::sel`.
pub const SEL_L: u8 = 1;
pub const SEL_R: u8 = 2;
pub const SEL_O: u8 = 4;
pub const SEL_M: u8 = 8;

/// Wire hint kinds matching `MultiStark/Examples/PlonkExport.lean`.
pub const HINT_INPUT: u8 = 0;
pub const HINT_SOLVE: u8 = 1;
pub const HINT_BIT: u8 = 2;
pub const HINT_CHALLENGE: u8 = 3;
pub const HINT_FREE: u8 = 4;

/// One decoded 26-byte packed gate from an `ix-aiur-scs-v1` file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedGate {
  pub a: u32,
  pub b: u32,
  pub c: u32,
  pub sel: u8,
  pub alpha_id: u32,
  pub beta_id: u32,
  pub omega_id: u32,
  pub qc: i8,
}

/// Expanded PLONK gate coefficients `qL·a + qR·b + qO·c + qM·a·b + qC = 0`
/// matching `Aiur.Plonk.GGate.toGate`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GateCoeffs<C: KzgCurve> {
  pub ql: C::Fr,
  pub qr: C::Fr,
  pub qo: C::Fr,
  pub qm: C::Fr,
  pub qc: C::Fr,
}

/// One decoded 9-byte wire hint.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WireHint {
  Input,
  Solve { gate: u32 },
  Bit { wire: u32, bit: u32 },
  Challenge,
  Free,
}

/// A validated `ix-aiur-scs-v1` constraint system over `C::Fr`.
#[derive(Clone, Debug)]
pub struct ScsFile<C: KzgCurve> {
  pub publics: usize,
  pub wires: usize,
  pub gates_count: usize,
  pub pre: usize,
  pub gamma: u32,
  pub beta: u32,
  pub cells: usize,
  pub outputs: Vec<u32>,
  pub coeffs: Vec<C::Fr>,
  pub commits: Vec<u32>,
  pub tables: Vec<Table>,
  pub sha256: [u8; 32],
  gates_raw: Vec<u8>,
  hints_raw: Vec<u8>,
}

/// Convert a signed 8-bit gate constant `qC` into `C::Fr`.
#[inline]
pub fn i8_to_fr<C: KzgCurve>(value: i8) -> C::Fr {
  if value >= 0 {
    C::Fr::from(u64::from(value.unsigned_abs()))
  } else {
    -C::Fr::from(u64::from(value.unsigned_abs()))
  }
}

/// Lowercase hexadecimal formatting for a 32-byte digest.
pub fn hex_digest(digest: &[u8; 32]) -> String {
  let mut out = String::with_capacity(64);
  for &byte in digest {
    use core::fmt::Write;
    let _ = write!(&mut out, "{byte:02x}");
  }
  out
}

/// Parse a 64-character lowercase/uppercase hex string into a 32-byte digest.
pub fn parse_hex_digest(hex: &str) -> Result<[u8; 32], String> {
  if hex.len() != 64 {
    return Err(format!(
      "expected 64 hex chars for SHA-256, got {}",
      hex.len()
    ));
  }
  let mut out = [0u8; 32];
  for (i, slot) in out.iter_mut().enumerate() {
    *slot = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16)
      .map_err(|e| format!("invalid hex digit in digest: {e}"))?;
  }
  Ok(out)
}

fn read_u16_le(data: &[u8], offset: usize) -> u16 {
  u16::from_le_bytes(data[offset..offset + 2].try_into().expect("2-byte slice"))
}

fn read_u32_le(data: &[u8], offset: usize) -> u32 {
  u32::from_le_bytes(data[offset..offset + 4].try_into().expect("4-byte slice"))
}

fn read_u64_le(data: &[u8], offset: usize) -> u64 {
  u64::from_le_bytes(data[offset..offset + 8].try_into().expect("8-byte slice"))
}

fn decode_fr_le_canonical<C: KzgCurve>(bytes: &[u8]) -> Result<C::Fr, String> {
  let limbs = [
    read_u64_le(bytes, 0),
    read_u64_le(bytes, 8),
    read_u64_le(bytes, 16),
    read_u64_le(bytes, 24),
  ];
  C::Fr::from_bigint(BigInt(limbs))
    .ok_or_else(|| "non-canonical Fr coefficient (>= r)".to_owned())
}

impl<C: KzgCurve> ScsFile<C> {
  /// Read an `ix-aiur-scs-v1` file from disk, check its SHA-256 against
  /// `expected_sha256_hex`, and validate every section.
  pub fn read_pinned(
    path: &Path,
    expected_sha256_hex: &str,
  ) -> Result<Self, String> {
    let expected = parse_hex_digest(expected_sha256_hex)?;
    let data =
      std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let actual: [u8; 32] = Sha256::digest(&data).into();
    if actual != expected {
      return Err(format!(
        "SCS file {} SHA-256 {} differs from pinned {}",
        path.display(),
        hex_digest(&actual),
        expected_sha256_hex
      ));
    }
    Self::parse(&data)
  }

  /// Parse and completely validate an `ix-aiur-scs-v1` (`ixscs001`) byte slice.
  pub fn parse(data: &[u8]) -> Result<Self, String> {
    if data.len() < 88 || &data[..8] != MAGIC {
      return Err("not an ix-aiur-scs-v1 file".into());
    }
    let sha256: [u8; 32] = Sha256::digest(data).into();
    let mut hdr = [0u64; 10];
    for (i, slot) in hdr.iter_mut().enumerate() {
      *slot = read_u64_le(data, 8 + 8 * i);
    }
    let [
      publics_u64,
      outputs_u64,
      wires_u64,
      gates_u64,
      pre_u64,
      commits_u64,
      gamma_u64,
      beta_u64,
      coeffs_u64,
      tables_u64,
    ] = hdr;

    const U32_LIMIT: u64 = 1u64 << 32;
    let max_pub = u64::try_from(MAX_PUBLIC_INPUTS).expect("fits u64");
    if wires_u64 == 0
      || wires_u64 >= U32_LIMIT
      || gates_u64 >= U32_LIMIT
      || coeffs_u64 >= U32_LIMIT
      || commits_u64 >= U32_LIMIT
      || tables_u64 >= (1u64 << 16)
      || publics_u64 == 0
      || publics_u64 > max_pub
      || outputs_u64 > max_pub
      || pre_u64 > gates_u64
      || gamma_u64 >= wires_u64
      || beta_u64 >= wires_u64
    {
      return Err("invalid ix-aiur-scs-v1 header".into());
    }

    let publics = usize::try_from(publics_u64).map_err(|e| e.to_string())?;
    let outputs_len =
      usize::try_from(outputs_u64).map_err(|e| e.to_string())?;
    let wires = usize::try_from(wires_u64).map_err(|e| e.to_string())?;
    let gates_count = usize::try_from(gates_u64).map_err(|e| e.to_string())?;
    let pre = usize::try_from(pre_u64).map_err(|e| e.to_string())?;
    let commits_len =
      usize::try_from(commits_u64).map_err(|e| e.to_string())?;
    let coeffs_len = usize::try_from(coeffs_u64).map_err(|e| e.to_string())?;
    let tables_len = usize::try_from(tables_u64).map_err(|e| e.to_string())?;
    let gamma = u32::try_from(gamma_u64).map_err(|e| e.to_string())?;
    let beta = u32::try_from(beta_u64).map_err(|e| e.to_string())?;

    let body_end = 88usize
      .checked_add(outputs_len.checked_mul(4).ok_or("outputs overflow")?)
      .and_then(|o| o.checked_add(coeffs_len.checked_mul(32)?))
      .and_then(|o| o.checked_add(gates_count.checked_mul(GATE_BYTES)?))
      .and_then(|o| o.checked_add(commits_len.checked_mul(4)?))
      .and_then(|o| o.checked_add(wires.checked_mul(HINT_BYTES)?))
      .ok_or("ix-aiur-scs-v1 body size overflow")?;
    if data.len() < body_end {
      return Err("truncated ix-aiur-scs-v1 file".into());
    }

    let mut offset = 88usize;
    let in_wire_range = |w: u32| (w as usize) < wires;

    let mut outputs = Vec::with_capacity(outputs_len);
    for _ in 0..outputs_len {
      let w = read_u32_le(data, offset);
      if !in_wire_range(w) {
        return Err("ix-aiur-scs-v1 output wire out of range".into());
      }
      outputs.push(w);
      offset += 4;
    }

    let mut coeffs = Vec::with_capacity(coeffs_len);
    for i in 0..coeffs_len {
      let val = decode_fr_le_canonical::<C>(&data[offset..offset + 32])
        .map_err(|e| format!("coefficient {i}: {e}"))?;
      if val == C::FR_ZERO {
        return Err(format!("ix-aiur-scs-v1 coefficient {i} is zero"));
      }
      coeffs.push(val);
      offset += 32;
    }

    let gates_bytes_len = gates_count * GATE_BYTES;
    let gates_slice = &data[offset..offset + gates_bytes_len];
    offset += gates_bytes_len;
    for i in 0..gates_count {
      let g = decode_gate(gates_slice, i);
      if !in_wire_range(g.a)
        || !in_wire_range(g.b)
        || !in_wire_range(g.c)
        || g.sel > 15
        || (g.alpha_id as usize) >= coeffs_len
        || (g.beta_id as usize) >= coeffs_len
        || (g.omega_id as usize) >= coeffs_len
      {
        return Err(format!("ix-aiur-scs-v1 gate {i} out of range"));
      }
    }

    let mut commits = Vec::with_capacity(commits_len);
    let mut seen_commit = vec![false; wires];
    for _ in 0..commits_len {
      let w = read_u32_le(data, offset);
      if !in_wire_range(w) || seen_commit[w as usize] {
        return Err(
          "ix-aiur-scs-v1 commit wire out of range or duplicated".into(),
        );
      }
      seen_commit[w as usize] = true;
      commits.push(w);
      offset += 4;
    }

    let hints_bytes_len = wires * HINT_BYTES;
    let hints_slice = &data[offset..offset + hints_bytes_len];
    offset += hints_bytes_len;
    let mut cells = 0usize;
    let mut challenges = 0usize;
    for w_idx in 0..wires {
      let w_u32 = u32::try_from(w_idx).expect("wire fits u32");
      let off = w_idx * HINT_BYTES;
      let kind = hints_slice[off];
      let hx = read_u32_le(hints_slice, off + 1);
      let hy = read_u32_le(hints_slice, off + 5);
      match kind {
        HINT_INPUT => {
          if w_idx != cells {
            return Err("ix-aiur-scs-v1 input wires are not a prefix".into());
          }
          cells += 1;
        },
        HINT_SOLVE => {
          if (hx as usize) >= gates_count {
            return Err(format!(
              "wire {w_idx} solve hint references out-of-range gate {hx}"
            ));
          }
          let g = decode_gate(gates_slice, hx as usize);
          if g.a != w_u32 && g.b != w_u32 && g.c != w_u32 {
            return Err(format!(
              "wire {w_idx} solve hint references gate {hx} without it"
            ));
          }
        },
        HINT_BIT => {
          if !in_wire_range(hx) || hy >= 256 {
            return Err(format!("wire {w_idx} bit hint out of range"));
          }
        },
        HINT_CHALLENGE => {
          if w_u32 != gamma {
            return Err(
              "ix-aiur-scs-v1 challenge hint on a wire other than gamma".into(),
            );
          }
          challenges += 1;
        },
        HINT_FREE => {},
        other => {
          return Err(format!("wire {w_idx} has unknown hint kind {other}"));
        },
      }
    }
    if challenges != 1 || cells < publics {
      return Err(
        "ix-aiur-scs-v1 requires one gamma challenge and publics among inputs"
          .into(),
      );
    }
    for &w in outputs.iter().chain(&commits) {
      if (w as usize) >= cells {
        return Err(
          "ix-aiur-scs-v1 outputs and commits must be input wires".into(),
        );
      }
    }

    let mut tables = Vec::with_capacity(tables_len);
    for _ in 0..tables_len {
      if data.len() < offset + 2 {
        return Err("truncated ix-aiur-scs-v1 table header".into());
      }
      let name_len = usize::from(read_u16_le(data, offset));
      offset += 2;
      if data.len() < offset + name_len + 16 {
        return Err("truncated ix-aiur-scs-v1 table entry".into());
      }
      let name = std::str::from_utf8(&data[offset..offset + name_len])
        .map_err(|e| format!("ix-aiur-scs-v1 table name not UTF-8: {e}"))?
        .to_owned();
      offset += name_len;
      let cell_base = read_u64_le(data, offset);
      let rows = read_u32_le(data, offset + 8);
      let width = read_u32_le(data, offset + 12);
      offset += 16;
      let end = u64::from(rows)
        .checked_mul(u64::from(width))
        .and_then(|span| cell_base.checked_add(span))
        .ok_or("ix-aiur-scs-v1 table cell range overflow")?;
      if end > u64::try_from(cells).expect("cells fits u64") {
        return Err(format!(
          "ix-aiur-scs-v1 table {name:?} exceeds input wires"
        ));
      }
      tables.push(Table { name, cell_base, rows, width });
    }

    if offset != data.len() {
      return Err("trailing bytes in ix-aiur-scs-v1 file".into());
    }

    Ok(Self {
      publics,
      wires,
      gates_count,
      pre,
      gamma,
      beta,
      cells,
      outputs,
      coeffs,
      commits,
      tables,
      sha256,
      gates_raw: gates_slice.to_vec(),
      hints_raw: hints_slice.to_vec(),
    })
  }

  /// Decode packed gate `index` (`0..self.gates_count`).
  #[inline]
  pub fn gate(&self, index: usize) -> PackedGate {
    decode_gate(&self.gates_raw, index)
  }

  /// Expand a [`PackedGate`] to PLONK coefficients `(qL, qR, qO, qM, qC)`
  /// matching `Aiur.Plonk.GGate.toGate`.
  #[inline]
  pub fn gate_coeffs(&self, gate: PackedGate) -> GateCoeffs<C> {
    let al = self.coeffs[gate.alpha_id as usize];
    let be = self.coeffs[gate.beta_id as usize];
    let om = self.coeffs[gate.omega_id as usize];
    GateCoeffs {
      ql: if gate.sel & SEL_L != 0 { al } else { C::FR_ZERO },
      qr: if gate.sel & SEL_R != 0 { be } else { C::FR_ZERO },
      qo: if gate.sel & SEL_O != 0 { om } else { C::FR_ZERO },
      qm: if gate.sel & SEL_M != 0 { al * be } else { C::FR_ZERO },
      qc: i8_to_fr::<C>(gate.qc),
    }
  }

  /// Evaluate `qL·a + qR·b + qO·c + qM·a·b + qC` on a wire assignment.
  #[inline]
  pub fn eval_gate(&self, index: usize, wires: &[C::Fr]) -> C::Fr {
    let g = self.gate(index);
    let c = self.gate_coeffs(g);
    let wa = wires[g.a as usize];
    let wb = wires[g.b as usize];
    let wc = wires[g.c as usize];
    c.ql * wa + c.qr * wb + c.qo * wc + c.qm * (wa * wb) + c.qc
  }

  /// Decode the wire hint for `wire` (`0..self.wires`).
  #[inline]
  pub fn hint(&self, wire: u32) -> WireHint {
    let off = (wire as usize) * HINT_BYTES;
    let kind = self.hints_raw[off];
    let hx = read_u32_le(&self.hints_raw, off + 1);
    let hy = read_u32_le(&self.hints_raw, off + 5);
    match kind {
      HINT_INPUT => WireHint::Input,
      HINT_SOLVE => WireHint::Solve { gate: hx },
      HINT_BIT => WireHint::Bit { wire: hx, bit: hy },
      HINT_CHALLENGE => WireHint::Challenge,
      _ => WireHint::Free,
    }
  }

  /// Lowercase hex SHA-256 digest of the parsed file bytes.
  pub fn sha256_hex(&self) -> String {
    hex_digest(&self.sha256)
  }

  /// Extract the witness input descriptor compatible with [`crate::aiur_backend::plonk::scs::Inputs`].
  pub fn to_inputs(&self) -> Inputs {
    Inputs {
      format: INPUTS_FORMAT.into(),
      publics: self.publics,
      cells: self.cells,
      outputs: self.outputs.clone(),
      tables: self.tables.clone(),
    }
  }
}

#[inline]
fn decode_gate(raw: &[u8], index: usize) -> PackedGate {
  let off = index * GATE_BYTES;
  PackedGate {
    a: read_u32_le(raw, off),
    b: read_u32_le(raw, off + 4),
    c: read_u32_le(raw, off + 8),
    sel: raw[off + 12],
    alpha_id: read_u32_le(raw, off + 13),
    beta_id: read_u32_le(raw, off + 17),
    omega_id: read_u32_le(raw, off + 21),
    qc: i8::from_le_bytes([raw[off + 25]]),
  }
}

/// Builder to serialize a valid `ix-aiur-scs-v1` binary buffer (used for tests
/// and synthetic fixture generation).
#[derive(Clone, Debug)]
pub struct ScsBuilder<C: KzgCurve> {
  pub publics: usize,
  pub wires: usize,
  pub pre: usize,
  pub gamma: u32,
  pub beta: u32,
  pub outputs: Vec<u32>,
  pub coeffs: Vec<C::Fr>,
  pub gates: Vec<PackedGate>,
  pub commits: Vec<u32>,
  pub hints: Vec<WireHint>,
  pub tables: Vec<Table>,
}

impl<C: KzgCurve> ScsBuilder<C> {
  /// Encode into canonical `ix-aiur-scs-v1` (`ixscs001`) bytes.
  pub fn encode(&self) -> Vec<u8> {
    assert_eq!(self.hints.len(), self.wires);
    let mut out = Vec::new();
    out.extend_from_slice(MAGIC);
    for v in [
      self.publics,
      self.outputs.len(),
      self.wires,
      self.gates.len(),
      self.pre,
      self.commits.len(),
      self.gamma as usize,
      self.beta as usize,
      self.coeffs.len(),
      self.tables.len(),
    ] {
      out.extend_from_slice(
        &u64::try_from(v).expect("header field fits u64").to_le_bytes(),
      );
    }
    for &w in &self.outputs {
      out.extend_from_slice(&w.to_le_bytes());
    }
    for &c in &self.coeffs {
      let bytes = c.into_bigint().to_bytes_le();
      assert_eq!(bytes.len(), 32);
      out.extend_from_slice(&bytes);
    }
    for g in &self.gates {
      out.extend_from_slice(&g.a.to_le_bytes());
      out.extend_from_slice(&g.b.to_le_bytes());
      out.extend_from_slice(&g.c.to_le_bytes());
      out.push(g.sel);
      out.extend_from_slice(&g.alpha_id.to_le_bytes());
      out.extend_from_slice(&g.beta_id.to_le_bytes());
      out.extend_from_slice(&g.omega_id.to_le_bytes());
      out.push(g.qc.to_le_bytes()[0]);
    }
    for &w in &self.commits {
      out.extend_from_slice(&w.to_le_bytes());
    }
    for &hint in &self.hints {
      let (kind, x, y) = match hint {
        WireHint::Input => (HINT_INPUT, 0, 0),
        WireHint::Solve { gate } => (HINT_SOLVE, gate, 0),
        WireHint::Bit { wire, bit } => (HINT_BIT, wire, bit),
        WireHint::Challenge => (HINT_CHALLENGE, 0, 0),
        WireHint::Free => (HINT_FREE, 0, 0),
      };
      out.push(kind);
      out.extend_from_slice(&x.to_le_bytes());
      out.extend_from_slice(&y.to_le_bytes());
    }
    for t in &self.tables {
      let name_bytes = t.name.as_bytes();
      let name_len = u16::try_from(name_bytes.len()).expect("name fits u16");
      out.extend_from_slice(&name_len.to_le_bytes());
      out.extend_from_slice(name_bytes);
      out.extend_from_slice(&t.cell_base.to_le_bytes());
      out.extend_from_slice(&t.rows.to_le_bytes());
      out.extend_from_slice(&t.width.to_le_bytes());
    }
    out
  }
}
