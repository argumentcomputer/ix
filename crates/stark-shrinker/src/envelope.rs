//! Canonical fail-closed wire envelope (`IXSTARK6\0`) and VK digest derivation
//! for Endpoint 1 native `Fp^3` STARK shrinking (`--stark-128` / `--stark-128-zk`).

use aiur::trace::stark::Parameters;
use multi_stark::{
  p3_adapter::zk::{ZK_RANDOMIZER_WIDTH, min_zk_log_degree},
  types::CommitmentParameters,
};

/// 9-byte magic prefix distinguishing shrunk native `Fp^3` STARK envelopes from
/// `IXAIUR2\0`, `IXAGGR2\0`, and KZG/Groth16 (`IXCMP*`/`IXBN*`) payloads.
pub const ENVELOPE_MAGIC: &[u8; 9] = b"IXSTARK6\0";

/// Envelope schema version.
pub const ENVELOPE_VERSION: u16 = 1;

/// Retired `v5` (`Fp^2`) is rejected fail-closed; only Protocol `v6` (`Fp^3`)
/// and `v6-zk` (`Fp^3` hiding) are admitted.
pub const PROTOCOL_VERSION: u16 = 6;

/// Cubic Goldilocks extension degree (`Fp^3 = Fp[X] / (X^3 - X - 1)`).
pub const EXTENSION_DEGREE: u16 = 3;

/// `FriBatching::Tensor` wire tag. Horner batching (`0`) is rejected fail-closed.
pub const FRI_BATCHING_TENSOR: u8 = 1;

/// Recursive verifier entrypoint wrapped by the shrinker.
pub const ENTRYPOINT: &str = "MultiStark::verify_multi_stark_proof";

/// Domain separation context for independent shrinker verifying-key pinning.
const SHRINKER_VK_CONTEXT: &str = "ix/stark-shrinker/v1/vk";

/// Fixed binary header size in bytes (everything before `proof_bytes`).
pub const HEADER_LEN: usize = 9 // magic
  + 2 // envelope_version
  + 2 // protocol_version
  + 2 // extension_degree
  + 1 // mode_tag
  + 1 // fri_batching
  + 2 * 9 // lb, cap, lfp, mla, q, cpow, qpow, zk_randomizer_width, min_log_degree
  + 32 * 3 // shrinker_vk_digest, inner_vk_digest, claim_digest
  + 8; // proof_len

/// Default shrinker parameters: `log_blowup = 3, num_queries = 78, query_pow = 20`.
///
/// - 133.49 bits finite-`m` (`m = 16`) Johnson list-decoding soundness (+5.49b headroom)
/// - 84.74 bits provable unique-decoding (`CertiFRI`) soundness
/// - 254 bits conjectured ethSTARK soundness
/// - `max_quotient_degree = 8` (accommodates both `v6` and `v6-zk`)
/// - `min_zk_log_degree(78, 3) = 8` (256 rows, matching `U8` table height)
pub const DEFAULT_PARAMS: Parameters = Parameters {
  log_blowup: 3,
  num_queries: 78,
  commit_proof_of_work_bits: 0,
  query_proof_of_work_bits: 20,
};

/// Compact shrinker parameters: `log_blowup = 4, num_queries = 66, query_pow = 20`.
///
/// - 149.03 bits finite-`m` (`m = 16`) Johnson list-decoding soundness (+21.03b headroom)
/// - 80.19 bits provable unique-decoding (`CertiFRI`) soundness
/// - 284 bits conjectured ethSTARK soundness
/// - `max_quotient_degree = 16`
/// - `min_zk_log_degree(66, 3) = 8` (256 rows)
pub const COMPACT_PARAMS: Parameters = Parameters {
  log_blowup: 4,
  num_queries: 66,
  commit_proof_of_work_bits: 0,
  query_proof_of_work_bits: 20,
};

/// Output mode of the native `Fp^3` STARK shrinker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum ShrinkMode {
  /// `--stark-128`: transparent Protocol `v6` (`GoldilocksBlake3V6Config`, NON-ZK).
  Stark128 = 1,
  /// `--stark-128-zk`: hiding Protocol `v6-zk` (`GoldilocksBlake3V6ZkConfig`, 128-bit ZK).
  Stark128Zk = 2,
}

impl ShrinkMode {
  pub const fn tag(self) -> u8 {
    self as u8
  }

  pub fn from_tag(tag: u8) -> Result<Self, String> {
    match tag {
      1 => Ok(Self::Stark128),
      2 => Ok(Self::Stark128Zk),
      other => Err(format!(
        "unsupported IXSTARK6 mode tag {other} (expected 1 for --stark-128 or 2 for --stark-128-zk)"
      )),
    }
  }

  pub const fn is_zk(self) -> bool {
    matches!(self, Self::Stark128Zk)
  }

  pub const fn cli_flag(self) -> &'static str {
    match self {
      Self::Stark128 => "--stark-128",
      Self::Stark128Zk => "--stark-128-zk",
    }
  }

  pub const fn protocol_name(self) -> &'static str {
    match self {
      Self::Stark128 => "Protocol v6",
      Self::Stark128Zk => "Protocol v6-zk",
    }
  }

  /// Expected `zk_randomizer_width` for this mode.
  pub const fn expected_randomizer_width(self) -> usize {
    match self {
      Self::Stark128 => 0,
      Self::Stark128Zk => ZK_RANDOMIZER_WIDTH,
    }
  }

  /// Expected `min_log_degree` for this mode at `num_queries`.
  pub const fn expected_min_log_degree(self, num_queries: usize) -> usize {
    match self {
      Self::Stark128 => 0,
      Self::Stark128Zk => {
        min_zk_log_degree(num_queries, EXTENSION_DEGREE as usize)
      },
    }
  }
}

/// Validated metadata header of an `IXSTARK6\0` shrunk proof envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EnvelopeHeader {
  pub mode: ShrinkMode,
  pub params: Parameters,
  pub zk_randomizer_width: u16,
  pub min_log_degree: u16,
  pub shrinker_vk_digest: [u8; 32],
  pub inner_vk_digest: [u8; 32],
  pub claim_digest: [u8; 32],
  pub proof_len: u64,
}

/// Complete decoded `IXSTARK6\0` shrunk proof envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShrinkEnvelope {
  pub header: EnvelopeHeader,
  pub proof_bytes: Vec<u8>,
}

/// Fast prefix check matching `Ix.Cli.StarkShrinker.isShrunk`.
pub fn is_shrunk(bytes: &[u8]) -> bool {
  bytes.starts_with(ENVELOPE_MAGIC)
}

/// Independently derive the canonical shrinker verifying-key pin committing to
/// mode, protocol parameters, ZK parameters, entrypoint identity, `system.vk_digest`,
/// and the preprocessed Merkle cap root(s).
#[allow(clippy::too_many_arguments)]
pub fn compute_shrinker_vk_digest(
  mode: ShrinkMode,
  params: Parameters,
  zk_randomizer_width: usize,
  min_log_degree: usize,
  entry_call_channel: u64,
  entry_function_index: u64,
  system_vk_digest: &[u8; 32],
  preprocessed_roots: Option<&[[u8; 32]]>,
) -> Result<[u8; 32], String> {
  let cp: CommitmentParameters = params.commitment();
  let fp = params.fri();
  let mut hasher = blake3::Hasher::new_derive_key(SHRINKER_VK_CONTEXT);
  hasher.update(&[mode.tag()]);
  hasher.update(&PROTOCOL_VERSION.to_le_bytes());
  hasher.update(&EXTENSION_DEGREE.to_le_bytes());
  hasher.update(&[FRI_BATCHING_TENSOR]);
  for value in [
    cp.log_blowup,
    cp.cap_height,
    fp.log_final_poly_len,
    fp.max_log_arity,
    fp.num_queries,
    fp.commit_proof_of_work_bits,
    fp.query_proof_of_work_bits,
    zk_randomizer_width,
    min_log_degree,
  ] {
    let word = u16::try_from(value).map_err(|err| {
      format!("shrinker VK parameter {value} exceeds u16: {err}")
    })?;
    hasher.update(&word.to_le_bytes());
  }
  hasher.update(&entry_call_channel.to_le_bytes());
  hasher.update(&entry_function_index.to_le_bytes());
  hasher.update(system_vk_digest);
  match preprocessed_roots {
    None => {
      hasher.update(&[0u8]);
    },
    Some(roots) => {
      if roots.len() != 1 {
        return Err(format!(
          "shrinker preprocessed MerkleCap must have 1 root (cap_height = 0), got {}",
          roots.len()
        ));
      }
      hasher.update(&[1u8]);
      hasher.update(&1u16.to_le_bytes());
      hasher.update(&roots[0]);
    },
  }
  Ok(*hasher.finalize().as_bytes())
}

fn read_u16_le(bytes: &[u8], pos: &mut usize) -> Result<u16, String> {
  let end = pos.checked_add(2).ok_or("header offset overflow")?;
  let slice =
    bytes.get(*pos..end).ok_or("truncated IXSTARK6 envelope header")?;
  *pos = end;
  Ok(u16::from_le_bytes([slice[0], slice[1]]))
}

fn read_u64_le(bytes: &[u8], pos: &mut usize) -> Result<u64, String> {
  let end = pos.checked_add(8).ok_or("header offset overflow")?;
  let slice =
    bytes.get(*pos..end).ok_or("truncated IXSTARK6 envelope header")?;
  *pos = end;
  Ok(u64::from_le_bytes(slice.try_into().expect("8-byte slice")))
}

fn read_array32(bytes: &[u8], pos: &mut usize) -> Result<[u8; 32], String> {
  let end = pos.checked_add(32).ok_or("header offset overflow")?;
  let slice =
    bytes.get(*pos..end).ok_or("truncated IXSTARK6 envelope header")?;
  *pos = end;
  Ok(slice.try_into().expect("32-byte slice"))
}

/// Parse and strictly validate the header of an `IXSTARK6\0` envelope without
/// allocating the proof payload.
pub fn peek_header(bytes: &[u8]) -> Result<EnvelopeHeader, String> {
  if bytes.len() < HEADER_LEN {
    return Err(format!(
      "IXSTARK6 envelope too short ({} bytes, minimum {HEADER_LEN})",
      bytes.len()
    ));
  }
  if !is_shrunk(bytes) {
    return Err("invalid magic: expected IXSTARK6\\0 envelope".into());
  }
  let mut pos = ENVELOPE_MAGIC.len();
  let envelope_version = read_u16_le(bytes, &mut pos)?;
  if envelope_version != ENVELOPE_VERSION {
    return Err(format!(
      "unsupported IXSTARK6 envelope version {envelope_version} (expected {ENVELOPE_VERSION})"
    ));
  }
  let protocol_version = read_u16_le(bytes, &mut pos)?;
  if protocol_version != PROTOCOL_VERSION {
    return Err(format!(
      "unsupported STARK protocol version {protocol_version}: Protocol v5 is retired; only Protocol v6 ({PROTOCOL_VERSION}) is accepted"
    ));
  }
  let extension_degree = read_u16_le(bytes, &mut pos)?;
  if extension_degree != EXTENSION_DEGREE {
    return Err(format!(
      "unsupported extension degree {extension_degree}: Fp^2 is retired; only Fp^3 ({EXTENSION_DEGREE}) is accepted"
    ));
  }
  let mode = ShrinkMode::from_tag(bytes[pos])?;
  pos += 1;
  let fri_batching = bytes[pos];
  pos += 1;
  if fri_batching != FRI_BATCHING_TENSOR {
    return Err(format!(
      "unsupported FRI batching tag {fri_batching}: only FriBatching::Tensor ({FRI_BATCHING_TENSOR}) is accepted"
    ));
  }
  let log_blowup = usize::from(read_u16_le(bytes, &mut pos)?);
  let cap_height = usize::from(read_u16_le(bytes, &mut pos)?);
  let log_final_poly_len = usize::from(read_u16_le(bytes, &mut pos)?);
  let max_log_arity = usize::from(read_u16_le(bytes, &mut pos)?);
  let num_queries = usize::from(read_u16_le(bytes, &mut pos)?);
  let commit_pow_bits = usize::from(read_u16_le(bytes, &mut pos)?);
  let query_pow_bits = usize::from(read_u16_le(bytes, &mut pos)?);
  let zk_randomizer_width = read_u16_le(bytes, &mut pos)?;
  let min_log_degree = read_u16_le(bytes, &mut pos)?;
  let shrinker_vk_digest = read_array32(bytes, &mut pos)?;
  let inner_vk_digest = read_array32(bytes, &mut pos)?;
  let claim_digest = read_array32(bytes, &mut pos)?;
  let proof_len = read_u64_le(bytes, &mut pos)?;
  debug_assert_eq!(pos, HEADER_LEN);

  if cap_height != 0 || log_final_poly_len != 0 || max_log_arity != 1 {
    return Err(format!(
      "unsupported FRI shape (cap_height={cap_height}, log_final_poly_len={log_final_poly_len}, max_log_arity={max_log_arity}); expected (0, 0, 1)"
    ));
  }

  let params = Parameters {
    log_blowup,
    num_queries,
    commit_proof_of_work_bits: commit_pow_bits,
    query_proof_of_work_bits: query_pow_bits,
  };
  params.check().map_err(|e| {
    format!("IXSTARK6 parameters below 128-bit security floor: {e}")
  })?;

  match mode {
    ShrinkMode::Stark128 => {
      if zk_randomizer_width != 0 || min_log_degree != 0 {
        return Err(format!(
          "transparent --stark-128 envelope must have zk_randomizer_width=0 and min_log_degree=0 (got {zk_randomizer_width}, {min_log_degree})"
        ));
      }
    },
    ShrinkMode::Stark128Zk => {
      if usize::from(zk_randomizer_width) < ZK_RANDOMIZER_WIDTH {
        return Err(format!(
          "v6-zk envelope randomizer width {zk_randomizer_width} is below minimum {ZK_RANDOMIZER_WIDTH}"
        ));
      }
      if usize::from(zk_randomizer_width) != ZK_RANDOMIZER_WIDTH {
        return Err(format!(
          "unsupported v6-zk randomizer width {zk_randomizer_width} (expected {ZK_RANDOMIZER_WIDTH})"
        ));
      }
      let expected_min =
        min_zk_log_degree(num_queries, EXTENSION_DEGREE as usize);
      if usize::from(min_log_degree) != expected_min {
        return Err(format!(
          "v6-zk envelope min_log_degree {min_log_degree} does not match required {expected_min} for num_queries={num_queries}"
        ));
      }
      if log_blowup < 3 {
        return Err(format!(
          "v6-zk shrinker requires log_blowup >= 3 (got {log_blowup})"
        ));
      }
    },
  }

  let proof_len_usize = usize::try_from(proof_len).map_err(|err| {
    format!("IXSTARK6 proof_len overflows platform usize: {err}")
  })?;
  if proof_len_usize == 0 {
    return Err("IXSTARK6 envelope contains empty proof payload".into());
  }
  let expected_total = HEADER_LEN
    .checked_add(proof_len_usize)
    .ok_or("IXSTARK6 envelope length overflow")?;
  if bytes.len() != expected_total {
    return Err(format!(
      "IXSTARK6 envelope length mismatch: header declares {expected_total} bytes (header {HEADER_LEN} + proof {proof_len_usize}), got {} bytes",
      bytes.len()
    ));
  }

  Ok(EnvelopeHeader {
    mode,
    params,
    zk_randomizer_width,
    min_log_degree,
    shrinker_vk_digest,
    inner_vk_digest,
    claim_digest,
    proof_len,
  })
}

impl ShrinkEnvelope {
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let header = peek_header(bytes)?;
    let proof_bytes = bytes[HEADER_LEN..].to_vec();
    Ok(Self { header, proof_bytes })
  }

  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let proof_len = u64::try_from(self.proof_bytes.len())
      .map_err(|err| format!("proof length exceeds u64: {err}"))?;
    if proof_len != self.header.proof_len {
      return Err(
        "envelope header proof_len disagrees with proof_bytes length".into(),
      );
    }
    let cp = self.header.params.commitment();
    let fp = self.header.params.fri();
    let mut out = Vec::with_capacity(HEADER_LEN + self.proof_bytes.len());
    out.extend_from_slice(ENVELOPE_MAGIC);
    out.extend_from_slice(&ENVELOPE_VERSION.to_le_bytes());
    out.extend_from_slice(&PROTOCOL_VERSION.to_le_bytes());
    out.extend_from_slice(&EXTENSION_DEGREE.to_le_bytes());
    out.push(self.header.mode.tag());
    out.push(FRI_BATCHING_TENSOR);
    for value in [
      cp.log_blowup,
      cp.cap_height,
      fp.log_final_poly_len,
      fp.max_log_arity,
      fp.num_queries,
      fp.commit_proof_of_work_bits,
      fp.query_proof_of_work_bits,
    ] {
      let word = u16::try_from(value)
        .map_err(|err| format!("parameter {value} exceeds u16: {err}"))?;
      out.extend_from_slice(&word.to_le_bytes());
    }
    out.extend_from_slice(&self.header.zk_randomizer_width.to_le_bytes());
    out.extend_from_slice(&self.header.min_log_degree.to_le_bytes());
    out.extend_from_slice(&self.header.shrinker_vk_digest);
    out.extend_from_slice(&self.header.inner_vk_digest);
    out.extend_from_slice(&self.header.claim_digest);
    out.extend_from_slice(&proof_len.to_le_bytes());
    debug_assert_eq!(out.len(), HEADER_LEN);
    out.extend_from_slice(&self.proof_bytes);
    Ok(out)
  }
}
