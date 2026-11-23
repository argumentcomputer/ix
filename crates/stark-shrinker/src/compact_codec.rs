//! Lossless, canonical, fail-closed fixed-shape codec for Protocol `v6` (`Fp^3`)
//! and `v6-zk` (`Fp^3` hiding) `multi-stark` proofs.
//!
//! `multi_stark::prover::Proof::to_bytes()` uses `bincode` Fixint, which prefixes
//! every nested `Vec<Val>` / `Vec<ExtVal3>` with an 8-byte `u64` length header
//! even when the verifier already knows the exact shape from `System`, `active`,
//! `log_degrees`, and `FriParameters`. Stripping those redundant fixed-shape
//! length prefixes saves ~20–40 KB per proof with zero change to soundness, ZK,
//! or the underlying `Proof<SC>` verified by `System::verify_multiple_claims`.

use multi_stark::{
  config::ProofConfig,
  expr::Source,
  p3_adapter::zk::{HidingMultiProof, ZK_LEAF_SALT_BYTES},
  p3_field::{BasedVectorSpace, PrimeField64},
  prover::{Commitments, Proof},
  system::System,
  traits::Pcs,
  types::{
    Commitment, ExtVal3, FriParameters, GoldilocksBlake3V6Config,
    GoldilocksBlake3V6ZkConfig, Val,
  },
};
use p3_fri::{BatchMultiOpening, CommitPhaseMultiStep, FriProof};
use p3_merkle_tree::PrunedMerklePaths;

const CODEC_VERSION: u8 = 1;
const EXTENSION_D: usize = 3;

/// Expected per-batch matrix widths and OOD point counts derived purely from
/// trusted `System` metadata plus the proof's `(active, log_degrees)`.
struct ProofLayout {
  active_indices: Vec<usize>,
  max_log_lde: usize,
  cap_height: usize,
  num_queries: usize,
  max_log_arity: usize,
  log_final_poly_len: usize,
  log_blowup: usize,
  has_preprocessed: bool,
  ood_shapes: [Vec<(usize, usize)>; 4], // (points, width) per matrix
  batch_widths: Vec<Vec<usize>>,        // 3 or 4 batches
}

fn expected_cap_roots(cap_height: usize, log_height: usize) -> usize {
  1usize << cap_height.min(log_height)
}

fn compute_layout<SC>(
  system: &System<SC>,
  cap_height: usize,
  fri: FriParameters,
  active: &[bool],
  log_degrees: &[u8],
) -> Result<ProofLayout, String>
where
  SC: ProofConfig<Challenge = ExtVal3>,
  SC::Pcs: Pcs<F = Val, Commitment = Commitment>,
{
  let is_zk = system.config.is_zk();
  let zk_shift = usize::from(is_zk);
  if active.len() != system.circuits.len() {
    return Err("active bitmap length mismatch".into());
  }
  let active_indices: Vec<usize> =
    active.iter().enumerate().filter_map(|(i, &a)| a.then_some(i)).collect();
  let num_active = active_indices.len();
  if num_active == 0 {
    return Err("proof has no active circuits".into());
  }
  if log_degrees.len() != num_active {
    return Err("log_degrees length mismatch".into());
  }
  let max_log_deg =
    log_degrees.iter().copied().map(usize::from).max().unwrap_or(0);
  let log_blowup = system.config.log_blowup();
  let max_log_lde = max_log_deg
    .checked_add(zk_shift)
    .and_then(|v| v.checked_add(log_blowup))
    .ok_or("max_log_lde overflow")?;

  let mut s1_ood = Vec::with_capacity(num_active);
  let mut s1_widths = Vec::with_capacity(num_active);
  let mut s2_ood = Vec::with_capacity(num_active + 1);
  let mut s2_widths = Vec::with_capacity(num_active + 1);
  let mut q_ood = Vec::with_capacity(num_active + 1);
  let mut q_widths = Vec::with_capacity(num_active + 1);

  for &ci in &active_indices {
    let c = &system.circuits[ci];
    let s1_pts = 1 + usize::from(system.opens_next_row(ci, Source::Main));
    s1_ood.push((s1_pts, c.main_width));
    s1_widths.push(c.main_width);

    s2_ood.push((2, c.stage_2_width));
    s2_widths.push(c.stage_2_width);

    let q_deg = c.quotient_degree_for(is_zk);
    let q_slices = if is_zk { 2 * q_deg } else { q_deg };
    let qw =
      q_slices.checked_mul(EXTENSION_D).ok_or("quotient width overflow")?;
    q_ood.push((1, qw));
    q_widths.push(qw);
  }

  if is_zk && num_active > 1 {
    let mask_w = (num_active - 1) * EXTENSION_D;
    s2_ood.push((1, mask_w));
    s2_widths.push(mask_w);
  }
  if is_zk {
    let rw = system.config.zk_randomizer_width();
    q_ood.push((1, rw));
    q_widths.push(rw);
  }

  let has_preprocessed = system.preprocessed_commit.is_some();
  let mut prep_ood = Vec::new();
  let mut prep_widths = Vec::new();
  if has_preprocessed {
    for (ci, (&prep_idx, &is_active)) in
      system.preprocessed_indices.iter().zip(active).enumerate()
    {
      if prep_idx.is_some() {
        let c = &system.circuits[ci];
        let pts = if is_active {
          1 + usize::from(system.opens_next_row(ci, Source::Preprocessed))
        } else {
          usize::from(!system.config.omit_inactive_preprocessed_openings())
        };
        prep_ood.push((pts, c.preprocessed_width));
        prep_widths.push(c.preprocessed_width);
      }
    }
  }

  let mut batch_widths = vec![s1_widths, s2_widths, q_widths];
  if has_preprocessed {
    batch_widths.push(prep_widths);
  }

  Ok(ProofLayout {
    active_indices,
    max_log_lde,
    cap_height,
    num_queries: fri.num_queries,
    max_log_arity: fri.max_log_arity,
    log_final_poly_len: fri.log_final_poly_len,
    log_blowup,
    has_preprocessed,
    ood_shapes: [s1_ood, s2_ood, q_ood, prep_ood],
    batch_widths,
  })
}

fn write_u16(out: &mut Vec<u8>, v: usize) -> Result<(), String> {
  let word = u16::try_from(v)
    .map_err(|err| format!("compact codec: {v} exceeds u16: {err}"))?;
  out.extend_from_slice(&word.to_le_bytes());
  Ok(())
}

fn write_u32(out: &mut Vec<u8>, v: usize) -> Result<(), String> {
  let word = u32::try_from(v)
    .map_err(|err| format!("compact codec: {v} exceeds u32: {err}"))?;
  out.extend_from_slice(&word.to_le_bytes());
  Ok(())
}

#[inline]
fn write_val(out: &mut Vec<u8>, v: Val) {
  out.extend_from_slice(&v.as_canonical_u64().to_le_bytes());
}

#[inline]
fn write_ext3(out: &mut Vec<u8>, e: ExtVal3) {
  let coeffs = e.as_basis_coefficients_slice();
  debug_assert_eq!(coeffs.len(), EXTENSION_D);
  for &c in coeffs {
    write_val(out, c);
  }
}

fn write_cap(
  out: &mut Vec<u8>,
  cap: &Commitment,
  expected_roots: usize,
) -> Result<(), String> {
  let roots = cap.roots();
  if roots.len() != expected_roots {
    return Err(format!(
      "compact codec: expected {expected_roots} cap roots, got {}",
      roots.len()
    ));
  }
  for root in roots {
    out.extend_from_slice(root);
  }
  Ok(())
}

fn write_ood_round(
  out: &mut Vec<u8>,
  round: &[Vec<Vec<ExtVal3>>],
  shapes: &[(usize, usize)],
) -> Result<(), String> {
  if round.len() != shapes.len() {
    return Err(format!(
      "compact codec: OOD matrix count {} != expected {}",
      round.len(),
      shapes.len()
    ));
  }
  for (mat, &(pts, width)) in round.iter().zip(shapes) {
    if mat.len() != pts {
      return Err(format!(
        "compact codec: OOD point count {} != expected {pts}",
        mat.len()
      ));
    }
    for row in mat {
      if row.len() != width {
        return Err(format!(
          "compact codec: OOD row width {} != expected {width}",
          row.len()
        ));
      }
      for &val in row {
        write_ext3(out, val);
      }
    }
  }
  Ok(())
}

fn write_pruned_hashes(
  out: &mut Vec<u8>,
  pruned: &PrunedMerklePaths<u8, 32>,
) -> Result<(), String> {
  write_u32(out, pruned.sibling_hashes.len())?;
  for hash in &pruned.sibling_hashes {
    out.extend_from_slice(hash);
  }
  Ok(())
}

fn write_hiding_multi(
  out: &mut Vec<u8>,
  proof: &HidingMultiProof,
) -> Result<(), String> {
  write_u16(out, proof.salts.len())?;
  for group in &proof.salts {
    write_u32(out, group.len())?;
    for salt in group {
      out.extend_from_slice(salt);
    }
  }
  write_pruned_hashes(out, &proof.pruned)
}

struct Cursor<'a> {
  bytes: &'a [u8],
  pos: usize,
}

impl<'a> Cursor<'a> {
  const fn new(bytes: &'a [u8]) -> Self {
    Self { bytes, pos: 0 }
  }

  fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self.pos.checked_add(n).ok_or("compact codec offset overflow")?;
    let slice =
      self.bytes.get(self.pos..end).ok_or("compact codec: unexpected EOF")?;
    self.pos = end;
    Ok(slice)
  }

  fn read_u8(&mut self) -> Result<u8, String> {
    Ok(self.take(1)?[0])
  }

  fn read_u16(&mut self) -> Result<usize, String> {
    let b = self.take(2)?;
    Ok(usize::from(u16::from_le_bytes([b[0], b[1]])))
  }

  fn read_u32(&mut self) -> Result<usize, String> {
    let b = self.take(4)?;
    usize::try_from(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
      .map_err(|err| format!("compact codec: u32 overflows usize: {err}"))
  }

  fn read_val(&mut self) -> Result<Val, String> {
    let b = self.take(8)?;
    let raw = u64::from_le_bytes(b.try_into().expect("8 bytes"));
    if raw >= Val::ORDER_U64 {
      return Err(format!("compact codec: noncanonical Goldilocks word {raw}"));
    }
    Ok(Val::new(raw))
  }

  fn read_ext3(&mut self) -> Result<ExtVal3, String> {
    let c0 = self.read_val()?;
    let c1 = self.read_val()?;
    let c2 = self.read_val()?;
    ExtVal3::from_basis_coefficients_slice(&[c0, c1, c2])
      .ok_or_else(|| "compact codec: ExtVal3 basis error".into())
  }

  fn read_hash(&mut self) -> Result<[u8; 32], String> {
    let b = self.take(32)?;
    Ok(b.try_into().expect("32 bytes"))
  }

  fn read_salt(&mut self) -> Result<[u8; ZK_LEAF_SALT_BYTES], String> {
    let b = self.take(ZK_LEAF_SALT_BYTES)?;
    Ok(b.try_into().expect("16 bytes"))
  }

  fn read_cap(&mut self, expected_roots: usize) -> Result<Commitment, String> {
    let mut roots = Vec::with_capacity(expected_roots);
    for _ in 0..expected_roots {
      roots.push(self.read_hash()?);
    }
    Ok(Commitment::new(roots))
  }

  fn read_ood_round(
    &mut self,
    shapes: &[(usize, usize)],
  ) -> Result<Vec<Vec<Vec<ExtVal3>>>, String> {
    let mut round = Vec::with_capacity(shapes.len());
    for &(pts, width) in shapes {
      let mut mat = Vec::with_capacity(pts);
      for _ in 0..pts {
        let mut row = Vec::with_capacity(width);
        for _ in 0..width {
          row.push(self.read_ext3()?);
        }
        mat.push(row);
      }
      round.push(mat);
    }
    Ok(round)
  }

  fn read_pruned_hashes(
    &mut self,
  ) -> Result<PrunedMerklePaths<u8, 32>, String> {
    let count = self.read_u32()?;
    let remaining = self.bytes.len().saturating_sub(self.pos);
    if count > remaining / 32 {
      return Err(
        "compact codec: sibling hash count exceeds input size".into(),
      );
    }
    let mut sibling_hashes = Vec::with_capacity(count);
    for _ in 0..count {
      sibling_hashes.push(self.read_hash()?);
    }
    Ok(PrunedMerklePaths { sibling_hashes })
  }

  fn read_hiding_multi(&mut self) -> Result<HidingMultiProof, String> {
    let groups = self.read_u16()?;
    if groups > 64 {
      return Err("compact codec: excessive salt height groups".into());
    }
    let mut salts = Vec::with_capacity(groups);
    for _ in 0..groups {
      let count = self.read_u32()?;
      let remaining = self.bytes.len().saturating_sub(self.pos);
      if count > remaining / ZK_LEAF_SALT_BYTES {
        return Err("compact codec: salt count exceeds input size".into());
      }
      let mut group = Vec::with_capacity(count);
      for _ in 0..count {
        group.push(self.read_salt()?);
      }
      salts.push(group);
    }
    let pruned = self.read_pruned_hashes()?;
    Ok(HidingMultiProof { salts, pruned })
  }

  fn finish(&self) -> Result<(), String> {
    if self.pos != self.bytes.len() {
      return Err(format!(
        "compact codec: {} trailing bytes",
        self.bytes.len() - self.pos
      ));
    }
    Ok(())
  }
}

fn encode_active_bits(out: &mut Vec<u8>, active: &[bool]) {
  let num_bytes = active.len().div_ceil(8);
  let start = out.len();
  out.resize(start + num_bytes, 0u8);
  for (i, &bit) in active.iter().enumerate() {
    if bit {
      out[start + (i / 8)] |= 1u8 << (i % 8);
    }
  }
}

fn decode_active_bits(
  cur: &mut Cursor<'_>,
  num_circuits: usize,
) -> Result<Vec<bool>, String> {
  let num_bytes = num_circuits.div_ceil(8);
  let bytes = cur.take(num_bytes)?;
  // Reject non-zero unused padding bits to guarantee a single canonical encoding.
  let used_in_last = num_circuits % 8;
  if used_in_last != 0 {
    let mask = !((1u8 << used_in_last) - 1);
    if bytes[num_bytes - 1] & mask != 0 {
      return Err("compact codec: noncanonical active bitmap padding".into());
    }
  }
  let mut active = Vec::with_capacity(num_circuits);
  for i in 0..num_circuits {
    active.push((bytes[i / 8] & (1u8 << (i % 8))) != 0);
  }
  Ok(active)
}

fn encode_header_and_ood<SC>(
  out: &mut Vec<u8>,
  system: &System<SC>,
  cap_height: usize,
  fri: FriParameters,
  proof: &Proof<SC>,
) -> Result<ProofLayout, String>
where
  SC: ProofConfig<Challenge = ExtVal3>,
  SC::Pcs: Pcs<F = Val, Commitment = Commitment>,
{
  let layout =
    compute_layout(system, cap_height, fri, &proof.active, &proof.log_degrees)?;
  out.push(CODEC_VERSION);
  encode_active_bits(out, &proof.active);
  out.extend_from_slice(&proof.log_degrees);
  if proof.intermediate_accumulators.len() != layout.active_indices.len() {
    return Err(
      "compact codec: intermediate_accumulators count mismatch".into(),
    );
  }
  for &acc in &proof.intermediate_accumulators {
    write_ext3(out, acc);
  }
  let cap_roots = expected_cap_roots(layout.cap_height, layout.max_log_lde);
  write_cap(out, &proof.commitments.stage_1_trace, cap_roots)?;
  write_cap(out, &proof.commitments.stage_2_trace, cap_roots)?;
  write_cap(out, &proof.commitments.quotient_chunks, cap_roots)?;

  write_ood_round(out, &proof.stage_1_opened_values, &layout.ood_shapes[0])?;
  write_ood_round(out, &proof.stage_2_opened_values, &layout.ood_shapes[1])?;
  write_ood_round(out, &proof.quotient_opened_values, &layout.ood_shapes[2])?;
  match (&proof.preprocessed_opened_values, layout.has_preprocessed) {
    (Some(prep), true) => write_ood_round(out, prep, &layout.ood_shapes[3])?,
    (None, false) => {},
    _ => {
      return Err("compact codec: preprocessed_opened_values mismatch".into());
    },
  }
  Ok(layout)
}

fn write_input_rows(
  out: &mut Vec<u8>,
  opened_values: &[Vec<Vec<Val>>],
  num_queries: usize,
  widths: &[usize],
) -> Result<(), String> {
  if opened_values.len() != num_queries {
    return Err(format!(
      "compact codec: input batch query count {} != {num_queries}",
      opened_values.len()
    ));
  }
  for q_rows in opened_values {
    if q_rows.len() != widths.len() {
      return Err(format!(
        "compact codec: input batch matrix count {} != {}",
        q_rows.len(),
        widths.len()
      ));
    }
    for (row, &w) in q_rows.iter().zip(widths) {
      if row.len() != w {
        return Err(format!(
          "compact codec: input batch row width {} != {w}",
          row.len()
        ));
      }
      for &val in row {
        write_val(out, val);
      }
    }
  }
  Ok(())
}

fn read_input_rows(
  cur: &mut Cursor<'_>,
  num_queries: usize,
  widths: &[usize],
) -> Result<Vec<Vec<Vec<Val>>>, String> {
  let mut opened_values = Vec::with_capacity(num_queries);
  for _ in 0..num_queries {
    let mut q_rows = Vec::with_capacity(widths.len());
    for &w in widths {
      let mut row = Vec::with_capacity(w);
      for _ in 0..w {
        row.push(cur.read_val()?);
      }
      q_rows.push(row);
    }
    opened_values.push(q_rows);
  }
  Ok(opened_values)
}

/// Canonical fixed-shape compact encoding of a transparent Protocol `v6` proof.
pub fn encode_v6(
  system: &System<GoldilocksBlake3V6Config>,
  proof: &Proof<GoldilocksBlake3V6Config>,
) -> Result<Vec<u8>, String> {
  let mut out = Vec::with_capacity(256 * 1024);
  let layout = encode_header_and_ood(
    &mut out,
    system,
    system.config.cap_height(),
    system.config.fri_parameters(),
    proof,
  )?;
  let fri = &proof.opening_proof;
  let num_rounds = fri.commit_phase_openings.len();
  if fri.commit_phase_commits.len() != num_rounds
    || fri.commit_pow_witnesses.len() != num_rounds
  {
    return Err("compact codec: FRI commit phase length mismatch".into());
  }
  let num_rounds_u8 = u8::try_from(num_rounds).map_err(|err| {
    format!("compact codec: FRI round count exceeds u8: {err}")
  })?;
  out.push(num_rounds_u8);
  for step in &fri.commit_phase_openings {
    out.push(step.log_arity);
  }

  let mut cur_log_h = layout.max_log_lde;
  for (comm, step) in
    fri.commit_phase_commits.iter().zip(&fri.commit_phase_openings)
  {
    let la = usize::from(step.log_arity);
    if la == 0 || la > layout.max_log_arity || la > cur_log_h {
      return Err("compact codec: invalid FRI log_arity".into());
    }
    cur_log_h -= la;
    write_cap(
      &mut out,
      comm,
      expected_cap_roots(layout.cap_height, cur_log_h),
    )?;
  }
  if cur_log_h != layout.log_blowup + layout.log_final_poly_len {
    return Err("compact codec: FRI total log reduction mismatch".into());
  }
  for &w in &fri.commit_pow_witnesses {
    write_val(&mut out, w);
  }
  write_val(&mut out, fri.query_pow_witness);

  let expected_final = 1usize << layout.log_final_poly_len;
  if fri.final_poly.len() != expected_final {
    return Err("compact codec: final_poly length mismatch".into());
  }
  for &c in &fri.final_poly {
    write_ext3(&mut out, c);
  }

  if fri.input_openings.len() != layout.batch_widths.len() {
    return Err("compact codec: input_openings batch count mismatch".into());
  }
  for (opening, widths) in fri.input_openings.iter().zip(&layout.batch_widths) {
    write_input_rows(
      &mut out,
      &opening.opened_values,
      layout.num_queries,
      widths,
    )?;
    write_pruned_hashes(&mut out, &opening.opening_proof)?;
  }

  for step in &fri.commit_phase_openings {
    let expected_sibs = (1usize << usize::from(step.log_arity)) - 1;
    if step.sibling_values.len() != layout.num_queries {
      return Err("compact codec: FRI sibling query count mismatch".into());
    }
    for sibs in &step.sibling_values {
      if sibs.len() != expected_sibs {
        return Err("compact codec: FRI sibling arity mismatch".into());
      }
      for &val in sibs {
        write_ext3(&mut out, val);
      }
    }
    write_pruned_hashes(&mut out, &step.opening_proof)?;
  }

  Ok(out)
}

/// Fail-closed canonical fixed-shape decoder for a transparent Protocol `v6` proof.
pub fn decode_v6(
  system: &System<GoldilocksBlake3V6Config>,
  bytes: &[u8],
) -> Result<Proof<GoldilocksBlake3V6Config>, String> {
  let mut cur = Cursor::new(bytes);
  let version = cur.read_u8()?;
  if version != CODEC_VERSION {
    return Err(format!("compact codec: unsupported version {version}"));
  }
  let active = decode_active_bits(&mut cur, system.circuits.len())?;
  let num_active = active.iter().filter(|&&a| a).count();
  let log_degrees = cur.take(num_active)?.to_vec();
  let layout = compute_layout(
    system,
    system.config.cap_height(),
    system.config.fri_parameters(),
    &active,
    &log_degrees,
  )?;

  let mut intermediate_accumulators = Vec::with_capacity(num_active);
  for _ in 0..num_active {
    intermediate_accumulators.push(cur.read_ext3()?);
  }
  let cap_roots = expected_cap_roots(layout.cap_height, layout.max_log_lde);
  let commitments = Commitments {
    stage_1_trace: cur.read_cap(cap_roots)?,
    stage_2_trace: cur.read_cap(cap_roots)?,
    quotient_chunks: cur.read_cap(cap_roots)?,
  };
  let stage_1_opened_values = cur.read_ood_round(&layout.ood_shapes[0])?;
  let stage_2_opened_values = cur.read_ood_round(&layout.ood_shapes[1])?;
  let quotient_opened_values = cur.read_ood_round(&layout.ood_shapes[2])?;
  let preprocessed_opened_values = if layout.has_preprocessed {
    Some(cur.read_ood_round(&layout.ood_shapes[3])?)
  } else {
    None
  };

  let num_rounds = usize::from(cur.read_u8()?);
  let log_arities = cur.take(num_rounds)?.to_vec();
  let mut commit_phase_commits = Vec::with_capacity(num_rounds);
  let mut cur_log_h = layout.max_log_lde;
  for &la_u8 in &log_arities {
    let la = usize::from(la_u8);
    if la == 0 || la > layout.max_log_arity || la > cur_log_h {
      return Err("compact codec: invalid FRI log_arity".into());
    }
    cur_log_h -= la;
    commit_phase_commits
      .push(cur.read_cap(expected_cap_roots(layout.cap_height, cur_log_h))?);
  }
  if cur_log_h != layout.log_blowup + layout.log_final_poly_len {
    return Err("compact codec: FRI total log reduction mismatch".into());
  }

  let mut commit_pow_witnesses = Vec::with_capacity(num_rounds);
  for _ in 0..num_rounds {
    commit_pow_witnesses.push(cur.read_val()?);
  }
  let query_pow_witness = cur.read_val()?;

  let expected_final = 1usize << layout.log_final_poly_len;
  let mut final_poly = Vec::with_capacity(expected_final);
  for _ in 0..expected_final {
    final_poly.push(cur.read_ext3()?);
  }

  let mut input_openings = Vec::with_capacity(layout.batch_widths.len());
  for widths in &layout.batch_widths {
    let opened_values = read_input_rows(&mut cur, layout.num_queries, widths)?;
    let opening_proof = cur.read_pruned_hashes()?;
    input_openings.push(BatchMultiOpening { opened_values, opening_proof });
  }

  let mut commit_phase_openings = Vec::with_capacity(num_rounds);
  for &la_u8 in &log_arities {
    let expected_sibs = (1usize << usize::from(la_u8)) - 1;
    let mut sibling_values = Vec::with_capacity(layout.num_queries);
    for _ in 0..layout.num_queries {
      let mut sibs = Vec::with_capacity(expected_sibs);
      for _ in 0..expected_sibs {
        sibs.push(cur.read_ext3()?);
      }
      sibling_values.push(sibs);
    }
    let opening_proof = cur.read_pruned_hashes()?;
    commit_phase_openings.push(CommitPhaseMultiStep {
      log_arity: la_u8,
      sibling_values,
      opening_proof,
    });
  }

  cur.finish()?;
  Ok(Proof {
    active,
    commitments,
    intermediate_accumulators,
    log_degrees,
    opening_proof: FriProof {
      commit_phase_commits,
      commit_pow_witnesses,
      input_openings,
      commit_phase_openings,
      final_poly,
      query_pow_witness,
    },
    quotient_opened_values,
    preprocessed_opened_values,
    stage_1_opened_values,
    stage_2_opened_values,
  })
}

/// Canonical fixed-shape compact encoding of a hiding Protocol `v6-zk` proof.
pub fn encode_v6_zk(
  system: &System<GoldilocksBlake3V6ZkConfig>,
  proof: &Proof<GoldilocksBlake3V6ZkConfig>,
) -> Result<Vec<u8>, String> {
  let mut out = Vec::with_capacity(256 * 1024);
  let layout = encode_header_and_ood(
    &mut out,
    system,
    system.config.cap_height(),
    system.config.fri_parameters(),
    proof,
  )?;
  let fri = &proof.opening_proof;
  let num_rounds = fri.commit_phase_openings.len();
  if fri.commit_phase_commits.len() != num_rounds
    || fri.commit_pow_witnesses.len() != num_rounds
  {
    return Err("compact codec: FRI commit phase length mismatch".into());
  }
  let num_rounds_u8 = u8::try_from(num_rounds).map_err(|err| {
    format!("compact codec: FRI round count exceeds u8: {err}")
  })?;
  out.push(num_rounds_u8);
  for step in &fri.commit_phase_openings {
    out.push(step.log_arity);
  }

  let mut cur_log_h = layout.max_log_lde;
  for (comm, step) in
    fri.commit_phase_commits.iter().zip(&fri.commit_phase_openings)
  {
    let la = usize::from(step.log_arity);
    if la == 0 || la > layout.max_log_arity || la > cur_log_h {
      return Err("compact codec: invalid FRI log_arity".into());
    }
    cur_log_h -= la;
    write_cap(
      &mut out,
      comm,
      expected_cap_roots(layout.cap_height, cur_log_h),
    )?;
  }
  if cur_log_h != layout.log_blowup + layout.log_final_poly_len {
    return Err("compact codec: FRI total log reduction mismatch".into());
  }
  for &w in &fri.commit_pow_witnesses {
    write_val(&mut out, w);
  }
  write_val(&mut out, fri.query_pow_witness);

  let expected_final = 1usize << layout.log_final_poly_len;
  if fri.final_poly.len() != expected_final {
    return Err("compact codec: final_poly length mismatch".into());
  }
  for &c in &fri.final_poly {
    write_ext3(&mut out, c);
  }

  if fri.input_openings.len() != layout.batch_widths.len() {
    return Err("compact codec: input_openings batch count mismatch".into());
  }
  for (opening, widths) in fri.input_openings.iter().zip(&layout.batch_widths) {
    write_input_rows(
      &mut out,
      &opening.opened_values,
      layout.num_queries,
      widths,
    )?;
    write_hiding_multi(&mut out, &opening.opening_proof)?;
  }

  for step in &fri.commit_phase_openings {
    let expected_sibs = (1usize << usize::from(step.log_arity)) - 1;
    if step.sibling_values.len() != layout.num_queries {
      return Err("compact codec: FRI sibling query count mismatch".into());
    }
    for sibs in &step.sibling_values {
      if sibs.len() != expected_sibs {
        return Err("compact codec: FRI sibling arity mismatch".into());
      }
      for &val in sibs {
        write_ext3(&mut out, val);
      }
    }
    write_hiding_multi(&mut out, &step.opening_proof)?;
  }

  Ok(out)
}

/// Fail-closed canonical fixed-shape decoder for a hiding Protocol `v6-zk` proof.
pub fn decode_v6_zk(
  system: &System<GoldilocksBlake3V6ZkConfig>,
  bytes: &[u8],
) -> Result<Proof<GoldilocksBlake3V6ZkConfig>, String> {
  let mut cur = Cursor::new(bytes);
  let version = cur.read_u8()?;
  if version != CODEC_VERSION {
    return Err(format!("compact codec: unsupported version {version}"));
  }
  let active = decode_active_bits(&mut cur, system.circuits.len())?;
  let num_active = active.iter().filter(|&&a| a).count();
  let log_degrees = cur.take(num_active)?.to_vec();
  let layout = compute_layout(
    system,
    system.config.cap_height(),
    system.config.fri_parameters(),
    &active,
    &log_degrees,
  )?;

  let mut intermediate_accumulators = Vec::with_capacity(num_active);
  for _ in 0..num_active {
    intermediate_accumulators.push(cur.read_ext3()?);
  }
  let cap_roots = expected_cap_roots(layout.cap_height, layout.max_log_lde);
  let commitments = Commitments {
    stage_1_trace: cur.read_cap(cap_roots)?,
    stage_2_trace: cur.read_cap(cap_roots)?,
    quotient_chunks: cur.read_cap(cap_roots)?,
  };
  let stage_1_opened_values = cur.read_ood_round(&layout.ood_shapes[0])?;
  let stage_2_opened_values = cur.read_ood_round(&layout.ood_shapes[1])?;
  let quotient_opened_values = cur.read_ood_round(&layout.ood_shapes[2])?;
  let preprocessed_opened_values = if layout.has_preprocessed {
    Some(cur.read_ood_round(&layout.ood_shapes[3])?)
  } else {
    None
  };

  let num_rounds = usize::from(cur.read_u8()?);
  let log_arities = cur.take(num_rounds)?.to_vec();
  let mut commit_phase_commits = Vec::with_capacity(num_rounds);
  let mut cur_log_h = layout.max_log_lde;
  for &la_u8 in &log_arities {
    let la = usize::from(la_u8);
    if la == 0 || la > layout.max_log_arity || la > cur_log_h {
      return Err("compact codec: invalid FRI log_arity".into());
    }
    cur_log_h -= la;
    commit_phase_commits
      .push(cur.read_cap(expected_cap_roots(layout.cap_height, cur_log_h))?);
  }
  if cur_log_h != layout.log_blowup + layout.log_final_poly_len {
    return Err("compact codec: FRI total log reduction mismatch".into());
  }

  let mut commit_pow_witnesses = Vec::with_capacity(num_rounds);
  for _ in 0..num_rounds {
    commit_pow_witnesses.push(cur.read_val()?);
  }
  let query_pow_witness = cur.read_val()?;

  let expected_final = 1usize << layout.log_final_poly_len;
  let mut final_poly = Vec::with_capacity(expected_final);
  for _ in 0..expected_final {
    final_poly.push(cur.read_ext3()?);
  }

  let mut input_openings = Vec::with_capacity(layout.batch_widths.len());
  for widths in &layout.batch_widths {
    let opened_values = read_input_rows(&mut cur, layout.num_queries, widths)?;
    let opening_proof = cur.read_hiding_multi()?;
    input_openings.push(BatchMultiOpening { opened_values, opening_proof });
  }

  let mut commit_phase_openings = Vec::with_capacity(num_rounds);
  for &la_u8 in &log_arities {
    let expected_sibs = (1usize << usize::from(la_u8)) - 1;
    let mut sibling_values = Vec::with_capacity(layout.num_queries);
    for _ in 0..layout.num_queries {
      let mut sibs = Vec::with_capacity(expected_sibs);
      for _ in 0..expected_sibs {
        sibs.push(cur.read_ext3()?);
      }
      sibling_values.push(sibs);
    }
    let opening_proof = cur.read_hiding_multi()?;
    commit_phase_openings.push(CommitPhaseMultiStep {
      log_arity: la_u8,
      sibling_values,
      opening_proof,
    });
  }

  cur.finish()?;
  Ok(Proof {
    active,
    commitments,
    intermediate_accumulators,
    log_degrees,
    opening_proof: FriProof {
      commit_phase_commits,
      commit_pow_witnesses,
      input_openings,
      commit_phase_openings,
      final_poly,
      query_pow_witness,
    },
    quotient_opened_values,
    preprocessed_opened_values,
    stage_1_opened_values,
    stage_2_opened_values,
  })
}
