//! Vertical circuit merger and FRI-arity height aligner for `multi-stark`
//! Plonkish circuits with compact BLAKE3 custom gates. Its equivalence with
//! the unmerged lowering is not proved: it is checked by the differential
//! test `tests/merged_blake3_differential.rs`, and `try_merge` admits only the
//! lowering that test covers (`COMPACT_BLAKE3_STRUCTURE_DIGEST`).
//!
//! `multi-stark`'s `Circuit::lower_to_multi_stark_sharded` with compact BLAKE3
//! emits 9 auxiliary circuits alongside the computation trace(s) and merged
//! `ByteGadgets` table:
//! - 6 BLAKE3 pipeline circuits (`t0..t5`: widths 32, 40, 32, 40, 12, 4)
//! - 3 BLAKE3 fixed tables (`xor`: 65536, `split`: 512, `byte`: 256)
//!
//! Because every constraint and lookup in those 10 auxiliary circuits is purely
//! row-local (`RowOffset::Current`), we vertically multiplex them with zero
//! soundness loss and zero `multi-stark` modifications into just **2 circuits**:
//! 1. `B3_All` (`t0 + t1 + t2 + t3 + t4 + t5`, `main_width = 40`, `prep_width = 24`,
//!    `max_constraint_degree = 3`, `29` lookups)
//! 2. `UnifiedTable` (`ByteGadgets + B3 xor + B3 split(4/7) + B3 byte`,
//!    `main_width = 1`, `prep_width = 4`, **`1` single lookup**, uniform height
//!    aligned to `max_log - k * max_log_arity` for zero forced low-arity FRI rounds!)

use multi_stark::{
  expr::{ColRef, Expr, RowOffset, Source},
  lookup::Lookup,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  plonkish::{Assignment, MultiStarkCircuit},
  system::CircuitInputs,
  types::Val,
};

const B3_MAIN_WIDTHS: [usize; 6] = [32, 40, 32, 40, 12, 4];
const B3_PREP_WIDTHS: [usize; 6] = [14, 14, 14, 14, 8, 18];
const B3_TABLE_PREPS: [(usize, usize); 3] = [(65536, 3), (512, 4), (256, 1)];

/// Private table IDs on channel `(ns, 2, table_id, c0, c1, c2)` used exclusively
/// by `B3_All` and `UnifiedTable`. Validated fail-closed to be strictly greater
/// than every `ByteGadgets` table ID in the lowered circuit.
const TID_B3_XOR: usize = 10;
const TID_B3_SPLIT4: usize = 11;
const TID_B3_SPLIT7: usize = 12;
const TID_B3_BYTE: usize = 13;

/// Structure digest ([`compact_blake3_structure_digest`]) of the lowered
/// compact-BLAKE3 circuits that `B3_All` and `UnifiedTable` restate by hand.
/// `try_merge` refuses any other lowering: a change to `multi-stark`'s BLAKE3
/// gadget (a new constraint, lookup or table entry, even at the same widths)
/// must be reviewed against the merged circuits, and the differential test
/// `tests/merged_blake3_differential.rs` re-run, before this constant moves.
pub const COMPACT_BLAKE3_STRUCTURE_DIGEST: [u8; 32] = [
  0x7e, 0xbc, 0x5b, 0x47, 0xc3, 0x96, 0x6b, 0x0c, 0x1a, 0x0b, 0x34, 0xb2, 0xd1,
  0xf0, 0xf7, 0x12, 0x8d, 0x35, 0x05, 0xb4, 0xb3, 0x34, 0x43, 0x6a, 0x7c, 0x21,
  0x1f, 0x5d, 0xb8, 0x4a, 0xc8, 0x70,
];

const STRUCTURE_DIGEST_CONTEXT: &str =
  "ix/stark-shrinker/circuit-merge/compact-blake3-structure/v1";

fn hash_expr(hasher: &mut blake3::Hasher, expr: &Expr<Val>) {
  match expr {
    Expr::Const(c) => {
      hasher.update(&[0]);
      hasher.update(&c.as_canonical_u64().to_le_bytes());
    },
    Expr::Var(col) => {
      let source = match col.source {
        Source::Preprocessed => 0u8,
        Source::Main => 1,
        Source::Stage2 => 2,
      };
      let offset = match col.offset {
        RowOffset::Current => 0u8,
        RowOffset::Next => 1,
      };
      hasher.update(&[1, source, offset]);
      hasher.update(&col.index.to_le_bytes());
    },
    Expr::Public(i) => {
      hasher.update(&[2]);
      hasher.update(&i.to_le_bytes());
    },
    Expr::IsFirstRow => {
      hasher.update(&[3]);
    },
    Expr::IsLastRow => {
      hasher.update(&[4]);
    },
    Expr::IsTransition => {
      hasher.update(&[5]);
    },
    Expr::Add(a, b) => {
      hasher.update(&[6]);
      hash_expr(hasher, a);
      hash_expr(hasher, b);
    },
    Expr::Sub(a, b) => {
      hasher.update(&[7]);
      hash_expr(hasher, a);
      hash_expr(hasher, b);
    },
    Expr::Mul(a, b) => {
      hasher.update(&[8]);
      hash_expr(hasher, a);
      hash_expr(hasher, b);
    },
    Expr::Neg(a) => {
      hasher.update(&[9]);
      hash_expr(hasher, a);
    },
  }
}

fn hash_len(hasher: &mut blake3::Hasher, len: usize) {
  hasher.update(&(len as u64).to_le_bytes());
}

/// BLAKE3 digest of what `try_merge` discards from the lowered compact-BLAKE3
/// circuits `t0..t5` and their three tables (`definitions[b3_start..][..9]`):
/// every circuit's widths, lookup group size, constraints (base, and the
/// count of extension ones) and lookups, and the tables' fixed contents. The
/// pipeline traces' fixed matrices (row activations and constants, which
/// depend on the hashed messages) are excluded; `try_merge` copies them.
pub fn compact_blake3_structure_digest(
  defs: &[CircuitInputs<Val>],
) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new_derive_key(STRUCTURE_DIGEST_CONTEXT);
  hash_len(&mut hasher, defs.len());
  for (i, def) in defs.iter().enumerate() {
    hash_len(&mut hasher, def.main_width);
    hash_len(&mut hasher, def.preprocessed.as_ref().map_or(0, Matrix::width));
    hash_len(&mut hasher, def.lookup_group_size);
    hash_len(&mut hasher, def.constraints.len());
    for c in &def.constraints {
      hash_expr(&mut hasher, c);
    }
    hash_len(&mut hasher, def.ext_constraints.len());
    hash_len(&mut hasher, def.lookups.len());
    for lookup in &def.lookups {
      hash_expr(&mut hasher, &lookup.multiplicity);
      hash_len(&mut hasher, lookup.args.len());
      for arg in &lookup.args {
        hash_expr(&mut hasher, arg);
      }
    }
    // The three tables (after the six pipeline traces) are fixed content.
    if i >= 6
      && let Some(prep) = def.preprocessed.as_ref()
    {
      hash_len(&mut hasher, prep.height());
      for v in &prep.values {
        hasher.update(&v.as_canonical_u64().to_le_bytes());
      }
    }
  }
  *hasher.finalize().as_bytes()
}

/// Plan describing how the original `MultiStarkCircuit` traces map into the
/// merged layout (`Comp_0..Comp_{m-1}`, `B3_All`, `UnifiedTable`), including
/// optional FRI-arity height alignment padding.
#[derive(Clone, Debug)]
pub struct MergedLayout {
  num_main: usize,
  merged: bool,
  byte_table_index: usize,
  byte_table_rows: usize,
  b3_start_index: usize,
  b3_active_rows: [usize; 6],
  b3_height: usize,
  table_height: usize,
  /// Final padded height of each output circuit (after optional FRI-arity
  /// height alignment).
  aligned_heights: Vec<usize>,
  /// When true, all circuits (`Comp_0..Comp_{m-1}`, `B3_All`, `UnifiedTable`)
  /// are horizontally packed into ONE single circuit (`num_circuits == 1`) of
  /// height `packed_height`!
  packed_single: bool,
  packed_height: usize,
  packed_main_width: usize,
  packed_main_offsets: Vec<usize>,
}

/// Compute the smallest power-of-two height `>= height` whose `log2` is
/// congruent to `max_log (mod step)` (and `<= 1 << max_log`), avoiding forced
/// low-arity FRI folds on `max_log_arity = step`!
fn align_height_for_arity(height: usize, max_log: usize, step: usize) -> usize {
  let log_h = height.ilog2() as usize;
  if step <= 1 || log_h >= max_log {
    return height;
  }
  let diff = max_log - log_h;
  let rem = diff % step;
  if rem == 0 {
    return height;
  }
  // Round log_h UP by `rem` so `(max_log - aligned_log) % step == 0`.
  let aligned_log = (log_h + rem).min(max_log);
  1usize << aligned_log
}

impl MergedLayout {
  /// Inspect `definitions` (produced by `compiled.circuit_inputs()` after
  /// `merge_table_traces`) and, if it matches the standard compact-BLAKE3
  /// Plonkish layout, vertically merge `t0..t5` into `B3_All` and all 4 fixed
  /// tables into a 1-lookup `UnifiedTable`, then optionally align low-width
  /// auxiliary/tail trace heights to `max_log - k * align_arity`.
  pub fn try_merge(
    compiled: &MultiStarkCircuit<Val>,
    mut definitions: Vec<CircuitInputs<Val>>,
    namespace: u8,
    max_trace_height: usize,
    align_arity: usize,
    pack_single_circuit: bool,
  ) -> Result<(Vec<CircuitInputs<Val>>, Self), String> {
    let num_main = compiled.main_heights().len();
    let expected_total = num_main + 1 + 9;
    if definitions.len() != expected_total {
      let aligned_heights = definitions
        .iter()
        .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
        .collect();
      return Ok((
        definitions,
        Self {
          num_main,
          merged: false,
          byte_table_index: 0,
          byte_table_rows: 0,
          b3_start_index: 0,
          b3_active_rows: [0; 6],
          b3_height: 0,
          table_height: 0,
          aligned_heights,
          packed_single: false,
          packed_height: 0,
          packed_main_width: 0,
          packed_main_offsets: Vec::new(),
        },
      ));
    }

    let byte_idx = num_main;
    let b3_start = num_main + 1;

    // Validate exact shapes fail-closed before merging.
    let byte_prep = definitions[byte_idx]
      .preprocessed
      .as_ref()
      .ok_or("expected preprocessed matrix on merged ByteGadgets table")?;
    if definitions[byte_idx].main_width != 1 || byte_prep.width() != 4 {
      return Err(format!(
        "unexpected ByteGadgets table shape (main={}, prep={})",
        definitions[byte_idx].main_width,
        byte_prep.width()
      ));
    }
    let byte_table_rows = byte_prep.height();
    // Ensure ByteGadgets table IDs in p(0) are strictly disjoint from TID_B3_*.
    for r in 0..byte_table_rows {
      let tid = byte_prep.values[r * 4].as_canonical_u64();
      if tid >= TID_B3_XOR as u64 {
        return Err(format!(
          "ByteGadgets table_id {tid} collides with reserved BLAKE3 table IDs (>= {TID_B3_XOR})"
        ));
      }
    }

    for t in 0..6 {
      let def = &definitions[b3_start + t];
      let prep = def
        .preprocessed
        .as_ref()
        .ok_or("missing preprocessed matrix on BLAKE3 trace")?;
      if def.main_width != B3_MAIN_WIDTHS[t]
        || prep.width() != B3_PREP_WIDTHS[t]
      {
        return Err(format!(
          "unexpected BLAKE3 t{t} shape (main={}, prep={})",
          def.main_width,
          prep.width()
        ));
      }
    }
    for (ti, &(exp_h, exp_w)) in B3_TABLE_PREPS.iter().enumerate() {
      let def = &definitions[b3_start + 6 + ti];
      let prep = def
        .preprocessed
        .as_ref()
        .ok_or("missing preprocessed matrix on BLAKE3 table")?;
      if def.main_width != 1 || prep.height() != exp_h || prep.width() != exp_w
      {
        return Err(format!(
          "unexpected BLAKE3 table {ti} shape (main={}, h={}, w={})",
          def.main_width,
          prep.height(),
          prep.width()
        ));
      }
    }

    // The hand-written `B3_All` and `UnifiedTable` restate exactly the
    // lowering with this structure; refuse any other.
    let structure =
      compact_blake3_structure_digest(&definitions[b3_start..b3_start + 9]);
    if structure != COMPACT_BLAKE3_STRUCTURE_DIGEST {
      return Err(format!(
        "the lowered compact-BLAKE3 circuits (structure digest {}) are not the ones the merged B3_All/UnifiedTable circuits restate ({}); review circuit_merge.rs against multi-stark's BLAKE3 gadget",
        blake3::Hash::from_bytes(structure).to_hex(),
        blake3::Hash::from_bytes(COMPACT_BLAKE3_STRUCTURE_DIGEST).to_hex()
      ));
    }

    // Count contiguous active rows of each BLAKE3 sub-trace t0..t5.
    // Row 0 is ALWAYS kept (carries p(1) == 1 activation marker).
    let mut b3_active_rows = [0usize; 6];
    for t in 0..6 {
      let prep = definitions[b3_start + t].preprocessed.as_ref().unwrap();
      let h = prep.height();
      let w = prep.width();
      let mut last_nonzero = 0usize;
      for r in (0..h).rev() {
        let row = &prep.values[r * w..(r + 1) * w];
        if row.iter().any(|&v| v != Val::ZERO) {
          last_nonzero = r;
          break;
        }
      }
      b3_active_rows[t] = last_nonzero + 1;
    }

    let b3_used: usize = b3_active_rows.iter().sum();
    let b3_height = b3_used.max(2).next_power_of_two();
    let table_used = byte_table_rows + 65536 + 512 + 256;
    let raw_table_height = table_used.max(2).next_power_of_two();
    if b3_height > max_trace_height || raw_table_height > max_trace_height {
      let aligned_heights = definitions
        .iter()
        .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
        .collect();
      return Ok((
        definitions,
        Self {
          num_main,
          merged: false,
          byte_table_index: 0,
          byte_table_rows: 0,
          b3_start_index: 0,
          b3_active_rows: [0; 6],
          b3_height: 0,
          table_height: 0,
          aligned_heights,
          packed_single: false,
          packed_height: 0,
          packed_main_width: 0,
          packed_main_offsets: Vec::new(),
        },
      ));
    }

    // Compute max_log across computation shards + B3_All + UnifiedTable.
    let max_comp_h = definitions[..num_main]
      .iter()
      .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
      .max()
      .unwrap_or(0);
    let max_h = max_comp_h.max(b3_height).max(raw_table_height);
    let max_log = max_h.ilog2() as usize;

    // Align UnifiedTable height to `max_log - k * align_arity` (costs almost
    // zero prover work since main_width = 1, prep_width = 4, and eliminates
    // forced low-arity FRI rounds!).
    let table_height = if align_arity > 1 {
      align_height_for_arity(raw_table_height, max_log, align_arity)
        .min(max_trace_height)
    } else {
      raw_table_height
    };

    let b3_prep = build_b3_all_preprocessed(
      &definitions[b3_start..b3_start + 6],
      &b3_active_rows,
      b3_height,
    );
    let b3_def = build_b3_all_circuit(Val::from_u8(namespace), b3_prep);

    let table_prep = build_unified_table_preprocessed(
      definitions[byte_idx].preprocessed.as_ref().unwrap(),
      &definitions[b3_start + 6..b3_start + 9],
      table_height,
    )?;
    let table_def =
      build_unified_table_circuit(Val::from_u8(namespace), table_prep);

    // Keep computation shards 0..num_main, replace the 10 auxiliary circuits with [B3_All, UnifiedTable].
    definitions.truncate(num_main);
    definitions.push(b3_def);
    definitions.push(table_def);

    // Also align any small narrow computation tail shard (main_width <= 4) to
    // `max_log - k * align_arity` so EVERY trace aligns cleanly with FRI arity!
    // Padding a computation shard with all-zero rows is 100% sound: all
    // selectors (p(0..5), public_enable, table_enable, hash_enable) are 0,
    // and copy labels p(5..5+2w) are 0 (self-cancelling push/pull in LogUp).
    if align_arity > 1 {
      for def in &mut definitions[..num_main] {
        if let Some(prep) = def.preprocessed.as_mut() {
          let cur_h = prep.height();
          let target_h = align_height_for_arity(cur_h, max_log, align_arity)
            .min(max_trace_height);
          if target_h > cur_h && def.main_width <= 4 {
            let w = prep.width();
            prep.values.resize(target_h * w, Val::ZERO);
          }
        }
      }
    }

    let aligned_heights: Vec<usize> = definitions
      .iter()
      .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
      .collect();

    if pack_single_circuit && definitions.len() > 1 {
      let (packed_def, packed_height, packed_main_width, packed_main_offsets) =
        pack_circuits_horizontally(definitions)?;
      return Ok((
        vec![packed_def],
        Self {
          num_main,
          merged: true,
          byte_table_index: byte_idx,
          byte_table_rows,
          b3_start_index: b3_start,
          b3_active_rows,
          b3_height,
          table_height,
          aligned_heights,
          packed_single: true,
          packed_height,
          packed_main_width,
          packed_main_offsets,
        },
      ));
    }

    Ok((
      definitions,
      Self {
        num_main,
        merged: true,
        byte_table_index: byte_idx,
        byte_table_rows,
        b3_start_index: b3_start,
        b3_active_rows,
        b3_height,
        table_height,
        aligned_heights,
        packed_single: false,
        packed_height: 0,
        packed_main_width: 0,
        packed_main_offsets: Vec::new(),
      },
    ))
  }

  pub const fn is_merged(&self) -> bool {
    self.merged
  }

  pub const fn b3_height(&self) -> usize {
    self.b3_height
  }

  /// Build all stage-1 traces in merged circuit order, padding aligned traces
  /// with zero rows to match their aligned preprocessed heights.
  pub fn build_traces(
    &self,
    compiled: &MultiStarkCircuit<Val>,
    assignment: &Assignment<Val>,
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    let shards = compiled
      .trace_shards(assignment)
      .map_err(|e| format!("trace shards failed: {e}"))?;
    if !self.merged {
      return (0..compiled.num_circuits())
        .map(|i| shards.trace(i).map_err(|e| format!("trace {i}: {e}")))
        .collect();
    }

    let mut out = Vec::with_capacity(self.num_main + 2);
    for ci in 0..self.num_main {
      let mut tr =
        shards.trace(ci).map_err(|e| format!("comp trace {ci}: {e}"))?;
      let target_h = self.aligned_heights[ci];
      if target_h > tr.height() {
        let w = tr.width();
        tr.values.resize(target_h * w, Val::ZERO);
      }
      out.push(tr);
    }

    // Build B3_All main trace (height = b3_height, width = 40).
    let mut b3_vals = vec![Val::ZERO; self.b3_height * 40];
    let mut dst_row = 0usize;
    for (t, (&expected_w, &active)) in
      B3_MAIN_WIDTHS.iter().zip(self.b3_active_rows.iter()).enumerate()
    {
      let tr = shards
        .trace(self.b3_start_index + t)
        .map_err(|e| format!("b3 trace t{t}: {e}"))?;
      let src_w = tr.width();
      debug_assert_eq!(src_w, expected_w);
      for r in active..tr.height() {
        let row = &tr.values[r * src_w..(r + 1) * src_w];
        if row.iter().any(|&v| v != Val::ZERO) {
          return Err(format!(
            "b3 trace t{t} has nonzero witness value on inactive row {r}"
          ));
        }
      }
      for r in 0..active {
        let src = &tr.values[r * src_w..(r + 1) * src_w];
        let dst = &mut b3_vals[(dst_row + r) * 40..(dst_row + r + 1) * 40];
        match t {
          0..=3 => {
            dst[..src_w].copy_from_slice(src);
          },
          4 => {
            dst[12..16].copy_from_slice(&src[0..4]);
            dst[16..20].copy_from_slice(&src[4..8]);
            dst[20..24].copy_from_slice(&src[8..12]);
            dst[28..32].copy_from_slice(&src[8..12]);
          },
          5 => {
            dst[0..4].copy_from_slice(&src[0..4]);
          },
          _ => unreachable!(),
        }
      }
      dst_row += active;
    }
    out.push(RowMajorMatrix::new(b3_vals, 40));

    // Build UnifiedTable main trace (height = table_height, width = 1).
    // Padding rows beyond active table entries have multiplicity 0.
    let mut tbl_vals = vec![Val::ZERO; self.table_height];
    let mut offset = 0usize;
    let byte_tr = shards
      .trace(self.byte_table_index)
      .map_err(|e| format!("byte table trace: {e}"))?;
    debug_assert_eq!(byte_tr.height(), self.byte_table_rows);
    tbl_vals[offset..offset + self.byte_table_rows]
      .copy_from_slice(&byte_tr.values);
    offset += self.byte_table_rows;
    for (ti, &(exp_h, _)) in B3_TABLE_PREPS.iter().enumerate() {
      let tr = shards
        .trace(self.b3_start_index + 6 + ti)
        .map_err(|e| format!("b3 table {ti} trace: {e}"))?;
      debug_assert_eq!(tr.height(), exp_h);
      tbl_vals[offset..offset + exp_h].copy_from_slice(&tr.values);
      offset += exp_h;
    }
    out.push(RowMajorMatrix::new_col(tbl_vals));

    if self.packed_single {
      let mut packed =
        vec![Val::ZERO; self.packed_height * self.packed_main_width];
      for (tr, &col_offset) in out.iter().zip(&self.packed_main_offsets) {
        let h = tr.height();
        let w = tr.width();
        debug_assert!(h <= self.packed_height);
        for r in 0..h {
          let src = &tr.values[r * w..(r + 1) * w];
          let dst = &mut packed[r * self.packed_main_width + col_offset
            ..r * self.packed_main_width + col_offset + w];
          dst.copy_from_slice(src);
        }
      }
      return Ok(vec![RowMajorMatrix::new(packed, self.packed_main_width)]);
    }

    Ok(out)
  }
}

fn remap_expr(
  expr: &Expr<Val>,
  main_offset: usize,
  prep_offset: usize,
) -> Result<Expr<Val>, String> {
  match expr {
    Expr::Const(v) => Ok(Expr::Const(*v)),
    Expr::Var(ColRef { source, offset, index }) => {
      if *offset != RowOffset::Current {
        return Err(
          "horizontal packing requires purely row-local constraints (RowOffset::Current)".into(),
        );
      }
      let new_idx = match source {
        Source::Main => (*index as usize)
          .checked_add(main_offset)
          .and_then(|v| u32::try_from(v).ok())
          .ok_or("packed main column index overflow")?,
        Source::Preprocessed => (*index as usize)
          .checked_add(prep_offset)
          .and_then(|v| u32::try_from(v).ok())
          .ok_or("packed preprocessed column index overflow")?,
        Source::Stage2 => {
          return Err(
            "horizontal packing does not support Stage2 references in user constraints".into(),
          );
        },
      };
      Ok(Expr::Var(ColRef {
        source: *source,
        offset: RowOffset::Current,
        index: new_idx,
      }))
    },
    Expr::Add(a, b) => Ok(Expr::Add(
      Box::new(remap_expr(a, main_offset, prep_offset)?),
      Box::new(remap_expr(b, main_offset, prep_offset)?),
    )),
    Expr::Sub(a, b) => Ok(Expr::Sub(
      Box::new(remap_expr(a, main_offset, prep_offset)?),
      Box::new(remap_expr(b, main_offset, prep_offset)?),
    )),
    Expr::Mul(a, b) => Ok(Expr::Mul(
      Box::new(remap_expr(a, main_offset, prep_offset)?),
      Box::new(remap_expr(b, main_offset, prep_offset)?),
    )),
    Expr::Neg(a) => {
      Ok(Expr::Neg(Box::new(remap_expr(a, main_offset, prep_offset)?)))
    },
    Expr::Public(_)
    | Expr::IsFirstRow
    | Expr::IsLastRow
    | Expr::IsTransition => Err(
      "horizontal packing does not support boundary/public expressions".into(),
    ),
  }
}

/// Horizontally pack multiple purely row-local circuits into ONE single circuit
/// of height `H = max_k h_k` (`num_circuits == 1`, single quotient polynomial,
/// zero `acc_mask` in `v6-zk`, single height group, single leaf salt per batch!).
fn pack_circuits_horizontally(
  defs: Vec<CircuitInputs<Val>>,
) -> Result<(CircuitInputs<Val>, usize, usize, Vec<usize>), String> {
  let packed_height = defs
    .iter()
    .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
    .max()
    .unwrap_or(0);
  if packed_height == 0 || !packed_height.is_power_of_two() {
    return Err(
      "horizontal packing requires non-empty power-of-two preprocessed heights"
        .into(),
    );
  }

  let mut main_offsets = Vec::with_capacity(defs.len());
  let mut prep_offsets = Vec::with_capacity(defs.len());
  let mut total_main_w = 0usize;
  let mut total_prep_w = 0usize;
  for d in &defs {
    if !d.ext_constraints.is_empty() {
      return Err("horizontal packing does not support ext_constraints".into());
    }
    let prep = d.preprocessed.as_ref().ok_or(
      "horizontal packing requires preprocessed matrices on every sub-circuit",
    )?;
    main_offsets.push(total_main_w);
    prep_offsets.push(total_prep_w);
    total_main_w += d.main_width;
    total_prep_w += prep.width();
  }

  let mut packed_prep = vec![Val::ZERO; packed_height * total_prep_w];
  let mut packed_constraints = Vec::new();
  let mut packed_lookups = Vec::new();

  for (idx, d) in defs.into_iter().enumerate() {
    let m_off = main_offsets[idx];
    let p_off = prep_offsets[idx];
    let prep = d.preprocessed.unwrap();
    let h = prep.height();
    let w = prep.width();
    for r in 0..h {
      let src = &prep.values[r * w..(r + 1) * w];
      let dst = &mut packed_prep
        [r * total_prep_w + p_off..r * total_prep_w + p_off + w];
      dst.copy_from_slice(src);
    }
    // Note: for UnifiedTable (the last circuit, main_width == 1), pad rows
    // h..packed_height by repeating genuine row 0 (multiplicity is 0 on those
    // rows, and repeating row 0 never introduces an invalid table entry!).
    // For Comp and B3_All, all-zero rows keep every selector and multiplicity 0.
    if d.main_width == 1 && h < packed_height && w > 0 {
      let row0 = &prep.values[..w];
      for r in h..packed_height {
        let dst = &mut packed_prep
          [r * total_prep_w + p_off..r * total_prep_w + p_off + w];
        dst.copy_from_slice(row0);
      }
    }

    for c in &d.constraints {
      packed_constraints.push(remap_expr(c, m_off, p_off)?);
    }
    for l in &d.lookups {
      let mult = remap_expr(&l.multiplicity, m_off, p_off)?;
      let args = l
        .args
        .iter()
        .map(|a| remap_expr(a, m_off, p_off))
        .collect::<Result<Vec<_>, _>>()?;
      packed_lookups.push(Lookup { multiplicity: mult, args });
    }
  }

  let def = CircuitInputs {
    main_width: total_main_w,
    preprocessed: Some(RowMajorMatrix::new(packed_prep, total_prep_w)),
    constraints: packed_constraints,
    lookups: packed_lookups,
    lookup_group_size: 3,
    ..Default::default()
  };
  Ok((def, packed_height, total_main_w, main_offsets))
}

fn build_b3_all_preprocessed(
  b3_defs: &[CircuitInputs<Val>],
  active_rows: &[usize; 6],
  b3_height: usize,
) -> RowMajorMatrix<Val> {
  const W: usize = 24;
  let mut vals = vec![Val::ZERO; b3_height * W];
  let mut dst_row = 0usize;
  for t in 0..6 {
    let prep = b3_defs[t].preprocessed.as_ref().unwrap();
    let sw = prep.width();
    let active = active_rows[t];
    for r in 0..active {
      let src = &prep.values[r * sw..(r + 1) * sw];
      let dst = &mut vals[(dst_row + r) * W..(dst_row + r + 1) * W];
      dst[1] = src[1];
      if src[1] != Val::ZERO {
        dst[0] = Val::from_usize(t);
      }
      dst[14 + t] = src[0];
      match t {
        0..=3 => {
          dst[2..8].copy_from_slice(&src[2..8]);
          dst[8..14].copy_from_slice(&src[8..14]);
        },
        4 => {
          dst[5..8].copy_from_slice(&src[2..5]);
          dst[11..14].copy_from_slice(&src[5..8]);
        },
        5 => {
          dst[2] = src[2];
          dst[8] = src[3];
          dst[3..7].copy_from_slice(&src[4..8]);
          dst[9..13].copy_from_slice(&src[8..12]);
          dst[20..24].copy_from_slice(&src[12..16]);
          dst[7] = src[16];
          dst[13] = src[17];
        },
        _ => unreachable!(),
      }
    }
    dst_row += active;
  }
  RowMajorMatrix::new(vals, W)
}

fn build_b3_all_circuit(
  namespace: Val,
  preprocessed: RowMajorMatrix<Val>,
) -> CircuitInputs<Val> {
  let c = |x: usize| Expr::constant(Val::from_usize(x));
  let m = |x: usize| Expr::main(u32::try_from(x).expect("main col"));
  let p = |x: usize| Expr::preprocessed(u32::try_from(x).expect("prep col"));
  let ns = Expr::constant(namespace);

  let sel_t0 = p(14);
  let sel_t1 = p(15);
  let sel_t2 = p(16);
  let sel_t3 = p(17);
  let sel_t4 = p(18);
  let sel_t5 = p(19);

  let sel_add =
    sel_t0.clone() + sel_t1.clone() + sel_t2.clone() + sel_t3.clone();
  let en_0_4 = sel_add.clone() + sel_t4.clone();
  let en_copy0 = sel_add.clone() + sel_t5.clone();
  let en_split = sel_t1.clone() + sel_t3.clone();
  // Degree-1 table ID selector: 11 on t1 (bits=4), 12 on t3 (bits=7).
  let split_tid =
    c(TID_B3_SPLIT4) * sel_t1.clone() + c(TID_B3_SPLIT7) * sel_t3.clone();

  let mut constraints = Vec::with_capacity(16);
  for i in 0..4 {
    let carry = m(24 + i);
    constraints.push(carry.clone() * (carry.clone() - c(1)) * (carry - c(2)));
  }
  for i in 0..4 {
    let prev_carry = if i == 0 { c(0) } else { m(23 + i) };
    let eq =
      m(i) + m(4 + i) + m(8 + i) + prev_carry - m(16 + i) - c(256) * m(24 + i);
    constraints.push(sel_add.clone() * eq);
  }
  for i in 0..4 {
    let eq0 = m(20 + i) - m(28 + (i + 2) % 4);
    let eq1 = m(20 + i) - m(36 + (i + 1) % 4) - c(16) * m(32 + (i + 2) % 4);
    let eq2 = m(20 + i) - m(28 + (i + 1) % 4);
    let eq3 = m(20 + i) - m(36 + i) - c(2) * m(32 + (i + 1) % 4);
    let eq4 = m(20 + i) - m(28 + i);
    constraints.push(
      sel_t0.clone() * eq0
        + sel_t1.clone() * eq1
        + sel_t2.clone() * eq2
        + sel_t3.clone() * eq3
        + sel_t4.clone() * eq4,
    );
  }
  for i in 0..4 {
    constraints.push(sel_t5.clone() * p(3 + i) * (m(i) - p(9 + i)));
  }

  let mut lookups = Vec::with_capacity(29);
  lookups.push(Lookup::pull(p(1), vec![ns.clone(), c(4), c(3), p(0)]));

  let copy_args = |slot: usize, label_col: usize| {
    let mut a = vec![ns.clone(), c(4), c(0), p(label_col)];
    a.extend((0..4).map(|i| m(slot * 4 + i)));
    a
  };
  lookups.push(Lookup::push(en_copy0.clone(), copy_args(0, 2)));
  lookups.push(Lookup::pull(en_copy0, copy_args(0, 8)));
  for slot in 1..3 {
    lookups.push(Lookup::push(sel_add.clone(), copy_args(slot, 2 + slot)));
    lookups.push(Lookup::pull(sel_add.clone(), copy_args(slot, 8 + slot)));
  }
  for slot in 3..6 {
    lookups.push(Lookup::push(en_0_4.clone(), copy_args(slot, 2 + slot)));
    lookups.push(Lookup::pull(en_0_4.clone(), copy_args(slot, 8 + slot)));
  }

  // Unified 6-argument table channel `(ns, 2, table_id, col0, col1, col2)`:
  // 1. B3 XOR table queries (TID_B3_XOR = 10).
  for i in 0..4 {
    lookups.push(Lookup::pull(
      en_0_4.clone(),
      vec![ns.clone(), c(2), c(TID_B3_XOR), m(12 + i), m(16 + i), m(28 + i)],
    ));
  }
  // 2. B3 Split table queries (TID_B3_SPLIT4 = 11 on t1, TID_B3_SPLIT7 = 12 on t3).
  for i in 0..4 {
    lookups.push(Lookup::pull(
      en_split.clone(),
      vec![
        ns.clone(),
        c(2),
        split_tid.clone(),
        m(28 + i),
        m(32 + i),
        m(36 + i),
      ],
    ));
  }
  // 3. B3 Byte range queries (TID_B3_BYTE = 13 on t5).
  for i in 0..4 {
    lookups.push(Lookup::pull(
      sel_t5.clone(),
      vec![ns.clone(), c(2), c(TID_B3_BYTE), m(i), c(0), c(0)],
    ));
  }
  // 4. Bridge queries (t5 -> generic Plonkish computation trace).
  for i in 0..4 {
    lookups.push(Lookup::pull(
      p(20 + i),
      vec![ns.clone(), c(4), c(4), p(7), p(13) + c(i), m(i)],
    ));
  }

  CircuitInputs {
    main_width: 40,
    preprocessed: Some(preprocessed),
    constraints,
    lookups,
    lookup_group_size: 3,
    ..Default::default()
  }
}

fn build_unified_table_preprocessed(
  byte_prep: &RowMajorMatrix<Val>,
  b3_table_defs: &[CircuitInputs<Val>],
  table_height: usize,
) -> Result<RowMajorMatrix<Val>, String> {
  const W: usize = 4;
  let mut vals = vec![Val::ZERO; table_height * W];
  let mut offset = 0usize;

  // Sub-table 0: merged ByteGadgets table (already [tid, c0, c1, c2]).
  for r in 0..byte_prep.height() {
    let src = &byte_prep.values[r * 4..(r + 1) * 4];
    let dst = &mut vals[(offset + r) * W..(offset + r + 1) * W];
    dst.copy_from_slice(src);
  }
  offset += byte_prep.height();

  // Sub-table 1: B3 xor ([a, b, a^b]) -> [TID_B3_XOR, a, b, a^b].
  let xor_prep = b3_table_defs[0].preprocessed.as_ref().unwrap();
  for r in 0..xor_prep.height() {
    let src = &xor_prep.values[r * 3..(r + 1) * 3];
    let dst = &mut vals[(offset + r) * W..(offset + r + 1) * W];
    dst[0] = Val::from_usize(TID_B3_XOR);
    dst[1..4].copy_from_slice(src);
  }
  offset += xor_prep.height();

  // Sub-table 2: B3 split ([bits, x, lo, hi]) -> [TID_B3_SPLIT4/7, x, lo, hi].
  let split_prep = b3_table_defs[1].preprocessed.as_ref().unwrap();
  for r in 0..split_prep.height() {
    let src = &split_prep.values[r * 4..(r + 1) * 4];
    let tid = match src[0].as_canonical_u64() {
      4 => TID_B3_SPLIT4,
      7 => TID_B3_SPLIT7,
      other => {
        return Err(format!("unexpected BLAKE3 split bit width {other}"));
      },
    };
    let dst = &mut vals[(offset + r) * W..(offset + r + 1) * W];
    dst[0] = Val::from_usize(tid);
    dst[1..4].copy_from_slice(&src[1..4]);
  }
  offset += split_prep.height();

  // Sub-table 3: B3 byte ([b]) -> [TID_B3_BYTE, b, 0, 0].
  let byte_b3_prep = b3_table_defs[2].preprocessed.as_ref().unwrap();
  for r in 0..byte_b3_prep.height() {
    let b = byte_b3_prep.values[r];
    let dst = &mut vals[(offset + r) * W..(offset + r + 1) * W];
    dst[0] = Val::from_usize(TID_B3_BYTE);
    dst[1] = b;
  }
  offset += byte_b3_prep.height();

  // Padding rows repeat genuine row 0 (never introducing an invalid entry!).
  let row0 = [vals[0], vals[1], vals[2], vals[3]];
  for r in offset..table_height {
    vals[r * W..(r + 1) * W].copy_from_slice(&row0);
  }

  Ok(RowMajorMatrix::new(vals, W))
}

fn build_unified_table_circuit(
  namespace: Val,
  preprocessed: RowMajorMatrix<Val>,
) -> CircuitInputs<Val> {
  let c = |x: usize| Expr::constant(Val::from_usize(x));
  let m0 = Expr::main(0);
  let p = |x: usize| Expr::preprocessed(u32::try_from(x).expect("prep col"));
  let ns = Expr::constant(namespace);

  // Single 6-argument table lookup serving BOTH ByteGadgets AND all 3 BLAKE3 tables!
  CircuitInputs {
    main_width: 1,
    preprocessed: Some(preprocessed),
    constraints: vec![],
    lookups: vec![Lookup::push(m0, vec![ns, c(2), p(0), p(1), p(2), p(3)])],
    lookup_group_size: 1,
    ..Default::default()
  }
}
