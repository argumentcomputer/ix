//! The v2 layout through the verified Lean pass (`Aiur.Tiling.Periodic`).
//!
//! The exporter (`tiling_export2`) reads [`input2`] and writes the layout
//! `Periodic.narrow_heap_sound_compact` is about, together with every circuit
//! the stage proves. [`Layout::export`] runs it and streams the fixed matrix
//! from its standard output into memory (the matrix is never written to
//! disk); [`Layout::load`] reads a layout from files. [`Backend::from_lean`]
//! lowers the exported function circuits, validates the layout against that
//! lowering and makes the exported fixed matrix and circuits the stage's.
//! Witness generation stays in [`Backend`].
//!
//! **Input** (`ix-tiling-v2-input-2`): the compiled artifact (`artifact`,
//! absolute, and `artifact_blake3`), `width`, `shards`, `circuits` (layout
//! order, the entry's first: `chip` name, `cap` instances per shard,
//! `"unroll": true` and its stage count `"stages"` on `Blake3::compress`), `rom` (`[width, capacity]` per
//! memory width) and `entry`. The exporter decodes the artifact and lowers
//! its chips (`IChip.lower`), and takes the map claims and the request from
//! it; Rust supplies no circuit.
//!
//! **Output** (`ix-tiling-v2-layout-1`, plus a fixed matrix in the
//! `IXTLFX01` format of `TilingExport.lean`):
//!
//! - `width`, `shards`, `caps`, `fixed_width`, `places` (rows of one chip
//!   layout), `labels_per_shard` (`labelOffset 1`), `ids_per_shard`
//!   (`idOffset 1`);
//! - `templates`: per circuit, `Export2.template` with *all* slots: the
//!   prototype's, then `{"invocation": true}` if the receive is chunked,
//!   then the virtual multiplicity slots, and `virtual`, their indices;
//! - `buses`: `[tag, sub, code, lane]` per channel;
//! - `request`: the request's tuples (`padded2`);
//! - `tables` (stacked) or `compact` (compact table descriptors, with the
//!   tables' fixed matrices in `tables.bin`);
//! - `circuits`: per laid-out circuit, `Bridge.lower` of its chip as a
//!   [`Graph`]; `narrow_circuits`: the shard circuits `S.circuit k`;
//!   `compact_circuits`: `Compact.circuit W` of the map and ROM tables;
//! - the fixed file: `Sharded.fixedAt` of the chip layout, rows `0..places`.
//!
//! Validation ([`Backend::adopt_lean`]): every template must equal this
//! crate's lowering of the exported graph of the same circuit (prototype
//! slots and physical rows), its logical slots must be the invocation and
//! virtual slots the numbering implies, every bus code must be
//! `tag + 4·sub`, the label and id strides must match, the table descriptors
//! must have the compact shape, and the request must be the claim tuples up
//! to trailing zeros. The shard and table circuits proved are the exported
//! graphs read literally ([`Graph::circuit_inputs`]); this crate's own
//! `narrow_circuit`, `compact_circuit` and `compile_graph` lowering are only
//! compared with them on request ([`Backend::rust_cross_check`]).

use super::super::{decimal, parse_scalar, parse_scalar_for, usize_of};
use super::{
  Backend, Config, LaneUse, Placement, Row, SlotDef, Stacked, Target, Template,
  Term, ts,
};
use crate::aiur_backend::{AiurCurve, Bn254, kzg::Compiler};
use crate::kzg::{CurveScalar, KzgConfig, Scalar, curve::Bn254 as Bn254Curve};
use aiur::trace::TracePlan;
use multi_stark::{
  expr::{ColRef, Expr, RowOffset, Source},
  graph::{ConstraintGraph, Node, NodeId},
  lookup::Lookup,
  system::{CircuitInputs, extension_params},
  traits::{Algebra, Field, PrimeField},
};
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use serde_json::{Value, json};
use std::{
  io::Read,
  path::Path,
  process::{Command, Stdio},
  time::Instant,
};

/// An exported v2 layout, not yet validated.
pub struct Layout {
  pub out: Value,
  pub fixed_rows: usize,
  pub fixed_width: usize,
  pub fixed: Vec<Scalar>,
  /// The compact tables' fixed matrices (`tables.bin`), map table first, as
  /// `(rows, width, values)`; empty for a stacked-table export.
  pub tables: Vec<(usize, usize, Vec<Scalar>)>,
}

impl Layout {
  pub fn load(output: &Path, fixed: &Path) -> Result<Self, String> {
    let file = std::fs::File::open(fixed)
      .map_err(|e| format!("{}: {e}", fixed.display()))?;
    let (fixed_rows, fixed_width, fixed) = read_fixed(file, None)?;
    Self::with_fixed(output, fixed_rows, fixed_width, fixed, None)
  }

  /// A stored export: the layout `output`, the fixed matrix `fixed` (read
  /// with `height` rows reserved, as [`Self::export`] does) and, when given,
  /// the compact tables.
  pub fn load_export(
    output: &Path,
    fixed: &Path,
    tables: Option<&Path>,
    height: usize,
  ) -> Result<Self, String> {
    let file = std::fs::File::open(fixed)
      .map_err(|e| format!("{}: {e}", fixed.display()))?;
    let (fixed_rows, fixed_width, fixed) = read_fixed(file, Some(height))?;
    Self::with_fixed(output, fixed_rows, fixed_width, fixed, tables)
  }

  /// Runs `exporter input output /dev/stdout` (stderr to `log`) and reads
  /// the fixed matrix from its standard output while it runs, reserving
  /// `height` rows so that padding to the trace height does not reallocate.
  /// Returns the layout and the seconds until the exporter finished.
  /// With `tables`, the exporter also writes the compact tables there
  /// (`narrow_heap_sound_compact`), which the layout then carries.
  pub fn export(
    exporter: &Path,
    input: &Path,
    output: &Path,
    log: &Path,
    height: usize,
    tables: Option<&Path>,
  ) -> Result<(Self, f64), String> {
    let started = Instant::now();
    let log_file = std::fs::File::create(log)
      .map_err(|e| format!("{}: {e}", log.display()))?;
    let mut command = Command::new(exporter);
    command.arg(input).arg(output).arg("/dev/stdout");
    if let Some(path) = tables {
      command.arg(path);
    }
    let mut child = command
      .stdout(Stdio::piped())
      .stderr(log_file)
      .spawn()
      .map_err(|e| format!("{}: {e}", exporter.display()))?;
    let stdout = child.stdout.take().ok_or("exporter without stdout")?;
    let read = read_fixed(stdout, Some(height));
    if read.is_err() {
      let _ = child.kill();
    }
    let status = child.wait().map_err(|e| e.to_string())?;
    let seconds = started.elapsed().as_secs_f64();
    if !status.success() {
      return Err(format!(
        "{} failed ({status}); see {}",
        exporter.display(),
        log.display()
      ));
    }
    let (fixed_rows, fixed_width, fixed) = read?;
    Ok((
      Self::with_fixed(output, fixed_rows, fixed_width, fixed, tables)?,
      seconds,
    ))
  }

  fn with_fixed(
    output: &Path,
    fixed_rows: usize,
    fixed_width: usize,
    fixed: Vec<Scalar>,
    tables: Option<&Path>,
  ) -> Result<Self, String> {
    let tables = match tables {
      Some(path) => {
        let bytes = std::fs::read(path)
          .map_err(|e| format!("{}: {e}", path.display()))?;
        let mut rest = &bytes[..];
        let mut blocks = vec![];
        while !rest.is_empty() {
          let (block, used) = read_block(rest)?;
          blocks.push(block);
          rest = &rest[used..];
        }
        blocks
      },
      None => vec![],
    };
    let out: Value = serde_json::from_slice(
      &std::fs::read(output)
        .map_err(|e| format!("{}: {e}", output.display()))?,
    )
    .map_err(|e| e.to_string())?;
    if out["format"] != "ix-tiling-v2-layout-1" {
      return Err("not a v2 tiling layout".into());
    }
    Ok(Self { out, fixed_rows, fixed_width, fixed, tables })
  }
}

/// One `IXTLFX01` block at the start of `bytes`, and the bytes it used,
/// decoded into curve `C`'s scalar field.
pub(crate) fn read_block_for<C: AiurCurve>(
  bytes: &[u8],
) -> Result<((usize, usize, Vec<CurveScalar<C>>), usize), String> {
  use ark_ff::{BigInt, PrimeField};
  if bytes.len() < 24 || &bytes[..8] != b"IXTLFX01" {
    return Err("not a tiling fixed matrix block".into());
  }
  let word = |i: usize| {
    usize::try_from(u64::from_le_bytes(
      bytes[i..i + 8].try_into().expect("eight bytes"),
    ))
    .map_err(|e| format!("fixed matrix dimension: {e}"))
  };
  let (rows, width) = (word(8)?, word(16)?);
  let mut values = Vec::with_capacity(rows * width);
  let mut p = 24;
  for _ in 0..rows * width {
    let len = *bytes.get(p).ok_or("truncated fixed matrix block")? as usize;
    if len > 32 || p + 1 + len > bytes.len() {
      return Err("bad fixed matrix entry".into());
    }
    let mut limbs = [0u64; 4];
    for (i, b) in bytes[p + 1..p + 1 + len].iter().enumerate() {
      limbs[i / 8] |= u64::from(*b) << (8 * (i % 8));
    }
    values.push(CurveScalar::<C>::new(
      C::Fr::from_bigint(BigInt(limbs))
        .ok_or("fixed entry is not below the modulus")?,
    ));
    p += 1 + len;
  }
  Ok(((rows, width, values), p))
}

/// One `IXTLFX01` block at the start of `bytes`, and the bytes it used.
pub(crate) fn read_block(
  bytes: &[u8],
) -> Result<((usize, usize, Vec<Scalar>), usize), String> {
  read_block_for::<Bn254Curve>(bytes)
}

/// Decodes an `IXTLFX01` matrix (`rows`, `width` as u64, then every entry as
/// a length byte and that many little-endian bytes) from a stream. Blocks are
/// split at row boundaries sequentially and decoded in parallel.
fn read_fixed(
  mut r: impl Read,
  height: Option<usize>,
) -> Result<(usize, usize, Vec<Scalar>), String> {
  use ark_ff::{BigInt, PrimeField};
  let mut header = [0u8; 24];
  r.read_exact(&mut header).map_err(|e| format!("fixed matrix header: {e}"))?;
  if &header[..8] != b"IXTLFX01" {
    return Err("not a tiling fixed matrix".into());
  }
  let word = |i: usize| {
    usize::try_from(u64::from_le_bytes(
      header[i..i + 8].try_into().expect("eight bytes"),
    ))
    .map_err(|e| format!("fixed matrix dimension: {e}"))
  };
  let (rows, width) = (word(8)?, word(16)?);
  if width == 0 {
    return Err("fixed matrix without columns".into());
  }
  let mut values: Vec<Scalar> =
    Vec::with_capacity(height.unwrap_or(rows).max(rows) * width);
  let mut pending: Vec<u8> = vec![];
  let mut block = vec![0u8; 64 << 20];
  let mut done = 0;
  loop {
    let mut n = 0;
    while n < block.len() {
      match r.read(&mut block[n..]) {
        Ok(0) => break,
        Ok(k) => n += k,
        Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {},
        Err(e) => return Err(format!("fixed matrix: {e}")),
      }
    }
    pending.extend_from_slice(&block[..n]);
    let mut starts = vec![];
    let mut at = 0;
    'rows: while done + starts.len() < rows {
      let mut p = at;
      for _ in 0..width {
        let Some(&len) = pending.get(p) else { break 'rows };
        if len > 32 {
          return Err("fixed entry wider than a field element".into());
        }
        p += 1 + len as usize;
        if p > pending.len() {
          break 'rows;
        }
      }
      starts.push(at);
      at = p;
    }
    values.resize((done + starts.len()) * width, Scalar::ZERO);
    let bytes = &pending;
    values[done * width..]
      .par_chunks_mut(width)
      .zip(starts.par_iter())
      .try_for_each(|(out, &start)| {
        let mut p = start;
        for x in out.iter_mut() {
          let len = bytes[p] as usize;
          let mut limbs = [0u64; 4];
          for (i, b) in bytes[p + 1..p + 1 + len].iter().enumerate() {
            limbs[i / 8] |= u64::from(*b) << (8 * (i % 8));
          }
          *x = Scalar::new(
            ark_bn254::Fr::from_bigint(BigInt(limbs))
              .ok_or("fixed entry is not below the modulus")?,
          );
          p += 1 + len;
        }
        Ok::<(), String>(())
      })?;
    done += starts.len();
    pending.drain(..at);
    if n == 0 {
      break;
    }
  }
  if done != rows || !pending.is_empty() {
    return Err(format!(
      "fixed matrix has {done} complete rows of {rows} and {} trailing bytes",
      pending.len()
    ));
  }
  Ok((rows, width, values))
}

/// A template in the JSON format of `Export2.template`, prototype slots only.
pub fn template_json(t: &Template, wide: usize) -> Value {
  let term = |t: &Term| match *t {
    Term::Linear(c, s) => json!(["lin", decimal(c), s]),
    Term::Product(c, a, b) => json!(["prod", decimal(c), a, b]),
  };
  let slots: Vec<Value> = t
    .slots
    .iter()
    .map(|s| match s {
      SlotDef::Column { body, col } => json!({"column": body * wide + col}),
      SlotDef::Sum(terms, k) => json!({"sum": {"terms": terms.iter().map(term).collect::<Vec<_>>(), "k": decimal(*k)}}),
      SlotDef::Key(m) => json!({"key": m}),
    })
    .collect();
  let rows: Vec<Value> = t
    .rows
    .iter()
    .map(|r| match r {
      Row::Gate { lanes, spans } => json!({"gate": {
        "lanes": lanes.iter().map(|l| match l {
          LaneUse::Empty => json!("empty"),
          LaneUse::Gate { qm, q, qc, cells } => json!({"gate": {"qm": decimal(*qm),
            "q": q.iter().map(|&x| decimal(x)).collect::<Vec<_>>(), "qc": decimal(*qc), "cells": cells.to_vec()}}),
          LaneUse::Message { ts, mk, mc, cells } => json!({"msg": {"ts": decimal(*ts), "mk": decimal(*mk),
            "mc": decimal(*mc), "cells": cells.to_vec()}}),
        }).collect::<Vec<_>>(),
        "spans": spans.iter().map(|&(s, n)| json!([s, n])).collect::<Vec<_>>()}}),
      Row::Message { ts, mk, mc, receive_key, cells } => json!({"message": {"ts": decimal(*ts), "mk": decimal(*mk),
        "mc": decimal(*mc), "key": receive_key, "cells": cells}}),
    })
    .collect();
  json!({"slots": slots, "rows": rows})
}

/// Writes `values` (`rows × width`, row-major) in the `IXTLFX01` format.
pub fn write_fixed(
  path: &Path,
  rows: usize,
  width: usize,
  values: &[Scalar],
) -> Result<(), String> {
  let mut out = b"IXTLFX01".to_vec();
  out.extend_from_slice(&(rows as u64).to_le_bytes());
  out.extend_from_slice(&(width as u64).to_le_bytes());
  for x in &values[..rows * width] {
    let bytes: Vec<u8> =
      x.canonical_limbs_le().iter().flat_map(|l| l.to_le_bytes()).collect();
    let n = bytes.iter().rposition(|&b| b != 0).map_or(0, |i| i + 1);
    out.push(u8::try_from(n).expect("a scalar has at most 32 bytes"));
    out.extend_from_slice(&bytes[..n]);
  }
  std::fs::write(path, out).map_err(|e| format!("{}: {e}", path.display()))
}

/// The slots the verified layout appends to the prototype's: the invocation
/// slot, then one virtual slot `mk + mc·x` (or `mk`) per message with a
/// virtual multiplicity, in message order.
pub fn logical_extra(t: &Template) -> Vec<Value> {
  let mut out = vec![];
  if t
    .messages
    .iter()
    .any(|m| m.target == Target::Receive && m.placement == Placement::Chunked)
  {
    out.push(json!({"invocation": true}));
  }
  for m in t.messages.iter().filter(|m| m.is_virtual()) {
    let terms: Vec<Value> =
      m.mult.map(|x| json!(["lin", decimal(m.mc), x])).into_iter().collect();
    out.push(json!({"sum": {"terms": terms, "k": decimal(m.mk)}}));
  }
  out
}

/// A stacked table's descriptor in the exporter's format (`tableJson`).
pub fn table_json(t: &Stacked) -> Value {
  json!({
    "tag": decimal(Scalar::from_u64(t.tag)),
    "sub": decimal(Scalar::from_u64(t.sub)),
    "rows": t.rows,
    "key_base": t.key_base,
    "main_width": t.main_width,
    "slices": t.slices,
  })
}

fn naturals(v: &Value, key: &str) -> Result<Vec<usize>, String> {
  v[key]
    .as_array()
    .ok_or(format!("layout without {key}"))?
    .iter()
    .map(usize_of)
    .collect()
}

/// `u` without trailing zeros.
fn trimmed(u: &[Scalar]) -> &[Scalar] {
  let n = u.iter().rposition(|x| *x != Scalar::ZERO).map_or(0, |i| i + 1);
  &u[..n]
}

/// `input` in the exporter's graph format (`graphJson`), through
/// `compile_graph`: fixed column `j` is variable `main_width + j`.
fn circuit_json(input: &CircuitInputs<Scalar>) -> Result<Value, String> {
  let g = input
    .compile_graph(&extension_params::<KzgConfig>())
    .map_err(|e| format!("{e:?}"))?;
  let w = input.main_width;
  let nodes = g
    .nodes
    .iter()
    .map(|n| {
      Ok(match *n {
        Node::Const(k) => json!(["const", decimal(k)]),
        Node::Var(c)
          if c.offset == RowOffset::Current && c.source == Source::Main =>
        {
          json!(["var", c.index])
        },
        Node::Var(c)
          if c.offset == RowOffset::Current
            && c.source == Source::Preprocessed =>
        {
          json!(["var", w + c.index as usize])
        },
        Node::Add(x, y) => json!(["add", x.0, y.0]),
        Node::Sub(x, y) => json!(["sub", x.0, y.0]),
        Node::Mul(x, y) => json!(["mul", x.0, y.0]),
        Node::Neg(x) => json!(["neg", x.0]),
        _ => {
          return Err(
            "circuit reads a next row, a selector or a public".to_owned(),
          );
        },
      })
    })
    .collect::<Result<Vec<_>, String>>()?;
  Ok(json!({
    "width": w,
    "fixed_width": input.preprocessed.as_ref().map_or(0, |m| m.width),
    "nodes": nodes,
    "zeros": g.zeros.iter().map(|z| z.0).collect::<Vec<_>>(),
    "lookups": g.lookups.iter().map(|l| json!([l.multiplicity.0, l.args.iter().map(|a| a.0).collect::<Vec<_>>()])).collect::<Vec<_>>(),
  }))
}

impl Backend<'_, '_, '_> {
  /// The layout the exporter produces for this configuration, derived from
  /// this backend's lowering, numbering and shard circuits: a round-trip
  /// check of [`Self::adopt_lean`] in the backend's tests.
  pub fn lean_reference(&self) -> Result<Layout, String> {
    let c = self.cols();
    let w = self.config.width;
    let mut templates = vec![];
    for &f in &self.order {
      let t = &self.templates[f];
      let mut v = template_json(t, self.compiler.inputs()[f].main_width);
      let extra = logical_extra(t);
      let first_virtual = t.slots.len()
        + usize::from(
          extra.first().is_some_and(|s| s.get("invocation").is_some()),
        );
      v["slots"].as_array_mut().expect("slots").extend(extra);
      v["virtual"] =
        json!((first_virtual..t.logical_slots).collect::<Vec<_>>());
      templates.push(v);
    }
    let buses = self.buses();
    let buses: Vec<Value> = buses
      .iter()
      .map(|&(code, lane)| {
        let code = code.canonical_u64().expect("bus codes are below 2^64");
        json!([
          decimal(Scalar::from_u64(code % 4)),
          decimal(Scalar::from_u64(code / 4)),
          decimal(Scalar::from_u64(code)),
          lane
        ])
      })
      .collect();
    let entry =
      self.entry_circuit.ok_or("the Lean layout needs Config::entry")?;
    let recv = &self.templates[entry].messages[0];
    let mut claim = vec![Scalar::from_u64(super::CALL), Scalar::ZERO];
    claim[1] = match recv.target {
      Target::Receive => {
        let functions = self.plan.program().program().functions.len();
        Scalar::from_u64(
          (0..functions)
            .find(|&f| self.callee_circuit[f] == entry)
            .ok_or("entry function")? as u64,
        )
      },
      _ => return Err("entry message is not a receive".into()),
    };
    claim.resize(2 + recv.payload.len(), Scalar::ZERO);
    let pad = if recv.placement == Placement::Lane { 4 } else { w };
    let request: Vec<Value> = self
      .claims(&claim, Scalar::ZERO)
      .into_iter()
      .map(|mut t| {
        t.resize(t.len().max(pad), Scalar::ZERO);
        json!(t.into_iter().map(decimal).collect::<Vec<_>>())
      })
      .collect();
    let out = json!({
      "format": "ix-tiling-v2-layout-1",
      "width": w,
      "shards": self.shards,
      "caps": self.order.iter().map(|&f| self.per_shard[f]).collect::<Vec<_>>(),
      "fixed_width": c.width(),
      "places": self.rows_per_shard,
      "labels_per_shard": self.labels_per_shard,
      "ids_per_shard": self.ids_per_shard,
      "templates": templates,
      "buses": buses,
      "request": request,
      "tables": self.stacked().iter().map(table_json).collect::<Vec<_>>(),
      "narrow_circuits": (0..self.shards)
        .map(|s| circuit_json(&self.narrow_circuit(s, Some(RowMajorMatrix::new(vec![Scalar::ZERO; c.width()], c.width())))))
        .collect::<Result<Vec<_>, _>>()?,
    });
    let mut fixed = self.narrow_fixed().values;
    fixed.truncate(self.rows_per_shard * c.width());
    Ok(Layout {
      out,
      fixed_rows: self.rows_per_shard,
      fixed_width: c.width(),
      fixed,
      tables: vec![],
    })
  }

  /// Validates `layout` against this backend's circuits and numbering and
  /// makes its fixed matrix the shared narrow fixed matrix.
  pub fn adopt_lean(&mut self, layout: Layout) -> Result<(), String> {
    let out = &layout.out;
    let c = self.cols();
    if usize_of(&out["width"])? != self.config.width
      || usize_of(&out["shards"])? != self.shards
    {
      return Err("exported width or shard count differs".into());
    }
    let caps: Vec<usize> =
      self.order.iter().map(|&f| self.per_shard[f]).collect();
    if naturals(out, "caps")? != caps {
      return Err("exported capacities differ".into());
    }
    if usize_of(&out["labels_per_shard"])? as u64 != self.labels_per_shard
      || usize_of(&out["ids_per_shard"])? as u64 != self.ids_per_shard
    {
      return Err("exported label or id stride differs".into());
    }
    let tv = out["templates"].as_array().ok_or("layout without templates")?;
    if tv.len() != self.order.len() {
      return Err("one template per function circuit".into());
    }
    for (k, (&f, v)) in self.order.iter().zip(tv).enumerate() {
      let t = &self.templates[f];
      let name = &self.compiler.names()[f];
      let want = template_json(t, self.compiler.inputs()[f].main_width);
      let slots = v["slots"]
        .as_array()
        .ok_or(format!("{name}: template without slots"))?;
      if slots.len() != t.logical_slots || slots.len() < t.slots.len() {
        return Err(format!(
          "{name}: {} exported slots, {} logical",
          slots.len(),
          t.logical_slots
        ));
      }
      if slots[..t.slots.len()] != want["slots"].as_array().expect("slots")[..]
        || v["rows"] != want["rows"]
      {
        return Err(format!(
          "{name} (layout circuit {k}): exported template differs from the lowering"
        ));
      }
      if slots[t.slots.len()..] != logical_extra(t)[..] {
        return Err(format!("{name}: invocation or virtual slots differ"));
      }
      let first_virtual = t.slots.len()
        + usize::from(
          slots
            .get(t.slots.len())
            .is_some_and(|s| s.get("invocation").is_some()),
        );
      if naturals(v, "virtual")?
        != (first_virtual..t.logical_slots).collect::<Vec<_>>()
      {
        return Err(format!("{name}: virtual slot list differs"));
      }
    }
    let mut exported = vec![];
    for b in out["buses"].as_array().ok_or("layout without buses")? {
      let e = b.as_array().ok_or("bad bus entry")?;
      let [tag, sub, code, lane] = &e[..] else {
        return Err("bus entries are [tag, sub, code, lane]".into());
      };
      exported.push((
        parse_scalar(code)?.canonical_u64().ok_or("bus code")?,
        lane.as_bool().ok_or("bus lane flag")?,
      ));
      let (tag, sub) = (parse_scalar(tag)?, parse_scalar(sub)?);
      let tag = tag.canonical_u64().ok_or("bus tag")?;
      let sub = sub.canonical_u64().ok_or("bus sub")?;
      if parse_scalar(code)? != ts(tag, sub) {
        return Err(format!(
          "bus ({tag}, {sub}) has code {code}, not tag + 4·sub"
        ));
      }
    }
    let mut own: Vec<(u64, bool)> = self
      .buses()
      .iter()
      .map(|&(c, l)| (c.canonical_u64().expect("bus codes are below 2^64"), l))
      .collect();
    exported.sort_unstable();
    own.sort_unstable();
    if exported != own {
      return Err("exported bus table differs from this backend's".into());
    }
    if layout.fixed_width != c.width()
      || layout.fixed_rows != self.rows_per_shard
      || usize_of(&out["places"])? != self.rows_per_shard
      || usize_of(&out["fixed_width"])? != c.width()
    {
      return Err("exported fixed matrix shape differs".into());
    }
    let described = out["compact"].as_array().map_or(&[][..], Vec::as_slice);
    let compact = if described.is_empty() {
      let tables: Vec<Value> = self.stacked().iter().map(table_json).collect();
      if out["tables"].as_array() != Some(&tables) {
        return Err(
          "exported stacked tables differ from this backend's".into(),
        );
      }
      None
    } else {
      // The compact shape of §5g: the map table (`n = W − 1`), then the ROM
      // table (`n = 1`), each with the exported fixed rows.
      let w = self.config.width;
      if out["tables"].as_array().is_some_and(|t| !t.is_empty())
        || described.len() != 2
        || layout.tables.len() != 2
      {
        return Err(
          "a compact export has exactly a map and a ROM table".into(),
        );
      }
      let mut tables = vec![];
      for (k, (d, (rows, width, values))) in
        described.iter().zip(&layout.tables).enumerate()
      {
        let n = usize_of(&d["n_fixed"])?;
        let expected = if k == 0 { w - 1 } else { 1 };
        if n != expected
          || usize_of(&d["main_width"])? != w - n
          || usize_of(&d["fixed_width"])? != 3 + n
          || *width != 3 + n
          || usize_of(&d["rows"])? != *rows
        {
          return Err(format!(
            "compact table {k} does not have the exported shape"
          ));
        }
        let mut t = super::CompactTable {
          n_fixed: n,
          main_width: w - n,
          rows: *rows,
          fixed: RowMajorMatrix::new(vec![], 3 + n),
        };
        let mut v = values.clone();
        v.resize(t.height() * (3 + n), Scalar::ZERO);
        t.fixed = RowMajorMatrix::new(v, 3 + n);
        tables.push(t);
      }
      let [map, rom]: [super::CompactTable; 2] = tables
        .try_into()
        .map_err(|t: Vec<_>| format!("{} compact tables, not two", t.len()))?;
      Some([map, rom])
    };
    let n = layout.fixed_rows * layout.fixed_width;
    let mut values = layout.fixed;
    values.truncate(n);
    values.resize(self.height * c.width(), Scalar::ZERO);
    let request = out["request"]
      .as_array()
      .ok_or("layout without request")?
      .iter()
      .map(|t| {
        t.as_array()
          .ok_or("bad request tuple")?
          .iter()
          .map(parse_scalar)
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    let graphs = |key: &str| -> Result<Vec<Graph>, String> {
      out[key]
        .as_array()
        .ok_or(format!("layout without {key}"))?
        .iter()
        .map(Graph::parse)
        .collect()
    };
    let narrow = graphs("narrow_circuits")?;
    if narrow.len() != self.shards
      || narrow
        .iter()
        .any(|g| g.width != self.config.width || g.fixed_width != c.width())
    {
      return Err("exported shard circuits do not have the shard shape".into());
    }
    let compact_circuits = match &compact {
      Some(tables) => {
        let g = graphs("compact_circuits")?;
        if g.len() != 2
          || g.iter().zip(tables).any(|(g, t)| {
            g.width != t.main_width || g.fixed_width != t.fixed.width
          })
        {
          return Err(
            "exported compact circuits do not have the compact tables' shape"
              .into(),
          );
        }
        g
      },
      None => vec![],
    };
    self.lean = Some(super::LeanFixed {
      fixed: RowMajorMatrix::new(values, c.width()),
      request,
      compact,
      narrow,
      compact_circuits,
    });
    Ok(())
  }

  /// Checks that `claims` have the exported request's shape: the same
  /// tuples, codes, chunk keys and lengths up to trailing zeros. The
  /// exported payload is a placeholder.
  pub fn check_lean_request(
    &self,
    claims: &[Vec<Scalar>],
  ) -> Result<(), String> {
    let Some(lean) = &self.lean else { return Ok(()) };
    let keyed = self.entry_circuit.is_some_and(|f| {
      self.templates[f].messages[0].placement == Placement::Chunked
    });
    let header = if keyed { 2 } else { 1 };
    let same = claims.len() == lean.request.len()
      && claims.iter().zip(&lean.request).all(|(a, b)| {
        a.len() >= header
          && b.len() >= a.len()
          && a[..header] == b[..header]
          && trimmed(&b[a.len()..]).is_empty()
      });
    if same {
      Ok(())
    } else {
      Err("the claim does not have the exported request's shape".into())
    }
  }
}

/// A circuit as the exporter writes it (`TilingExport2.graphJson`, the graph
/// format of `Export.parseGraph` with `fixed_width`): nodes in topological
/// order; variable `v < width` is main column `v`, `width ≤ v` is fixed column
/// `v − width`; every `zeros` node is a constraint and every lookup is
/// `push(node m, [node a…])`.
#[derive(Clone, Debug)]
pub struct Graph<C: AiurCurve = Bn254Curve> {
  pub width: usize,
  pub fixed_width: usize,
  pub nodes: Vec<Node<CurveScalar<C>>>,
  pub zeros: Vec<NodeId>,
  pub lookups: Vec<Lookup<NodeId>>,
}

impl<C: AiurCurve> Graph<C> {
  pub fn parse(v: &Value) -> Result<Self, String> {
    let width = usize_of(&v["width"])?;
    let fixed_width = v.get("fixed_width").map_or(Ok(0), usize_of)?;
    let raw = v["nodes"].as_array().ok_or("graph without nodes")?;
    let id = |k: usize| {
      u32::try_from(k).map(NodeId).map_err(|e| format!("graph node {k}: {e}"))
    };
    let mut nodes = Vec::with_capacity(raw.len());
    for (i, n) in raw.iter().enumerate() {
      let n = n.as_array().ok_or("bad graph node")?;
      let op = n.first().and_then(Value::as_str).ok_or("bad graph node")?;
      let child = |k: usize| -> Result<NodeId, String> {
        let c = n.get(k).map_or(Err("missing operand".to_owned()), usize_of)?;
        if c >= i {
          return Err("graph nodes are not in topological order".into());
        }
        id(c)
      };
      nodes.push(match op {
        "const" => Node::Const(parse_scalar_for::<C>(
          n.get(1).ok_or("constant without value")?,
        )?),
        "var" => {
          let x = n
            .get(1)
            .map_or(Err("variable without index".to_owned()), usize_of)?;
          let (source, index) = if x < width {
            (Source::Main, x)
          } else if x < width + fixed_width {
            (Source::Preprocessed, x - width)
          } else {
            return Err(format!(
              "variable {x} outside {width} main and {fixed_width} fixed columns"
            ));
          };
          let index =
            u32::try_from(index).map_err(|e| format!("variable {x}: {e}"))?;
          Node::Var(ColRef { source, offset: RowOffset::Current, index })
        },
        "add" => Node::Add(child(1)?, child(2)?),
        "sub" => Node::Sub(child(1)?, child(2)?),
        "mul" => Node::Mul(child(1)?, child(2)?),
        "neg" => Node::Neg(child(1)?),
        _ => return Err(format!("unknown graph node {op}")),
      });
    }
    let node = |x: &Value| -> Result<NodeId, String> {
      let k = usize_of(x)?;
      if k >= nodes.len() {
        return Err("graph root out of range".into());
      }
      id(k)
    };
    let zeros = v["zeros"]
      .as_array()
      .ok_or("graph without zeros")?
      .iter()
      .map(node)
      .collect::<Result<_, _>>()?;
    let lookups = v["lookups"]
      .as_array()
      .ok_or("graph without lookups")?
      .iter()
      .map(|l| {
        let m = node(l.get(0).ok_or("lookup without multiplicity")?)?;
        let args = l
          .get(1)
          .and_then(Value::as_array)
          .ok_or("lookup without arguments")?;
        Ok(Lookup::push(
          m,
          args.iter().map(node).collect::<Result<_, String>>()?,
        ))
      })
      .collect::<Result<_, String>>()?;
    Ok(Self { width, fixed_width, nodes, zeros, lookups })
  }

  /// The one-row constraint graph the template lowering reads (no fixed
  /// columns).
  pub fn constraint_graph(
    &self,
  ) -> Result<ConstraintGraph<CurveScalar<C>>, String> {
    if self.fixed_width != 0 {
      return Err("a function circuit graph has no fixed columns".into());
    }
    let mut degrees: Vec<u32> = Vec::with_capacity(self.nodes.len());
    for n in &self.nodes {
      let d = |x: &NodeId| degrees[x.index()];
      let k: u32 = match n {
        Node::Const(_) => 0,
        Node::Var(_) => 1,
        Node::Add(a, b) | Node::Sub(a, b) => d(a).max(d(b)),
        Node::Mul(a, b) => d(a) + d(b),
        Node::Neg(a) => d(a),
        _ => {
          return Err("row selectors and publics are not graph nodes".into());
        },
      };
      degrees.push(k);
    }
    let max_constraint_degree =
      self.zeros.iter().map(|z| degrees[z.index()]).max().unwrap_or(0);
    Ok(ConstraintGraph {
      nodes: self.nodes.clone(),
      degrees,
      zeros: self.zeros.clone(),
      lookups: self.lookups.clone(),
      lookup_prefix_len: self.nodes.len(),
      max_constraint_degree,
    })
  }

  fn exprs(&self) -> Vec<Expr<CurveScalar<C>>> {
    let mut e: Vec<Expr<CurveScalar<C>>> = Vec::with_capacity(self.nodes.len());
    for n in &self.nodes {
      let x = match *n {
        Node::Const(k) => Expr::Const(k),
        Node::Var(c) => Expr::Var(c),
        Node::Add(a, b) => e[a.index()].clone() + e[b.index()].clone(),
        Node::Sub(a, b) => e[a.index()].clone() - e[b.index()].clone(),
        Node::Mul(a, b) => e[a.index()].clone() * e[b.index()].clone(),
        Node::Neg(a) => -e[a.index()].clone(),
        Node::Public(_)
        | Node::IsFirstRow
        | Node::IsLastRow
        | Node::IsTransition => {
          unreachable!("parsed graphs hold no row selectors or publics")
        },
      };
      e.push(x);
    }
    e
  }

  /// The multi-stark circuit of this graph read literally, with `fixed` as
  /// its fixed matrix and the lookup grouping of `lookup_budget`.
  pub fn circuit_inputs(
    &self,
    fixed: Option<RowMajorMatrix<CurveScalar<C>>>,
    lookup_budget: usize,
  ) -> CircuitInputs<CurveScalar<C>> {
    let mut input = self.inputs(None);
    input.preprocessed = (self.fixed_width > 0).then(|| {
      RowMajorMatrix::new(
        vec![CurveScalar::<C>::ZERO; self.fixed_width],
        self.fixed_width,
      )
    });
    // Group sizes depend only on expression shapes.
    input.lookup_group_size =
      super::super::group_size_for::<C>(&input, lookup_budget);
    input.preprocessed = fixed;
    input
  }

  /// [`Self::circuit_inputs`] without lookup grouping.
  pub fn inputs(
    &self,
    fixed: Option<RowMajorMatrix<CurveScalar<C>>>,
  ) -> CircuitInputs<CurveScalar<C>> {
    let e = self.exprs();
    CircuitInputs {
      main_width: self.width,
      preprocessed: fixed,
      constraints: self.zeros.iter().map(|z| e[z.index()].clone()).collect(),
      lookups: self
        .lookups
        .iter()
        .map(|l| {
          Lookup::push(
            e[l.multiplicity.index()].clone(),
            l.args.iter().map(|a| e[a.index()].clone()).collect(),
          )
        })
        .collect(),
      ..Default::default()
    }
  }
}

fn eval_expr<C: AiurCurve>(
  e: &Expr<CurveScalar<C>>,
  main: &[CurveScalar<C>],
  fixed: &[CurveScalar<C>],
) -> Result<CurveScalar<C>, String> {
  Ok(match e {
    Expr::Const(k) => *k,
    Expr::Var(c) if c.offset == RowOffset::Current => match c.source {
      Source::Main => main[c.index as usize],
      Source::Preprocessed => fixed[c.index as usize],
      Source::Stage2 => return Err("stage-two variable".into()),
    },
    Expr::Add(a, b) => {
      eval_expr::<C>(a, main, fixed)? + eval_expr::<C>(b, main, fixed)?
    },
    Expr::Sub(a, b) => {
      eval_expr::<C>(a, main, fixed)? - eval_expr::<C>(b, main, fixed)?
    },
    Expr::Mul(a, b) => {
      eval_expr::<C>(a, main, fixed)? * eval_expr::<C>(b, main, fixed)?
    },
    Expr::Neg(a) => -eval_expr::<C>(a, main, fixed)?,
    _ => return Err("row selector, public or next-row variable".into()),
  })
}

/// Whether two one-row circuits over curve `C` agree as constraint and lookup
/// multisets at `trials` pseudo-random points: every constraint value and every
/// lookup's multiplicity and arguments.
pub fn same_circuit_for<C: AiurCurve>(
  a: &CircuitInputs<CurveScalar<C>>,
  b: &CircuitInputs<CurveScalar<C>>,
  trials: usize,
) -> Result<bool, String> {
  let fw = |c: &CircuitInputs<CurveScalar<C>>| {
    c.preprocessed.as_ref().map_or(0, |m| m.width)
  };
  if a.main_width != b.main_width
    || fw(a) != fw(b)
    || a.lookups.len() != b.lookups.len()
  {
    return Ok(false);
  }
  let mut seed = 0x9e37_79b9_7f4a_7c15u64;
  let mut next = || {
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    CurveScalar::<C>::from_u64(seed)
  };
  type Point = (Vec<String>, Vec<Vec<String>>);
  let at = |c: &CircuitInputs<CurveScalar<C>>,
            main: &[CurveScalar<C>],
            fixed: &[CurveScalar<C>]|
   -> Result<Point, String> {
    let text = |x: CurveScalar<C>| x.0.to_string();
    let mut zeros: Vec<String> = c
      .constraints
      .iter()
      .map(|z| eval_expr::<C>(z, main, fixed).map(text))
      .collect::<Result<_, _>>()?;
    zeros.retain(|z| z != "0");
    zeros.sort();
    zeros.dedup();
    let mut lookups: Vec<Vec<String>> = c
      .lookups
      .iter()
      .map(|l| {
        std::iter::once(&l.multiplicity)
          .chain(&l.args)
          .map(|x| eval_expr::<C>(x, main, fixed).map(text))
          .collect()
      })
      .collect::<Result<_, String>>()?;
    lookups.sort();
    Ok((zeros, lookups))
  };
  for _ in 0..trials {
    let main: Vec<CurveScalar<C>> = (0..a.main_width).map(|_| next()).collect();
    let fixed: Vec<CurveScalar<C>> = (0..fw(a)).map(|_| next()).collect();
    if at(a, &main, &fixed)? != at(b, &main, &fixed)? {
      return Ok(false);
    }
  }
  Ok(true)
}

/// Whether two one-row BN254 circuits agree as constraint and lookup multisets
/// at `trials` pseudo-random points.
pub fn same_circuit(
  a: &CircuitInputs<Scalar>,
  b: &CircuitInputs<Scalar>,
  trials: usize,
) -> Result<bool, String> {
  same_circuit_for::<Bn254Curve>(a, b, trials)
}

/// The function circuits in layout order (the entry's first) and, per
/// compiler function circuit, the callable it implements; the unrolled
/// `Blake3::compress` circuit and its stage count if `config` asks for it.
fn layout_order(
  compiler: &Compiler<'_, '_>,
  plan: &TracePlan<'_, Bn254>,
  config: &Config,
) -> Result<(Vec<usize>, Option<(usize, usize)>), String> {
  let nf = compiler.function_circuits();
  let layout = plan.layout()?;
  let program = plan.program().program();
  let callee: Vec<usize> = plan
    .function_chips()
    .iter()
    .map(|&chip| layout.placements[chip].circuit)
    .collect();
  let entry = match &config.entry {
    Some(name) => Some(callee[plan.program().entry(name)?.function]),
    None => None,
  };
  let order =
    entry.into_iter().chain((0..nf).filter(|&f| Some(f) != entry)).collect();
  let unrolled = if config.unroll_compress
    && let Some(f) =
      program.functions.iter().position(|f| f.name == super::COMPRESS)
  {
    Some((callee[f], super::compress_stages(&program.functions[f])?))
  } else {
    None
  };
  Ok((order, unrolled))
}

/// The exporter's input in format 2 (`ix-tiling-v2-input-2`): the artifact
/// and the configuration only. The exporter lowers the artifact's chips
/// itself (`IChip.lower`) and takes the map claims and the request from it.
/// `config` must fix the shard count. `artifact_blake3` names the artifact's
/// contents, so that a cache keyed by the input file distinguishes artifacts
/// at one path.
pub fn input2(
  compiler: &Compiler<'_, '_>,
  plan: &TracePlan<'_, Bn254>,
  config: &Config,
  artifact: &Path,
  artifact_blake3: &str,
) -> Result<Value, String> {
  let shards = config.shards.ok_or("format 2 needs a fixed shard count")?;
  let nf = compiler.function_circuits();
  if config.capacities.len() != nf {
    return Err("one capacity per function circuit".into());
  }
  let (order, unrolled) = layout_order(compiler, plan, config)?;
  let circuits: Vec<Value> = order
    .iter()
    .map(|&c| {
      let mut v = json!({"chip": compiler.names()[c], "cap": config.capacities[c].div_ceil(shards)});
      if let Some((u, stages)) = unrolled
        && u == c
      {
        v["unroll"] = json!(true);
        v["stages"] = json!(stages);
      }
      v
    })
    .collect();
  let widths: Vec<usize> = compiler
    .names()
    .iter()
    .filter_map(|n| {
      n.strip_prefix("<ROM:")?.strip_suffix('>')?.parse::<usize>().ok()
    })
    .collect();
  if widths.len() != config.rom_capacities.len() {
    return Err("one ROM capacity per memory width".into());
  }
  let artifact = std::path::absolute(artifact)
    .map_err(|e| format!("{}: {e}", artifact.display()))?;
  let mut v = json!({
    "format": "ix-tiling-v2-input-2",
    "artifact": artifact,
    "artifact_blake3": artifact_blake3,
    "width": config.width,
    "shards": shards,
    "circuits": circuits,
    "rom": widths.iter().zip(&config.rom_capacities).map(|(w, c)| json!([w, c])).collect::<Vec<_>>(),
  });
  if let Some(&first) = order.first()
    && config.entry.is_some()
  {
    v["entry"] = json!(compiler.names()[first]);
  }
  Ok(v)
}

impl<'c, 'p, 'a> Backend<'c, 'p, 'a> {
  /// The backend over the exported circuits of a format-2 layout: each
  /// function circuit's template is this crate's lowering of the exporter's
  /// `Bridge.lower` graph (`circuits[k].wide`), and the layout is then
  /// validated and adopted ([`Self::adopt_lean`]).
  pub fn from_lean(
    compiler: &'c Compiler<'p, 'a>,
    plan: &'p TracePlan<'a, Bn254>,
    config: Config,
    layout: Layout,
  ) -> Result<Self, String> {
    let nf = compiler.function_circuits();
    let (order, unrolled) = layout_order(compiler, plan, &config)?;
    let exported = layout.out["circuits"]
      .as_array()
      .ok_or("layout without circuits (not format 2)")?;
    if exported.len() != order.len() {
      return Err("one exported circuit per function circuit".into());
    }
    let mut graphs: Vec<Option<ConstraintGraph<Scalar>>> =
      (0..nf).map(|_| None).collect();
    for (&c, v) in order.iter().zip(exported) {
      let name = &compiler.names()[c];
      if v["chip"].as_str() != Some(name.as_str()) {
        return Err(format!("exported circuit {} is not {name}", v["chip"]));
      }
      let stages = unrolled.filter(|&(u, _)| u == c).map(|(_, n)| n as u64);
      if v["unroll"].as_bool() != Some(stages.is_some())
        || (stages.is_some() && v["stages"].as_u64() != stages)
      {
        return Err(format!("{name}: exported unrolling differs"));
      }
      let g = Graph::parse(&v["wide"]).map_err(|e| format!("{name}: {e}"))?;
      if g.width != compiler.inputs()[c].main_width {
        return Err(format!(
          "{name}: exported graph has {} columns, the wide trace {}",
          g.width,
          compiler.inputs()[c].main_width
        ));
      }
      graphs[c] =
        Some(g.constraint_graph().map_err(|e| format!("{name}: {e}"))?);
    }
    let graphs = graphs
      .into_iter()
      .collect::<Option<Vec<_>>>()
      .ok_or("a function circuit was not exported")?;
    let mut backend = Self::with_graphs(compiler, plan, config, Some(graphs))?;
    backend.adopt_lean(layout)?;
    Ok(backend)
  }

  /// Cross-checks of the adopted export against this crate's own
  /// construction, none of which the proof uses: the templates lowered from
  /// `compile_graph` instead of the exported graphs (the count that differ),
  /// and `narrow_circuit`/`compact_circuit` against the exported shard and
  /// table circuits (equal constraint and lookup multisets at random points).
  pub fn rust_cross_check(&self) -> Result<Value, String> {
    let lean = self.lean.as_ref().ok_or("no adopted Lean layout")?;
    let rust = Backend::new(self.compiler, self.plan, self.config.clone())?;
    let differing: Vec<&str> = self
      .order
      .iter()
      .filter(|&&f| {
        let w = self.compiler.inputs()[f].main_width;
        template_json(&self.templates[f], w)
          != template_json(&rust.templates[f], w)
      })
      .map(|&f| self.compiler.names()[f].as_str())
      .collect();
    let budget = self.config.lookup_budget;
    let probe = |w: usize| Some(RowMajorMatrix::new(vec![Scalar::ZERO; w], w));
    let mut narrow_same = true;
    for (s, g) in lean.narrow.iter().enumerate() {
      let mine = self.narrow_circuit(s, probe(g.fixed_width));
      narrow_same &= same_circuit(
        &g.circuit_inputs(probe(g.fixed_width), budget),
        &mine,
        4,
      )?;
    }
    let mut compact_same = true;
    if let Some(tables) = self.compact() {
      for (t, g) in tables.iter().zip(&lean.compact_circuits) {
        let mine = self.compact_circuit(
          t,
          RowMajorMatrix::new(vec![Scalar::ZERO; t.fixed.width], t.fixed.width),
        );
        compact_same &= same_circuit(
          &g.circuit_inputs(probe(g.fixed_width), budget),
          &mine,
          4,
        )?;
      }
    }
    Ok(json!({
      "templates": self.order.len(),
      "templates_differing_from_compile_graph": differing.len(),
      "differing": differing,
      "rust_rows_per_shard": rust.rows_per_shard,
      "narrow_circuit_equal": narrow_same,
      "compact_circuit_equal": compact_same,
    }))
  }
}
