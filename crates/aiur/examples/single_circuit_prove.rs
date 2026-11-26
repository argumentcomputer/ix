//! Prove and verify a Lean-exported formally certified single-circuit Goldilocks
//! STARK (`wide_export --single-circuit --pow2-rows`, backed by
//! `Aiur.Tiling.SingleCircuit.wide_single_circuit_sound_goldilocks`) end-to-end
//! in `multi-stark`.
//!
//! Usage:
//!   single_circuit_prove PACKAGE.ixa LAYOUT.json FIXED.bin
//!     [--args N,N,...] [--controls] [--fri-mla K] [--fri-lfp K]
//!     [--log-blowup K] [--num-queries K] [--query-pow K] [--commit-pow K]
//!     [--lookup-group K] [--no-check] [--proof-out PATH] [--report-out PATH]

use aiur::artifact::{
  self, EXECUTION_MAGIC, ExecutionPackage, PACKAGE_MAGIC, Package,
};
use aiur::field::FieldBackend;
use aiur::hints::HintChannels;
use aiur::trace::TracePlan;
use aiur::trace::stark::{MAX_BATCH_ROWS, Parameters, Proof};
use multi_stark::eval::VarValues;
use multi_stark::expr::Expr;
use multi_stark::graph::ConstraintGraph;
use multi_stark::lookup::{
  Lookup, MAX_LOOKUP_GROUP, logup_max_degree, stage2_width,
};
use multi_stark::p3_adapter::fri_batching::FriBatching;
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use multi_stark::p3_matrix::Matrix;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::system::{CircuitInputs, System, extension_params};
use multi_stark::types::{
  CommitmentParameters, FriParameters, GoldilocksBlake3V6Config, Val,
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use serde_json::{Value, json};
use std::error::Error;
use std::path::Path;
use std::time::Instant;

const LAYOUT_FORMAT: &str = "ix-wide-layout-1";
const FIXED_MAGIC: &[u8; 8] = b"IXTLFX01";
const CALL_TAG: u64 = 1;

const USAGE: &str = "usage: single_circuit_prove PACKAGE.ixa LAYOUT.json FIXED.bin \
  [--args N,N,...] [--controls] [--fri-mla K] [--fri-lfp K] \
  [--log-blowup K] [--num-queries K] [--query-pow K] [--commit-pow K] \
  [--lookup-group K] [--no-check] [--proof-out PATH] [--report-out PATH]";

struct Cli {
  package: String,
  layout: String,
  fixed: String,
  override_args: Option<Vec<u64>>,
  controls: bool,
  check: bool,
  log_blowup: usize,
  num_queries: usize,
  commit_pow: usize,
  query_pow: usize,
  fri_mla: usize,
  fri_lfp: usize,
  lookup_group: Option<usize>,
  proof_out: Option<String>,
  report_out: Option<String>,
}

fn parse_usize_flag(
  flag: &str,
  raw: &mut std::env::Args,
) -> Result<usize, String> {
  let value = raw.next().ok_or_else(|| format!("{flag} expects an integer"))?;
  value
    .parse::<usize>()
    .map_err(|e| format!("invalid {flag} value {value:?}: {e}"))
}

fn parse_cli() -> Result<Cli, String> {
  let defaults = Parameters::DEFAULT;
  let mut pos = Vec::new();
  let mut override_args: Option<Vec<u64>> = None;
  let mut controls = false;
  let mut check = true;
  let mut log_blowup = defaults.log_blowup;
  let mut num_queries = defaults.num_queries;
  let mut commit_pow = defaults.commit_proof_of_work_bits;
  let mut query_pow = defaults.query_proof_of_work_bits;
  let mut fri_mla = 1usize;
  let mut fri_lfp = 0usize;
  let mut lookup_group: Option<usize> = None;
  let mut proof_out: Option<String> = None;
  let mut report_out: Option<String> = None;

  let mut raw = std::env::args();
  let _exe = raw.next();
  while let Some(arg) = raw.next() {
    match arg.as_str() {
      "--args" => {
        let list =
          raw.next().ok_or("--args expects a comma-separated integer list")?;
        override_args = Some(
          list
            .split(',')
            .filter(|w| !w.is_empty())
            .map(|w| {
              w.parse::<u64>()
                .map_err(|e| format!("invalid --args element {w:?}: {e}"))
            })
            .collect::<Result<_, _>>()?,
        );
      },
      "--controls" => controls = true,
      "--no-check" => check = false,
      "--fri-mla" => fri_mla = parse_usize_flag("--fri-mla", &mut raw)?,
      "--fri-lfp" => fri_lfp = parse_usize_flag("--fri-lfp", &mut raw)?,
      "--log-blowup" => {
        log_blowup = parse_usize_flag("--log-blowup", &mut raw)?;
      },
      "--num-queries" => {
        num_queries = parse_usize_flag("--num-queries", &mut raw)?;
      },
      "--query-pow" => query_pow = parse_usize_flag("--query-pow", &mut raw)?,
      "--commit-pow" => {
        commit_pow = parse_usize_flag("--commit-pow", &mut raw)?;
      },
      "--lookup-group" => {
        lookup_group = Some(parse_usize_flag("--lookup-group", &mut raw)?);
      },
      "--proof-out" => {
        proof_out =
          Some(raw.next().ok_or("--proof-out expects a file path")?);
      },
      "--report-out" => {
        report_out =
          Some(raw.next().ok_or("--report-out expects a file path")?);
      },
      "-h" | "--help" => return Err(USAGE.into()),
      other if other.starts_with("--") => {
        return Err(format!("unknown option {other}\n{USAGE}"));
      },
      other => pos.push(other.to_owned()),
    }
  }
  if pos.len() != 3 {
    return Err(USAGE.into());
  }
  if !(1..=10).contains(&fri_mla) {
    return Err(format!("--fri-mla must be in 1..=10, got {fri_mla}"));
  }
  if log_blowup == 0 || log_blowup > 6 {
    return Err(format!("--log-blowup must be in 1..=6, got {log_blowup}"));
  }
  if num_queries == 0 {
    return Err("--num-queries must be positive".into());
  }
  let mut iter = pos.into_iter();
  Ok(Cli {
    package: iter.next().unwrap(),
    layout: iter.next().unwrap(),
    fixed: iter.next().unwrap(),
    override_args,
    controls,
    check,
    log_blowup,
    num_queries,
    commit_pow,
    query_pow,
    fri_mla,
    fri_lfp,
    lookup_group,
    proof_out,
    report_out,
  })
}

fn peak_rss_kb() -> Option<u64> {
  let status = std::fs::read_to_string("/proc/self/status").ok()?;
  let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
  line.split_whitespace().nth(1)?.parse().ok()
}

fn natural(v: &Value, ctx: &str) -> Result<usize, String> {
  v.as_u64()
    .and_then(|n| usize::try_from(n).ok())
    .ok_or_else(|| format!("{ctx}: expected natural number, got {v}"))
}

fn scalar(v: &Value, ctx: &str) -> Result<Val, String> {
  let n = match v {
    Value::String(s) => {
      s.parse::<u64>().map_err(|e| format!("{ctx}: invalid scalar {s}: {e}"))?
    },
    _ => v
      .as_u64()
      .ok_or_else(|| format!("{ctx}: expected field element, got {v}"))?,
  };
  if n >= Val::ORDER_U64 {
    return Err(format!("{ctx}: scalar {n} exceeds Goldilocks modulus"));
  }
  Ok(Val::from_u64(n))
}

#[derive(Clone, Debug)]
enum ConstituentKind {
  Unit { chip: String },
  Map { length: usize },
  Rom { words: usize },
}

#[derive(Clone, Debug)]
struct Constituent {
  kind: ConstituentKind,
  rows: usize,
  main_offset: usize,
  main_width: usize,
  fixed_offset: usize,
  active_col: Option<usize>,
}

struct SingleCircuitLayout {
  rows: usize,
  main_width: usize,
  fixed_width: usize,
  num_constraints: usize,
  num_lookups: usize,
  bound: u64,
  request: Vec<Val>,
  constituents: Vec<Constituent>,
  constraints: Vec<Expr<Val>>,
  lookups: Vec<Lookup<Expr<Val>>>,
}

fn parse_graph(
  v: &Value,
  expected_main_width: usize,
  expected_fixed_width: usize,
) -> Result<(Vec<Expr<Val>>, Vec<Lookup<Expr<Val>>>), String> {
  let width = natural(&v["width"], "circuit.width")?;
  let fixed_width = natural(&v["fixed_width"], "circuit.fixed_width")?;
  if width != expected_main_width || fixed_width != expected_fixed_width {
    return Err(format!(
      "circuit dimensions ({width} main, {fixed_width} fixed) disagree with \
       single_circuit ({expected_main_width} main, {expected_fixed_width} fixed)"
    ));
  }
  let column = |x: usize| {
    u32::try_from(x).map_err(|e| format!("column {x} overflows u32: {e}"))
  };
  let raw_nodes = v["nodes"]
    .as_array()
    .ok_or("single_circuit.circuit missing nodes array")?;
  let mut nodes: Vec<Expr<Val>> = Vec::with_capacity(raw_nodes.len());
  for (i, n) in raw_nodes.iter().enumerate() {
    let arr = n.as_array().ok_or_else(|| format!("graph node {i} not array"))?;
    let op = arr
      .first()
      .and_then(Value::as_str)
      .ok_or_else(|| format!("graph node {i} missing op"))?;
    let child = |k: usize| -> Result<Expr<Val>, String> {
      let idx = natural(
        arr
          .get(k)
          .ok_or_else(|| format!("graph node {i} ({op}) missing operand {k}"))?,
        "graph operand",
      )?;
      if idx >= i {
        return Err(format!(
          "graph node {i} references non-topological operand {idx}"
        ));
      }
      Ok(nodes[idx].clone())
    };
    let expr = match op {
      "const" => Expr::constant(scalar(
        arr.get(1).ok_or_else(|| format!("const node {i} missing value"))?,
        "const node",
      )?),
      "var" => {
        let x = natural(
          arr.get(1).ok_or_else(|| format!("var node {i} missing index"))?,
          "var node",
        )?;
        if x < width {
          Expr::main(column(x)?)
        } else if x < width + fixed_width {
          Expr::preprocessed(column(x - width)?)
        } else {
          return Err(format!(
            "var {x} outside {width} main + {fixed_width} fixed columns"
          ));
        }
      },
      "add" => child(1)? + child(2)?,
      "sub" => child(1)? - child(2)?,
      "mul" => child(1)? * child(2)?,
      "neg" => -child(1)?,
      other => return Err(format!("unknown graph node op {other:?}")),
    };
    nodes.push(expr);
  }
  let lookup_node = |x: &Value, ctx: &str| -> Result<Expr<Val>, String> {
    let idx = natural(x, ctx)?;
    nodes
      .get(idx)
      .cloned()
      .ok_or_else(|| format!("{ctx}: node index {idx} out of range"))
  };
  let constraints = v["zeros"]
    .as_array()
    .ok_or("single_circuit.circuit missing zeros array")?
    .iter()
    .map(|z| lookup_node(z, "zeros"))
    .collect::<Result<Vec<_>, _>>()?;
  let lookups = v["lookups"]
    .as_array()
    .ok_or("single_circuit.circuit missing lookups array")?
    .iter()
    .map(|l| {
      let arr = l.as_array().ok_or("lookup entry not an array")?;
      let m = lookup_node(
        arr.first().ok_or("lookup missing multiplicity")?,
        "lookup.multiplicity",
      )?;
      let args = arr
        .get(1)
        .and_then(Value::as_array)
        .ok_or("lookup missing args array")?
        .iter()
        .map(|a| lookup_node(a, "lookup.arg"))
        .collect::<Result<Vec<_>, _>>()?;
      // Lean's IChip.lower / mapCircuit / romCircuit already encode signs in
      // multiplicity (-mult for providers, +enable for consumers).
      Ok(Lookup::push(m, args))
    })
    .collect::<Result<Vec<_>, String>>()?;
  Ok((constraints, lookups))
}

fn parse_layout(bytes: &[u8]) -> Result<SingleCircuitLayout, String> {
  let root: Value = serde_json::from_slice(bytes)
    .map_err(|e| format!("failed to parse layout JSON: {e}"))?;
  if root["format"].as_str() != Some(LAYOUT_FORMAT) {
    return Err(format!(
      "unexpected layout format {:?} (expected {LAYOUT_FORMAT:?})",
      root["format"]
    ));
  }
  let expected_modulus = Val::ORDER_U64.to_string();
  if root["modulus"].as_str() != Some(expected_modulus.as_str()) {
    return Err(format!(
      "layout modulus {:?} is not Goldilocks ({expected_modulus})",
      root["modulus"]
    ));
  }
  if let Some(field_val) = root.get("field")
    && field_val.as_str() != Some("goldilocks")
  {
    return Err(format!(
      "layout field {field_val} is not \"goldilocks\""
    ));
  }
  let request = root["request"]
    .as_array()
    .ok_or("layout missing request array")?
    .iter()
    .map(|x| scalar(x, "request"))
    .collect::<Result<Vec<_>, _>>()?;
  let bound = root["bound"]
    .as_u64()
    .ok_or("layout missing u64 bound")?;

  let sc = root
    .get("single_circuit")
    .filter(|v| v.is_object())
    .ok_or(
      "layout missing \"single_circuit\" object \
       (re-export with `wide_export --single-circuit --pow2-rows`)",
    )?;
  let num_circuits = natural(&sc["num_circuits"], "single_circuit.num_circuits")?;
  if num_circuits != 1 {
    return Err(format!(
      "single_circuit.num_circuits must be 1, got {num_circuits}"
    ));
  }
  let rows = natural(&sc["rows"], "single_circuit.rows")?;
  if rows == 0 || !rows.is_power_of_two() {
    return Err(format!(
      "single_circuit.rows ({rows}) must be a positive power of two \
       (re-export with --pow2-rows)"
    ));
  }
  if u64::try_from(rows).is_ok_and(|r| r > MAX_BATCH_ROWS) {
    return Err(format!(
      "single_circuit.rows ({rows}) exceeds Goldilocks depth bound 2^39"
    ));
  }
  let main_width = natural(&sc["main_width"], "single_circuit.main_width")?;
  let fixed_width = natural(&sc["fixed_width"], "single_circuit.fixed_width")?;
  let num_constraints =
    natural(&sc["num_constraints"], "single_circuit.num_constraints")?;
  let num_lookups = natural(&sc["num_lookups"], "single_circuit.num_lookups")?;

  let raw_constituents = sc["constituents"]
    .as_array()
    .ok_or("single_circuit missing constituents array")?;
  let mut constituents = Vec::with_capacity(raw_constituents.len());
  let mut expected_m_off = 0usize;
  let mut expected_f_off = 0usize;
  for (idx, c) in raw_constituents.iter().enumerate() {
    let c_rows = natural(&c["rows"], "constituent.rows")?;
    let m_off = natural(&c["main_offset"], "constituent.main_offset")?;
    let m_w = natural(&c["main_width"], "constituent.main_width")?;
    let f_off = natural(&c["fixed_offset"], "constituent.fixed_offset")?;
    let f_w = natural(&c["fixed_width"], "constituent.fixed_width")?;
    let active_col = match c.get("active_col") {
      Some(v) if !v.is_null() => {
        Some(natural(v, "constituent.active_col")?)
      },
      _ => None,
    };
    if c_rows > rows {
      return Err(format!(
        "constituent {idx} rows ({c_rows}) exceeds packed rows ({rows})"
      ));
    }
    if m_off != expected_m_off || f_off != expected_f_off {
      return Err(format!(
        "constituent {idx} offset mismatch: got (m={m_off}, f={f_off}), \
         expected (m={expected_m_off}, f={expected_f_off})"
      ));
    }
    let needs_act = c_rows < rows;
    match (needs_act, active_col) {
      (true, Some(ac)) if ac == f_off + f_w => {},
      (false, None) => {},
      _ => {
        return Err(format!(
          "constituent {idx} active_col {active_col:?} disagrees with \
           rows={c_rows} vs packed_rows={rows} (f_off={f_off}, f_w={f_w})"
        ));
      },
    }
    let kind = match c["kind"].as_str() {
      Some("unit") => {
        let chip = c["chip"]
          .as_str()
          .ok_or_else(|| format!("unit constituent {idx} missing chip name"))?
          .to_owned();
        ConstituentKind::Unit { chip }
      },
      Some("map") => {
        let length = natural(&c["length"], "map constituent.length")?;
        if m_w != 1 || f_w != length + 1 {
          return Err(format!(
            "map constituent {idx} shape mismatch: m_w={m_w}, f_w={f_w}, length={length}"
          ));
        }
        ConstituentKind::Map { length }
      },
      Some("rom") => {
        let words = natural(&c["words"], "rom constituent.words")?;
        if m_w != words + 1 || f_w != 1 {
          return Err(format!(
            "rom constituent {idx} shape mismatch: m_w={m_w}, f_w={f_w}, words={words}"
          ));
        }
        ConstituentKind::Rom { words }
      },
      other => {
        return Err(format!(
          "constituent {idx} has unsupported kind {other:?}"
        ));
      },
    };
    expected_m_off = expected_m_off
      .checked_add(m_w)
      .ok_or("packed main width overflow")?;
    expected_f_off = expected_f_off
      .checked_add(f_w + usize::from(needs_act))
      .ok_or("packed fixed width overflow")?;
    constituents.push(Constituent {
      kind,
      rows: c_rows,
      main_offset: m_off,
      main_width: m_w,
      fixed_offset: f_off,
      active_col,
    });
  }
  if expected_m_off != main_width || expected_f_off != fixed_width {
    return Err(format!(
      "constituent widths sum to ({expected_m_off} main, {expected_f_off} fixed), \
       expected ({main_width} main, {fixed_width} fixed)"
    ));
  }

  let (constraints, lookups) =
    parse_graph(&sc["circuit"], main_width, fixed_width)?;
  if constraints.len() != num_constraints {
    return Err(format!(
      "constraint count mismatch: graph has {}, metadata says {num_constraints}",
      constraints.len()
    ));
  }
  if lookups.len() != num_lookups {
    return Err(format!(
      "lookup count mismatch: graph has {}, metadata says {num_lookups}",
      lookups.len()
    ));
  }
  Ok(SingleCircuitLayout {
    rows,
    main_width,
    fixed_width,
    num_constraints,
    num_lookups,
    bound,
    request,
    constituents,
    constraints,
    lookups,
  })
}

/// Read ONE `IXTLFX01` fixed-matrix block and enforce exact EOF and dimensions.
fn read_single_fixed_block(
  bytes: &[u8],
  expected_rows: usize,
  expected_width: usize,
) -> Result<RowMajorMatrix<Val>, String> {
  if bytes.len() < 24 || &bytes[..8] != FIXED_MAGIC {
    return Err("FIXED.bin does not begin with IXTLFX01 magic".into());
  }
  let read_u64 = |off: usize| -> Result<usize, String> {
    let raw = u64::from_le_bytes(
      bytes[off..off + 8].try_into().expect("8-byte header word"),
    );
    usize::try_from(raw)
      .map_err(|e| format!("FIXED.bin dimension {raw} overflows usize: {e}"))
  };
  let rows = read_u64(8)?;
  let width = read_u64(16)?;
  if rows != expected_rows || width != expected_width {
    return Err(format!(
      "FIXED.bin dimensions ({rows} x {width}) do not match single_circuit \
       ({expected_rows} x {expected_width})"
    ));
  }
  let cells = rows.checked_mul(width).ok_or("FIXED.bin cell count overflow")?;
  if cells > bytes.len() - 24 {
    return Err("truncated IXTLFX01 fixed matrix block".into());
  }
  let mut values = Vec::with_capacity(cells);
  let mut p = 24usize;
  for cell_idx in 0..cells {
    let len = usize::from(*bytes.get(p).ok_or("truncated FIXED.bin entry")?);
    if len > 8 || p + 1 + len > bytes.len() {
      return Err(format!("malformed FIXED.bin entry at cell {cell_idx}"));
    }
    let mut x = 0u64;
    for (i, &b) in bytes[p + 1..p + 1 + len].iter().enumerate() {
      x |= u64::from(b) << (8 * i);
    }
    if x >= Val::ORDER_U64 {
      return Err(format!(
        "FIXED.bin entry {x} at cell {cell_idx} is not below Goldilocks modulus"
      ));
    }
    values.push(Val::from_u64(x));
    p += 1 + len;
  }
  if p != bytes.len() {
    return Err(format!(
      "FIXED.bin has {} trailing bytes after single IXTLFX01 block",
      bytes.len() - p
    ));
  }
  Ok(RowMajorMatrix::new(values, width))
}

/// Validate `active_col` selectors and ROM row-index addresses in `fixed`.
fn validate_fixed_matrix(
  layout: &SingleCircuitLayout,
  fixed: &RowMajorMatrix<Val>,
) -> Result<(), String> {
  let fw = layout.fixed_width;
  for (idx, c) in layout.constituents.iter().enumerate() {
    if let Some(ac) = c.active_col {
      for r in 0..layout.rows {
        let got = fixed.values[r * fw + ac];
        let want = if r < c.rows { Val::ONE } else { Val::ZERO };
        if got != want {
          return Err(format!(
            "FIXED.bin active_col mismatch at constituent {idx} row {r}: \
             got {}, expected {}",
            got.as_canonical_u64(),
            want.as_canonical_u64()
          ));
        }
      }
    }
    if matches!(c.kind, ConstituentKind::Rom { .. }) {
      for r in 0..c.rows {
        let got = fixed.values[r * fw + c.fixed_offset];
        let want = Val::from_usize(r);
        if got != want {
          return Err(format!(
            "FIXED.bin ROM addr mismatch at constituent {idx} row {r}: \
             got {}, expected {r}",
            got.as_canonical_u64()
          ));
        }
      }
    }
  }
  Ok(())
}

/// Choose the lowest-FFT-cost `lookup_group_size` within the blowup budget
/// without altering the certified lookup list order.
fn choose_lookup_group(
  graph: &ConstraintGraph<Val>,
  packed_rows: usize,
  log_blowup: usize,
  ext_degree: usize,
  requested: Option<usize>,
) -> Result<usize, String> {
  let blowup = 1usize << log_blowup;
  let max_allowed = blowup + 1;
  let c_deg = graph.max_constraint_degree as usize;
  if c_deg > max_allowed {
    return Err(format!(
      "constraint degree {c_deg} exceeds blowup capacity {max_allowed} \
       (increase --log-blowup above {log_blowup})"
    ));
  }
  let deg1 = logup_max_degree(graph, 1) as usize;
  if deg1 > max_allowed {
    return Err(format!(
      "lookup degree {deg1} exceeds blowup capacity {max_allowed} \
       (increase --log-blowup above {log_blowup})"
    ));
  }
  if let Some(g) = requested {
    if !(1..=MAX_LOOKUP_GROUP).contains(&g) {
      return Err(format!(
        "--lookup-group must be in 1..={MAX_LOOKUP_GROUP}, got {g}"
      ));
    }
    let d = c_deg.max(logup_max_degree(graph, g) as usize);
    let q = (d.max(2) - 1).next_power_of_two();
    if q > blowup {
      return Err(format!(
        "--lookup-group {g} yields degree {d} (quotient {q} > blowup {blowup})"
      ));
    }
    return Ok(g);
  }
  let h = packed_rows as u128;
  let b = blowup as u128;
  let ext = ext_degree as u128;
  let fft = |n: u128| n * u128::from(n.max(2).ilog2());
  let max_g = graph.lookups.len().clamp(1, MAX_LOOKUP_GROUP);
  let mut best_g = 1usize;
  let mut best_cost = u128::MAX;
  for g in 1..=max_g {
    let d = c_deg.max(logup_max_degree(graph, g) as usize);
    let q = (d.max(2) - 1).next_power_of_two();
    if q > blowup {
      continue;
    }
    let s2 = stage2_width(graph.lookups.len(), g, ext_degree) as u128;
    let q128 = q as u128;
    let cost = (b + 1) * s2 * fft(h)
      + ext * (fft(q128 * h) + q128 * fft(b * h));
    if cost < best_cost {
      best_cost = cost;
      best_g = g;
    }
  }
  Ok(best_g)
}

/// Directly evaluate EVERY constraint on EVERY row and exact LogUp ledger
/// balance on the compiled certified `ConstraintGraph`.
fn check_packed_circuit(
  graph: &ConstraintGraph<Val>,
  main: &RowMajorMatrix<Val>,
  fixed: Option<&RowMajorMatrix<Val>>,
  claim: &[Val],
) -> Result<(), String> {
  let rows = main.height();
  let main_w = main.width;
  let fixed_w = fixed.map_or(0, |f| f.width);

  let eval_row = |row_idx: usize,
                  buf: &mut Vec<Val>,
                  ledger: &mut FxHashMap<Vec<Val>, Val>|
   -> Result<(), String> {
    let next_idx = if row_idx + 1 == rows { 0 } else { row_idx + 1 };
    let main_cur = &main.values[row_idx * main_w..(row_idx + 1) * main_w];
    let main_nxt = &main.values[next_idx * main_w..(next_idx + 1) * main_w];
    let (pre_cur, pre_nxt): (&[Val], &[Val]) = match fixed {
      Some(f) if fixed_w > 0 => (
        &f.values[row_idx * fixed_w..(row_idx + 1) * fixed_w],
        &f.values[next_idx * fixed_w..(next_idx + 1) * fixed_w],
      ),
      _ => (&[], &[]),
    };
    let vars = VarValues {
      preprocessed: [pre_cur, pre_nxt],
      main: [main_cur, main_nxt],
      stage2: [&[], &[]],
      publics: &[],
      is_first_row: if row_idx == 0 { Val::ONE } else { Val::ZERO },
      is_last_row: if row_idx + 1 == rows { Val::ONE } else { Val::ZERO },
      is_transition: if row_idx + 1 < rows { Val::ONE } else { Val::ZERO },
    };
    graph.sweep(&vars, buf);
    for (ci, &z) in graph.zeros.iter().enumerate() {
      let val = buf[z.index()];
      if val != Val::ZERO {
        return Err(format!(
          "row {row_idx}: constraint {ci} is nonzero ({})",
          val.as_canonical_u64()
        ));
      }
    }
    for l in &graph.lookups {
      let mult = buf[l.multiplicity.index()];
      if mult != Val::ZERO {
        let tuple: Vec<Val> = l.args.iter().map(|&a| buf[a.index()]).collect();
        let acc = ledger.entry(tuple).or_insert(Val::ZERO);
        *acc += mult;
      }
    }
    Ok(())
  };

  #[cfg(feature = "parallel")]
  let mut ledger: FxHashMap<Vec<Val>, Val> = (0..rows)
    .into_par_iter()
    .try_fold(
      || (Vec::with_capacity(graph.nodes.len()), FxHashMap::default()),
      |(mut buf, mut local), row_idx| {
        eval_row(row_idx, &mut buf, &mut local)?;
        Ok::<_, String>((buf, local))
      },
    )
    .try_reduce(
      || (Vec::new(), FxHashMap::default()),
      |(_, mut left), (_, right)| {
        for (k, v) in right {
          let e = left.entry(k).or_insert(Val::ZERO);
          *e += v;
        }
        Ok((Vec::new(), left))
      },
    )
    .map(|(_, m)| m)?;

  #[cfg(not(feature = "parallel"))]
  let mut ledger: FxHashMap<Vec<Val>, Val> = {
    let mut buf = Vec::with_capacity(graph.nodes.len());
    let mut acc = FxHashMap::default();
    for row_idx in 0..rows {
      eval_row(row_idx, &mut buf, &mut acc)?;
    }
    acc
  };

  // Public claim contributes +1 to the LogUp balance.
  let entry = ledger.entry(claim.to_vec()).or_insert(Val::ZERO);
  *entry += Val::ONE;

  let mut unbalanced = 0usize;
  let mut sample = String::new();
  for (tuple, net) in &ledger {
    if *net != Val::ZERO {
      if unbalanced == 0 {
        let words: Vec<u64> =
          tuple.iter().map(|v| v.as_canonical_u64()).collect();
        sample = format!("tuple={words:?} net={}", net.as_canonical_u64());
      }
      unbalanced += 1;
    }
  }
  if unbalanced > 0 {
    return Err(format!(
      "LogUp balance failed: {unbalanced} unbalanced message(s) (first: {sample})"
    ));
  }
  Ok(())
}

/// Horizontally pack all constituent main traces (`unit`, `map`, `rom`) into
/// one `rows x main_width` matrix matching `SingleCircuit.packMain`.
fn pack_main_matrix(
  layout: &SingleCircuitLayout,
  fixed: &RowMajorMatrix<Val>,
  plan: &TracePlan<'_, aiur::field::NativeField<Val>>,
  record: &aiur::Execution<aiur::field::NativeField<Val>>,
  trace: &aiur::trace::Trace<Val>,
) -> Result<RowMajorMatrix<Val>, String> {
  let packed_rows = layout.rows;
  let main_w = layout.main_width;
  let fixed_w = layout.fixed_width;

  let mut chip_index: FxHashMap<&str, usize> = FxHashMap::default();
  for (i, m) in trace.matrices.iter().enumerate() {
    chip_index.insert(m.chip.as_str(), i);
  }

  // Collect total execution + depth-range multiplicities for every static map row.
  let prog = plan.program().program();
  let n_funcs = prog.functions.len();
  let mut map_counts: Vec<Vec<u64>> = Vec::with_capacity(prog.maps.len());
  for mi in 0..prog.maps.len() {
    let counts = record
      .queries
      .fixed_counts(n_funcs + mi)
      .ok_or_else(|| format!("missing static map counts for map {mi}"))?;
    map_counts.push(counts.to_vec());
  }
  for (range_idx, global_callable) in plan.depth_range_tables() {
    let uses = trace.ranges.table(range_idx);
    let mi = global_callable
      .checked_sub(n_funcs)
      .ok_or("depth range callable index precedes maps")?;
    let counts = map_counts
      .get_mut(mi)
      .ok_or("depth range map index out of range")?;
    if uses.len() > counts.len() {
      return Err("depth range counts exceed static map table".into());
    }
    for (c, &u) in counts.iter_mut().zip(uses) {
      *c = c
        .checked_add(u)
        .filter(|&v| v < Val::ORDER_U64)
        .ok_or("map multiplicity reaches Goldilocks characteristic")?;
    }
  }

  // Build map demand table: encoded claim `[CALL, callable, input..., output...] -> mult`.
  let mut map_demand: FxHashMap<Vec<Val>, u64> = FxHashMap::default();
  for (mi, map) in prog.maps.iter().enumerate() {
    let in_rows = &prog.tables[map.input].rows;
    let out_rows = &prog.tables[map.output].rows;
    let callable_val = Val::from_u64(
      u64::try_from(n_funcs + mi)
        .map_err(|e| format!("map callable overflows u64: {e}"))?,
    );
    for (row_idx, &count) in map_counts[mi].iter().enumerate() {
      if count == 0 {
        continue;
      }
      if count >= Val::ORDER_U64 {
        return Err("map multiplicity reaches Goldilocks characteristic".into());
      }
      let in_row = &in_rows[row_idx];
      let out_row = &out_rows[row_idx];
      let mut claim = Vec::with_capacity(2 + in_row.len() + out_row.len());
      claim.push(Val::from_u64(CALL_TAG));
      claim.push(callable_val);
      claim.extend(in_row.iter().copied().map(Val::from_u64));
      claim.extend(out_row.iter().copied().map(Val::from_u64));
      let entry = map_demand.entry(claim).or_insert(0);
      *entry = entry
        .checked_add(count)
        .filter(|&v| v < Val::ORDER_U64)
        .ok_or("aggregated map multiplicity overflows field")?;
    }
  }

  let rom_counts: FxHashMap<usize, usize> =
    record.memory.width_counts().collect();

  let total_cells = packed_rows
    .checked_mul(main_w)
    .ok_or("packed main trace size overflow")?;
  let mut packed = Val::zero_vec(total_cells);

  let mut packed_chips: FxHashSet<usize> = FxHashSet::default();
  let mut packed_roms: FxHashSet<usize> = FxHashSet::default();

  for (idx, c) in layout.constituents.iter().enumerate() {
    match &c.kind {
      ConstituentKind::Unit { chip } => {
        let &mi = chip_index.get(chip.as_str()).ok_or_else(|| {
          format!("constituent {idx}: unknown chip {chip:?} in package")
        })?;
        let matrix = &trace.matrices[mi];
        if matrix.width + 1 != c.main_width {
          return Err(format!(
            "unit {chip}: trace width + 1 ({}) != constituent main_width ({})",
            matrix.width + 1,
            c.main_width
          ));
        }
        if matrix.unpadded_height > c.rows {
          return Err(format!(
            "unit {chip}: execution needs {} rows, but layout capacity is {}",
            matrix.unpadded_height, c.rows
          ));
        }
        for r in 0..matrix.unpadded_height {
          let mult = matrix.multiplicities[r];
          if mult >= Val::ORDER_U64 {
            return Err(format!(
              "unit {chip} row {r}: multiplicity reaches field characteristic"
            ));
          }
          let dst =
            &mut packed[r * main_w + c.main_offset..r * main_w + c.main_offset + c.main_width];
          dst[..matrix.width].copy_from_slice(matrix.row(r));
          dst[matrix.width] = Val::from_u64(mult);
        }
        packed_chips.insert(mi);
      },
      ConstituentKind::Map { length } => {
        for r in 0..c.rows {
          let f_base = r * fixed_w + c.fixed_offset;
          if fixed.values[f_base] == Val::ONE {
            let claim = &fixed.values[f_base + 1..f_base + 1 + *length];
            if let Some(count) = map_demand.remove(claim) {
              packed[r * main_w + c.main_offset] = Val::from_u64(count);
            }
          }
        }
      },
      ConstituentKind::Rom { words } => {
        let count = rom_counts.get(words).copied().unwrap_or(0);
        if count > c.rows {
          return Err(format!(
            "ROM width {words}: execution uses {count} cells, \
             exceeding layout capacity {}",
            c.rows
          ));
        }
        for addr in 0..count {
          let entry = record
            .memory
            .get_by_width(*words, addr)
            .ok_or_else(|| format!("missing ROM cell ({words}, {addr})"))?;
          if entry.address != addr || entry.cell.value.len() != *words {
            return Err(format!(
              "ROM cell ({words}, {addr}) address/width mismatch"
            ));
          }
          if entry.multiplicity >= Val::ORDER_U64 {
            return Err(format!(
              "ROM cell ({words}, {addr}) multiplicity reaches field characteristic"
            ));
          }
          let dst = &mut packed
            [addr * main_w + c.main_offset..addr * main_w + c.main_offset + c.main_width];
          dst[0] = Val::from_u64(entry.multiplicity);
          dst[1..].copy_from_slice(entry.cell.value);
        }
        packed_roms.insert(*words);
      },
    }
  }

  for (i, m) in trace.matrices.iter().enumerate() {
    if m.unpadded_height > 0 && !packed_chips.contains(&i) {
      return Err(format!(
        "active chip {} ({} rows) is missing from single_circuit constituents",
        m.chip, m.unpadded_height
      ));
    }
  }
  if !map_demand.is_empty() {
    let sample = map_demand
      .keys()
      .next()
      .map(|k| k.iter().map(|v| v.as_canonical_u64()).collect::<Vec<_>>())
      .unwrap_or_default();
    return Err(format!(
      "{} demanded map claim(s) missing from FIXED.bin (first: {sample:?})",
      map_demand.len()
    ));
  }
  for (&width, &count) in &rom_counts {
    if count > 0 && !packed_roms.contains(&width) {
      return Err(format!(
        "active ROM width {width} ({count} cells) missing from single_circuit constituents"
      ));
    }
  }

  Ok(RowMajorMatrix::new(packed, main_w))
}

fn make_config(
  cli: &Cli,
) -> (CommitmentParameters, FriParameters, GoldilocksBlake3V6Config) {
  let commitment =
    CommitmentParameters { log_blowup: cli.log_blowup, cap_height: 0 };
  let fri = FriParameters {
    log_final_poly_len: cli.fri_lfp,
    max_log_arity: cli.fri_mla,
    num_queries: cli.num_queries,
    commit_proof_of_work_bits: cli.commit_pow,
    query_proof_of_work_bits: cli.query_pow,
  };
  let config = GoldilocksBlake3V6Config::with_device(
    commitment,
    fri,
    FriBatching::Tensor,
    None,
  );
  (commitment, fri, config)
}

fn find_tamper_main_cell(
  layout: &SingleCircuitLayout,
  main: &RowMajorMatrix<Val>,
) -> (usize, usize, Val, String) {
  let w = main.width;
  for c in &layout.constituents {
    if let ConstituentKind::Unit { chip } = &c.kind
      && c.main_width >= 2
    {
      let act_col = c.main_offset + c.main_width - 2;
      let mult_col = c.main_offset + c.main_width - 1;
      for r in 0..c.rows {
        if main.values[r * w + act_col] == Val::ONE
          && main.values[r * w + mult_col] != Val::ZERO
        {
          return (
            r,
            act_col,
            Val::ZERO,
            format!("unit {chip} row {r} activation col {act_col} (1 -> 0)"),
          );
        }
      }
    }
  }
  (
    0,
    0,
    main.values[0] + Val::ONE,
    "packed_main(0, 0) (+1)".to_owned(),
  )
}

fn find_tamper_fixed_cell(
  layout: &SingleCircuitLayout,
  main: &RowMajorMatrix<Val>,
  fixed: &RowMajorMatrix<Val>,
) -> (usize, usize, Val, String) {
  let mw = main.width;
  let fw = fixed.width;
  for (idx, c) in layout.constituents.iter().enumerate() {
    if matches!(c.kind, ConstituentKind::Map { .. }) {
      for r in 0..c.rows {
        if main.values[r * mw + c.main_offset] != Val::ZERO {
          let col = c.fixed_offset + 1;
          let new_val = fixed.values[r * fw + col] + Val::ONE;
          return (
            r,
            col,
            new_val,
            format!("map constituent {idx} row {r} fixed col {col} (+1)"),
          );
        }
      }
    }
  }
  for (idx, c) in layout.constituents.iter().enumerate() {
    if matches!(c.kind, ConstituentKind::Rom { .. }) {
      for r in 0..c.rows {
        if main.values[r * mw + c.main_offset] != Val::ZERO {
          let col = c.fixed_offset;
          let new_val = fixed.values[r * fw + col] + Val::ONE;
          return (
            r,
            col,
            new_val,
            format!("rom constituent {idx} row {r} addr col {col} (+1)"),
          );
        }
      }
    }
  }
  for (idx, c) in layout.constituents.iter().enumerate() {
    if let Some(ac) = c.active_col
      && main.values[c.main_offset + c.main_width - 1] != Val::ZERO
    {
      return (
        0,
        ac,
        Val::ZERO,
        format!("constituent {idx} row 0 active_col {ac} (1 -> 0)"),
      );
    }
  }
  (
    0,
    0,
    fixed.values[0] + Val::ONE,
    "fixed(0, 0) (+1)".to_owned(),
  )
}

fn main() -> Result<(), Box<dyn Error>> {
  let cli = parse_cli().map_err(std::io::Error::other)?;
  let total_start = Instant::now();

  // Step 1: Parse LAYOUT.json and FIXED.bin.
  let prep_start = Instant::now();
  let layout_bytes = std::fs::read(&cli.layout)
    .map_err(|e| format!("failed to read {}: {e}", cli.layout))?;
  let layout = parse_layout(&layout_bytes)?;
  let fixed_bytes = std::fs::read(&cli.fixed)
    .map_err(|e| format!("failed to read {}: {e}", cli.fixed))?;
  let fixed =
    read_single_fixed_block(&fixed_bytes, layout.rows, layout.fixed_width)?;
  validate_fixed_matrix(&layout, &fixed)?;

  let log_height = usize::try_from(layout.rows.ilog2())?;
  if log_height + cli.log_blowup > 32 {
    return Err(format!(
      "domain 2^({log_height} + {}) exceeds Goldilocks 2-adicity 32",
      cli.log_blowup
    )
    .into());
  }
  if cli.fri_lfp > log_height {
    return Err(format!(
      "--fri-lfp {} exceeds trace log_height {log_height}",
      cli.fri_lfp
    )
    .into());
  }

  // Step 2a: Load PACKAGE.ixa and register host hint channels.
  let (raw_bytes, digest) = artifact::read(Path::new(&cli.package))?;
  let (package, embedded_args, embedded_hints, kind) =
    if raw_bytes.starts_with(PACKAGE_MAGIC) {
      let pkg = Package::decode(&raw_bytes)
        .map_err(|e| format!("invalid program package {}: {e}", cli.package))?;
      (pkg, Vec::new(), Vec::new(), "program")
    } else if raw_bytes.starts_with(EXECUTION_MAGIC) {
      let exec = ExecutionPackage::decode(&raw_bytes).map_err(|e| {
        format!("invalid execution package {}: {e}", cli.package)
      })?;
      (exec.package, exec.args, exec.hints, "execution")
    } else {
      return Err(format!(
        "unrecognized artifact magic in {} (expected IXAIURP\\0 or IXAIURX\\0)",
        cli.package
      )
      .into());
    };
  eprintln!("artifact {} ({kind}): blake3 {digest}", cli.package);

  let (program, trace_artifact) = package.traced()?;
  let mut program = program.check_field::<Val>()?;
  program.track_depth(&trace_artifact)?;
  let field = program.field();
  let address =
    field.decode(cli.override_args.as_deref().unwrap_or(&embedded_args))?;
  let mut channels = HintChannels::new();
  aiur::library::u32::register(&mut channels, field)?;
  aiur::library::u64::register(&mut channels, field)?;
  aiur::library::ixcc::register(&mut channels, field)?;
  let hints = program.prepare_hint_channels(&embedded_hints, &channels)?;
  let plan = TracePlan::new(&program, trace_artifact)?;

  // Match entry to LAYOUT.json's request callable ID (request = [CALL, id, 0..]).
  if layout.request.len() < 2
    || layout.request[0] != Val::from_u64(CALL_TAG)
    || layout.request[2..].iter().any(|&v| v != Val::ZERO)
  {
    return Err("LAYOUT.json request is not a valid [CALL, id, 0..] template".into());
  }
  let req_callable = usize::try_from(layout.request[1].as_canonical_u64())?;
  let entry = program
    .program()
    .entries
    .iter()
    .find(|e| {
      let chip_name = &plan.artifact().chips[plan.function_chips()[e.function]].name;
      plan.callable_id(chip_name) == Some(req_callable)
    })
    .or_else(|| program.program().entries.first())
    .ok_or("no selected entrypoint in package")?
    .name
    .clone();
  let prepare_ms = prep_start.elapsed().as_secs_f64() * 1000.0;

  // Step 3a: Build 1-circuit System directly from certified single_circuit.circuit.
  let setup_start = Instant::now();
  let ext_params = extension_params::<GoldilocksBlake3V6Config>();
  let mut circuit_input = CircuitInputs {
    main_width: layout.main_width,
    preprocessed: (layout.fixed_width > 0).then(|| fixed.clone()),
    constraints: layout.constraints.clone(),
    lookups: layout.lookups.clone(),
    ..Default::default()
  };
  let pre_graph = circuit_input
    .compile_graph(&ext_params)
    .map_err(|e| format!("single-circuit graph compilation failed: {e:?}"))?;
  let lookup_group_size = choose_lookup_group(
    &pre_graph,
    layout.rows,
    cli.log_blowup,
    ext_params.degree,
    cli.lookup_group,
  )?;
  circuit_input.lookup_group_size = lookup_group_size;

  let (commitment, fri, config) = make_config(&cli);
  let (system, key) = System::new(config, vec![circuit_input]);
  assert_eq!(system.circuits.len(), 1);
  let circuit = &system.circuits[0];
  let setup_ms = setup_start.elapsed().as_secs_f64() * 1000.0;

  // Step 2b: Execute and horizontally pack main trace (`packMain`).
  let exec_start = Instant::now();
  let record = hints.execute(&entry, address.clone())?;
  let execution_ms = exec_start.elapsed().as_secs_f64() * 1000.0;

  let pack_start = Instant::now();
  let public_args = plan.public_args(&record, &entry, &address)?;
  let claim = plan.public_claim(&entry, &public_args, &record.output)?;
  if claim.len() != layout.request.len() || claim[..2] != layout.request[..2] {
    return Err(format!(
      "public claim header/length (len={}, head={:?}) disagrees with \
       LAYOUT.json request (len={}, head={:?})",
      claim.len(),
      claim.iter().take(2).map(|v| v.as_canonical_u64()).collect::<Vec<_>>(),
      layout.request.len(),
      layout.request.iter().take(2).map(|v| v.as_canonical_u64()).collect::<Vec<_>>(),
    )
    .into());
  }
  let trace = plan.generate(&record, &entry, &address, false)?;
  let packed_main = pack_main_matrix(&layout, &fixed, &plan, &record, &trace)?;
  let output_words: Vec<u64> =
    record.output.iter().map(|v| v.as_canonical_u64()).collect();
  let arg_words: Vec<u64> =
    address.iter().map(|v| v.as_canonical_u64()).collect();
  let claim_words: Vec<u64> =
    claim.iter().map(|v| v.as_canonical_u64()).collect();
  let pack_ms = pack_start.elapsed().as_secs_f64() * 1000.0;

  // Step 3b: Verify every constraint and exact LogUp balance on certified graph.
  let check_start = Instant::now();
  if cli.check {
    check_packed_circuit(
      &circuit.graph,
      &packed_main,
      circuit.preprocessed.as_ref(),
      &claim,
    )?;
  }
  let check_ms = check_start.elapsed().as_secs_f64() * 1000.0;

  // Step 3c: Prove and verify 1-circuit STARK.
  eprintln!(
    "Proving certified 1-circuit STARK: rows={} main_w={} fixed_w={} s2_w={} \
     q_deg={} lg={} constraints={} lookups={} fri(mla={}, lfp={})...",
    layout.rows,
    layout.main_width,
    layout.fixed_width,
    circuit.stage_2_width,
    circuit.quotient_degree(),
    circuit.lookup_group_size,
    layout.num_constraints,
    layout.num_lookups,
    fri.max_log_arity,
    fri.log_final_poly_len,
  );
  let prove_start = Instant::now();
  let proof = system.prove_streaming(&key, &claim, vec![packed_main.clone()]);
  let prove_ms = prove_start.elapsed().as_secs_f64() * 1000.0;

  let proof_bytes = proof.to_bytes()?;
  let decoded = Proof::from_bytes(&proof_bytes)?;
  let expected_log_deg = u8::try_from(log_height)?;
  if decoded.active != [true] || decoded.log_degrees != [expected_log_deg] {
    return Err(format!(
      "unexpected proof shape: active={:?} log_degrees={:?}",
      decoded.active, decoded.log_degrees
    )
    .into());
  }

  let verify_start = Instant::now();
  system
    .verify(&claim, &decoded)
    .map_err(|e| format!("1-circuit STARK verification failed: {e:?}"))?;
  let verify_ms = verify_start.elapsed().as_secs_f64() * 1000.0;
  let total_ms = total_start.elapsed().as_secs_f64() * 1000.0;
  let rss_kb = peak_rss_kb();

  eprintln!(
    "single_circuit_prove: num_circuits=1 rows={} main_width={} fixed_width={} \
     stage2_width={} quotient_degree={} lookup_group={} constraints={} lookups={} \
     fri_mla={} fri_lfp={} proof_bytes={} prove_ms={:.2} verify_ms={:.2}",
    layout.rows,
    layout.main_width,
    layout.fixed_width,
    circuit.stage_2_width,
    circuit.quotient_degree(),
    circuit.lookup_group_size,
    layout.num_constraints,
    layout.num_lookups,
    fri.max_log_arity,
    fri.log_final_poly_len,
    proof_bytes.len(),
    prove_ms,
    verify_ms,
  );

  // Step 5: Mandatory negative controls (--controls).
  let controls_report = if cli.controls {
    eprintln!("Running negative controls (forged output, tampered main, tampered fixed)...");

    // Control 1: Forged output claim (flip LSB of last claim word).
    let mut forged_claim = claim.clone();
    let last_idx = forged_claim.len() - 1;
    forged_claim[last_idx] =
      Val::from_u64(forged_claim[last_idx].as_canonical_u64() ^ 1);
    let forged_verify_err = match system.verify(&forged_claim, &decoded) {
      Ok(()) => {
        return Err("CONTROL FAILED: verifier accepted honest proof under forged output claim".into());
      },
      Err(e) => format!("{e:?}"),
    };
    let forged_proof =
      system.prove_streaming(&key, &forged_claim, vec![packed_main.clone()]);
    let forged_reprove_err = match system.verify(&forged_claim, &forged_proof) {
      Ok(()) => {
        return Err("CONTROL FAILED: verifier accepted forged proof for wrong output claim".into());
      },
      Err(e) => format!("{e:?}"),
    };

    // Control 2: Tampered main trace cell.
    let mut tampered_main = packed_main.clone();
    let (tm_r, tm_c, tm_val, tm_desc) =
      find_tamper_main_cell(&layout, &packed_main);
    tampered_main.values[tm_r * tampered_main.width + tm_c] = tm_val;
    let tampered_main_check_rejected = check_packed_circuit(
      &circuit.graph,
      &tampered_main,
      circuit.preprocessed.as_ref(),
      &claim,
    )
    .is_err();
    let tampered_main_proof =
      system.prove_streaming(&key, &claim, vec![tampered_main]);
    let tampered_main_err = match system.verify(&claim, &tampered_main_proof) {
      Ok(()) => {
        return Err(format!(
          "CONTROL FAILED: verifier accepted tampered main trace ({tm_desc})"
        )
        .into());
      },
      Err(e) => format!("{e:?}"),
    };

    // Control 3: Tampered fixed matrix cell.
    let (
      tf_desc,
      tampered_fixed_honest_vk_err,
      tampered_fixed_self_err,
    ) = if layout.fixed_width > 0 {
      let mut tampered_fixed = fixed.clone();
      let (tf_r, tf_c, tf_val, tf_desc) =
        find_tamper_fixed_cell(&layout, &packed_main, &fixed);
      tampered_fixed.values[tf_r * tampered_fixed.width + tf_c] = tf_val;
      let tampered_input = CircuitInputs {
        main_width: layout.main_width,
        preprocessed: Some(tampered_fixed),
        constraints: layout.constraints.clone(),
        lookups: layout.lookups.clone(),
        lookup_group_size,
        ..Default::default()
      };
      let (_, _, tampered_cfg) = make_config(&cli);
      let (tampered_system, tampered_key) =
        System::new(tampered_cfg, vec![tampered_input]);
      let tampered_fixed_proof = tampered_system.prove_streaming(
        &tampered_key,
        &claim,
        vec![packed_main],
      );
      let honest_vk_err = match system.verify(&claim, &tampered_fixed_proof) {
        Ok(()) => {
          return Err(format!(
            "CONTROL FAILED: honest verifier accepted proof with tampered fixed matrix ({tf_desc})"
          )
          .into());
        },
        Err(e) => format!("{e:?}"),
      };
      let self_err = match tampered_system.verify(&claim, &tampered_fixed_proof)
      {
        Ok(()) => {
          return Err(format!(
            "CONTROL FAILED: tampered-fixed system accepted broken relation ({tf_desc})"
          )
          .into());
        },
        Err(e) => format!("{e:?}"),
      };
      (tf_desc, honest_vk_err, self_err)
    } else {
      return Err(
        "CONTROL FAILED: cannot tamper fixed matrix because fixed_width == 0"
          .into(),
      );
    };

    eprintln!(
      "Negative controls PASSED: forged_output=REJECTED, tampered_main({tm_desc})=REJECTED, \
       tampered_fixed({tf_desc})=REJECTED (honest VK & self)"
    );
    json!({
      "enabled": true,
      "all_passed": true,
      "forged_output_verify_rejected": true,
      "forged_output_verify_error": forged_verify_err,
      "forged_output_reprove_rejected": true,
      "forged_output_reprove_error": forged_reprove_err,
      "tampered_main_target": tm_desc,
      "tampered_main_check_rejected": tampered_main_check_rejected,
      "tampered_main_verify_rejected": true,
      "tampered_main_verify_error": tampered_main_err,
      "tampered_fixed_target": tf_desc,
      "tampered_fixed_honest_vk_rejected": true,
      "tampered_fixed_honest_vk_error": tampered_fixed_honest_vk_err,
      "tampered_fixed_self_rejected": true,
      "tampered_fixed_self_error": tampered_fixed_self_err,
    })
  } else {
    json!({ "enabled": false })
  };

  if let Some(path) = &cli.proof_out {
    std::fs::write(path, &proof_bytes)?;
  }

  let report = json!({
    "artifact_blake3": digest.to_string(),
    "entry": entry,
    "args": arg_words,
    "output": output_words,
    "claim": claim_words,
    "bound": layout.bound,
    "num_circuits": 1,
    "rows": layout.rows,
    "main_width": layout.main_width,
    "fixed_width": layout.fixed_width,
    "stage2_width": circuit.stage_2_width,
    "quotient_degree": circuit.quotient_degree(),
    "lookup_group_size": circuit.lookup_group_size,
    "constraints": layout.num_constraints,
    "lookups": layout.num_lookups,
    "constituents": layout.constituents.len(),
    "fri": {
      "log_blowup": commitment.log_blowup,
      "cap_height": commitment.cap_height,
      "num_queries": fri.num_queries,
      "commit_proof_of_work_bits": fri.commit_proof_of_work_bits,
      "query_proof_of_work_bits": fri.query_proof_of_work_bits,
      "max_log_arity": fri.max_log_arity,
      "log_final_poly_len": fri.log_final_poly_len,
    },
    "proof_bytes": proof_bytes.len(),
    "proof_kb": f64::from(u32::try_from(proof_bytes.len()).unwrap_or(u32::MAX)) / 1024.0,
    "prepare_ms": prepare_ms,
    "setup_ms": setup_ms,
    "execution_ms": execution_ms,
    "pack_ms": pack_ms,
    "check_ms": check_ms,
    "prove_ms": prove_ms,
    "verify_ms": verify_ms,
    "total_ms": total_ms,
    "peak_rss_kb": rss_kb,
    "verified": true,
    "controls": controls_report,
  });

  if let Some(path) = &cli.report_out {
    serde_json::to_writer_pretty(
      std::io::BufWriter::new(std::fs::File::create(path)?),
      &report,
    )?;
  }
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}
