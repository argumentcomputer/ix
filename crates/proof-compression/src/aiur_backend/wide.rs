//! The circuits of an untiled BN254 stage from the Lean exporter
//! (`wide_export`, `aiur-template-lean-plan.md` §8 "Wide stages" and
//! "`wide_export` options"): the tables of `WideStage.wide_heap_sound` (or,
//! with groups and `map_layout: "shared"`, `grouped_heap_sound_shared`), in
//! ledger order.
//!
//! - **Units**: one per laid-out single chip, `IChip.lower` of the artifact's
//!   chip with `rows` = its capacity and no fixed columns. Its main columns
//!   are the compiler's wide trace columns, so the wide witness fills it
//!   unchanged.
//! - **Groups**: one per trace group, `IGroup.lower` (main width
//!   `width + 1`, the last column the receive multiplicity), the circuit the
//!   compiler lowering builds for the group, over the same trace columns.
//! - **Maps**: one per claim length, `rows` the next power of two of its
//!   claims: `mapCircuit L` (main `mult`, fixed `sel` and the claim cells),
//!   or with `map_padding: "repeat"` `mapCircuitD L`. With `map_layout:
//!   "shared"` instead one table per input-table height in the compiler's
//!   layout (`SharedTable`, `kind "map_shared"`): fixed column 0 = 1 and the
//!   distinct input/output tables' cells, one main count column per map and
//!   lookup `push(−count_k, [CALL, id_k, cells_k])`.
//! - **ROMs**: one per memory width, `romCircuit w` (main `mult` and the `w`
//!   words, fixed `addr` = the row index), `rows` = its capacity. The height
//!   is fixed by the `addr` column, so the capacity is part of the key.
//!
//! [`input`] writes the exporter's input (`ix-wide-input-1`) for a
//! compiler's single-chip function circuits, [`grouped_input`] for a
//! grouped layout with shared map tables. [`export_cached`] runs the
//! exporter through a cache keyed by the exporter binary and the input, and
//! [`Layout::load`] reads its output. A consumer reads every circuit as its
//! [`Graph`] literally; [`Stage`] maps a grouped layout onto the compiler's
//! witness traces.

use super::{
  AiurCurve, AiurField,
  kzg::{Compiler, lookup_group_size},
  template::v2::lean::{Graph, read_block_for, same_circuit_for},
};
use crate::kzg::{CurveScalar, KzgCurve, curve::Bn254 as Bn254Curve};
use aiur::{
  field::FieldBackend,
  trace::{FunctionCircuit, TracePlan},
};
use multi_stark::{
  expr::{Expr, RowOffset, Source},
  system::CircuitInputs,
  traits::Field,
};
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
  path::{Path, PathBuf},
  process::Command,
  time::Instant,
};

const WIDE_COMPLETE_FORMAT: &str = "ix-wide-export-complete-v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WideCompleteMarker {
  format: String,
  key: String,
  exporter_blake3: String,
  input_blake3: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  artifact_blake3: Option<String>,
  layout_blake3: String,
  fixed_blake3: String,
}

fn wide_blake3_file(path: &Path) -> Result<String, String> {
  let mut hasher = blake3::Hasher::new();
  let mut file = std::fs::File::open(path)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  std::io::copy(&mut file, &mut hasher)
    .map_err(|e| format!("{}: {e}", path.display()))?;
  Ok(hasher.finalize().to_hex().to_string())
}

fn wide_check_input_artifact(
  input: &Value,
  base_dir: &Path,
) -> Result<Option<String>, String> {
  let Some(obj) = input.as_object() else {
    return Ok(None);
  };
  let artifact_path_str = obj.get("artifact").and_then(|v| v.as_str());
  let artifact_pin_str = obj.get("artifact_blake3").and_then(|v| v.as_str());
  match (artifact_path_str, artifact_pin_str) {
    (Some(_), None) => Err(
      "wide export input references an artifact without artifact_blake3".into(),
    ),
    (_, Some(pin)) => {
      let normalized = pin.to_ascii_lowercase();
      if normalized.len() != 64
        || !normalized.bytes().all(|b| b.is_ascii_hexdigit())
      {
        return Err(format!("invalid wide export artifact_blake3 pin: {pin}"));
      }
      if let Some(rel) = artifact_path_str {
        let p = Path::new(rel);
        let resolved =
          if p.is_absolute() { p.to_path_buf() } else { base_dir.join(p) };
        let actual = wide_blake3_file(&resolved)?;
        if actual != normalized {
          return Err(format!(
            "wide export artifact {} BLAKE3 {actual} differs from pinned {normalized}",
            resolved.display()
          ));
        }
      }
      Ok(Some(normalized))
    },
    (None, None) => Ok(None),
  }
}

fn verify_wide_complete(
  dir: &Path,
  key: &str,
  exporter_blake3: &str,
  input: &Value,
  input_blake3: &str,
) -> Result<(), String> {
  let complete_path = dir.join("complete");
  let raw = std::fs::read(&complete_path)
    .map_err(|e| format!("{}: {e}", complete_path.display()))?;
  if raw.is_empty() {
    return Err(format!(
      "{}: unauthenticated empty complete marker; refusing stale wide export cache",
      complete_path.display()
    ));
  }
  let marker: WideCompleteMarker =
    serde_json::from_slice(&raw).map_err(|e| {
      format!(
        "{}: malformed wide complete marker ({e})",
        complete_path.display()
      )
    })?;
  if marker.format != WIDE_COMPLETE_FORMAT
    || marker.key != key
    || marker.exporter_blake3 != exporter_blake3
    || marker.input_blake3 != input_blake3
  {
    return Err(format!(
      "{}: wide complete marker metadata differs from request",
      complete_path.display()
    ));
  }
  let expected_artifact = wide_check_input_artifact(input, dir)?;
  if marker.artifact_blake3 != expected_artifact {
    return Err(format!(
      "{}: wide complete marker artifact_blake3 differs from request",
      complete_path.display()
    ));
  }
  for (name, expected) in [
    ("input.json", marker.input_blake3.as_str()),
    ("layout.json", marker.layout_blake3.as_str()),
    ("fixed.bin", marker.fixed_blake3.as_str()),
  ] {
    let path = dir.join(name);
    let actual = wide_blake3_file(&path)?;
    if actual != expected {
      return Err(format!(
        "{}: BLAKE3 {actual} differs from wide complete marker {expected}",
        path.display()
      ));
    }
  }
  Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedMap {
  pub callable: u64,
  /// Fixed columns of the map's input then output cells.
  pub cells: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
  Unit { chip: String },
  Group { group: String, members: Vec<String> },
  Map { length: usize },
  MapShared { maps: Vec<SharedMap>, real_rows: usize },
  Rom { words: usize },
}

pub struct Table<C: AiurCurve = Bn254Curve> {
  pub kind: Kind,
  pub rows: usize,
  pub graph: Graph<C>,
  /// The exported fixed matrix of a map or ROM table, `rows` high.
  pub fixed: Option<RowMajorMatrix<CurveScalar<C>>>,
}

impl<C: AiurCurve> Table<C> {
  pub fn name(&self) -> String {
    match &self.kind {
      Kind::Unit { chip } => chip.clone(),
      Kind::Group { group, .. } => group.clone(),
      Kind::Map { length } => format!("<map:{length}>"),
      Kind::MapShared { maps, .. } => {
        let ids: Vec<String> =
          maps.iter().map(|m| m.callable.to_string()).collect();
        format!("<maps:{}>", ids.join(","))
      },
      Kind::Rom { words } => format!("<ROM:{words}>"),
    }
  }
}

pub struct Layout<C: AiurCurve = Bn254Curve> {
  pub tables: Vec<Table<C>>,
  pub request: Vec<CurveScalar<C>>,
  pub bound: u64,
}

/// The exporter's input (`ix-wide-input-1`, field `F::Curve::NAME`): every
/// function circuit of `compiler` as a unit with `capacities[i]` rows, and one
/// ROM table per memory width with the capacity of its ROM circuit. The
/// function circuits must be single chips. `artifact_blake3` names the
/// artifact's contents, so that a cache keyed by the input distinguishes
/// artifacts at one path.
#[allow(clippy::too_many_arguments)]
pub fn input<F: AiurField>(
  compiler: &Compiler<'_, '_, F>,
  capacities: &[usize],
  artifact: &Path,
  artifact_blake3: &str,
  entry: &str,
  all_maps: bool,
  pow2: bool,
  map_padding: Option<&str>,
) -> Result<Value, String> {
  let names = compiler.names();
  if capacities.len() != names.len() {
    return Err("one capacity per compiler circuit".into());
  }
  let nf = compiler.function_circuits();
  let circuits: Vec<Value> =
    (0..nf).map(|i| json!({"chip": names[i], "cap": capacities[i]})).collect();
  let rom: Vec<Value> = names
    .iter()
    .zip(capacities)
    .filter_map(|(n, &cap)| {
      let words: usize =
        n.strip_prefix("<ROM:")?.strip_suffix('>')?.parse().ok()?;
      Some(json!([words, cap]))
    })
    .collect();
  let artifact = std::path::absolute(artifact)
    .map_err(|e| format!("{}: {e}", artifact.display()))?;
  let mut v = json!({
    "format": "ix-wide-input-1", "field": F::Curve::NAME,
    "artifact": artifact, "artifact_blake3": artifact_blake3,
    "circuits": circuits, "rom": rom, "entry": entry,
    "all_maps": all_maps, "pow2": pow2,
  });
  if let Some(padding) = map_padding {
    v["map_padding"] = json!(padding);
  }
  Ok(v)
}

/// The exporter's input for a grouped plan (field `F::Curve::NAME`): every
/// ungrouped chip of the layout as a unit and every trace group as a group,
/// all with `function_rows` rows; `rom` as `(words, capacity)` per memory
/// width; every map kept in the compiler's shared layout (`all_maps`,
/// `map_layout: "shared"`) and power-of-two row counts. The entry is the chip
/// of the program entry `entry`.
pub fn grouped_input<F: AiurField>(
  plan: &TracePlan<'_, F>,
  function_rows: usize,
  rom: &[(usize, usize)],
  artifact: &Path,
  artifact_blake3: &str,
  entry: &str,
) -> Result<Value, String> {
  let layout = plan.layout()?;
  let chips = &plan.artifact().chips;
  let groups = &plan.artifact().groups;
  let mut circuits = vec![];
  let mut grouped = vec![];
  for circuit in &layout.circuits {
    match *circuit {
      FunctionCircuit::Chip(i) => {
        circuits.push(json!({"chip": chips[i].name, "cap": function_rows}))
      },
      FunctionCircuit::Group(i) => {
        grouped.push(json!({"group": groups[i].name, "cap": function_rows}))
      },
    }
  }
  let function = plan.program().entry(entry)?.function;
  let entry_chip = &chips
    [*plan.function_chips().get(function).ok_or("entry without a chip")?]
  .name;
  let artifact = std::path::absolute(artifact)
    .map_err(|e| format!("{}: {e}", artifact.display()))?;
  Ok(json!({
    "format": "ix-wide-input-1", "field": F::Curve::NAME,
    "artifact": artifact, "artifact_blake3": artifact_blake3,
    "circuits": circuits, "groups": grouped,
    "rom": rom.iter().map(|&(w, c)| json!([w, c])).collect::<Vec<_>>(),
    "entry": entry_chip,
    "all_maps": true, "pow2": true, "map_layout": "shared",
  }))
}

/// Where an export came from.
pub struct Exported<C: AiurCurve = Bn254Curve> {
  pub layout: Layout<C>,
  /// The cache entry (`exporter ‖ input` BLAKE3) or the work directory.
  pub dir: PathBuf,
  pub exporter_blake3: String,
  pub cached: bool,
  pub seconds: f64,
}

/// The exporter and cache directory named by `IX_WIDE_EXPORT` (required) and
/// `IX_WIDE_EXPORT_CACHE` (optional).
pub fn exporter_from_env() -> Result<(PathBuf, Option<PathBuf>), String> {
  let exporter = std::env::var_os("IX_WIDE_EXPORT")
    .ok_or("IX_WIDE_EXPORT (the wide_export binary) is not set")?;
  Ok((
    exporter.into(),
    std::env::var_os("IX_WIDE_EXPORT_CACHE").map(PathBuf::from),
  ))
}

/// Runs `exporter` on `input`, or replays its earlier output, loading the
/// resulting layout into curve `C`.
pub fn export_cached_for<C: AiurCurve>(
  input: &Value,
  exporter: &Path,
  cache: Option<&Path>,
  work: &Path,
) -> Result<Exported<C>, String> {
  let started = Instant::now();
  let read =
    |p: &Path| std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()));
  let binary = read(exporter)?;
  let input_bytes =
    serde_json::to_vec_pretty(input).map_err(|e| e.to_string())?;
  let exporter_blake3 = blake3::hash(&binary).to_hex().to_string();
  let mut hasher = blake3::Hasher::new();
  hasher.update(&binary);
  hasher.update(&input_bytes);
  let key = hasher.finalize().to_hex().to_string();
  let input_blake3 = blake3::hash(&input_bytes).to_hex().to_string();
  let (dir, staging) = match cache {
    Some(cache) => {
      let dir = cache.join(&key);
      if dir.exists() {
        verify_wide_complete(
          &dir,
          &key,
          &exporter_blake3,
          input,
          &input_blake3,
        )?;
        let layout = Layout::<C>::load_for(
          &dir.join("layout.json"),
          &dir.join("fixed.bin"),
        )?;
        return Ok(Exported {
          layout,
          dir,
          exporter_blake3,
          cached: true,
          seconds: started.elapsed().as_secs_f64(),
        });
      }
      let staging = cache.join(format!("{key}.tmp-{}", std::process::id()));
      (dir, staging)
    },
    None => (work.to_path_buf(), work.to_path_buf()),
  };
  std::fs::create_dir_all(&staging)
    .map_err(|e| format!("{}: {e}", staging.display()))?;
  let write = |p: &Path, b: &[u8]| {
    std::fs::write(p, b).map_err(|e| format!("{}: {e}", p.display()))
  };
  write(&staging.join("input.json"), &input_bytes)?;
  let artifact_blake3 = wide_check_input_artifact(input, &staging)?;
  let log = staging.join("export.log");
  let log_file = std::fs::File::create(&log)
    .map_err(|e| format!("{}: {e}", log.display()))?;
  let status = Command::new(exporter)
    .arg(staging.join("input.json"))
    .arg(staging.join("layout.json"))
    .arg(staging.join("fixed.bin"))
    .stderr(log_file)
    .status()
    .map_err(|e| format!("{}: {e}", exporter.display()))?;
  if !status.success() {
    return Err(format!(
      "{} failed ({status}); see {}",
      exporter.display(),
      log.display()
    ));
  }
  let layout = Layout::<C>::load_for(
    &staging.join("layout.json"),
    &staging.join("fixed.bin"),
  )?;
  if staging != dir {
    let marker = WideCompleteMarker {
      format: WIDE_COMPLETE_FORMAT.to_owned(),
      key: key.clone(),
      exporter_blake3: exporter_blake3.clone(),
      input_blake3: input_blake3.clone(),
      artifact_blake3,
      layout_blake3: wide_blake3_file(&staging.join("layout.json"))?,
      fixed_blake3: wide_blake3_file(&staging.join("fixed.bin"))?,
    };
    write(
      &staging.join("complete"),
      &serde_json::to_vec_pretty(&marker).map_err(|e| e.to_string())?,
    )?;
    // A concurrent writer may have published the same entry first; verify its
    // complete marker before adopting it.
    if std::fs::rename(&staging, &dir).is_err() {
      let _ = std::fs::remove_dir_all(&staging);
      verify_wide_complete(&dir, &key, &exporter_blake3, input, &input_blake3)?;
    }
  }
  Ok(Exported {
    layout,
    dir,
    exporter_blake3,
    cached: false,
    seconds: started.elapsed().as_secs_f64(),
  })
}

/// Runs `exporter` on `input`, or replays its earlier output, loading the
/// resulting layout over BN254.
pub fn export_cached(
  input: &Value,
  exporter: &Path,
  cache: Option<&Path>,
  work: &Path,
) -> Result<Exported, String> {
  export_cached_for::<Bn254Curve>(input, exporter, cache, work)
}

impl<C: AiurCurve> Layout<C> {
  /// Runs `exporter input output fixed` (stderr to `log`) and loads its
  /// output; returns the layout and the exporter's seconds.
  pub fn export_for(
    exporter: &Path,
    input: &Path,
    output: &Path,
    fixed: &Path,
    log: &Path,
  ) -> Result<(Self, f64), String> {
    let started = Instant::now();
    let log_file = std::fs::File::create(log)
      .map_err(|e| format!("{}: {e}", log.display()))?;
    let status = Command::new(exporter)
      .arg(input)
      .arg(output)
      .arg(fixed)
      .stderr(log_file)
      .status()
      .map_err(|e| format!("{}: {e}", exporter.display()))?;
    let seconds = started.elapsed().as_secs_f64();
    if !status.success() {
      return Err(format!(
        "{} failed ({status}); see {}",
        exporter.display(),
        log.display()
      ));
    }
    Ok((Self::load_for(output, fixed)?, seconds))
  }

  pub fn load_for(output: &Path, fixed: &Path) -> Result<Self, String> {
    use ark_ff::BigInteger;
    let read =
      |p: &Path| std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()));
    let out: Value =
      serde_json::from_slice(&read(output)?).map_err(|e| e.to_string())?;
    if out["format"] != "ix-wide-layout-1" {
      return Err("not a wide stage layout".into());
    }
    let modulus = num_bigint::BigUint::from_bytes_le(
      &<C::Fr as ark_ff::PrimeField>::MODULUS.to_bytes_le(),
    );
    if out["modulus"].as_str() != Some(modulus.to_string().as_str()) {
      return Err(format!("the wide layout is not over {}", C::NAME));
    }
    let bytes = read(fixed)?;
    let mut rest = &bytes[..];
    let mut tables = vec![];
    let count = |v: &Value, what: &str| {
      v.as_u64()
        .and_then(|n| usize::try_from(n).ok())
        .ok_or_else(|| format!("table without {what}"))
    };
    for t in out["tables"].as_array().ok_or("wide layout without tables")? {
      let rows = count(&t["rows"], "rows")?;
      let kind = match t["kind"].as_str() {
        Some("unit") => Kind::Unit {
          chip: t["chip"].as_str().ok_or("unit without chip")?.into(),
        },
        Some("group") => Kind::Group {
          group: t["group"].as_str().ok_or("group without name")?.into(),
          members: t["members"]
            .as_array()
            .ok_or("group without members")?
            .iter()
            .map(|m| m.as_str().map(String::from).ok_or("bad group member"))
            .collect::<Result<_, _>>()?,
        },
        Some("map") => Kind::Map { length: count(&t["length"], "length")? },
        Some("map_shared") => Kind::MapShared {
          maps: t["maps"]
            .as_array()
            .ok_or("shared map table without maps")?
            .iter()
            .map(|m| {
              Ok(SharedMap {
                callable: m["callable"]
                  .as_u64()
                  .ok_or("shared map without callable")?,
                cells: m["cells"]
                  .as_array()
                  .ok_or("shared map without cells")?
                  .iter()
                  .map(|c| count(c, "cell column"))
                  .collect::<Result<_, String>>()?,
              })
            })
            .collect::<Result<_, String>>()?,
          real_rows: count(&t["real_rows"], "real rows")?,
        },
        Some("rom") => Kind::Rom { words: count(&t["words"], "words")? },
        _ => return Err("unknown table kind".into()),
      };
      let graph = Graph::<C>::parse(&t["circuit"])?;
      let fixed = if matches!(kind, Kind::Unit { .. } | Kind::Group { .. }) {
        if graph.fixed_width != 0 {
          return Err("a function table has no fixed columns".into());
        }
        None
      } else {
        let ((r, w, values), used) = read_block_for::<C>(rest)?;
        rest = &rest[used..];
        if r != rows || w != graph.fixed_width {
          return Err("a fixed block does not have its table's shape".into());
        }
        Some(RowMajorMatrix::new(values, w))
      };
      tables.push(Table { kind, rows, graph, fixed });
    }
    if !rest.is_empty() {
      return Err("trailing fixed blocks".into());
    }
    let request = out["request"]
      .as_array()
      .ok_or("wide layout without request")?
      .iter()
      .map(super::template::parse_scalar_for::<C>)
      .collect::<Result<_, _>>()?;
    Ok(Self {
      tables,
      request,
      bound: out["bound"].as_u64().ok_or("wide layout without bound")?,
    })
  }
}

impl Layout<Bn254Curve> {
  pub fn export(
    exporter: &Path,
    input: &Path,
    output: &Path,
    fixed: &Path,
    log: &Path,
  ) -> Result<(Self, f64), String> {
    Self::export_for(exporter, input, output, fixed, log)
  }

  pub fn load(output: &Path, fixed: &Path) -> Result<Self, String> {
    Self::load_for(output, fixed)
  }
}

/// The compiler trace a stage table is filled from.
#[derive(Clone, Debug)]
pub enum Origin {
  /// A function circuit's trace, unchanged.
  Function(usize),
  /// A fixed map table's trace; main column `k` is the compiler's column
  /// `columns[k]`.
  Map { circuit: usize, columns: Vec<usize> },
  /// A compiler ROM trace (`[count, active, address, words…]`), converted to
  /// `romCircuit` rows and padded with zero rows to `rows`.
  Rom { circuit: usize, rows: usize },
}

/// A grouped, shared-map layout as the circuits of a proof system, each
/// mapped to the compiler trace that fills it. Circuit order is the
/// export's: units, groups, shared maps, ROMs; function circuits come first.
pub struct Stage<C: AiurCurve = Bn254Curve> {
  pub names: Vec<String>,
  /// The exported circuits read literally, with the exported fixed matrices
  /// and the compiler lowering's lookup grouping.
  pub inputs: Vec<CircuitInputs<CurveScalar<C>>>,
  pub origins: Vec<Origin>,
  pub function_circuits: usize,
  pub request: Vec<CurveScalar<C>>,
  /// `(words, capacity)` per ROM table, in table order.
  pub rom: Vec<(usize, usize)>,
  /// Constraint-graph nodes of every exported circuit.
  pub graph_nodes: usize,
}

/// `⌈count·(1 + headroom)⌉` rows, for a finite `headroom ≥ 0`.
// std has no checked float-to-integer conversion; the product is checked to
// be finite, non-negative and below 2^52 before the cast.
#[allow(
  clippy::cast_possible_truncation,
  clippy::cast_sign_loss,
  clippy::cast_precision_loss
)]
pub fn with_headroom(count: usize, headroom: f64) -> Result<usize, String> {
  if !(headroom.is_finite() && headroom >= 0.0) {
    return Err(format!(
      "headroom {headroom} is not a finite non-negative fraction"
    ));
  }
  let rows = (count as f64 * (1.0 + headroom)).ceil();
  if rows >= f64::from(1u32 << 26) * f64::from(1u32 << 26) {
    return Err(format!("{count} rows with headroom {headroom} overflow"));
  }
  Ok(rows as usize)
}

/// `(words, capacity)` per memory width: the next power of two of
/// `⌈count·(1 + headroom)⌉` (at least one row) for every compiler ROM
/// circuit's `count` in `raw` (raw compiler row counts).
pub fn rom_capacities<F: AiurField>(
  compiler: &Compiler<'_, '_, F>,
  raw: &[usize],
  headroom: f64,
) -> Result<Vec<(usize, usize)>, String> {
  compiler
    .names()
    .iter()
    .zip(raw)
    .filter_map(|(n, &count)| {
      Some((
        n.strip_prefix("<ROM:")?.strip_suffix('>')?.parse::<usize>().ok()?,
        count,
      ))
    })
    .map(|(w, count)| {
      let rows = with_headroom(count, headroom)?;
      Ok((
        w,
        rows
          .max(1)
          .checked_next_power_of_two()
          .ok_or("ROM capacity overflow")?,
      ))
    })
    .collect()
}

impl<C: AiurCurve> Stage<C> {
  /// Reads `layout` as circuits and maps every table to its compiler trace:
  /// units and groups by name, shared map tables by their callables, ROM
  /// tables by width. Every function circuit, fixed map table and ROM width
  /// of `compiler` must be covered exactly once, and the exported request
  /// must name `entry`'s call.
  pub fn new(
    layout: Layout<C>,
    compiler: &Compiler<'_, '_, C::Field>,
    plan: &TracePlan<'_, C::Field>,
    entry_claim: &[CurveScalar<C>],
    lookup_budget: Option<usize>,
  ) -> Result<Self, String> {
    let names = compiler.names();
    let nf = compiler.function_circuits();
    let functions = plan.program().program().functions.len() as u64;
    let map_tables = compiler.map_tables();
    let mut used = vec![false; names.len()];
    let mut take = |c: usize, what: &str| -> Result<usize, String> {
      if std::mem::replace(&mut used[c], true) {
        return Err(format!("{what} is exported twice"));
      }
      Ok(c)
    };
    let by_name = |name: &str| (0..nf).find(|&c| names[c] == name);
    let mut out_names = vec![];
    let mut inputs = vec![];
    let mut origins = vec![];
    let mut rom = vec![];
    let mut graph_nodes = 0;
    let mut function_circuits = 0;
    for (index, table) in layout.tables.into_iter().enumerate() {
      let name = table.name();
      let origin = match &table.kind {
        Kind::Unit { chip } => Origin::Function(take(
          by_name(chip).ok_or(format!("{chip}: not a compiler single chip"))?,
          &name,
        )?),
        Kind::Group { group, .. } => Origin::Function(take(
          by_name(group).ok_or(format!("{group}: not a compiler group"))?,
          &name,
        )?),
        Kind::MapShared { maps, .. } => {
          let mut callables: Vec<u64> =
            maps.iter().map(|m| m.callable).collect();
          callables.sort_unstable();
          let t = map_tables
            .iter()
            .position(|t| {
              let mut ids: Vec<u64> =
                t.iter().map(|&m| functions + m as u64).collect();
              ids.sort_unstable();
              ids == callables
            })
            .ok_or(format!(
              "{name}: no compiler map table has these callables"
            ))?;
          let columns = maps
            .iter()
            .map(|m| {
              map_tables[t]
                .iter()
                .position(|&k| functions + k as u64 == m.callable)
                .expect("matched callables")
            })
            .collect();
          let circuit = take(nf + t, &name)?;
          let height = compiler.inputs()[circuit]
            .preprocessed
            .as_ref()
            .map_or(0, |f| f.height());
          if height != table.rows {
            return Err(format!(
              "{name}: {} rows, the compiler table {height}",
              table.rows
            ));
          }
          Origin::Map { circuit, columns }
        },
        Kind::Rom { words } => {
          let rom_name = format!("<ROM:{words}>");
          let circuit = (0..names.len())
            .find(|&c| names[c] == rom_name)
            .ok_or(format!("{name}: no compiler ROM circuit of this width"))?;
          rom.push((*words, table.rows));
          Origin::Rom { circuit: take(circuit, &name)?, rows: table.rows }
        },
        Kind::Map { .. } => {
          return Err(format!(
            "{name}: per-length map tables need map_layout \"shared\""
          ));
        },
      };
      if matches!(origin, Origin::Function(_)) {
        if function_circuits != index {
          return Err("function tables must precede map and ROM tables".into());
        }
        function_circuits += 1;
        if table.graph.width != compiler.inputs()[index_of(&origin)].main_width
        {
          return Err(format!(
            "{name}: exported main width differs from the compiler trace"
          ));
        }
      }
      graph_nodes += table.graph.nodes.len();
      let mut input = table.graph.inputs(table.fixed);
      input.lookup_group_size = lookup_group_size::<C>(&input, lookup_budget)
        .map_err(|e| format!("{name}: {e}"))?;
      out_names.push(name);
      inputs.push(input);
      origins.push(origin);
    }
    if let Some(c) = used.iter().position(|&u| !u) {
      return Err(format!("{}: compiler circuit not exported", names[c]));
    }
    if layout.request.len() != entry_claim.len()
      || layout.request.get(..2) != entry_claim.get(..2)
    {
      return Err("the exported request is not the entry's call".into());
    }
    Ok(Self {
      names: out_names,
      inputs,
      origins,
      function_circuits,
      request: layout.request,
      rom,
      graph_nodes,
    })
  }

  /// Per table, the compiler circuit it is filled from.
  pub fn compiler_circuits(&self) -> Vec<usize> {
    self.origins.iter().map(index_of).collect()
  }

  /// Compiler row counts (raw or padded, in compiler order) in table order;
  /// ROM tables report their pinned capacity.
  pub fn rows(&self, compiler_rows: &[usize]) -> Vec<usize> {
    self
      .origins
      .iter()
      .map(|o| match *o {
        Origin::Rom { rows, .. } => rows,
        ref o => compiler_rows[index_of(o)],
      })
      .collect()
  }

  /// Fails unless every ROM width's recorded count (raw compiler rows) fits
  /// its pinned capacity.
  pub fn check_rom(&self, raw: &[usize]) -> Result<(), String> {
    for (name, origin) in self.names.iter().zip(&self.origins) {
      if let Origin::Rom { circuit, rows } = *origin
        && raw[circuit] > rows
      {
        return Err(format!(
          "{name}: the execution has {} ROM rows, the key pins {rows}; rebuild the key with a larger ROM capacity",
          raw[circuit]
        ));
      }
    }
    Ok(())
  }

  /// The compiler's main traces (compiler order) as this stage's (table
  /// order).
  pub fn traces(
    &self,
    traces: Vec<RowMajorMatrix<CurveScalar<C>>>,
  ) -> Result<Vec<RowMajorMatrix<CurveScalar<C>>>, String> {
    use p3_maybe_rayon::prelude::*;
    let mut traces: Vec<Option<RowMajorMatrix<CurveScalar<C>>>> =
      traces.into_iter().map(Some).collect();
    self
      .origins
      .iter()
      .map(|o| {
        let trace = traces
          .get_mut(index_of(o))
          .and_then(Option::take)
          .ok_or("missing compiler trace")?;
        match o {
          Origin::Function(_) => Ok(trace),
          Origin::Map { columns, .. } => {
            if columns.iter().enumerate().all(|(k, &c)| k == c)
              && columns.len() == trace.width
            {
              return Ok(trace);
            }
            let mut values =
              vec![C::FIELD.zero(); trace.height() * columns.len()];
            values
              .par_chunks_mut(columns.len().max(1))
              .zip(trace.values.par_chunks(trace.width.max(1)))
              .for_each(|(out, row)| {
                for (value, &c) in out.iter_mut().zip(columns) {
                  *value = row[c];
                }
              });
            Ok(RowMajorMatrix::new(values, columns.len()))
          },
          Origin::Rom { rows, .. } => rom_rows::<C>(&trace, *rows),
        }
      })
      .collect()
  }

  /// Compares every exported circuit with the compiler lowering's: function
  /// and map circuits at random points ([`same_circuit_for`]) and their fixed
  /// matrices entry for entry; ROM tables against `romCircuit w` and the
  /// compiler ROM circuit's lookup under the [`rom_rows`] conversion.
  pub fn rust_cross_check(
    &self,
    compiler: &Compiler<'_, '_, C::Field>,
  ) -> Result<Value, String> {
    let rust = compiler.inputs();
    let mut differing = vec![];
    let mut fixed_differing = vec![];
    let mut permuted = vec![];
    for (k, origin) in self.origins.iter().enumerate() {
      let lean = &self.inputs[k];
      let ok = match origin {
        Origin::Function(c) => {
          same_circuit_for::<C>(lean, &rust[*c], 4)?
            && lean.lookup_group_size == rust[*c].lookup_group_size
        },
        Origin::Map { circuit, columns } => {
          if !columns.iter().enumerate().all(|(i, &c)| i == c) {
            permuted.push(self.names[k].clone());
          }
          let fixed_same =
            match (&lean.preprocessed, &rust[*circuit].preprocessed) {
              (Some(a), Some(b)) => a.width == b.width && a.values == b.values,
              _ => false,
            };
          if !fixed_same {
            fixed_differing.push(self.names[k].clone());
          }
          let mut mine = rust[*circuit].clone();
          mine.main_width = columns.len();
          let relabel = |e: &Expr<CurveScalar<C>>| remap_main(e, columns);
          mine.lookups = mine
            .lookups
            .iter()
            .map(|l| {
              multi_stark::lookup::Lookup::push(
                relabel(&l.multiplicity),
                l.args.iter().map(relabel).collect(),
              )
            })
            .collect();
          mine.constraints = mine.constraints.iter().map(relabel).collect();
          same_circuit_for::<C>(lean, &mine, 4)?
            && lean.lookup_group_size == rust[*circuit].lookup_group_size
        },
        Origin::Rom { circuit, rows } => {
          let words = lean
            .main_width
            .checked_sub(1)
            .ok_or("ROM table without columns")?;
          let addr_ok = lean.preprocessed.as_ref().is_some_and(|f| {
            f.width == 1
              && f.height() == *rows
              && f
                .values
                .iter()
                .enumerate()
                .all(|(i, &v)| v == C::FIELD.from_u64(i as u64))
          });
          if !addr_ok {
            fixed_differing.push(self.names[k].clone());
          }
          rom_same::<C>(lean, &rust[*circuit], words)?
        },
      };
      if !ok {
        differing.push(self.names[k].clone());
      }
    }
    Ok(json!({
      "circuits": self.inputs.len(),
      "function_circuits": self.function_circuits,
      "differing": differing,
      "fixed_differing": fixed_differing,
      "map_columns_permuted": permuted,
      "equal": differing.is_empty() && fixed_differing.is_empty(),
    }))
  }
}

fn index_of(origin: &Origin) -> usize {
  match *origin {
    Origin::Function(c)
    | Origin::Map { circuit: c, .. }
    | Origin::Rom { circuit: c, .. } => c,
  }
}

fn remap_main<S: Clone>(e: &Expr<S>, columns: &[usize]) -> Expr<S> {
  let r = |x: &Expr<S>| Box::new(remap_main(x, columns));
  match e {
    Expr::Var(c) if c.source == Source::Main => {
      let k = columns
        .iter()
        .position(|&j| j == c.index as usize)
        .expect("permuted map column");
      let mut c = *c;
      c.index = u32::try_from(k).expect("a permuted map column fits u32");
      Expr::Var(c)
    },
    Expr::Add(a, b) => Expr::Add(r(a), r(b)),
    Expr::Sub(a, b) => Expr::Sub(r(a), r(b)),
    Expr::Mul(a, b) => Expr::Mul(r(a), r(b)),
    Expr::Neg(a) => Expr::Neg(r(a)),
    e => e.clone(),
  }
}

/// Evaluates `e` at one row, with main columns `main`, fixed columns `fixed`
/// and no next-row, selector or public variables.
fn eval<C: AiurCurve>(
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
    Expr::Add(a, b) => eval::<C>(a, main, fixed)? + eval::<C>(b, main, fixed)?,
    Expr::Sub(a, b) => eval::<C>(a, main, fixed)? - eval::<C>(b, main, fixed)?,
    Expr::Mul(a, b) => eval::<C>(a, main, fixed)? * eval::<C>(b, main, fixed)?,
    Expr::Neg(a) => -eval::<C>(a, main, fixed)?,
    _ => return Err("row selector, public or next-row variable".into()),
  })
}

/// Whether `lean` is `romCircuit words` (no constraints; one lookup
/// `push(−mult, [ROM, words, addr, words…])` over main `[mult, words…]` and
/// fixed `[addr]`) and its lookup equals the compiler ROM circuit's
/// (`[count, active, address, words…]`) on an active row under
/// [`rom_rows`], at random points.
fn rom_same<C: AiurCurve>(
  lean: &CircuitInputs<CurveScalar<C>>,
  rust: &CircuitInputs<CurveScalar<C>>,
  words: usize,
) -> Result<bool, String> {
  if !lean.constraints.is_empty()
    || lean.lookups.len() != 1
    || rust.lookups.len() != 1
    || lean.preprocessed.as_ref().map(|f| f.width) != Some(1)
    || rust.main_width != words + 3
  {
    return Ok(false);
  }
  let rom = CurveScalar::<C>::from_u64(2);
  let mut seed = 0x2545_f491_4f6c_dd1du64;
  let mut next = || {
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    CurveScalar::<C>::from_u64(seed)
  };
  for _ in 0..4 {
    let (mult, addr) = (next(), next());
    let cells: Vec<CurveScalar<C>> = (0..words).map(|_| next()).collect();
    let main: Vec<CurveScalar<C>> =
      std::iter::once(mult).chain(cells.iter().copied()).collect();
    let rust_row: Vec<CurveScalar<C>> = [mult, C::FIELD.one(), addr]
      .into_iter()
      .chain(cells.iter().copied())
      .collect();
    let tuple = |l: &multi_stark::lookup::Lookup<Expr<CurveScalar<C>>>,
                 m: &[CurveScalar<C>],
                 f: &[CurveScalar<C>]|
     -> Result<Vec<CurveScalar<C>>, String> {
      std::iter::once(&l.multiplicity)
        .chain(&l.args)
        .map(|x| eval::<C>(x, m, f))
        .collect()
    };
    let a = tuple(&lean.lookups[0], &main, &[addr])?;
    let b = tuple(&rust.lookups[0], &rust_row, &[])?;
    let expected: Vec<CurveScalar<C>> =
      [-mult, rom, CurveScalar::<C>::from_u64(words as u64), addr]
        .into_iter()
        .chain(cells.iter().copied())
        .collect();
    if a != b || a != expected {
      return Ok(false);
    }
  }
  Ok(true)
}

/// A compiler ROM trace (`[count, active, address, words…]`, consecutive
/// addresses from 0, inactive rows zero) as `rows` rows of `romCircuit`
/// (`[mult, words…]`, row `a` at address `a`, the address being the table's
/// fixed column), zero-padded.
pub fn rom_rows<C: AiurCurve>(
  trace: &RowMajorMatrix<CurveScalar<C>>,
  rows: usize,
) -> Result<RowMajorMatrix<CurveScalar<C>>, String> {
  let width = trace.width.checked_sub(2).ok_or("ROM trace without words")?;
  let mut values = Vec::with_capacity(rows * width);
  for (a, row) in trace.values.chunks(trace.width).enumerate() {
    if row[1] == C::FIELD.one() {
      if a >= rows {
        return Err(format!("ROM trace has more than its {rows} pinned rows"));
      }
      if row[2] != C::FIELD.from_u64(a as u64) {
        return Err("nonconsecutive ROM addresses".into());
      }
    } else if row.iter().any(|&x| x != C::FIELD.zero()) {
      return Err("an inactive ROM row is not zero".into());
    }
    if a < rows {
      values.push(row[0]);
      values.extend_from_slice(&row[3..]);
    }
  }
  values.resize(rows * width, C::FIELD.zero());
  Ok(RowMajorMatrix::new(values, width))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::aiur_backend::Bn254;

  #[test]
  fn rom_rows_pads_to_the_pinned_height() {
    let s = |x: u64| Bn254.from_u64(x);
    let trace = RowMajorMatrix::new(
      vec![s(3), s(1), s(0), s(7), s(1), s(1), s(1), s(8)],
      4,
    );
    let rows = rom_rows::<Bn254Curve>(&trace, 4).unwrap();
    assert_eq!(rows.width, 2);
    assert_eq!(
      rows.values,
      vec![s(3), s(7), s(1), s(8), s(0), s(0), s(0), s(0)]
    );
    assert!(rom_rows::<Bn254Curve>(&trace, 1).is_err());
  }
}
