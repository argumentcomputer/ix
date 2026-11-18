//! A batch system whose circuits are the Lean exporter's (`wide_export`,
//! `docs/aiur-template-lean-plan.md` §8, "`wide_export` options"), read
//! literally from its layout and fixed matrices: single chips
//! (`IChip.lower`), trace groups (`Grouped.lowerGroup`), the compiler-layout
//! map tables (`map_layout: "shared"`) and the `romCircuit` ROM tables, in
//! that order. The key, prover and verifier come from these circuits only.
//!
//! Witness generation stays in [`Backend`], which this module uses as a
//! prover-side row generator: its stage-one traces are permuted into the
//! exported order, and each ROM circuit's rows `[count, active, address,
//! words…]` become `romCircuit` rows `[mult, words…]` at row `address`, at
//! the table's exact fixed height. A `romCircuit`'s fixed `addr` column covers
//! `[0, rows)`, so these proofs carry no `MEMSEG` boundary messages.
//!
//! [`WideBackend::cross_check`] compares the exported circuits with the
//! [`Backend`]'s own lowering at pseudo-random points.
use super::{
  batch, build_system, check_system_shape,
  tables::pair_lookups,
  witness::{LookupPlan, trace_lookups},
  *,
};
use crate::trace::FunctionCircuit;
use multi_stark::{
  batch::ShardInput,
  expr::{RowOffset, Source as Column},
  graph::{ConstraintGraph, Node},
  lookup::LookupValues,
};
use serde_json::{Value, json};
use std::path::Path;

pub const LAYOUT_FORMAT: &str = "ix-wide-layout-1";
pub const INPUT_FORMAT: &str = "ix-wide-input-1";
const FIXED_MAGIC: &[u8; 8] = b"IXTLFX01";

/// What an exported table proves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Kind {
  Unit {
    chip: String,
  },
  Group {
    group: String,
  },
  /// The callables of the maps sharing the table, one count column each.
  Map {
    callables: Vec<u64>,
  },
  Rom {
    words: usize,
  },
}

pub struct Table {
  pub kind: Kind,
  pub rows: usize,
  /// The exported circuit; a map or ROM table carries its fixed matrix.
  pub circuit: CircuitInputs<Val>,
}

/// An exported Goldilocks layout (`ix-wide-layout-1`), not yet validated.
pub struct Export {
  pub tables: Vec<Table>,
  pub request: Vec<Val>,
  pub bound: u64,
}

fn natural(v: &Value) -> Result<usize, String> {
  v.as_u64()
    .and_then(|n| usize::try_from(n).ok())
    .ok_or_else(|| format!("expected a natural number, found {v}"))
}

fn scalar(v: &Value) -> Result<Val, String> {
  let n = match v {
    Value::String(s) => s.parse::<u64>().map_err(|e| format!("{s}: {e}"))?,
    _ => v.as_u64().ok_or_else(|| format!("expected a field element: {v}"))?,
  };
  if n >= Val::ORDER_U64 {
    return Err(format!("{n} is not below the Goldilocks modulus"));
  }
  Ok(Val::from_u64(n))
}

/// One `IXTLFX01` block at the start of `bytes` (`rows`, `width` as u64, then
/// every entry as a length byte and that many little-endian bytes), and the
/// bytes it used.
fn read_block(bytes: &[u8]) -> Result<(usize, usize, Vec<Val>, usize), String> {
  if bytes.len() < 24 || &bytes[..8] != FIXED_MAGIC {
    return Err("not a fixed matrix block".into());
  }
  let word = |i: usize| {
    usize::try_from(u64::from_le_bytes(
      bytes[i..i + 8].try_into().expect("eight bytes"),
    ))
    .map_err(|e| format!("fixed matrix dimension overflow: {e}"))
  };
  let (rows, width) = (word(8)?, word(16)?);
  let cells = rows.checked_mul(width).ok_or("fixed matrix size overflow")?;
  // Every entry takes at least its length byte.
  if cells > bytes.len() - 24 {
    return Err("truncated fixed matrix block".into());
  }
  let mut values = Vec::with_capacity(cells);
  let mut p = 24;
  for _ in 0..cells {
    let len = usize::from(*bytes.get(p).ok_or("truncated fixed matrix block")?);
    if len > 8 || p + 1 + len > bytes.len() {
      return Err("bad fixed matrix entry".into());
    }
    let mut x = 0u64;
    for (i, &b) in bytes[p + 1..p + 1 + len].iter().enumerate() {
      x |= u64::from(b) << (8 * i);
    }
    if x >= Val::ORDER_U64 {
      return Err("fixed entry is not below the modulus".into());
    }
    values.push(Val::from_u64(x));
    p += 1 + len;
  }
  Ok((rows, width, values, p))
}

/// A circuit as the exporter writes it (the graph format of
/// `Export.parseGraph`): nodes in topological order; variable `v < width` is
/// main column `v` and `width ≤ v` fixed column `v − width`; every `zeros`
/// node is a constraint and every lookup is `push(node m, [node a…])`.
fn circuit_inputs(
  v: &Value,
  fixed: Option<RowMajorMatrix<Val>>,
) -> Result<CircuitInputs<Val>, String> {
  let width = natural(&v["width"])?;
  let fixed_width = v.get("fixed_width").map_or(Ok(0), natural)?;
  if fixed.as_ref().map_or(0, |m| m.width) != fixed_width {
    return Err("a circuit's fixed width differs from its fixed matrix".into());
  }
  let column = |x: usize| {
    u32::try_from(x).map_err(|e| format!("column {x} overflows u32: {e}"))
  };
  let raw = v["nodes"].as_array().ok_or("graph without nodes")?;
  let mut nodes: Vec<Expr<Val>> = Vec::with_capacity(raw.len());
  for (i, n) in raw.iter().enumerate() {
    let n = n.as_array().ok_or("bad graph node")?;
    let op = n.first().and_then(Value::as_str).ok_or("bad graph node")?;
    let child = |k: usize| -> Result<Expr<Val>, String> {
      let c = n.get(k).map_or(Err("missing operand".to_owned()), natural)?;
      if c >= i {
        return Err("graph nodes are not in topological order".into());
      }
      Ok(nodes[c].clone())
    };
    let expr = match op {
      "const" => {
        Expr::constant(scalar(n.get(1).ok_or("constant without value")?)?)
      },
      "var" => {
        let x =
          n.get(1).map_or(Err("variable without index".to_owned()), natural)?;
        if x < width {
          Expr::main(column(x)?)
        } else if x < width + fixed_width {
          Expr::preprocessed(column(x - width)?)
        } else {
          return Err(format!(
            "variable {x} outside {width} main and {fixed_width} fixed columns"
          ));
        }
      },
      "add" => child(1)? + child(2)?,
      "sub" => child(1)? - child(2)?,
      "mul" => child(1)? * child(2)?,
      "neg" => -child(1)?,
      _ => return Err(format!("unknown graph node {op}")),
    };
    nodes.push(expr);
  }
  let node = |x: &Value| -> Result<Expr<Val>, String> {
    nodes
      .get(natural(x)?)
      .cloned()
      .ok_or_else(|| "graph root out of range".into())
  };
  let constraints = v["zeros"]
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
      let args =
        l.get(1).and_then(Value::as_array).ok_or("lookup without arguments")?;
      Ok(Lookup::push(m, args.iter().map(node).collect::<Result<_, String>>()?))
    })
    .collect::<Result<_, String>>()?;
  Ok(CircuitInputs {
    main_width: width,
    preprocessed: fixed,
    constraints,
    lookups,
    ..Default::default()
  })
}

impl Export {
  /// Parse the exporter's layout and its fixed file (one `IXTLFX01` block per
  /// map and ROM table, in table order). Only Goldilocks layouts with
  /// compiler-layout map tables are accepted.
  pub fn parse(layout: &[u8], fixed: &[u8]) -> Result<Self, String> {
    let out: Value = serde_json::from_slice(layout)
      .map_err(|e| format!("wide layout: {e}"))?;
    if out["format"] != LAYOUT_FORMAT {
      return Err("not a wide stage layout".into());
    }
    if out["modulus"].as_str() != Some(Val::ORDER_U64.to_string().as_str()) {
      return Err("the wide layout is not over Goldilocks".into());
    }
    let mut rest = fixed;
    let mut tables = vec![];
    for t in out["tables"].as_array().ok_or("wide layout without tables")? {
      let text = |key: &str| {
        t[key]
          .as_str()
          .map(str::to_owned)
          .ok_or_else(|| format!("table without {key}"))
      };
      let rows = natural(&t["rows"])?;
      let kind = match t["kind"].as_str() {
        Some("unit") => Kind::Unit { chip: text("chip")? },
        Some("group") => Kind::Group { group: text("group")? },
        Some("map_shared") => Kind::Map {
          callables: t["maps"]
            .as_array()
            .ok_or("shared map table without maps")?
            .iter()
            .map(|m| natural(&m["callable"]).map(|c| c as u64))
            .collect::<Result<_, _>>()?,
        },
        Some("rom") => Kind::Rom { words: natural(&t["words"])? },
        other => return Err(format!("unsupported wide table kind {other:?}")),
      };
      let fixed = if matches!(kind, Kind::Unit { .. } | Kind::Group { .. }) {
        None
      } else {
        let (r, w, values, used) = read_block(rest)?;
        rest = &rest[used..];
        if r != rows || w == 0 {
          return Err("a fixed block does not have its table's shape".into());
        }
        Some(RowMajorMatrix::new(values, w))
      };
      let circuit = circuit_inputs(&t["circuit"], fixed)?;
      tables.push(Table { kind, rows, circuit });
    }
    if !rest.is_empty() {
      return Err("trailing fixed blocks".into());
    }
    let request = out["request"]
      .as_array()
      .ok_or("wide layout without request")?
      .iter()
      .map(scalar)
      .collect::<Result<_, _>>()?;
    let bound = out["bound"].as_u64().ok_or("wide layout without bound")?;
    Ok(Self { tables, request, bound })
  }
}

impl<B: WitnessField> Backend<'_, '_, B> {
  /// This backend's circuit indices in the exporter's table order: single
  /// chips, then groups (each in layout order), then the map tables, then the
  /// ROM circuits by width.
  pub fn wide_order(&self) -> Result<Vec<usize>, String> {
    let layout = self.plan.layout()?;
    let singles = (0..self.members.len())
      .filter(|&ci| matches!(layout.circuits[ci], FunctionCircuit::Chip(_)));
    let groups = (0..self.members.len())
      .filter(|&ci| matches!(layout.circuits[ci], FunctionCircuit::Group(_)));
    Ok(
      singles
        .chain(groups)
        .chain(self.members.len()..self.system.circuits.len())
        .collect(),
    )
  }

  /// The exporter's input (`ix-wide-input-1`) for this backend's circuits,
  /// with `capacities` (exporter order, [`Self::wide_order`]) as the table
  /// rows: every map kept (`all_maps`) in the compiler's layout
  /// (`map_layout: "shared"`), power-of-two rows, and one ROM table per
  /// memory width whose capacity becomes its fixed height. `artifact` must
  /// hold the package this backend was built from; `artifact_blake3` names
  /// its contents, so that a cache keyed by the input tells artifacts apart.
  pub fn wide_input(
    &self,
    artifact: &Path,
    artifact_blake3: &str,
    entry: &str,
    capacities: &[usize],
  ) -> Result<Value, String> {
    let order = self.wide_order()?;
    if capacities.len() != order.len() {
      return Err(format!(
        "expected {} wide table capacities, got {}",
        order.len(),
        capacities.len()
      ));
    }
    let layout = self.plan.layout()?;
    let functions = self.members.len();
    let roms = functions + self.tables.len();
    let (mut circuits, mut groups, mut rom) = (vec![], vec![], vec![]);
    for (&ci, &cap) in order.iter().zip(capacities) {
      if ci < functions {
        match layout.circuits[ci] {
          FunctionCircuit::Chip(c) => circuits.push(
            json!({"chip": self.plan.artifact.chips[c].name, "cap": cap}),
          ),
          FunctionCircuit::Group(g) => {
            groups.push(json!({"group_index": g, "cap": cap}));
          },
        }
      } else if ci >= roms {
        rom.push(json!([self.rom.widths[ci - roms], cap]));
      }
    }
    Ok(json!({
      "format": INPUT_FORMAT, "field": "goldilocks",
      "artifact": artifact, "artifact_blake3": artifact_blake3,
      "circuits": circuits, "groups": groups, "rom": rom, "entry": entry,
      "all_maps": true, "pow2": true, "map_layout": "shared",
    }))
  }
}

/// Where an exported circuit's witness comes from: the [`Backend`] circuit
/// `ci`, and for a ROM its payload width and fixed height.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Source {
  Function { ci: usize },
  Table { ci: usize },
  Rom { ci: usize, words: usize, rows: usize },
}

impl Source {
  const fn ci(self) -> usize {
    match self {
      Self::Function { ci } | Self::Table { ci } | Self::Rom { ci, .. } => ci,
    }
  }
}

/// Exported circuits and their system, over a [`Backend`] that generates
/// the rows.
pub struct WideBackend<'p, 'a, B: WitnessField = PrimeField> {
  rust: Backend<'p, 'a, B>,
  system: System<GoldilocksBlake3Config>,
  key: ProverKey<GoldilocksBlake3Config>,
  names: Vec<String>,
  sources: Vec<Source>,
  lookup_plans: Vec<LookupPlan>,
  request: Vec<Val>,
  bound: u64,
}

/// What [`WideBackend::cross_check`] compared.
#[derive(Clone, Debug, Serialize)]
pub struct CrossCheck {
  pub trials: usize,
  pub function_circuits: usize,
  pub map_tables: usize,
  pub rom_tables: usize,
  pub mismatches: Vec<String>,
}

impl<'p, 'a, B: WitnessField> WideBackend<'p, 'a, B> {
  /// Adopt `export` as the system of `rust`'s program. Every exported table
  /// must be the one [`Backend::wide_order`] places there, with the same main
  /// width (and, for a map table, the same maps); a ROM table must be
  /// `romCircuit w` (main `[mult, words…]`, fixed `addr` = row index). The
  /// circuits themselves are taken as exported. Map tables get the lookup
  /// pairing rule of [`Backend`]'s fixed tables; every circuit is then
  /// tuned as in [`Backend`] (`build_system`).
  pub fn new(rust: Backend<'p, 'a, B>, export: Export) -> Result<Self, String> {
    if !rust.segmented_memory {
      return Err("a wide stage is proved as a batch".into());
    }
    let order = rust.wide_order()?;
    if export.tables.len() != order.len() {
      return Err(format!(
        "the export has {} tables, the program {} circuits",
        export.tables.len(),
        order.len()
      ));
    }
    let layout = rust.plan.layout()?;
    let functions = rust.members.len();
    let roms = functions + rust.tables.len();
    let callables = rust.plan.program.program.functions.len();
    let mut inputs = Vec::with_capacity(order.len());
    let mut names = Vec::with_capacity(order.len());
    let mut sources = Vec::with_capacity(order.len());
    for (position, (table, &ci)) in
      export.tables.into_iter().zip(&order).enumerate()
    {
      let name = &rust.names[ci];
      let mut circuit = table.circuit;
      let (expected, source) = if ci < functions {
        let kind = match layout.circuits[ci] {
          FunctionCircuit::Chip(c) => {
            Kind::Unit { chip: rust.plan.artifact.chips[c].name.clone() }
          },
          FunctionCircuit::Group(g) => {
            Kind::Group { group: rust.plan.artifact.groups[g].name.clone() }
          },
        };
        (kind, Source::Function { ci })
      } else if ci < roms {
        let maps = rust.tables[ci - functions].maps();
        let pair =
          pair_lookups(maps.len(), table.rows, rust.parameters.log_blowup);
        circuit.lookup_group_size = if pair { 2 } else { 1 };
        let kind = Kind::Map {
          callables: maps.iter().map(|&m| (callables + m) as u64).collect(),
        };
        (kind, Source::Table { ci })
      } else {
        let words = rust.rom.widths[ci - roms];
        let addresses = circuit.preprocessed.as_ref().is_some_and(|f| {
          f.width == 1
            && f
              .values
              .iter()
              .enumerate()
              .all(|(i, &a)| a == Val::from_usize(i))
        });
        if circuit.main_width != words + 1
          || !addresses
          || !table.rows.is_power_of_two()
          || !circuit.constraints.is_empty()
          || circuit.lookups.len() != 1
        {
          return Err(format!(
            "wide table {position} ({name}) is not romCircuit {words}"
          ));
        }
        (Kind::Rom { words }, Source::Rom { ci, words, rows: table.rows })
      };
      if table.kind != expected {
        return Err(format!(
          "wide table {position} is {:?}, expected {expected:?}",
          table.kind
        ));
      }
      let rust_circuit = &rust.system.circuits[ci];
      if !matches!(source, Source::Rom { .. })
        && (circuit.main_width != rust_circuit.main_width
          || circuit.preprocessed.as_ref().map_or(0, |f| f.height())
            != rust_circuit.preprocessed_height)
      {
        return Err(format!("wide table {position} ({name}) differs in shape"));
      }
      inputs.push(circuit);
      names.push(name.clone());
      sources.push(source);
    }
    #[cfg(feature = "cuda")]
    let device = Some(rust.device);
    #[cfg(not(feature = "cuda"))]
    let device = None;
    let (system, key) = build_system(inputs, &names, rust.parameters, device)?;
    let lookup_plans = system
      .circuits
      .iter()
      .map(|circuit| LookupPlan::compile(&circuit.graph))
      .collect::<Result<_, _>>()?;
    Ok(Self {
      rust,
      system,
      key,
      names,
      sources,
      lookup_plans,
      request: export.request,
      bound: export.bound,
    })
  }

  pub const fn parameters(&self) -> Parameters {
    self.rust.parameters
  }

  /// The row generator.
  pub const fn rows(&self) -> &Backend<'p, 'a, B> {
    &self.rust
  }

  /// The exporter's lookup bound (`bound` of its layout).
  pub const fn bound(&self) -> u64 {
    self.bound
  }

  pub fn statistics(&self) -> Vec<CircuitStatistics> {
    self
      .system
      .circuits
      .iter()
      .zip(&self.names)
      .map(|(c, name)| CircuitStatistics {
        name: name.clone(),
        stage1_width: c.main_width,
        stage2_width: c.stage_2_width,
        preprocessed_width: c.preprocessed_width,
        preprocessed_height: c.preprocessed_height,
        lookups: c.num_lookups,
        lookup_group_size: c.lookup_group_size,
        quotient_degree: c.quotient_degree(),
      })
      .collect()
  }

  pub fn claim(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
  ) -> Result<Vec<Val>, String> {
    self.rust.claim(entry, args, output)
  }

  /// Whether `claim` has the shape of the exporter's request `[CALL, id,
  /// 0…]`: the same length, call tag and callable.
  pub fn check_request(&self, claim: &[Val]) -> Result<(), String> {
    if claim.len() != self.request.len()
      || claim.get(..2) != self.request.get(..2)
      || self.request.iter().skip(2).any(|&x| x != Val::ZERO)
    {
      return Err(
        "the claim does not have the exported request's shape".into(),
      );
    }
    Ok(())
  }

  pub fn verifying_key_bytes(&self) -> Result<Vec<u8>, String> {
    Ok(stark_key::to_bytes(
      &self.system,
      self.parameters().commitment(),
      self.parameters().fri(),
    ))
  }

  /// Unpadded rows per exported circuit; a map table's are its height and a
  /// ROM table's its stored cells, at most its height.
  pub fn execution_rows(&self, record: &Execution<B>) -> Vec<usize> {
    let rows = self.rust.execution_rows(record);
    self.sources.iter().map(|s| rows[s.ci()]).collect()
  }

  pub fn execution_statistics(
    &self,
    record: &Execution<B>,
  ) -> ExecutionStatistics {
    let rust = self.rust.execution_statistics(record);
    ExecutionStatistics {
      log_blowup: rust.log_blowup,
      extension_degree: rust.extension_degree,
      circuits: self
        .statistics()
        .into_iter()
        .zip(&self.sources)
        .map(|(shape, source)| {
          let measured = &rust.circuits[source.ci()];
          CircuitMeasurements {
            shape,
            rows: measured.rows,
            cache_hits: measured.cache_hits,
          }
        })
        .collect(),
    }
  }

  /// Power-of-two log heights covering `rows` with `headroom`; fixed tables
  /// (maps and ROMs) keep their height, which must cover their rows.
  pub fn normalized_log_heights(
    &self,
    rows: &[usize],
    headroom: u8,
  ) -> Result<Vec<u8>, String> {
    if rows.len() != self.system.circuits.len() {
      return Err(format!(
        "expected {} circuit row counts, got {}",
        self.system.circuits.len(),
        rows.len()
      ));
    }
    rows
      .iter()
      .zip(&self.system.circuits)
      .enumerate()
      .map(|(index, (&count, circuit))| {
        let height = circuit.preprocessed_height;
        if height != 0 {
          if count > height {
            return Err(format!(
              "fixed circuit {index} has {count} rows, more than its height {height}"
            ));
          }
          return u8::try_from(height.ilog2())
            .map_err(|e| format!("fixed circuit {index} log height: {e}"));
        }
        let base = count
          .max(2)
          .checked_next_power_of_two()
          .ok_or_else(|| format!("circuit {index} row count {count} overflows"))?
          .ilog2();
        base
          .checked_add(u32::from(headroom))
          .and_then(|log| u8::try_from(log).ok())
          .filter(|&log| log <= 26)
          .ok_or_else(|| {
            format!(
              "circuit {index} normalized log height exceeds 2^26 (rows={count}, headroom={headroom})"
            )
          })
      })
      .collect()
  }

  /// `(payload_width, circuit_index)` of every ROM table, by width.
  pub fn memory_circuits(&self) -> Vec<(usize, usize)> {
    self
      .sources
      .iter()
      .enumerate()
      .filter_map(|(i, s)| match *s {
        Source::Rom { words, .. } => Some((words, i)),
        _ => None,
      })
      .collect()
  }

  /// `romCircuit` rows from a [`Backend`] ROM trace: cell `[count, 1,
  /// address, words…]` at row `address` as `[count, words…]`, zero rows
  /// elsewhere, `rows` high.
  fn rom_rows(
    trace: &RowMajorMatrix<Val>,
    words: usize,
    rows: usize,
  ) -> Result<RowMajorMatrix<Val>, String> {
    let width = words + 1;
    if trace.width != words + 3 {
      return Err("ROM trace width mismatch".into());
    }
    let mut values =
      Val::zero_vec(rows.checked_mul(width).ok_or("ROM size overflow")?);
    let mut used = vec![false; rows];
    for row in trace.values.chunks_exact(trace.width) {
      if row[1] == Val::ZERO {
        if row.iter().any(|&x| x != Val::ZERO) {
          return Err("nonzero ROM padding".into());
        }
        continue;
      }
      let address =
        usize::try_from(row[2].as_canonical_u64()).unwrap_or(usize::MAX);
      if row[1] != Val::ONE
        || address >= rows
        || std::mem::replace(&mut used[address], true)
      {
        return Err(format!(
          "ROM:{words} cell at address {address} outside 0..{rows}"
        ));
      }
      let dest = &mut values[address * width..(address + 1) * width];
      dest[0] = row[0];
      dest[1..].copy_from_slice(&row[3..]);
    }
    Ok(RowMajorMatrix::new(values, width))
  }

  fn witness(&self, traces: Vec<RowMajorMatrix<Val>>) -> SystemWitness<Val> {
    let lookups = if self.rust.gpu_lookup_only {
      traces
        .iter()
        .zip(&self.lookup_plans)
        .map(|(trace, plan)| {
          LookupValues::shape_only(trace.height(), plan.widths())
        })
        .collect()
    } else {
      let lookups = |(ci, trace): (usize, &RowMajorMatrix<Val>)| {
        trace_lookups(
          &self.lookup_plans[ci],
          trace,
          self.system.circuits[ci].preprocessed.as_ref(),
        )
      };
      #[cfg(feature = "parallel")]
      let lookups = traces.par_iter().enumerate().map(lookups).collect();
      #[cfg(not(feature = "parallel"))]
      let lookups = traces.iter().enumerate().map(lookups).collect();
      lookups
    };
    SystemWitness { traces, lookups }
  }

  /// Prove a single-shard execution padded to `log_heights` (every circuit
  /// active, fixed tables at their height), with no boundary messages.
  pub fn prove_normalized(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    record: Execution<B>,
    log_heights: &[u8],
  ) -> Result<(Vec<Val>, BatchProof), String> {
    if log_heights.len() != self.system.circuits.len() {
      return Err(format!(
        "expected {} normalized circuit log heights, got {}",
        self.system.circuits.len(),
        log_heights.len()
      ));
    }
    let rows = self.execution_rows(&record);
    for (index, ((&log, circuit), &rows)) in
      log_heights.iter().zip(&self.system.circuits).zip(&rows).enumerate()
    {
      if !(1..=26).contains(&log) {
        return Err(format!(
          "circuit {index} log height {log} must be in 1..=26"
        ));
      }
      if circuit.preprocessed_height != 0
        && circuit.preprocessed_height != 1 << log
      {
        return Err(format!(
          "fixed circuit {index} requires height {}, got 2^{log}",
          circuit.preprocessed_height
        ));
      }
      if rows > 1 << log {
        return Err(format!(
          "circuit {index} has {rows} unpadded rows, exceeding normalized height 2^{log}"
        ));
      }
    }
    check_system_shape(
      &self.system,
      self.parameters(),
      &vec![true; log_heights.len()],
      log_heights,
    )?;
    let claim = self.claim(entry, args, output)?;
    let mut generated = self.rust.generate_stage_1(&record, entry, args)?;
    drop(record);
    let convert = |(source, &log): (&Source, &u8)| {
      let height = 1usize << log;
      match *source {
        Source::Function { ci } | Source::Table { ci } => {
          let mut trace = std::mem::replace(
            &mut generated[ci],
            RowMajorMatrix::new(vec![], 1),
          );
          if trace.height() > height {
            return Err(format!("{} trace exceeds 2^{log}", self.names[ci]));
          }
          trace.values.resize(trace.width * height, Val::ZERO);
          Ok(trace)
        },
        Source::Rom { ci, words, rows } => {
          Self::rom_rows(&generated[ci], words, rows)
        },
      }
    };
    let traces = self
      .sources
      .iter()
      .zip(log_heights)
      .map(convert)
      .collect::<Result<Vec<_>, String>>()?;
    drop(generated);
    let witness = self.witness(traces);
    let proof = self.system.prove_batch(
      &self.key,
      vec![ShardInput { claims: vec![claim.clone()], witness }],
      vec![],
    );
    self.verify_batch(entry, args, output, &proof)?;
    Ok((claim, proof))
  }

  /// Verify with the exported system and the public call alone.
  pub fn verify_batch(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    proof: &BatchProof,
  ) -> Result<(), String> {
    batch::verify(
      &self.system,
      self.parameters().log_blowup,
      &[self.claim(entry, args, output)?],
      proof,
    )
  }

  /// Compare every exported circuit with [`Backend`]'s lowering of the same
  /// circuit at `trials` pseudo-random points: function circuits and map
  /// tables as constraint values (nonzero, as a set) and lookup messages (as
  /// a multiset), map tables also by their fixed matrices; a ROM table
  /// through the row conversion, its message at `[mult, words…]` with fixed
  /// `addr` against the [`Backend`] ROM's pull at `[mult, 1, addr, words…]`.
  pub fn cross_check(&self, trials: usize) -> Result<CrossCheck, String> {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = || {
      seed ^= seed << 13;
      seed ^= seed >> 7;
      seed ^= seed << 17;
      Val::from_u64(seed % Val::ORDER_U64)
    };
    let mut report = CrossCheck {
      trials,
      function_circuits: 0,
      map_tables: 0,
      rom_tables: 0,
      mismatches: vec![],
    };
    for (position, source) in self.sources.iter().enumerate() {
      let lean = &self.system.circuits[position];
      let rust = &self.rust.system.circuits[source.ci()];
      let name = &self.names[position];
      let mut same = true;
      match *source {
        Source::Function { .. } | Source::Table { .. } => {
          if matches!(source, Source::Function { .. }) {
            report.function_circuits += 1;
          } else {
            report.map_tables += 1;
            same &= lean.preprocessed.as_ref().map(|m| &m.values)
              == rust.preprocessed.as_ref().map(|m| &m.values);
          }
          same &= lean.main_width == rust.main_width
            && lean.preprocessed_width == rust.preprocessed_width
            && lean.num_lookups == rust.num_lookups;
          for _ in 0..trials {
            if !same {
              break;
            }
            let main: Vec<Val> = (0..lean.main_width).map(|_| next()).collect();
            let fixed: Vec<Val> =
              (0..lean.preprocessed_width).map(|_| next()).collect();
            same &= point(&lean.graph, &main, &fixed)?
              == point(&rust.graph, &main, &fixed)?;
          }
        },
        Source::Rom { words, .. } => {
          report.rom_tables += 1;
          same &= lean.graph.zeros.is_empty() && lean.num_lookups == 1;
          for _ in 0..trials {
            if !same {
              break;
            }
            let main: Vec<Val> = (0..=words).map(|_| next()).collect();
            let address = next();
            let mut row = vec![main[0], Val::ONE, address];
            row.extend_from_slice(&main[1..]);
            let ours = lookup(&lean.graph, 0, &main, &[address])?;
            let theirs = lookup(&rust.graph, 0, &row, &[])?;
            same &= ours == theirs;
          }
        },
      }
      if !same {
        report.mismatches.push(format!("{position}: {name}"));
      }
    }
    if report.mismatches.is_empty() {
      Ok(report)
    } else {
      Err(format!(
        "the exported circuits differ from the Rust lowering: {}",
        report.mismatches.join(", ")
      ))
    }
  }
}

/// Node values of a one-row graph at `(main, fixed)`; `None` for nodes that
/// read another row, stage two, publics or row selectors.
fn evaluate(
  graph: &ConstraintGraph<Val>,
  main: &[Val],
  fixed: &[Val],
) -> Vec<Option<Val>> {
  let mut values: Vec<Option<Val>> = Vec::with_capacity(graph.nodes.len());
  for node in &graph.nodes {
    let get = |id: &multi_stark::graph::NodeId| values[id.index()];
    let value = match node {
      Node::Const(k) => Some(*k),
      Node::Var(c) if c.offset == RowOffset::Current => match c.source {
        Column::Main => main.get(c.index as usize).copied(),
        Column::Preprocessed => fixed.get(c.index as usize).copied(),
        Column::Stage2 => None,
      },
      Node::Add(a, b) => get(a).zip(get(b)).map(|(a, b)| a + b),
      Node::Sub(a, b) => get(a).zip(get(b)).map(|(a, b)| a - b),
      Node::Mul(a, b) => get(a).zip(get(b)).map(|(a, b)| a * b),
      Node::Neg(a) => get(a).map(|a| -a),
      _ => None,
    };
    values.push(value);
  }
  values
}

type Message = Vec<u64>;

/// Lookup `index` of `graph` as `[multiplicity, args…]`, from its node values.
fn message(
  graph: &ConstraintGraph<Val>,
  values: &[Option<Val>],
  index: usize,
) -> Result<Message, String> {
  let l = graph.lookups.get(index).ok_or("missing lookup")?;
  std::iter::once(&l.multiplicity)
    .chain(&l.args)
    .map(|id| {
      values[id.index()]
        .map(|v| v.as_canonical_u64())
        .ok_or_else(|| "a lookup reads another row".to_owned())
    })
    .collect()
}

/// Lookup `index` of `graph` at `(main, fixed)`.
fn lookup(
  graph: &ConstraintGraph<Val>,
  index: usize,
  main: &[Val],
  fixed: &[Val],
) -> Result<Message, String> {
  message(graph, &evaluate(graph, main, fixed), index)
}

/// The nonzero constraint values (as a set) and the lookup messages (as a
/// multiset) of a one-row graph at `(main, fixed)`.
fn point(
  graph: &ConstraintGraph<Val>,
  main: &[Val],
  fixed: &[Val],
) -> Result<(Vec<u64>, Vec<Message>), String> {
  let values = evaluate(graph, main, fixed);
  let mut zeros = graph
    .zeros
    .iter()
    .map(|z| {
      values[z.index()]
        .map(|v| v.as_canonical_u64())
        .ok_or("a constraint reads another row")
    })
    .collect::<Result<Vec<_>, _>>()?;
  zeros.retain(|&z| z != 0);
  zeros.sort_unstable();
  zeros.dedup();
  let mut lookups = (0..graph.lookups.len())
    .map(|i| message(graph, &values, i))
    .collect::<Result<Vec<_>, _>>()?;
  lookups.sort();
  Ok((zeros, lookups))
}

#[cfg(test)]
mod tests {
  use super::*;

  fn block(rows: usize, values: &[u64]) -> Vec<u8> {
    let mut bytes = FIXED_MAGIC.to_vec();
    bytes.extend_from_slice(&(rows as u64).to_le_bytes());
    bytes.extend_from_slice(&((values.len() / rows) as u64).to_le_bytes());
    for &v in values {
      let le = v.to_le_bytes();
      let len = 8 - le.iter().rev().take_while(|&&b| b == 0).count();
      bytes.push(u8::try_from(len).expect("at most eight bytes"));
      bytes.extend_from_slice(&le[..len]);
    }
    bytes
  }

  /// A unit `[a, b, mult]` with `a·a − b = 0` and a pull of `[1, 7, a, b]`,
  /// and `romCircuit 1` over four addresses.
  fn layout() -> Value {
    json!({
      "format": LAYOUT_FORMAT, "modulus": Val::ORDER_U64.to_string(),
      "request": ["1", "7", "0", "0"], "bound": 9,
      "tables": [
        {"kind": "unit", "chip": "f", "rows": 2, "circuit": {
          "width": 3, "fixed_width": 0,
          "nodes": [["var", 0], ["var", 1], ["mul", 0, 0], ["sub", 2, 1],
                    ["const", "0"], ["var", 2], ["sub", 4, 5], ["const", "1"],
                    ["const", "7"]],
          "zeros": [3], "lookups": [[6, [7, 8, 0, 1]]]}},
        {"kind": "rom", "words": 1, "rows": 4, "circuit": {
          "width": 2, "fixed_width": 1,
          "nodes": [["const", "0"], ["var", 0], ["sub", 0, 1], ["const", "2"],
                    ["const", "1"], ["var", 2], ["var", 1]],
          "zeros": [], "lookups": [[2, [3, 4, 5, 6]]]}}
      ]
    })
  }

  #[test]
  fn export_parses_graphs_and_fixed_blocks_literally() {
    let bytes = serde_json::to_vec(&layout()).unwrap();
    let export = Export::parse(&bytes, &block(4, &[0, 1, 2, 3])).unwrap();
    assert_eq!(export.bound, 9);
    assert_eq!(export.request[1], Val::from_u64(7));
    let [unit, rom] = export.tables.as_slice() else { panic!("two tables") };
    assert_eq!(unit.kind, Kind::Unit { chip: "f".into() });
    assert_eq!(unit.circuit.main_width, 3);
    assert_eq!(unit.circuit.constraints.len(), 1);
    assert_eq!(rom.kind, Kind::Rom { words: 1 });
    let fixed = rom.circuit.preprocessed.as_ref().unwrap();
    assert_eq!(fixed.values, (0..4).map(Val::from_u64).collect::<Vec<_>>());
    // A missing, short or trailing fixed block, or a non-Goldilocks layout,
    // is rejected.
    assert!(Export::parse(&bytes, &[]).is_err());
    assert!(Export::parse(&bytes, &block(2, &[0, 1])).is_err());
    let mut trailing = block(4, &[0, 1, 2, 3]);
    trailing.extend(block(1, &[0]));
    assert!(Export::parse(&bytes, &trailing).is_err());
    let mut other = layout();
    other["modulus"] = "7".into();
    let other = serde_json::to_vec(&other).unwrap();
    assert!(Export::parse(&other, &block(4, &[0, 1, 2, 3])).is_err());
    assert!(
      Export::parse(&bytes, &block(4, &[0, 1, 2, Val::ORDER_U64])).is_err()
    );
  }

  #[test]
  fn rom_rows_place_each_cell_at_its_address() {
    let one = Val::ONE;
    let v = Val::from_u64;
    // [count, active, address, word], cells at addresses 0 and 1, padded.
    let trace = RowMajorMatrix::new(
      vec![v(3), one, v(0), v(10), v(1), one, v(1), v(11)]
        .into_iter()
        .chain(Val::zero_vec(8))
        .collect(),
      4,
    );
    let rows = WideBackend::<PrimeField>::rom_rows(&trace, 1, 4).unwrap();
    assert_eq!(rows.height(), 4);
    assert_eq!(rows.values[..4], [v(3), v(10), v(1), v(11)]);
    assert!(rows.values[4..].iter().all(|&x| x == Val::ZERO));
    assert!(WideBackend::<PrimeField>::rom_rows(&trace, 1, 1).is_err());
    let mut repeated = trace.clone();
    repeated.values[6] = v(0);
    assert!(WideBackend::<PrimeField>::rom_rows(&repeated, 1, 4).is_err());
  }
}
