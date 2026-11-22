//! Witness of the Lean-checked terminal constraint system (`ix-aiur-scs-v1`,
//! `plonk_export`; docs/aiur-plonk-lean-backend.md).
//!
//! The circuit's secret inputs are the file's input wires: the root table
//! (the public statement limbs, then the private pairing outputs) and every
//! other table's cells at `cell_base + row·width + column`. gnark's prover
//! computes every other wire. The input layout comes from the prepared
//! circuit (`inputs.json`, written by gnark's preparation from the pinned
//! file); a value in the wrong place fails the solve, never soundness.

use super::{Bn254, put_scalar};
use crate::aiur_backend::kzg::Compiler;
use crate::kzg::Scalar;
use aiur::{Execution, field::FieldBackend, trace::TracePlan};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::{Deserialize, Serialize};

pub const INPUTS_FORMAT: &str = "ix-aiur-scs-inputs-v1";

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct Table {
  pub name: String,
  pub cell_base: u64,
  pub rows: u32,
  pub width: u32,
}

/// The input wires of an `ix-aiur-scs-v1` file.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct Inputs {
  pub format: String,
  pub publics: usize,
  pub cells: usize,
  pub outputs: Vec<u32>,
  pub tables: Vec<Table>,
}

enum Feed {
  Root,
  /// A compiler function circuit's trace, unchanged.
  Trace(usize),
  /// A compiler ROM trace as `romCircuit` rows.
  Rom(usize),
  /// A compiler map table's count columns (`map_shared/<k>`, Lean's
  /// `sharedTablesOf`: the same tables in the same order, at their fixed
  /// heights), unchanged.
  Shared(usize),
}

/// The binary witness producer of one prepared terminal circuit.
pub struct Witness<'p, 'a> {
  plan: &'p TracePlan<'a, Bn254>,
  compiler: Compiler<'p, 'a>,
  entry: String,
  inputs: Inputs,
  feeds: Vec<Feed>,
}

/// The terminal's pairing configuration (`plonk_export` and gnark's
/// `PairingCheck` read it): the configuration's two G2 anchors.
pub fn pairing(
  plan: &TracePlan<'_, Bn254>,
  entry: &str,
  configuration: &crate::aiur_backend::pairing::final_program::Configuration,
) -> Result<super::Pairing, String> {
  Ok(super::Pairing {
    curve: "bn254",
    encoding: "affine-u80-v1",
    g2: configuration.terminal_coordinates(plan, entry)?,
  })
}

/// The stage `plonk_export` builds the constraint system for, in the
/// terminal schema's format (`ix-aiur-plonk-terminal-v1`): the function and
/// ROM circuits at these capacities and the public and output counts. The
/// exporter reads only these; the circuits' expressions come from the
/// `.ixa`, so they are left empty.
pub fn stage(
  plan: &TracePlan<'_, Bn254>,
  compiler: &Compiler<'_, '_>,
  capacities: &[usize],
  entry: &str,
  public_args: &[Scalar],
  output: &[Scalar],
) -> Result<serde_json::Value, String> {
  use crate::aiur_backend::pairing::final_program::ACCUMULATOR_WORDS;
  let claim = plan.public_claim(entry, public_args, output)?;
  if output.len() != ACCUMULATOR_WORDS || claim.len() != 4 + ACCUMULATOR_WORDS {
    return Err(
      "terminal requires two public statement limbs and 18 private outputs"
        .into(),
    );
  }
  let names = compiler.names();
  if capacities.len() != names.len() {
    return Err("wrong capacity count".into());
  }
  let nf = compiler.function_circuits();
  let rom = nf + compiler.map_tables().len();
  let circuits: Vec<_> = (0..names.len())
    .filter(|&i| i < nf || i >= rom)
    .map(|i| {
      // A ROM table's cells are `romCircuit`'s `[mult, words…]`.
      let width = compiler.inputs()[i].main_width - if i >= rom { 2 } else { 0 };
      serde_json::json!({"name": names[i], "rows": capacities[i], "main_width": width,
        "fixed_width": 0, "fixed": [], "nodes": [], "constraints": [], "lookups": []})
    })
    .collect();
  Ok(
    serde_json::json!({"format": super::TERMINAL_FORMAT, "callable": Bn254.try_to_u64(claim[1])?,
    "public_inputs": 2, "private_outputs": ACCUMULATOR_WORDS, "boolean_requests": true, "circuits": circuits}),
  )
}

impl<'p, 'a> Witness<'p, 'a> {
  /// Matches every table of `inputs` with its compiler source at these
  /// capacities (the execution's padded rows, which must be the file's), and
  /// requires every compiler circuit to feed exactly one table and the tables
  /// to tile the input wires.
  pub fn new(
    plan: &'p TracePlan<'a, Bn254>,
    compiler: Compiler<'p, 'a>,
    capacities: &[usize],
    entry: &str,
    inputs: Inputs,
  ) -> Result<Self, String> {
    let names = compiler.names();
    if inputs.format != INPUTS_FORMAT || capacities.len() != names.len() {
      return Err("SCS input layout or capacity count differs".into());
    }
    let nf = compiler.function_circuits();
    let tables = compiler.map_tables();
    let checked = plan.program();
    let program = checked.program();
    let mut used = vec![false; names.len()];
    let mut feeds = vec![];
    let rows_of = |t: &Table, index: usize| -> Result<(), String> {
      let width = u32::try_from(compiler.inputs()[index].main_width)
        .map_err(|e| e.to_string())?;
      let rom = names[index].starts_with("<ROM:");
      if t.rows as usize != capacities[index]
        || t.width != width - if rom { 2 } else { 0 }
      {
        return Err(format!(
          "{}: {}×{} in the SCS file, {}×{} here",
          t.name, t.rows, t.width, capacities[index], width
        ));
      }
      Ok(())
    };
    let mut claim = |index: usize| -> Result<(), String> {
      if std::mem::replace(&mut used[index], true) {
        return Err(format!("{} feeds two SCS tables", names[index]));
      }
      Ok(())
    };
    for t in &inputs.tables {
      let feed = if t.name == "root" {
        if t.cell_base != 0
          || t.rows != 1
          || t.width as usize != inputs.publics + inputs.outputs.len()
        {
          return Err("SCS root table is not the publics and outputs".into());
        }
        Feed::Root
      } else if let Some(k) = t.name.strip_prefix("map_shared/") {
        let k: usize =
          k.parse().map_err(|e| format!("{}: not a map table: {e}", t.name))?;
        let maps =
          tables.get(k).ok_or(format!("{}: no compiler map table", t.name))?;
        let real = maps
          .first()
          .map_or(0, |&m| program.tables[program.maps[m].input].rows.len());
        let height = if real == 0 {
          0
        } else {
          real.checked_next_power_of_two().ok_or("map table height")?
        };
        if t.width as usize != maps.len()
          || compiler.inputs()[nf + k].main_width != maps.len()
          || t.rows as usize != height
        {
          return Err(format!(
            "{}: {}×{} in the SCS file, {height}×{} here",
            t.name,
            t.rows,
            t.width,
            maps.len()
          ));
        }
        claim(nf + k)?;
        Feed::Shared(nf + k)
      } else if let Some(words) = t.name.strip_prefix("rom/") {
        let name = format!("<ROM:{words}>");
        let index = names
          .iter()
          .position(|n| *n == name)
          .ok_or(format!("{}: no compiler ROM circuit", t.name))?;
        rows_of(t, index)?;
        claim(index)?;
        Feed::Rom(index)
      } else {
        let index = names[..nf]
          .iter()
          .position(|n| *n == t.name)
          .ok_or(format!("{}: no compiler function circuit", t.name))?;
        rows_of(t, index)?;
        claim(index)?;
        Feed::Trace(index)
      };
      feeds.push(feed);
    }
    if let Some(index) = used.iter().position(|u| !u) {
      return Err(format!("{}: no SCS table", names[index]));
    }
    let mut spans: Vec<(u64, u64)> = inputs
      .tables
      .iter()
      .map(|t| {
        (t.cell_base, t.cell_base + u64::from(t.rows) * u64::from(t.width))
      })
      .collect();
    spans.sort();
    let mut end = 0;
    for (start, stop) in spans {
      if start != end {
        return Err("SCS tables do not tile the input wires".into());
      }
      end = stop;
    }
    if end != inputs.cells as u64
      || inputs
        .outputs
        .iter()
        .enumerate()
        .any(|(k, &w)| w as usize != inputs.publics + k)
    {
      return Err("SCS tables or outputs do not match the input wires".into());
    }
    Ok(Self { plan, compiler, entry: entry.into(), inputs, feeds })
  }

  pub fn inputs(&self) -> &Inputs {
    &self.inputs
  }

  /// gnark's binary witness: three big-endian u32 counts (publics, secrets,
  /// all), then the input wires in order as canonical big-endian words.
  pub fn binary(
    &self,
    record: &Execution<Bn254>,
    args: &[Scalar],
  ) -> Result<Vec<u8>, String> {
    let n = &self.inputs;
    let public_args = self.plan.public_args(record, &self.entry, args)?;
    let claim =
      self.plan.public_claim(&self.entry, &public_args, &record.output)?;
    if claim.len() != 2 + n.publics + n.outputs.len() {
      return Err("public claim width differs from the SCS root table".into());
    }
    let traces = self.compiler.generate(record, &self.entry, args)?;
    let mut out = Vec::with_capacity(12 + 32 * n.cells);
    for count in [n.publics, n.cells - n.publics, n.cells] {
      out
        .extend(u32::try_from(count).map_err(|e| e.to_string())?.to_be_bytes());
    }
    out.resize(12 + 32 * n.cells, 0);
    let words = &mut out[12..];
    let mut put = |wire: usize, value: Scalar| {
      let mut word = Vec::with_capacity(32);
      put_scalar(&mut word, value);
      words[32 * wire..32 * wire + 32].copy_from_slice(&word);
    };
    for (t, feed) in n.tables.iter().zip(&self.feeds) {
      let base = usize::try_from(t.cell_base)
        .map_err(|e| format!("{}: cell base: {e}", t.name))?;
      let matrix = |m: &RowMajorMatrix<Scalar>| -> Result<(), String> {
        if m.width != t.width as usize || m.height() > t.rows as usize {
          return Err(format!(
            "{}: the execution exceeds the SCS table",
            t.name
          ));
        }
        Ok(())
      };
      match feed {
        Feed::Root => {
          for (i, &value) in claim[2..].iter().enumerate() {
            put(base + i, value);
          }
        },
        Feed::Trace(i) | Feed::Shared(i) => {
          matrix(&traces[*i])?;
          for (k, &value) in traces[*i].values.iter().enumerate() {
            put(base + k, value);
          }
        },
        Feed::Rom(i) => {
          let rows = super::rom_rows(&traces[*i])?;
          matrix(&rows)?;
          for (k, &value) in rows.values.iter().enumerate() {
            put(base + k, value);
          }
        },
      }
    }
    Ok(out)
  }
}
