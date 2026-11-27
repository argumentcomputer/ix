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
use crate::aiur_backend::bls12_381::{self, Bls12381};
use crate::aiur_backend::kzg::Compiler;
use crate::kzg::{
  Scalar, VerifierParams,
  curve::{Bls12381 as Bls12381Curve, KzgCurve},
  field::{Bls12381Scalar, CurveScalar},
};
use aiur::{
  Execution, FieldWord,
  field::FieldBackend,
  trace::{FunctionCircuit, Placement, Polynomial, TracePlan},
};
use ark_ec::AffineRepr;
use multi_stark::traits::Algebra;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use serde::{Deserialize, Serialize};

pub const INPUTS_FORMAT: &str = "ix-aiur-scs-inputs-v1";
/// Number of private terminal output words for BLS12-381 `affine-u80-v1`
/// (`2 * (5 + 5 + 1) = 22`).
pub const BLS12_381_ACCUMULATOR_WORDS: usize = bls12_381::ACCUMULATOR_WORDS;

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

impl Inputs {
  /// Parse the input wire and table layout directly from a Lean-exported
  /// `ix-aiur-scs-v1` (`ixscs001`) binary file.
  pub fn from_ixscs(data: &[u8]) -> Result<Self, String> {
    const MAGIC: &[u8; 8] = b"ixscs001";
    const GATE_BYTES: usize = 26;
    const HINT_BYTES: usize = 9;
    if data.len() < 88 || &data[..8] != MAGIC {
      return Err("not an ix-aiur-scs-v1 file".into());
    }
    let header_u64 = |idx: usize| -> Result<usize, String> {
      let start = 8 + 8 * idx;
      let word = u64::from_le_bytes(
        data[start..start + 8].try_into().expect("8-byte header field"),
      );
      usize::try_from(word).map_err(|e| e.to_string())
    };
    let publics = header_u64(0)?;
    let outputs_len = header_u64(1)?;
    let wires = header_u64(2)?;
    let gates = header_u64(3)?;
    let commits = header_u64(5)?;
    let coeffs = header_u64(8)?;
    let tables_len = header_u64(9)?;

    let mut offset = 88usize;
    let body_end = offset
      .checked_add(outputs_len.checked_mul(4).ok_or("SCS outputs overflow")?)
      .and_then(|o| o.checked_add(coeffs.checked_mul(32)?))
      .and_then(|o| o.checked_add(gates.checked_mul(GATE_BYTES)?))
      .and_then(|o| o.checked_add(commits.checked_mul(4)?))
      .and_then(|o| o.checked_add(wires.checked_mul(HINT_BYTES)?))
      .ok_or("SCS body size overflow")?;
    if data.len() < body_end {
      return Err("truncated ix-aiur-scs-v1 file".into());
    }
    let mut outputs = Vec::with_capacity(outputs_len);
    for _ in 0..outputs_len {
      outputs.push(u32::from_le_bytes(
        data[offset..offset + 4].try_into().expect("4-byte output wire"),
      ));
      offset += 4;
    }
    offset += coeffs * 32 + gates * GATE_BYTES + commits * 4;
    let mut cells = 0usize;
    for w in 0..wires {
      let kind = data[offset + w * HINT_BYTES];
      if kind == 0 {
        if w != cells {
          return Err("SCS input wires are not a contiguous prefix".into());
        }
        cells += 1;
      }
    }
    offset += wires * HINT_BYTES;
    let mut tables = Vec::with_capacity(tables_len);
    for _ in 0..tables_len {
      if data.len() < offset + 2 {
        return Err("truncated ix-aiur-scs-v1 table header".into());
      }
      let name_len = usize::from(u16::from_le_bytes(
        data[offset..offset + 2].try_into().expect("2-byte name length"),
      ));
      offset += 2;
      if data.len() < offset + name_len + 16 {
        return Err("truncated ix-aiur-scs-v1 table entry".into());
      }
      let name = std::str::from_utf8(&data[offset..offset + name_len])
        .map_err(|e| format!("SCS table name is not UTF-8: {e}"))?
        .to_owned();
      offset += name_len;
      let cell_base = u64::from_le_bytes(
        data[offset..offset + 8].try_into().expect("8-byte cell_base"),
      );
      let rows = u32::from_le_bytes(
        data[offset + 8..offset + 12].try_into().expect("4-byte rows"),
      );
      let width = u32::from_le_bytes(
        data[offset + 12..offset + 16].try_into().expect("4-byte width"),
      );
      offset += 16;
      tables.push(Table { name, cell_base, rows, width });
    }
    if offset != data.len() {
      return Err("trailing bytes in ix-aiur-scs-v1 file".into());
    }
    Ok(Self { format: INPUTS_FORMAT.into(), publics, cells, outputs, tables })
  }
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

/// Write one canonical curve scalar as 32 big-endian bytes (gnark binary witness
/// and public-input wire format).
pub fn put_curve_scalar<C: KzgCurve>(out: &mut Vec<u8>, value: CurveScalar<C>) {
  for limb in value.canonical_limbs_le().into_iter().rev() {
    out.extend(limb.to_be_bytes());
  }
}

/// Write one canonical BLS12-381 scalar as 32 big-endian bytes.
pub fn put_bls12_381_scalar(out: &mut Vec<u8>, value: Bls12381Scalar) {
  put_curve_scalar::<Bls12381Curve>(out, value);
}

/// Canonical big-endian BLS12-381 `Fr` words in typed public-call order.
pub fn bls12_381_public_bytes(
  values: &[Bls12381Scalar],
) -> Result<Vec<u8>, String> {
  if values.len() > super::MAX_PUBLIC_INPUTS {
    return Err("too many Aiur BLS12-381 PLONK public fields".into());
  }
  let mut out = Vec::with_capacity(32 * values.len());
  for &value in values {
    put_bls12_381_scalar(&mut out, value);
  }
  Ok(out)
}

/// Serialize a gnark binary witness from `cells` (first `publics` public,
/// remainder secret) over `C::Fr`.
pub fn serialize_binary_witness<C: KzgCurve>(
  publics: usize,
  cells: &[CurveScalar<C>],
) -> Result<Vec<u8>, String> {
  if publics > cells.len() {
    return Err("public wire count exceeds total SCS cells".into());
  }
  let mut out = Vec::with_capacity(12 + 32 * cells.len());
  for count in [publics, cells.len() - publics, cells.len()] {
    out.extend(u32::try_from(count).map_err(|e| e.to_string())?.to_be_bytes());
  }
  for &value in cells {
    put_curve_scalar::<C>(&mut out, value);
  }
  Ok(out)
}

/// Terminal pairing configuration for BLS12-381 (`curve: "bls12-381"`,
/// `encoding: "affine-u80-v1"`, `22` accumulator words = `2 * (5 + 5 + 1)`).
pub fn bls12_381_pairing(
  anchors: [ark_bls12_381::G2Affine; 2],
) -> Result<super::Pairing, String> {
  for point in &anchors {
    if point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err(
        "BLS12-381 pairing anchor must be a nonzero G2 subgroup point".into(),
      );
    }
  }
  Ok(super::Pairing {
    curve: "bls12-381",
    encoding: "affine-u80-v1",
    g2: anchors.map(|point| bls12_381::encode_g2_coordinates(&point)),
  })
}

/// Build the BLS12-381 terminal pairing configuration directly from
/// independently authenticated KZG verifier parameters.
pub fn bls12_381_pairing_from_params(
  parameters: &VerifierParams<Bls12381Curve>,
) -> Result<super::Pairing, String> {
  bls12_381_pairing([parameters.g2, parameters.tau_g2])
}

fn eval_poly<B: FieldBackend<Word = FieldWord>>(
  poly: &Polynomial<FieldWord>,
  row: &[B::Element],
  field: B,
) -> B::Element {
  match poly {
    Polynomial::Const(value) => field.from_word(*value),
    Polynomial::Var(column) => row[*column],
    Polynomial::Add(terms) => field
      .add(eval_poly(&terms[0], row, field), eval_poly(&terms[1], row, field)),
    Polynomial::Sub(terms) => field
      .sub(eval_poly(&terms[0], row, field), eval_poly(&terms[1], row, field)),
    Polynomial::Mul(terms) => field
      .mul(eval_poly(&terms[0], row, field), eval_poly(&terms[1], row, field)),
  }
}

struct SharedMapGroup {
  maps: Vec<usize>,
  height: usize,
}

fn shared_map_groups<B: FieldBackend<Word = FieldWord>>(
  plan: &TracePlan<'_, B>,
) -> Result<Vec<SharedMapGroup>, String> {
  let program = plan.program().program();
  let mut groups: Vec<(usize, Vec<usize>)> = vec![];
  for (map, definition) in program.maps.iter().enumerate() {
    let real = program.tables[definition.input].rows.len();
    if let Some((_, maps)) = groups.iter_mut().find(|(rows, _)| *rows == real) {
      maps.push(map);
    } else {
      groups.push((real, vec![map]));
    }
  }
  groups
    .into_iter()
    .map(|(real, maps)| {
      let height = if real == 0 {
        0
      } else {
        real.checked_next_power_of_two().ok_or("map table height overflow")?
      };
      Ok(SharedMapGroup { maps, height })
    })
    .collect()
}

fn memory_widths_of<B: FieldBackend<Word = FieldWord>>(
  plan: &TracePlan<'_, B>,
) -> Vec<usize> {
  let mut widths: Vec<usize> = plan
    .artifact()
    .chips
    .iter()
    .flat_map(|chip| chip.memory.iter().map(|cell| cell.values.len()))
    .collect();
  widths.sort_unstable();
  widths.dedup();
  widths
}

/// Build an `ix-aiur-plonk-terminal-v1` stage schema JSON for `plonk_export`
/// from any checked [`TracePlan`] and [`Execution`] (BN254 or BLS12-381).
pub fn stage_for_plan<B, C>(
  plan: &TracePlan<'_, B>,
  entry: &str,
  record: &Execution<B>,
  public_args: &[CurveScalar<C>],
) -> Result<serde_json::Value, String>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>,
  C: KzgCurve,
{
  let field = plan.program().field();
  let layout = plan.layout()?;
  let artifact = plan.artifact();
  let claim = plan.public_claim(entry, public_args, &record.output)?;
  let callable = field.try_to_u64(claim[1])?;
  let mut function_rows = vec![0usize; layout.circuits.len()];
  for (function, &chip) in plan.function_chips().iter().enumerate() {
    let count = record
      .queries
      .callable_rows(function)
      .ok_or("missing function query count")?;
    let circuit = layout.placements[chip].circuit;
    function_rows[circuit] = function_rows[circuit]
      .checked_add(count)
      .ok_or("function row count overflow")?;
  }
  let mut circuits = Vec::new();
  for (circuit, raw_rows) in layout.circuits.iter().zip(function_rows) {
    let (name, width) = match *circuit {
      FunctionCircuit::Chip(i) => {
        (artifact.chips[i].name.clone(), artifact.chips[i].width + 1)
      },
      FunctionCircuit::Group(i) => {
        (artifact.groups[i].name.clone(), artifact.groups[i].width + 1)
      },
    };
    let rows = raw_rows
      .max(1)
      .checked_next_power_of_two()
      .ok_or("circuit row capacity overflow")?;
    circuits.push(serde_json::json!({
      "name": name,
      "rows": rows,
      "main_width": width,
      "fixed_width": 0,
      "fixed": [],
      "nodes": [],
      "constraints": [],
      "lookups": [],
    }));
  }
  let memory_widths = memory_widths_of(plan);
  let mut rom_counts = vec![0usize; memory_widths.len()];
  for (width, count) in record.memory.width_counts() {
    if count == 0 {
      continue;
    }
    let idx = memory_widths
      .binary_search(&width)
      .ok()
      .ok_or("recorded ROM width absent from artifact")?;
    rom_counts[idx] = count;
  }
  for (width, count) in memory_widths.into_iter().zip(rom_counts) {
    let rows = count
      .max(1)
      .checked_next_power_of_two()
      .ok_or("ROM capacity overflow")?;
    circuits.push(serde_json::json!({
      "name": format!("<ROM:{width}>"),
      "rows": rows,
      "main_width": width + 1,
      "fixed_width": 0,
      "fixed": [],
      "nodes": [],
      "constraints": [],
      "lookups": [],
    }));
  }
  Ok(serde_json::json!({
    "format": super::TERMINAL_FORMAT,
    "callable": callable,
    "public_inputs": public_args.len(),
    "private_outputs": record.output.len(),
    "boolean_requests": true,
    "circuits": circuits,
  }))
}

/// Build the BLS12-381 terminal stage schema (`2` public statement limbs and
/// `22` private pairing outputs) for `plonk_export --bls12-381`.
pub fn bls12_381_stage(
  plan: &TracePlan<'_, Bls12381>,
  entry: &str,
  record: &Execution<Bls12381>,
  public_args: &[Bls12381Scalar],
) -> Result<serde_json::Value, String> {
  if public_args.len() != 2
    || record.output.len() != BLS12_381_ACCUMULATOR_WORDS
  {
    return Err(
      "BLS12-381 terminal requires two public statement limbs and 22 private outputs"
        .into(),
    );
  }
  stage_for_plan::<Bls12381, Bls12381Curve>(plan, entry, record, public_args)
}

enum CurveFeed {
  Root,
  Function(usize),
  Shared(usize),
  Rom(usize),
}

/// Curve-generic `ix-aiur-scs-v1` binary witness producer directly over a
/// [`TracePlan`], supporting both [`Bn254`] and [`Bls12381`].
pub struct CurveWitness<'p, 'a, B, C>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>,
  C: KzgCurve,
{
  plan: &'p TracePlan<'a, B>,
  entry: String,
  inputs: Inputs,
  feeds: Vec<CurveFeed>,
  placements: Vec<Placement<FieldWord>>,
  function_widths: Vec<usize>,
  shared_groups: Vec<SharedMapGroup>,
  memory_widths: Vec<usize>,
  _curve: std::marker::PhantomData<C>,
}

/// BLS12-381 `ix-aiur-scs-v1` binary witness producer.
pub type Bls12381Witness<'p, 'a> =
  CurveWitness<'p, 'a, Bls12381, Bls12381Curve>;

impl<'p, 'a, B, C> CurveWitness<'p, 'a, B, C>
where
  B: FieldBackend<Element = CurveScalar<C>, Word = FieldWord>,
  C: KzgCurve,
{
  pub fn new(
    plan: &'p TracePlan<'a, B>,
    entry: &str,
    inputs: Inputs,
  ) -> Result<Self, String> {
    if inputs.format != INPUTS_FORMAT {
      return Err("SCS input layout format differs".into());
    }
    let layout = plan.layout()?;
    let artifact = plan.artifact();
    let mut function_names = Vec::with_capacity(layout.circuits.len());
    let mut function_widths = Vec::with_capacity(layout.circuits.len());
    for circuit in &layout.circuits {
      match *circuit {
        FunctionCircuit::Chip(i) => {
          function_names.push(artifact.chips[i].name.clone());
          function_widths.push(artifact.chips[i].width + 1);
        },
        FunctionCircuit::Group(i) => {
          function_names.push(artifact.groups[i].name.clone());
          function_widths.push(artifact.groups[i].width + 1);
        },
      }
    }
    let shared_groups = shared_map_groups(plan)?;
    let memory_widths = memory_widths_of(plan);
    let nf = function_names.len();
    let ns = shared_groups.len();
    let mut used = vec![false; nf + ns + memory_widths.len()];
    let mut claim_used = |slot: usize, name: &str| -> Result<(), String> {
      if std::mem::replace(&mut used[slot], true) {
        return Err(format!("{name} feeds two SCS tables"));
      }
      Ok(())
    };
    let mut feeds = Vec::with_capacity(inputs.tables.len());
    for t in &inputs.tables {
      let feed = if t.name == "root" {
        if t.cell_base != 0
          || t.rows != 1
          || t.width as usize != inputs.publics + inputs.outputs.len()
        {
          return Err("SCS root table is not the publics and outputs".into());
        }
        CurveFeed::Root
      } else if let Some(k) = t.name.strip_prefix("map_shared/") {
        let k: usize =
          k.parse().map_err(|e| format!("{}: not a map table: {e}", t.name))?;
        let group = shared_groups
          .get(k)
          .ok_or_else(|| format!("{}: no compiler map table", t.name))?;
        if t.width as usize != group.maps.len()
          || t.rows as usize != group.height
        {
          return Err(format!(
            "{}: {}×{} in SCS file, {}×{} here",
            t.name,
            t.rows,
            t.width,
            group.height,
            group.maps.len()
          ));
        }
        claim_used(nf + k, &t.name)?;
        CurveFeed::Shared(k)
      } else if let Some(words) = t.name.strip_prefix("rom/") {
        let w: usize = words
          .parse()
          .map_err(|e| format!("{}: invalid ROM width: {e}", t.name))?;
        let idx = memory_widths
          .binary_search(&w)
          .ok()
          .ok_or_else(|| format!("{}: no compiler ROM circuit", t.name))?;
        if t.width as usize != w + 1 {
          return Err(format!(
            "{}: width {} in SCS file, expected {}",
            t.name,
            t.width,
            w + 1
          ));
        }
        claim_used(nf + ns + idx, &t.name)?;
        CurveFeed::Rom(idx)
      } else {
        let idx = function_names
          .iter()
          .position(|n| *n == t.name)
          .ok_or_else(|| format!("{}: no compiler function circuit", t.name))?;
        if t.width as usize != function_widths[idx] {
          return Err(format!(
            "{}: width {} in SCS file, {} here",
            t.name, t.width, function_widths[idx]
          ));
        }
        claim_used(idx, &t.name)?;
        CurveFeed::Function(idx)
      };
      feeds.push(feed);
    }
    let mut spans: Vec<(u64, u64)> = inputs
      .tables
      .iter()
      .map(|t| {
        (t.cell_base, t.cell_base + u64::from(t.rows) * u64::from(t.width))
      })
      .collect();
    spans.sort();
    let mut end = 0u64;
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
    Ok(Self {
      plan,
      entry: entry.into(),
      inputs,
      feeds,
      placements: layout.placements,
      function_widths,
      shared_groups,
      memory_widths,
      _curve: std::marker::PhantomData,
    })
  }

  pub fn inputs(&self) -> &Inputs {
    &self.inputs
  }

  /// Serialize gnark's binary witness over `C::Fr`.
  pub fn binary(
    &self,
    record: &Execution<B>,
    args: &[CurveScalar<C>],
  ) -> Result<Vec<u8>, String> {
    let field = self.plan.program().field();
    let n = &self.inputs;
    let public_args = self.plan.public_args(record, &self.entry, args)?;
    let claim =
      self.plan.public_claim(&self.entry, &public_args, &record.output)?;
    if claim.len() != 2 + n.publics + n.outputs.len() {
      return Err("public claim width differs from the SCS root table".into());
    }
    let trace = self.plan.generate(record, &self.entry, args, true)?;
    // Pack function circuit traces.
    let mut fn_heights = vec![0usize; self.function_widths.len()];
    for (matrix, placement) in trace.matrices.iter().zip(&self.placements) {
      let height =
        if placement.grouped { matrix.unpadded_height } else { matrix.height };
      fn_heights[placement.circuit] = fn_heights[placement.circuit]
        .checked_add(height)
        .ok_or("function trace height overflow")?;
    }
    let mut fn_traces: Vec<RowMajorMatrix<CurveScalar<C>>> = fn_heights
      .iter()
      .zip(&self.function_widths)
      .map(|(&h, &w)| {
        let padded = if h == 0 { 0 } else { h.next_power_of_two() };
        RowMajorMatrix::new(vec![CurveScalar::<C>::ZERO; padded * w], w)
      })
      .collect();
    let mut cursors = vec![0usize; self.function_widths.len()];
    for ((chip, matrix), placement) in self
      .plan
      .artifact()
      .chips
      .iter()
      .zip(&trace.matrices)
      .zip(&self.placements)
    {
      let output = &mut fn_traces[placement.circuit];
      let first = cursors[placement.circuit];
      let width = output.width;
      for row_index in 0..matrix.unpadded_height {
        let source = matrix.row(row_index);
        if source[chip.activation] != CurveScalar::<C>::ONE {
          return Err("inactive real compiler row".into());
        }
        let dest = &mut output.values
          [(first + row_index) * width..(first + row_index + 1) * width];
        for (&column, &value) in placement.columns.iter().zip(source) {
          dest[column] = value;
        }
        dest[placement.selector] = CurveScalar::<C>::ONE;
        for write in &placement.writes {
          dest[write.column] = eval_poly(&write.value, dest, field);
        }
        *dest.last_mut().ok_or("empty compiler circuit")? =
          field.from_u64(matrix.multiplicities[row_index]);
      }
      cursors[placement.circuit] = first + matrix.unpadded_height;
    }

    // Pack shared map table multiplicities (including depth-range counts).
    let program = self.plan.program().program();
    let mut map_counts = (0..program.maps.len())
      .map(|map| {
        record
          .queries
          .fixed_counts(program.functions.len() + map)
          .map(<[u64]>::to_vec)
          .ok_or_else(|| "missing fixed-map counts".to_owned())
      })
      .collect::<Result<Vec<_>, _>>()?;
    for (table, callable) in self.plan.depth_range_tables() {
      let map = callable
        .checked_sub(program.functions.len())
        .ok_or("invalid depth map callable")?;
      let counts = map_counts.get_mut(map).ok_or("missing depth range map")?;
      for (count, &uses) in counts.iter_mut().zip(trace.ranges.table(table)) {
        *count =
          count.checked_add(uses).ok_or("depth range multiplicity overflow")?;
      }
    }

    // Group ROM cells by payload width.
    let mut rom_buckets = vec![vec![]; self.memory_widths.len()];
    for cell in record.memory.iter() {
      let bucket = self
        .memory_widths
        .binary_search(&cell.cell.value.len())
        .ok()
        .ok_or("recorded ROM width absent from artifact")?;
      rom_buckets[bucket].push(cell);
    }

    let mut cells = vec![CurveScalar::<C>::ZERO; n.cells];
    for (t, feed) in n.tables.iter().zip(&self.feeds) {
      let base = usize::try_from(t.cell_base)
        .map_err(|e| format!("{}: cell base: {e}", t.name))?;
      match feed {
        CurveFeed::Root => {
          for (i, &value) in claim[2..].iter().enumerate() {
            cells[base + i] = value;
          }
        },
        CurveFeed::Function(idx) => {
          let m = &fn_traces[*idx];
          if m.width != t.width as usize || m.height() > t.rows as usize {
            return Err(format!("{}: execution exceeds the SCS table", t.name));
          }
          cells[base..base + m.values.len()].copy_from_slice(&m.values);
        },
        CurveFeed::Shared(k) => {
          let group = &self.shared_groups[*k];
          let width = group.maps.len();
          for row in 0..group.height {
            for (col, &map) in group.maps.iter().enumerate() {
              let c = map_counts[map].get(row).copied().unwrap_or(0);
              cells[base + row * width + col] = field.from_u64(c);
            }
          }
        },
        CurveFeed::Rom(idx) => {
          let width = self.memory_widths[*idx] + 1;
          let bucket = &rom_buckets[*idx];
          if bucket.len() > t.rows as usize {
            return Err(format!(
              "{}: ROM execution exceeds the SCS table",
              t.name
            ));
          }
          for (address, cell) in bucket.iter().enumerate() {
            if cell.address != address {
              return Err("nonconsecutive ROM addresses".into());
            }
            let start = base + address * width;
            cells[start] = field.from_u64(cell.multiplicity);
            cells[start + 1..start + width].copy_from_slice(cell.cell.value);
          }
        },
      }
    }
    serialize_binary_witness::<C>(n.publics, &cells)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::{Fr as BlsFr, G2Affine as BlsG2};
  use ark_ec::CurveGroup;

  #[test]
  fn bls12_381_pairing_descriptor_and_scalar_serialization() {
    let g2 = BlsG2::generator();
    let tau_g2 = (g2 * BlsFr::from(7u64)).into_affine();
    let descriptor = bls12_381_pairing([g2, tau_g2]).unwrap();
    assert_eq!(descriptor.curve, "bls12-381");
    assert_eq!(descriptor.encoding, "affine-u80-v1");
    assert_eq!(BLS12_381_ACCUMULATOR_WORDS, 22);
    assert_eq!(
      bls12_381::decode_g2_coordinates(&descriptor.g2[0]).unwrap(),
      g2
    );
    assert_eq!(
      bls12_381::decode_g2_coordinates(&descriptor.g2[1]).unwrap(),
      tau_g2
    );
    assert!(bls12_381_pairing([BlsG2::identity(), tau_g2]).is_err());

    // Canonical 32-byte BE encoding retains values > BN254 Fr modulus.
    let minus_one = Bls12381.neg(Bls12381.one());
    let seven = Bls12381.from_u64(7);
    let pub_bytes = bls12_381_public_bytes(&[minus_one, seven]).unwrap();
    assert_eq!(pub_bytes.len(), 64);
    let mut expected_first = Vec::new();
    put_bls12_381_scalar(&mut expected_first, minus_one);
    assert_eq!(&pub_bytes[..32], expected_first.as_slice());
    assert_eq!(pub_bytes[63], 7);
    assert!(pub_bytes[32..63].iter().all(|&b| b == 0));

    let witness = serialize_binary_witness::<Bls12381Curve>(
      2,
      &[minus_one, seven, Bls12381.from_u64(99)],
    )
    .unwrap();
    assert_eq!(witness.len(), 12 + 3 * 32);
    assert_eq!(&witness[0..4], 2u32.to_be_bytes());
    assert_eq!(&witness[4..8], 1u32.to_be_bytes());
    assert_eq!(&witness[8..12], 3u32.to_be_bytes());
    assert_eq!(&witness[12..76], pub_bytes.as_slice());
    assert_eq!(witness[12 + 64 + 31], 99);
    assert!(serialize_binary_witness::<Bls12381Curve>(4, &[seven]).is_err());
    assert!(Inputs::from_ixscs(b"badmagic").is_err());
    assert!(Inputs::from_ixscs(b"ixscs001short").is_err());
  }

  #[test]
  fn real_bls12_381_plonk_export_and_witness_e2e() {
    let (Ok(ixa_path), Ok(out_dir), Ok(exporter)) = (
      std::env::var("IX_AIUR_BLS_E2E_IXA"),
      std::env::var("IX_AIUR_BLS_E2E_OUT"),
      std::env::var("IX_AIUR_BLS_PLONK_EXPORT"),
    ) else {
      return;
    };
    let ixa_bytes = std::fs::read(&ixa_path).unwrap();
    let plan = bls12_381::load_trace_plan(&ixa_bytes).unwrap();
    let entry = std::env::var("IX_AIUR_BLS_E2E_ENTRY")
      .unwrap_or_else(|_| plan.program().program().entries[0].name.clone());
    let args: Vec<Bls12381Scalar> = std::env::var("IX_AIUR_BLS_E2E_ARGS")
      .unwrap_or_default()
      .split(',')
      .filter(|s| !s.is_empty())
      .map(|s| Bls12381.from_u64(s.trim().parse::<u64>().unwrap()))
      .collect();
    let record =
      bls12_381::execute_plan(&plan, &entry, args.clone(), None).unwrap();
    let trace = plan.generate(&record, &entry, &args, true).unwrap();
    plan.check(&record, &trace, &entry, &args).unwrap();

    let out = std::path::PathBuf::from(out_dir);
    std::fs::create_dir_all(&out).unwrap();
    let schema =
      stage_for_plan::<Bls12381, Bls12381Curve>(&plan, &entry, &record, &args)
        .unwrap();
    let schema_path = out.join("schema.json");
    let scs_path = out.join("program.ixscs");
    let witness_path = out.join("witness.bin");
    std::fs::write(&schema_path, serde_json::to_vec_pretty(&schema).unwrap())
      .unwrap();

    let status = std::process::Command::new(&exporter)
      .arg(&ixa_path)
      .arg(&schema_path)
      .arg(&scs_path)
      .arg("--bls12-381")
      .status()
      .unwrap();
    assert!(status.success(), "plonk_export --bls12-381 failed: {status}");

    if let Ok(checker) = std::env::var("IX_AIUR_BLS_PLONK_CHECK") {
      let check = std::process::Command::new(&checker)
        .arg(&ixa_path)
        .arg(&schema_path)
        .arg("--bls12-381")
        .status()
        .unwrap();
      assert!(check.success(), "plonk_check_stage failed: {check}");
    }

    let scs_bytes = std::fs::read(&scs_path).unwrap();
    let inputs = Inputs::from_ixscs(&scs_bytes).unwrap();
    let witness = Bls12381Witness::new(&plan, &entry, inputs)
      .unwrap()
      .binary(&record, &args)
      .unwrap();
    std::fs::write(&witness_path, &witness).unwrap();
  }
}
