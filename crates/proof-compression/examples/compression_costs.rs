//! Compare saved Aiur wrapper and hand-written FRI reports without building traces.
//!
//! Usage: compression_costs compare WRAP_REPORT FRI_CIRCUIT_COST
//!        compression_costs plonk CONSTRAINTS PUBLIC_INPUTS RETAINED_POWERS MAX_DEGREE

use ix_proof_compression::pipeline::plonk_limits::{
  ParameterSize, maximum_domain,
};
use serde::{Deserialize, Serialize};
use std::{fs, io::Read, path::Path};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const MAX_REPORT_BYTES: u64 = 16 << 20;

fn canonical_digest(digest: &str) -> bool {
  digest.len() == 64
    && digest.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct InputIdentity {
  key_blake3: String,
  claims_blake3: String,
  proof_blake3: String,
}

impl InputIdentity {
  fn validate(&self) -> Result<()> {
    for digest in [&self.key_blake3, &self.claims_blake3, &self.proof_blake3] {
      if !canonical_digest(digest) {
        return Err(
          "input identity must contain canonical BLAKE3 hex digests".into(),
        );
      }
    }
    Ok(())
  }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct Parameters {
  log_blowup: u32,
  cap_height: u32,
  num_queries: u64,
  log_final_poly_len: u32,
  max_log_arity: u32,
  commit_proof_of_work_bits: u32,
  query_proof_of_work_bits: u32,
}

#[derive(Deserialize)]
struct WrapReport {
  format: String,
  input: InputIdentity,
  parameters: Parameters,
  field_bytes: u64,
  wrapper: serde_json::Value,
  execution_statistics: ExecutionStatistics,
  layout: WrapLayout,
}

#[derive(Deserialize)]
struct ExecutionStatistics {
  log_blowup: u32,
  extension_degree: u64,
  circuits: Vec<Circuit>,
}

#[derive(Deserialize)]
struct Circuit {
  name: String,
  rows: u64,
  stage1_width: u64,
  stage2_width: u64,
  preprocessed_width: u64,
  preprocessed_height: u64,
  quotient_degree: u64,
}

#[derive(Deserialize)]
struct WrapLayout {
  log_heights: Vec<u32>,
}

#[derive(Deserialize)]
struct FriReport {
  format: String,
  input: InputIdentity,
  parameters: Parameters,
  field_bytes: u64,
  #[serde(flatten)]
  construction: Construction,
  frontend: serde_json::Value,
  layout: FriLayout,
}

#[derive(Deserialize, Serialize)]
struct Construction {
  fixed_root_layout: bool,
  fixed_root_layout_blake3: Option<String>,
  compact_blake3: bool,
}

#[derive(Deserialize, Serialize)]
struct FriLayout {
  used_rows: u64,
  main_heights: Vec<u64>,
  main_width: u64,
  preprocessed_width: u64,
  table_heights: Vec<u64>,
  custom_traces: Vec<(u64, u64, u64)>,
  advice_cells: u64,
  preprocessed_cells: u64,
  trace_field_bytes: u64,
}

#[derive(Serialize)]
struct ArrayCosts {
  stage1_advice_cells: u64,
  preprocessed_cells: u64,
  stage1_and_preprocessed_cells: u64,
  stage1_and_preprocessed_field_bytes: u64,
  stage1_and_preprocessed_lde_bytes: u64,
}

fn add(a: u64, b: u64) -> Result<u64> {
  a.checked_add(b).ok_or_else(|| "cell count overflow".into())
}

fn mul(a: u64, b: u64) -> Result<u64> {
  a.checked_mul(b).ok_or_else(|| "cell/byte count overflow".into())
}

fn height(log: u32) -> Result<u64> {
  if log > 32 {
    return Err("trace height exceeds Goldilocks two-adicity".into());
  }
  Ok(1u64 << log)
}

fn arrays(
  advice: u64,
  preprocessed: u64,
  log_blowup: u32,
) -> Result<ArrayCosts> {
  let cells = add(advice, preprocessed)?;
  let bytes = mul(cells, 8)?;
  Ok(ArrayCosts {
    stage1_advice_cells: advice,
    preprocessed_cells: preprocessed,
    stage1_and_preprocessed_cells: cells,
    stage1_and_preprocessed_field_bytes: bytes,
    stage1_and_preprocessed_lde_bytes: mul(bytes, height(log_blowup)?)?,
  })
}

fn wrap_costs(report: &WrapReport) -> Result<serde_json::Value> {
  let statistics = &report.execution_statistics;
  if report.field_bytes != 8
    || statistics.log_blowup != report.parameters.log_blowup
    || statistics.extension_degree != 2
    || statistics.circuits.len() != report.layout.log_heights.len()
    || statistics.circuits.is_empty()
  {
    return Err("Aiur statistics and normalized layout disagree".into());
  }
  let (mut advice, mut fixed, mut stage2, mut quotient) = (0, 0, 0, 0);
  let mut circuits = Vec::with_capacity(statistics.circuits.len());
  for (circuit, &log) in
    statistics.circuits.iter().zip(&report.layout.log_heights)
  {
    let n = height(log)?;
    if !(1..=26).contains(&log)
      || circuit.rows > n
      || circuit.stage1_width == 0
      || circuit.quotient_degree == 0
      || !circuit.quotient_degree.is_power_of_two()
      || (circuit.preprocessed_width > 0 && circuit.preprocessed_height != n)
      || (circuit.preprocessed_width == 0 && circuit.preprocessed_height != 0)
      || log
        .checked_add(report.parameters.log_blowup)
        .is_none_or(|log| log > 32)
    {
      return Err(
        format!("invalid normalized shape for {}", circuit.name).into(),
      );
    }
    let stage1_cells = mul(n, circuit.stage1_width)?;
    let fixed_cells =
      mul(circuit.preprocessed_height, circuit.preprocessed_width)?;
    let stage2_cells = mul(n, circuit.stage2_width)?;
    let quotient_width =
      mul(circuit.quotient_degree, statistics.extension_degree)?;
    let quotient_cells = mul(n, quotient_width)?;
    advice = add(advice, stage1_cells)?;
    fixed = add(fixed, fixed_cells)?;
    stage2 = add(stage2, stage2_cells)?;
    quotient = add(quotient, quotient_cells)?;
    circuits.push(serde_json::json!({
      "name": circuit.name, "execution_rows": circuit.rows,
      "padded_height": n, "stage1_width": circuit.stage1_width,
      "stage2_base_field_width": circuit.stage2_width,
      "quotient_base_field_width": quotient_width,
      "preprocessed_width": circuit.preprocessed_width,
      "stage1_advice_cells": stage1_cells, "stage2_cells": stage2_cells,
      "quotient_cells": quotient_cells, "preprocessed_cells": fixed_cells,
    }));
  }
  Ok(serde_json::json!({
    "arrays": arrays(advice, fixed, report.parameters.log_blowup)?,
    "stage2_cells": stage2, "quotient_cells": quotient,
    "stage2_field_bytes": mul(stage2, 8)?,
    "quotient_field_bytes": mul(quotient, 8)?,
    "committed_cells_excluding_preprocessed": add(add(advice, stage2)?, quotient)?,
    "circuits": circuits,
  }))
}

fn fri_costs(report: &FriReport) -> Result<ArrayCosts> {
  if report.field_bytes != 8 || report.layout.main_width == 0 {
    return Err("expected a Goldilocks FRI circuit layout".into());
  }
  match (
    &report.construction.fixed_root_layout_blake3,
    report.construction.fixed_root_layout,
  ) {
    (Some(digest), true) if canonical_digest(digest) => {},
    (None, false) => {},
    _ => {
      return Err(
        "FRI construction has inconsistent fixed-layout identity".into(),
      );
    },
  }
  let layout = &report.layout;
  let (mut advice, mut fixed, mut rows) = (0, 0, 0);
  for &n in &layout.main_heights {
    rows = add(rows, n)?;
    advice = add(advice, mul(n, layout.main_width)?)?;
    fixed = add(fixed, mul(n, layout.preprocessed_width)?)?;
  }
  if rows < layout.used_rows {
    return Err("FRI computation rows exceed their padded capacity".into());
  }
  for &n in &layout.table_heights {
    advice = add(advice, n)?;
    fixed = add(fixed, mul(n, layout.main_width)?)?;
  }
  for &(n, main, preprocessed) in &layout.custom_traces {
    advice = add(advice, mul(n, main)?)?;
    fixed = add(fixed, mul(n, preprocessed)?)?;
  }
  for n in layout
    .main_heights
    .iter()
    .chain(&layout.table_heights)
    .copied()
    .chain(layout.custom_traces.iter().map(|&(n, _, _)| n))
  {
    if n < 2
      || !n.is_power_of_two()
      || n
        .ilog2()
        .checked_add(report.parameters.log_blowup)
        .is_none_or(|log| log > 32)
    {
      return Err("invalid FRI padded trace height".into());
    }
  }
  let result = arrays(advice, fixed, report.parameters.log_blowup)?;
  if layout.advice_cells != advice
    || layout.preprocessed_cells != fixed
    || layout.trace_field_bytes != result.stage1_and_preprocessed_field_bytes
  {
    return Err("FRI layout totals disagree with its dimensions".into());
  }
  Ok(result)
}

#[allow(
  clippy::cast_precision_loss,
  reason = "display ratio only; the report also retains both exact integer totals"
)]
fn display_ratio(numerator: u64, denominator: u64) -> f64 {
  numerator as f64 / denominator as f64
}

fn compare(wrap: &WrapReport, fri: &FriReport) -> Result<serde_json::Value> {
  if wrap.format != "ix-compress-wrap-profile-v1"
    || fri.format != "ix-fri-circuit-cost-v2"
  {
    return Err("unsupported compression cost report format".into());
  }
  wrap.input.validate()?;
  fri.input.validate()?;
  if wrap.input != fri.input {
    return Err(
      "reports verified different input key, claims or proof bytes".into(),
    );
  }
  if wrap.parameters != fri.parameters {
    return Err("reports use different outer FRI security parameters".into());
  }
  let aiur = wrap_costs(wrap)?;
  let handmade = fri_costs(fri)?;
  if handmade.stage1_and_preprocessed_cells == 0 {
    return Err("empty hand-written FRI layout".into());
  }
  let numerator = aiur["arrays"]["stage1_and_preprocessed_cells"]
    .as_u64()
    .ok_or("missing Aiur cell total")?;
  Ok(serde_json::json!({
    "format": "ix-compression-cost-comparison-v1",
    "input": wrap.input, "parameters": wrap.parameters, "field_bytes": 8,
    "aiur": aiur, "wrapper": wrap.wrapper,
    "handwritten_fri": {"arrays": handmade, "frontend": fri.frontend, "layout": fri.layout, "construction": fri.construction},
    "aiur_to_handwritten_stage1_and_preprocessed_ratio":
      display_ratio(numerator, handmade.stage1_and_preprocessed_cells),
    "scope": "Normalized single-shard Aiur stage-one and fixed arrays compared with hand-written FRI stage-one and fixed arrays. Frontend gates, stage-two and quotient cells are not ratio denominators. LDE bytes exclude Merkle trees, scratch, execution records and other prover memory. Saved reports are measurements, not proof certificates.",
  }))
}

fn read_report<T: serde::de::DeserializeOwned>(path: &str) -> Result<T> {
  let path = Path::new(path);
  let file = fs::File::open(path)?;
  if file.metadata()?.len() > MAX_REPORT_BYTES {
    return Err("compression cost report exceeds 16 MiB".into());
  }
  let mut bytes = Vec::new();
  file.take(MAX_REPORT_BYTES + 1).read_to_end(&mut bytes)?;
  if bytes.len() as u64 > MAX_REPORT_BYTES {
    return Err("compression cost report exceeds 16 MiB".into());
  }
  Ok(serde_json::from_slice(&bytes)?)
}

fn main() -> Result<()> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let report = match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
    ["compare", wrap, fri] => compare(&read_report(wrap)?, &read_report(fri)?)?,
    ["plonk", constraints, publics, retained, degree] => {
      let constraints: usize = constraints.parse()?;
      let public_inputs: usize = publics.parse()?;
      let retained: usize = retained.parse()?;
      let degree: usize = degree.parse()?;
      let size = ParameterSize::for_circuit(constraints, public_inputs)?;
      let capacity_error = size.check_capacity(retained, degree).err();
      let maximum = maximum_domain(retained, degree);
      serde_json::json!({
        "format": "ix-plonk-capacity-v1", "constraints": constraints,
        "public_inputs": public_inputs, "domain": size.domain(),
        "opening_powers": size.opening_powers(), "loaded_powers": size.loaded_powers(),
        "retained_powers": retained, "public_max_degree": degree,
        "fits": capacity_error.is_none(), "capacity_error": capacity_error,
        "maximum_domain_with_current_loader": maximum,
        "maximum_constraints_with_current_loader": maximum.and_then(|n| n.checked_sub(public_inputs)),
      })
    },
    _ => return Err("usage: compression_costs compare WRAP_REPORT FRI_CIRCUIT_COST | plonk CONSTRAINTS PUBLIC_INPUTS RETAINED_POWERS MAX_DEGREE".into()),
  };
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  fn reports() -> (WrapReport, FriReport) {
    let input = serde_json::json!({"key_blake3": "11".repeat(32), "claims_blake3": "22".repeat(32), "proof_blake3": "33".repeat(32)});
    let parameters = serde_json::json!({"log_blowup":2,"cap_height":0,"num_queries":100,"log_final_poly_len":0,"max_log_arity":1,"commit_proof_of_work_bits":0,"query_proof_of_work_bits":20});
    let wrap = serde_json::from_value(serde_json::json!({
      "format":"ix-compress-wrap-profile-v1", "input":input, "parameters":parameters, "field_bytes":8,
      "wrapper":{"artifact_blake3":"55".repeat(32),"key_blake3":"66".repeat(32),"entry":"CompressWrap::verify_root"},
      "layout":{"log_heights":[3,2]},
      "execution_statistics":{"log_blowup":2,"extension_degree":2,"circuits":[
        {"name":"fn","rows":5,"stage1_width":3,"stage2_width":4,"preprocessed_width":0,"preprocessed_height":0,"quotient_degree":2},
        {"name":"table","rows":4,"stage1_width":1,"stage2_width":2,"preprocessed_width":2,"preprocessed_height":4,"quotient_degree":1}
      ]}
    })).unwrap();
    let fri = serde_json::from_value(serde_json::json!({
      "format":"ix-fri-circuit-cost-v2", "input":input, "parameters":parameters,
      "fixed_root_layout":false,"fixed_root_layout_blake3":null,"compact_blake3":true,
      "field_bytes":8,"frontend":{"gates":1_000_000},
      "layout":{"used_rows":3,"main_heights":[4],"main_width":3,"preprocessed_width":5,
        "table_heights":[2],"custom_traces":[[2,2,1]],"advice_cells":18,"preprocessed_cells":28,"trace_field_bytes":368}
    })).unwrap();
    (wrap, fri)
  }

  #[test]
  fn compares_only_equivalent_stage_one_and_fixed_arrays() {
    let (wrap, fri) = reports();
    let report = compare(&wrap, &fri).unwrap();
    assert_eq!(report["aiur"]["arrays"]["stage1_and_preprocessed_cells"], 36);
    assert_eq!(report["aiur"]["stage2_cells"], 40);
    assert_eq!(report["aiur"]["quotient_cells"], 40);
    assert_eq!(
      report["handwritten_fri"]["arrays"]["stage1_and_preprocessed_cells"],
      46
    );
    assert_eq!(
      report["aiur"]["arrays"]["stage1_and_preprocessed_lde_bytes"],
      1152
    );
    assert_eq!(
      report["aiur_to_handwritten_stage1_and_preprocessed_ratio"],
      36.0 / 46.0
    );
  }

  #[test]
  fn refuses_mismatched_inputs_and_security_parameters() {
    let (wrap, mut fri) = reports();
    fri.input.proof_blake3 = "44".repeat(32);
    assert!(
      compare(&wrap, &fri).unwrap_err().to_string().contains("different input")
    );
    let (wrap, mut fri) = reports();
    fri.parameters.num_queries -= 1;
    assert!(
      compare(&wrap, &fri)
        .unwrap_err()
        .to_string()
        .contains("security parameters")
    );
  }

  #[test]
  fn retains_construction_choices_without_rejecting_alternate_implementations()
  {
    let (wrap, mut fri) = reports();
    fri.construction.compact_blake3 = false;
    fri.construction.fixed_root_layout = true;
    fri.construction.fixed_root_layout_blake3 = Some("77".repeat(32));
    let report = compare(&wrap, &fri).unwrap();
    assert_eq!(
      report["handwritten_fri"]["construction"]["compact_blake3"],
      false
    );
    assert_eq!(
      report["handwritten_fri"]["construction"]["fixed_root_layout_blake3"],
      "77".repeat(32)
    );
    fri.construction.fixed_root_layout_blake3 = None;
    assert!(compare(&wrap, &fri).is_err());
    fri.format = "ix-fri-circuit-cost-v1".into();
    assert!(compare(&wrap, &fri).unwrap_err().to_string().contains("format"));
  }

  #[test]
  fn rejects_underallocated_and_inconsistent_layouts() {
    let (mut wrap, fri) = reports();
    wrap.layout.log_heights[0] = 2;
    assert!(compare(&wrap, &fri).is_err());
    let (wrap, mut fri) = reports();
    fri.layout.advice_cells += 1;
    assert!(compare(&wrap, &fri).is_err());
    let (mut wrap, fri) = reports();
    wrap.execution_statistics.circuits[0].stage1_width = u64::MAX;
    assert!(compare(&wrap, &fri).is_err());
  }
}
