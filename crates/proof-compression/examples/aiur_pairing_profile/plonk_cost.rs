use ix_proof_compression::aiur_backend::plonk::{Node, Schema, gnark};
use std::{fs, path::Path};

/// Measure compiler increments at small capacities, preserving the full fixed
/// tables. The result is an extrapolation, not a full-capacity compilation.
pub(crate) fn estimate(
  schema: &Schema,
  directory: &Path,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
  let mut baseline = schema.clone();
  for circuit in &mut baseline.circuits {
    if circuit.fixed_width == 0 {
      circuit.rows = 2;
    }
  }
  let path = directory.join("capacity-sample.bin");
  let base = gnark::compile(&baseline, &path)?;
  let mut constraints = base.constraints as i128;
  let mut increments = vec![];
  for (index, actual) in schema.circuits.iter().enumerate() {
    if actual.fixed_width != 0 || actual.rows == 2 {
      continue;
    }
    let mut sample = baseline.clone();
    sample.circuits[index].rows = if actual.rows == 1 { 1 } else { 4 };
    let info = gnark::compile(&sample, &path)?;
    let difference = info.constraints as i128 - base.constraints as i128;
    let contribution = if actual.rows == 1 {
      difference
    } else {
      if difference < 0 || difference % 2 != 0 {
        return Err("nonlinear per-row compiler increment".into());
      }
      if actual.nodes.iter().any(|node| {
        matches!(
          node,
          Node::Main { next: true, .. }
            | Node::Fixed { next: true, .. }
            | Node::First
            | Node::Last
            | Node::Transition
        )
      }) {
        sample.circuits[index].rows = 8;
        let larger = gnark::compile(&sample, &path)?;
        if larger.constraints as i128 - base.constraints as i128
          != 3 * difference
        {
          return Err(
            "boundary-selector cost does not extrapolate linearly".into(),
          );
        }
      }
      (actual.rows as i128 - 2) * (difference / 2)
    };
    constraints = constraints
      .checked_add(contribution)
      .ok_or("constraint estimate overflow")?;
    increments.push(serde_json::json!({"name":actual.name,"actual_rows":actual.rows,"sample_rows":if actual.rows==1{1}else{4},"sample_difference":difference.to_string(),"full_contribution":contribution.to_string()}));
  }
  fs::remove_file(path)?;
  let constraints = u64::try_from(constraints)
    .map_err(|_error| "negative or overflowing constraint estimate")?;
  let domain = constraints
    .checked_add(schema.public_inputs as u64)
    .and_then(u64::checked_next_power_of_two)
    .ok_or("domain estimate overflow")?;
  Ok(
    serde_json::json!({"format":"ix-aiur-plonk-extrapolated-cost-v1","constraints_extrapolated":constraints,"domain_extrapolated":domain,"fits_retained_ignition":domain<=1<<25,"baseline_constraints":base.constraints,"baseline_dynamic_rows":2,"public_inputs":schema.public_inputs,"increments":increments}),
  )
}
