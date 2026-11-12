use ix_proof_compression::aiur_backend::plonk::{Node, Schema, gnark};
use p3_maybe_rayon::prelude::*;
use std::{fs, path::Path};

/// Measure compiler increments at small capacities, preserving the full fixed
/// tables. Four baseline rows keep adjacent-row products distinct around the
/// cycle. The result is an extrapolation, not a full-capacity compilation.
pub(crate) fn estimate(
  schema: &Schema,
  directory: &Path,
) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
  let mut baseline = schema.clone();
  for circuit in &mut baseline.circuits {
    if circuit.fixed_width == 0 {
      circuit.rows = 4;
    }
  }
  let path = directory.join("capacity-sample.bin");
  let base = gnark::compile(&baseline, &path)?;
  fs::remove_file(&path)?;
  let increments = schema.circuits.par_iter().enumerate().map(|(index, actual)| -> Result<Option<(i128, serde_json::Value)>, String> {
    if actual.fixed_width != 0 || actual.rows == 4 {
      return Ok(None);
    }
    let path = directory.join(format!("capacity-sample-{index}.bin"));
    let result = (|| -> Result<_, String> {
      let mut sample = baseline.clone();
      sample.circuits[index].rows = if actual.rows < 4 { actual.rows } else { 8 };
      let info = gnark::compile(&sample, &path).map_err(|error| error.to_string())?;
      let difference = info.constraints as i128 - base.constraints as i128;
      let mut measurement = serde_json::json!({"name":actual.name,"actual_rows":actual.rows,"sample_rows":sample.circuits[index].rows,"sample_difference":difference.to_string(),"baseline_constraints":base.constraints});
      let progress = directory.join(format!("capacity-sample-{index}.json"));
      fs::write(&progress, serde_json::to_vec_pretty(&measurement).map_err(|error| error.to_string())?).map_err(|error| error.to_string())?;
      let contribution = if actual.rows < 4 {
        difference
      } else {
        if difference < 0 || difference % 4 != 0 {
          return Err(format!("{}: nonlinear per-row compiler increment {difference}", actual.name));
        }
        if actual.nodes.iter().any(|node| matches!(node,
          Node::Main { next: true, .. } | Node::Fixed { next: true, .. }
            | Node::First | Node::Last | Node::Transition
        )) {
          sample.circuits[index].rows = 16;
          let larger = gnark::compile(&sample, &path).map_err(|error| error.to_string())?;
          measurement["second_sample_constraints"] = larger.constraints.into();
          if larger.constraints as i128 - base.constraints as i128 != 3 * difference {
            return Err(format!("{}: boundary-selector cost does not extrapolate linearly", actual.name));
          }
        }
        (actual.rows as i128 - 4) * (difference / 4)
      };
      measurement["full_contribution"] = contribution.to_string().into();
      fs::write(progress, serde_json::to_vec_pretty(&measurement).map_err(|error| error.to_string())?).map_err(|error| error.to_string())?;
      Ok(Some((contribution, measurement)))
    })();
    let _ = fs::remove_file(path);
    result
  }).collect::<Result<Vec<_>, _>>()?;
  let mut constraints = base.constraints as i128;
  let mut measured = Vec::new();
  for (contribution, measurement) in increments.into_iter().flatten() {
    constraints = constraints
      .checked_add(contribution)
      .ok_or("constraint estimate overflow")?;
    measured.push(measurement);
  }
  let constraints = u64::try_from(constraints)
    .map_err(|_error| "negative or overflowing constraint estimate")?;
  let domain = constraints
    .checked_add(schema.public_inputs as u64)
    .and_then(u64::checked_next_power_of_two)
    .ok_or("domain estimate overflow")?;
  Ok(
    serde_json::json!({"format":"ix-aiur-plonk-extrapolated-cost-v1","constraints_extrapolated":constraints,"domain_extrapolated":domain,"fits_retained_ignition":domain<=1<<25,"baseline_constraints":base.constraints,"baseline_dynamic_rows":4,"public_inputs":schema.public_inputs,"increments":measured}),
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::{artifact::WidePackage, field::FieldBackend, trace::TracePlan};
  use ix_proof_compression::aiur_backend::{
    Bn254, kzg::Compiler, plonk::Exporter,
  };
  use std::sync::Arc;

  #[test]
  fn extrapolation_matches_full_compile_with_rom_boundaries() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("../aiur/tests/fixtures/bn254-trace.ixa");
    let package = WidePackage::decode(&fs::read(path).unwrap()).unwrap();
    let trace = package.trace.unwrap();
    let mut program = package.program.check_with(Bn254).unwrap();
    program.track_depth(&trace).unwrap();
    let plan = TracePlan::new(Arc::new(program), trace).unwrap();
    let entry = "BN254Trace::run";
    let args = [Bn254.from_u64(3), Bn254.neg(Bn254.one())];
    let record = plan.program().execute(entry, args.to_vec()).unwrap();
    let public = plan.public_args(&record, entry, &args).unwrap();
    let compiler = Compiler::new(&plan).unwrap();
    let capacities: Vec<_> = compiler
      .row_counts(&record)
      .unwrap()
      .into_iter()
      .zip(compiler.inputs())
      .map(
        |(height, input)| {
          if input.preprocessed.is_some() { height } else { height.max(8) }
        },
      )
      .collect();
    let exporter =
      Exporter::new(&plan, &capacities, entry, &public, &record.output)
        .unwrap();
    let tag = std::time::SystemTime::now()
      .duration_since(std::time::UNIX_EPOCH)
      .unwrap()
      .as_nanos();
    let directory = std::env::temp_dir()
      .join(format!("ix-aiur-capacity-{}-{tag}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let predicted = estimate(exporter.schema(), &directory).unwrap();
    let actual =
      gnark::compile(exporter.schema(), &directory.join("full.bin")).unwrap();
    assert_eq!(
      predicted["constraints_extrapolated"].as_u64().unwrap(),
      actual.constraints as u64
    );
    assert_eq!(
      predicted["domain_extrapolated"].as_u64().unwrap(),
      actual.domain
    );
    fs::remove_dir_all(directory).unwrap();
  }
}
