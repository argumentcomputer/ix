use aiur::{artifact::Package, trace::stark::Parameters};
use serde_json::json;
use stark_verifier::compress_wrap::{
  Capacities, Input, LAYOUT_CONFIG_FORMAT, Layout, LayoutConfig, Statement,
  Wrapper,
};
use std::{error::Error, fs, path::Path, time::Instant};

const USAGE: &str = "research wrapper commands:\n  stark-verifier wrap-input ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 OUTPUT\n  stark-verifier wrap-plan PACKAGE ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 OUTPUT [HEADROOM]\n  stark-verifier wrap-layout PACKAGE ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 OUTPUT_JSON ROW_BOUNDS_JSON GROUPING VERSION [LEAN_CAPACITIES_LAYOUT]\n  stark-verifier wrap-prove PACKAGE ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 LAYOUT|LAYOUT_CONFIG OUTPUT [DEVICE]\n  stark-verifier wrap-verify PACKAGE PACKAGE_BLAKE3 WRAPPER_KEY_BLAKE3 EXPECTED_ROOT_KEY_BLAKE3 EXPECTED_ROOT_CLAIMS WRAPPER_PROOF [LAYOUT|LAYOUT_CONFIG]";

fn pin(value: &str) -> Result<[u8; 32], Box<dyn Error>> {
  Ok(*blake3::Hash::from_hex(value)?.as_bytes())
}

fn load_input(args: &[String]) -> Result<Input, Box<dyn Error>> {
  if args.len() < 4 {
    return Err(USAGE.into());
  }
  Ok(Input::from_bytes(
    &fs::read(&args[0])?,
    pin(&args[3])?,
    &fs::read(&args[1])?,
    &fs::read(&args[2])?,
  )?)
}

/// A plain layout, or a versioned configuration.
fn read_layout(
  path: &str,
) -> Result<(Layout, Option<LayoutConfig>), Box<dyn Error>> {
  let value: serde_json::Value = serde_json::from_slice(&fs::read(path)?)?;
  if value.get("format").is_some() {
    let config: LayoutConfig = serde_json::from_value(value)?;
    Ok((config.layout.clone(), Some(config)))
  } else {
    Ok((serde_json::from_value(value)?, None))
  }
}

/// The wrapper of the layout at `path` ([`Wrapper::for_layout`]), checked
/// against it, and the layout.
fn layout_wrapper(
  package: Package,
  path: &str,
  device: Option<i32>,
) -> Result<(Wrapper, Layout), Box<dyn Error>> {
  let (layout, config) = read_layout(path)?;
  let wrapper =
    Wrapper::for_layout(package, Parameters::default(), device, &layout)?;
  if let Some(config) = config {
    config.check(&wrapper)?;
  }
  Ok((wrapper, layout))
}

fn new_directory(path: &Path) -> Result<(), Box<dyn Error>> {
  fs::create_dir_all(path)?;
  if fs::read_dir(path)?.next().transpose()?.is_some() {
    return Err(
      format!("wrapper output directory is not empty: {}", path.display())
        .into(),
    );
  }
  Ok(())
}

fn write_input(out: &Path, input: &Input) -> Result<(), Box<dyn Error>> {
  fs::write(out.join("root-key.bin"), input.key_bytes())?;
  fs::write(out.join("root-claims.bin"), input.claims_bytes())?;
  fs::write(out.join("statement.bin"), input.statement().preimage())?;
  input.invocation().store(&out.join("input.ixi"))?;
  Ok(())
}

pub(crate) fn run(cli: &[String]) -> Result<(), Box<dyn Error>> {
  let args = &cli[2..];
  match cli[1].as_str() {
    "wrap-input" => {
      if args.len() != 5 {
        return Err(USAGE.into());
      }
      let input = load_input(args)?;
      let out = Path::new(&args[4]);
      new_directory(out)?;
      write_input(out, &input)?;
      println!(
        "verified root and wrote wrapper invocation to {}",
        out.display()
      );
      Ok(())
    },
    "wrap-verify" => {
      if !(6..=7).contains(&args.len()) {
        return Err(USAGE.into());
      }
      let bytes = fs::read(&args[0])?;
      let (artifact_pin, key_pin) = (pin(&args[1])?, pin(&args[2])?);
      let claims =
        stark_verifier::compress_wrap::decode_claims(&fs::read(&args[4])?)?;
      let expected = Statement::new(pin(&args[3])?, &claims);
      let proof = fs::read(&args[5])?;
      if let Some(path) = args.get(6) {
        let (layout, config) = read_layout(path)?;
        let wrapper = Wrapper::from_bytes_for_layout(
          &bytes,
          &artifact_pin,
          &key_pin,
          Parameters::default(),
          None,
          &layout,
        )?;
        if let Some(config) = config {
          config.check(&wrapper)?;
        }
        wrapper.verify_normalized(&expected, &proof, &layout)?;
      } else {
        let wrapper = Wrapper::from_bytes(
          &bytes,
          &artifact_pin,
          &key_pin,
          Parameters::default(),
          None,
        )?;
        wrapper.verify(&expected, &proof)?;
      }
      println!(
        "verified compression wrapper against the expected root key and claims"
      );
      Ok(())
    },
    "wrap-layout" => layout_config(args),
    "wrap-plan" | "wrap-prove" => profile_or_prove(&cli[1], args),
    _ => Err(USAGE.into()),
  }
}

fn profile_or_prove(mode: &str, args: &[String]) -> Result<(), Box<dyn Error>> {
  let prove = mode == "wrap-prove";
  let required = if prove { 7 } else { 6 };
  if !(required..=required + 1).contains(&args.len()) {
    return Err(USAGE.into());
  }
  let input = load_input(&args[1..])?;
  let out = Path::new(&args[if prove { 6 } else { 5 }]);
  let (package, artifact_digest) = Package::load(args[0].as_ref())?;
  let device =
    if prove { args.get(7).map(|x| x.parse()).transpose()? } else { None };
  let start = Instant::now();
  let (wrapper, supplied_layout) = if prove {
    let (wrapper, layout) = layout_wrapper(package, &args[5], device)?;
    (wrapper, Some(layout))
  } else {
    (Wrapper::new(package, Parameters::default(), device)?, None)
  };
  let setup_seconds = start.elapsed().as_secs_f64();
  let headroom = if prove {
    0
  } else {
    args.get(6).map(|x| x.parse()).transpose()?.unwrap_or(0)
  };
  new_directory(out)?;
  let start = Instant::now();
  let execution = wrapper.execute(&input)?;
  let execute_seconds = start.elapsed().as_secs_f64();
  let layout = match supplied_layout {
    Some(layout) => layout,
    None => wrapper.plan_layout(&execution, headroom)?,
  };
  let start = Instant::now();
  let admission = wrapper.admit(&execution, &layout)?;
  let admission_seconds = start.elapsed().as_secs_f64();
  let parameters = wrapper.parameters();
  let cp = parameters.commitment();
  let fp = parameters.fri();
  let mut report = json!({
    "format": "ix-compress-wrap-profile-v1",
    "input": {
      "key_blake3": blake3::hash(input.key_bytes()).to_hex().to_string(),
      "claims_blake3": blake3::hash(input.claims_bytes()).to_hex().to_string(),
      "proof_blake3": blake3::hash(input.proof_bytes()).to_hex().to_string(),
    },
    "wrapper": {
      "artifact_blake3": artifact_digest.to_string(),
      "key_blake3": blake3::hash(wrapper.key_bytes()).to_hex().to_string(),
      "entry": stark_verifier::compress_wrap::ENTRY,
      "lowering": wrapper.lowering(),
      "circuits": wrapper.circuit_statistics().len(),
      "fixed_circuits": wrapper
        .circuit_statistics()
        .iter()
        .filter(|c| c.preprocessed_height != 0)
        .count(),
      "rust_cross_check": wrapper.cross_check(),
      "setup_seconds": setup_seconds,
    },
    "parameters": {
      "log_blowup": cp.log_blowup,
      "cap_height": cp.cap_height,
      "num_queries": fp.num_queries,
      "log_final_poly_len": fp.log_final_poly_len,
      "max_log_arity": fp.max_log_arity,
      "commit_proof_of_work_bits": fp.commit_proof_of_work_bits,
      "query_proof_of_work_bits": fp.query_proof_of_work_bits,
    },
    "field_bytes": 8,
    "execution_seconds": execute_seconds,
    "execution_statistics": wrapper.statistics(&execution)?,
    "storage": execution.record().storage_usage(),
    "layout": layout,
    "layout_blake3": blake3::Hash::from(layout.blake3()?).to_hex().to_string(),
    "admission": admission,
    "admission_seconds": admission_seconds,
    "verified": false,
  });
  write_input(out, &input)?;
  fs::write(out.join("layout.json"), serde_json::to_vec_pretty(&layout)?)?;
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  if prove {
    let start = Instant::now();
    let result = wrapper.prove_normalized(execution, &layout)?;
    wrapper.verify_normalized(input.statement(), &result.proof, &layout)?;
    fs::write(out.join("key.bin"), result.key)?;
    fs::write(out.join("claims.bin"), result.claims)?;
    fs::write(out.join("proof.bin"), &result.proof)?;
    stark_verifier::Invocation {
      entry: stark_verifier::compress_wrap::ENTRY.into(),
      args: input.statement().arguments().to_vec(),
      streams: Default::default(),
    }
    .store(&out.join("public.ixi"))?;
    report["verified"] = true.into();
    report["proving_seconds"] = start.elapsed().as_secs_f64().into();
    report["proof_bytes"] = result.proof.len().into();
    report["shards"] = 1.into();
  }
  report["peak_rss_bytes"] =
    aiur::trace::stark::planning::peak_resident_memory().into();
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{report}");
  Ok(())
}

fn layout_config(args: &[String]) -> Result<(), Box<dyn Error>> {
  if !(9..=10).contains(&args.len()) {
    return Err(USAGE.into());
  }
  let input = load_input(&args[1..])?;
  let (package, _) = Package::load(args[0].as_ref())?;
  // With a Rust-lowering layout, the Lean wrapper's ROM tables take its
  // ROM capacities, and the row bounds are matched by circuit name.
  let lean = args.get(9).map(|path| read_layout(path)).transpose()?;
  let wrapper = match &lean {
    Some((rust, _)) => Wrapper::lean(
      package,
      Parameters::default(),
      None,
      Capacities::Rust(&rust.log_heights),
    )?,
    None => Wrapper::new(package, Parameters::default(), None)?,
  };
  let execution = wrapper.execute(&input)?;
  let bounds: serde_json::Value = serde_json::from_slice(&fs::read(&args[6])?)?;
  let circuits =
    bounds["circuits"].as_array().ok_or("row bounds need a circuits array")?;
  let statistics = wrapper.statistics(&execution)?;
  if circuits.len() != statistics.circuits.len() {
    return Err("row bounds list a different number of circuits".into());
  }
  let mut row_bounds = Vec::with_capacity(circuits.len());
  for (k, circuit) in statistics.circuits.iter().enumerate() {
    let name = circuit.shape.name.as_str();
    let bound = if lean.is_some() {
      circuits
        .iter()
        .find(|b| b["name"].as_str() == Some(name))
        .ok_or_else(|| format!("no row bound for {name}"))?
    } else if circuits[k]["name"].as_str() == Some(name) {
      &circuits[k]
    } else {
      return Err(format!("row bound for {name} is out of order").into());
    };
    row_bounds.push(usize::try_from(
      bound["max_rows"].as_u64().ok_or("row bound needs max_rows")?,
    )?);
  }
  let layout = wrapper.plan_capacities(&execution, &row_bounds)?;
  let admission = wrapper.admit(&execution, &layout)?;
  let sizing_input = json!({
    "root_key_blake3": blake3::hash(input.key_bytes()).to_hex().to_string(),
    "root_claims_blake3": blake3::hash(input.claims_bytes()).to_hex().to_string(),
    "root_proof_blake3": blake3::hash(input.proof_bytes()).to_hex().to_string(),
  });
  let config = LayoutConfig {
    format: LAYOUT_CONFIG_FORMAT.into(),
    version: args[8].parse()?,
    grouping: args[7].clone(),
    artifact_blake3: blake3::Hash::from(*wrapper.artifact_digest())
      .to_hex()
      .to_string(),
    layout_blake3: blake3::Hash::from(layout.blake3()?).to_hex().to_string(),
    layout,
    sizing: json!({
      "rule": "each resizable circuit at the smallest power of two covering both the sizing root's rows and its row bound; fixed tables at their preprocessed height",
      "row_bounds": bounds,
      "sizing_root": sizing_input,
      "admission": admission,
    }),
  };
  config.check(&wrapper)?;
  fs::write(&args[5], serde_json::to_vec_pretty(&config)?)?;
  println!(
    "{}",
    serde_json::to_string(
      &json!({"layout_blake3": config.layout_blake3, "key_blake3": config.layout.key_blake3})
    )?
  );
  Ok(())
}
