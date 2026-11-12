use aiur::{artifact::Package, trace::stark::Parameters};
use serde_json::json;
use stark_verifier::compress_wrap::{Input, Layout, Statement, Wrapper};
use std::{error::Error, fs, path::Path, time::Instant};

const USAGE: &str = "research wrapper commands:\n  stark-verifier wrap-input ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 OUTPUT\n  stark-verifier wrap-plan PACKAGE ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 OUTPUT [HEADROOM]\n  stark-verifier wrap-prove PACKAGE ROOT_KEY ROOT_CLAIMS ROOT_PROOF EXPECTED_KEY_BLAKE3 LAYOUT OUTPUT [DEVICE]\n  stark-verifier wrap-verify PACKAGE PACKAGE_BLAKE3 WRAPPER_KEY_BLAKE3 EXPECTED_ROOT_KEY_BLAKE3 EXPECTED_ROOT_CLAIMS WRAPPER_PROOF [LAYOUT]";

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
      let wrapper = Wrapper::from_bytes(
        &fs::read(&args[0])?,
        &pin(&args[1])?,
        &pin(&args[2])?,
        Parameters::default(),
        None,
      )?;
      let claims =
        stark_verifier::compress_wrap::decode_claims(&fs::read(&args[4])?)?;
      let expected = Statement::new(pin(&args[3])?, &claims);
      let proof = fs::read(&args[5])?;
      if let Some(path) = args.get(6) {
        let layout = serde_json::from_slice(&fs::read(path)?)?;
        wrapper.verify_normalized(&expected, &proof, &layout)?;
      } else {
        wrapper.verify(&expected, &proof)?;
      }
      println!(
        "verified compression wrapper against the expected root key and claims"
      );
      Ok(())
    },
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
  let wrapper = Wrapper::new(package, Parameters::default(), device)?;
  let supplied_layout: Option<Layout> = if prove {
    let layout = serde_json::from_slice(&fs::read(&args[5])?)?;
    wrapper.validate_layout(&layout)?;
    Some(layout)
  } else {
    None
  };
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
