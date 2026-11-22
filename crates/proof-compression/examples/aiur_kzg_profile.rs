//! Execute the Aiur verifier on an independently checked predecessor proof.
//! Counts do not allocate proving traces or establish a proving-time estimate.
use aiur::{
  artifact::WidePackage, hints::HintChannels, maps::MapOverrides,
  trace::TracePlan,
};
use ix_proof_compression::{
  aiur_backend::{
    Bn254, fq, g1,
    kzg::{Compiler, VerifyingKey},
    kzg_advice as wire,
  },
  kzg::{KzgConfig, Scalar},
};
use serde_json::json;
use std::{fs, path::PathBuf, sync::Arc};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() != 7 {
    return Err("usage: aiur_kzg_profile ARTIFACT KEY KEY_BLAKE3 CALL CALL_BLAKE3 PROOF NEW_OUTPUT".into());
  }
  let out = PathBuf::from(&args[6]);
  fs::create_dir(&out)?;
  let key_bytes = fs::read(&args[1])?;
  let key_pin = blake3::Hash::from_hex(&args[2])?;
  let key = VerifyingKey::from_bytes(&key_bytes, key_pin.as_bytes())?;
  let call_bytes = fs::read(&args[3])?;
  let call_pin = blake3::Hash::from_hex(&args[4])?;
  if blake3::hash(&call_bytes) != call_pin {
    return Err("expected call digest mismatch".into());
  }
  let (call, used): (Vec<Scalar>, usize) = bincode::serde::decode_from_slice(
    &call_bytes,
    bincode::config::standard().with_limit::<67108864>(),
  )?;
  if used != call_bytes.len()
    || bincode::serde::encode_to_vec(&call, bincode::config::standard())?
      != call_bytes
  {
    return Err("noncanonical expected call".into());
  }
  let bytes = fs::read(&args[5])?;
  key.verify_bytes(&call, &bytes)?;
  let proof = key.decode_proof(&bytes)?;
  let key_wire = wire::key_bytes(&key)?;
  let claims_wire = wire::claims_bytes(&[call])?;
  let proof_wire = wire::proof_bytes(&proof)?;
  let inputs = wire::Inputs::new(
    key_wire.clone(),
    claims_wire.clone(),
    proof_wire,
    vec![],
  )?;
  let artifact = fs::read(&args[0])?;
  let package = WidePackage::decode(&artifact)?;
  let trace = package.trace.ok_or("missing trace artifact")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  inputs.register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let public: Vec<_> = wire::digest_words(blake3::hash(&key_wire).as_bytes())
    .into_iter()
    .chain(wire::digest_words(blake3::hash(&claims_wire).as_bytes()))
    .collect();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute("KzgVerifier::verify_deferred", public)?;
  let compiler = Compiler::new(&plan)?;
  let heights = compiler.row_counts(&record)?;
  let mut circuits = vec![];
  for ((input, name), &height) in
    compiler.inputs().iter().zip(compiler.names()).zip(&heights)
  {
    let graph = input
      .compile_graph(&multi_stark::system::extension_params::<KzgConfig>())
      .map_err(|e| format!("graph: {e:?}"))?;
    let degree = graph.max_constraint_degree.max(
      multi_stark::lookup::logup_max_degree(&graph, input.lookup_group_size),
    ) as usize;
    let quotient = (degree.max(2) - 1).next_power_of_two();
    let auxiliary = multi_stark::lookup::stage2_width(
      input.lookups.len(),
      input.lookup_group_size,
      1,
    );
    circuits.push(json!({"name":name,"height":height,"stage1_width":input.main_width,"stage2_width":auxiliary,"quotient_degree":quotient,"main_cells":height*input.main_width,"lookup_cells":height*auxiliary,"quotient_cells":height*quotient,"fixed_cells":input.preprocessed.as_ref().map_or(0,|m|m.values.len())}));
  }
  let functions=plan.function_chips().iter().enumerate().map(|(index,&chip)| {
    Ok(json!({"name":plan.program().program().functions[index].name,"chip":plan.artifact().chips[chip].name,"rows":record.queries.callable_rows(index).ok_or("missing function query count")?}))
  }).collect::<Result<Vec<_>,String>>()?;
  let mut totals = serde_json::Map::new();
  for name in ["main_cells", "lookup_cells", "quotient_cells", "fixed_cells"] {
    totals.insert(
      name.into(),
      circuits.iter().map(|c| c[name].as_u64().unwrap()).sum::<u64>().into(),
    );
  }
  for name in ["stage1_width", "stage2_width", "quotient_degree"] {
    totals.insert(
      name.into(),
      circuits
        .iter()
        .filter(|c| c["height"].as_u64().unwrap() != 0)
        .map(|c| c[name].as_u64().unwrap())
        .sum::<u64>()
        .into(),
    );
  }
  let report = json!({
    "format":"ix-aiur-kzg-predecessor-profile-v1",
    "scope":"Native predecessor verification followed by Aiur execution and exact row-count profiling. No proving traces allocated; no runtime or peak-memory estimate.",
    "artifact_blake3":blake3::hash(&artifact).to_hex().as_str(),
    "input":{"key_blake3":key_pin.to_hex().as_str(),"call_blake3":call_pin.to_hex().as_str(),"proof_blake3":blake3::hash(&bytes).to_hex().as_str(),"proof_bytes":bytes.len()},
    "native_predecessor_verified":true,"output":record.output,
    "max_height":heights.iter().max(),"totals":totals,"function_rows":functions,"circuits":circuits,
  });
  fs::write(out.join("profile.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string_pretty(&report["totals"])?);
  Ok(())
}
