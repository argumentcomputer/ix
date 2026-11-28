//! Instance statistics of an artifact's batch for `lake exe fri-security`, in
//! the JSON format of `stark-verifier statistics KEY PROOF`, for a hypothetical
//! shard in which every circuit is active at `2^LOG_HEIGHT` rows (a circuit
//! with a fixed table at its table's height), under the default parameters.
//! Every real shard whose circuits are at most that high has at most these
//! columns, constraints and lookup rows, so the soundness terms of this
//! instance bound those of the real shards.
//!
//! CI's 128-bit `fri-security` gate (`Scripts/CheckFormal.lean`) evaluates the
//! instances this writes for the pinned IxVM program under
//! `Tests/Fixtures/fri-security/`; `security128GateCases` there gives the
//! command that regenerates them when the program changes.
//!
//! Usage: `artifact_statistics ARTIFACT.ixa LOG_HEIGHT`
use aiur::{
  artifact::Package,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::types::Val;

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let [path, log] = args.as_slice() else {
    return Err("usage: artifact_statistics ARTIFACT.ixa LOG_HEIGHT".into());
  };
  let log: u32 = log.parse()?;
  if log > 40 {
    return Err("LOG_HEIGHT must be at most 40".into());
  }
  let (package, digest) = Package::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {digest}");
  let mut program = package.program.check_field::<Val>()?;
  let trace = package.trace.ok_or("the artifact has no circuits")?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let parameters = Parameters::DEFAULT;
  let backend = Backend::for_statistics(&plan, Parameters::DEFAULT)?;
  let stats = backend.statistics();
  let mut circuits = vec![];
  for (circuit, stat) in backend.system().circuits.iter().zip(&stats) {
    let height = if circuit.preprocessed_width > 0 {
      stat.preprocessed_height as u64
    } else {
      1u64 << log
    };
    circuits.push(serde_json::json!({
      "main": circuit.main_width, "pre": circuit.preprocessed_width,
      "height": height, "lookups": circuit.num_lookups,
      "stage2": circuit.stage_2_width, "group": circuit.lookup_group_size,
      "max_degree": circuit.max_constraint_degree,
      "zeros": circuit.graph.zeros.len(),
      "max_lookup_width": circuit.graph.lookups.iter()
        .map(|l| l.args.len()).max().unwrap_or(0),
    }));
  }
  println!(
    "{}",
    serde_json::json!({
      "artifact_blake3": digest.to_string(),
      "log_blowup": parameters.log_blowup, "cap": 0,
      "num_queries": parameters.num_queries,
      "commit_pow": parameters.commit_proof_of_work_bits,
      "query_pow": parameters.query_proof_of_work_bits, "max_log_arity": 1,
      "shards": 1,
      "circuits": circuits,
    })
  );
  Ok(())
}
