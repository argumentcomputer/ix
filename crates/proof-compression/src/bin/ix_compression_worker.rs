//! The stage worker `ix compress` spawns: `ix-compression-worker <stage>
//! <args...>` runs one FRI, first KZG or recursive KZG stage. Stages run in
//! their own executable so the Lean executable links no KZG proving code or
//! its CUDA runtime, and so each heavy phase exits before the next starts.
fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<String> = std::env::args().skip(1).collect();
  let Some((stage, rest)) = args.split_first() else {
    return Err("usage: ix-compression-worker <fri|kzg|wrap> <args...>".into());
  };
  ix_proof_compression::pipeline::command(stage, rest)
}
