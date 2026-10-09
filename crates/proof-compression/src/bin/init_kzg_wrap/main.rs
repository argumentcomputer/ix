fn main() -> Result<(), Box<dyn std::error::Error>> {
  ix_proof_compression::pipeline::command(
    "wrap",
    &std::env::args().skip(1).collect::<Vec<_>>(),
  )
}
