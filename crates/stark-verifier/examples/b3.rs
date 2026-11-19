//! `b3 FILE...`: each file's BLAKE3, as `b3sum` prints it.
fn main() -> Result<(), Box<dyn std::error::Error>> {
  for path in std::env::args().skip(1) {
    println!("{}  {path}", blake3::hash(&std::fs::read(&path)?).to_hex());
  }
  Ok(())
}
