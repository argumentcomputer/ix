//! Inspect a `.ixes` manifest: list the heaviest shards (index, heartbeats,
//! block count) so you can target one with the host's `--only-shard`.
//!
//!   cargo run -p ix-kernel --release --example manifest_info -- <plan.ixes>

use ix_kernel::shard::ShardManifest;

fn main() {
  let path = std::env::args().nth(1).expect("usage: manifest_info <plan.ixes>");
  let bytes = std::fs::read(&path).expect("read .ixes");
  let m = ShardManifest::from_bytes(&bytes).expect("parse .ixes");
  let mut idx: Vec<(usize, u64, usize)> = m
    .shards
    .iter()
    .enumerate()
    .map(|(i, s)| (i, s.heartbeats, s.blocks.len()))
    .collect();
  idx.sort_by(|a, b| b.1.cmp(&a.1));
  println!("{} shards. Heaviest:", m.num_shards);
  for (i, hb, nb) in idx.iter().take(6) {
    println!(
      "  manifest index {i}: {hb} heartbeats, {nb} block(s)  → host --only-shard {}",
      i + 1
    );
  }
}
