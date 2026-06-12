//! Name the member defs of given shards of a `.ixes` manifest.
//!
//!   cargo run -p ix-kernel --release --example shard_names -- <env.ixe> <plan.ixes> <idx>...

use std::collections::HashMap;

use ix_common::address::Address;
use ix_kernel::shard::ShardManifest;
use ixon::constant::ConstantInfo as CI;
use ixon::env::Env as IxonEnv;

fn block_of(env: &IxonEnv, addr: &Address) -> Address {
  match env.get_const(addr) {
    Some(c) => match &c.info {
      CI::IPrj(p) => p.block.clone(),
      CI::CPrj(p) => p.block.clone(),
      CI::RPrj(p) => p.block.clone(),
      CI::DPrj(p) => p.block.clone(),
      _ => addr.clone(),
    },
    None => addr.clone(),
  }
}

fn main() {
  let a: Vec<String> = std::env::args().collect();
  let ixe = &a[1];
  let ixes = &a[2];
  let idxs: Vec<usize> = a[3..].iter().filter_map(|s| s.parse().ok()).collect();

  let env = IxonEnv::get(&mut &std::fs::read(ixe).unwrap()[..]).expect("get");
  let m =
    ShardManifest::from_bytes(&std::fs::read(ixes).unwrap()).expect("manifest");

  // block address -> member def names (group named consts by their home block).
  let mut block2names: HashMap<Address, Vec<String>> = HashMap::new();
  for e in env.named.iter() {
    let blk = block_of(&env, &e.value().addr);
    block2names.entry(blk).or_default().push(e.key().to_string());
  }

  for idx in idxs {
    let s = &m.shards[idx];
    println!(
      "\n=== shard {idx}: {} block(s), {} heartbeats ===",
      s.blocks.len(),
      s.heartbeats
    );
    let mut shown = 0;
    for b in &s.blocks {
      let mut names = block2names.get(b).cloned().unwrap_or_default();
      names.sort();
      names.dedup();
      if shown < 12 {
        if names.is_empty() {
          println!("  {}…  (no named member)", &b.hex()[..16]);
        } else {
          println!("  {}…  {}", &b.hex()[..16], names.join(", "));
        }
      }
      shown += 1;
    }
    if s.blocks.len() > 12 {
      println!("  … and {} more block(s)", s.blocks.len() - 12);
    }
  }
}
