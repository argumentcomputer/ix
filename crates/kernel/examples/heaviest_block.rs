//! Identify, by Lean name, the heaviest blocks in a `.ixe` — in particular the
//! atomic mutual block that floors sharding. Profiles the env (heartbeats per
//! block), ranks blocks, then reverse-maps each block's address to the Lean
//! names of its members via the env's `names` metadata.
//!
//!   cargo run -p ix-kernel --release --example heaviest_block -- <env.ixe> [top_k]

use ix_common::address::Address;
use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
use ix_kernel::profile::{ProfileBuilder, ProfileSink};
use ix_kernel::tc::TypeChecker;
use ixon::constant::ConstantInfo as CI;
use ixon::env::Env as IxonEnv;

/// A constant's home block: a projection's `block`, else the constant itself.
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
  let args: Vec<String> = std::env::args().collect();
  let Some(path) = args.get(1).cloned() else {
    eprintln!("usage: heaviest_block <env.ixe> [top_k]");
    std::process::exit(1);
  };
  let top_k: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(3);

  let bytes = std::fs::read(&path).expect("read .ixe");

  // ---- Profile (anon) for per-block heartbeats. ----
  let env = IxonEnv::get_anon(&mut &bytes[..]).expect("get_anon");
  let work = build_anon_work(&env).expect("build_anon_work");
  let mut kenv = KEnv::<Anon>::new();
  kenv.profile_sink = Some(ProfileSink::new(true));
  for item in &work {
    let kid = KId::<Anon>::new(item.primary().clone(), ());
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    let _ = tc.check_const(&kid);
    tc.finish_constant_accounting();
  }
  let sink = kenv.profile_sink.take().unwrap();
  let mut builder = ProfileBuilder::new();
  for (consumer, rec) in &sink.records {
    builder.block(block_of(&env, consumer), rec.fuel, 0, 1);
  }
  let profile = builder.finish();
  let mut blocks: Vec<(Address, u64)> =
    profile.blocks().iter().map(|b| (b.addr.clone(), b.heartbeats)).collect();
  blocks.sort_by(|a, b| b.1.cmp(&a.1));

  // ---- Full env for names; reverse-map addresses → Lean names. ----
  let full = IxonEnv::get(&mut &bytes[..]).expect("get");

  eprintln!(
    "env metadata: {} consts, {} named, {} names entries",
    full.consts.iter().count(),
    full.named.iter().count(),
    full.names.iter().count(),
  );
  // Diagnostic: is the heaviest anon block addr present in consts/names/named?
  if let Some((addr, _)) = blocks.first() {
    eprintln!(
      "diag: heaviest anon block {}…  in consts={} names={} named_addrs={}",
      &addr.hex()[..16],
      full.get_const(addr).is_some(),
      full.names.get(addr).is_some(),
      full.named.iter().any(|e| e.value().addr == *addr),
    );
  }
  eprintln!("diag: sample names entries (addr → name):");
  for e in full.names.iter().take(4) {
    eprintln!("   {}… → {}", &e.key().hex()[..16], e.value());
  }
  eprintln!("diag: sample consts keys:");
  for e in full.consts.iter().take(4) {
    eprintln!("   {}…", &e.key().hex()[..16]);
  }
  eprintln!("Top {top_k} blocks by heartbeats in {path}:");
  for (addr, hb) in blocks.iter().take(top_k) {
    let direct = full
      .named
      .iter()
      .find(|e| e.value().addr == *addr)
      .map(|e| e.key().to_string());
    let mut members: Vec<String> = full
      .named
      .iter()
      .filter(|e| block_of(&full, &e.value().addr) == *addr)
      .map(|e| e.key().to_string())
      .collect();
    members.sort();
    members.dedup();
    eprintln!("\n  {hb} heartbeats — block {}…", &addr.hex()[..16]);
    if let Some(n) = direct {
      eprintln!("    name: {n}");
    }
    eprintln!("    {} named member(s):", members.len());
    for m in members.iter().take(40) {
      eprintln!("      {m}");
    }
    if members.len() > 40 {
      eprintln!("      … and {} more", members.len() - 40);
    }
  }
}
