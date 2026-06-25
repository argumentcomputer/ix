//! Check a single named constant's block and dump per-constant reduction
//! histograms: which constants the kernel delta-unfolds, which recursors
//! fire iota, and how many `Nat.succ` peels happen. Reverse-maps addresses
//! to Lean names via the env's `named` metadata.
//!
//!   IX_REDUCE_HISTO=1 cargo run -p ix-kernel --release \
//!     --example block_reduce_histo -- <env.ixe> <Lean.Name> [top_k]

use std::sync::atomic::Ordering;

use ix_common::address::Address;
use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
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
  let (Some(path), Some(target)) = (args.get(1).cloned(), args.get(2).cloned())
  else {
    eprintln!("usage: block_reduce_histo <env.ixe> <Lean.Name> [top_k]");
    std::process::exit(1);
  };
  let top_k: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(40);

  if std::env::var_os("IX_REDUCE_HISTO").is_none() {
    eprintln!("warning: IX_REDUCE_HISTO is not set; histograms will be empty");
  }

  let bytes = std::fs::read(&path).expect("read .ixe");
  let full = IxonEnv::get(&mut &bytes[..]).expect("get");

  // Resolve the Lean name to its anon addr, then its home block.
  let Some(target_addr) = full
    .named
    .iter()
    .find(|e| e.key().to_string() == target)
    .map(|e| e.value().addr.clone())
  else {
    eprintln!("name not found in env: {target}");
    std::process::exit(1);
  };
  let target_block = block_of(&full, &target_addr);
  eprintln!(
    "target {target} addr={}… block={}…",
    &target_addr.hex()[..16],
    &target_block.hex()[..16]
  );

  // Find the anon work item for that block and check just that item.
  let env = IxonEnv::get_anon(&mut &bytes[..]).expect("get_anon");
  let work = build_anon_work(&env).expect("build_anon_work");
  let item = work
    .iter()
    .find(|item| block_of(&env, item.primary()) == target_block)
    .expect("no work item for target block");

  let mut kenv = KEnv::<Anon>::new();
  let start = std::time::Instant::now();
  let kid = KId::<Anon>::new(item.primary().clone(), ());
  let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
  let result = tc.check_const(&kid);
  let fuel = tc.fuel_used();
  eprintln!(
    "check_const: {:?} in {:.1}s, fuel(heartbeats)={fuel}",
    result.map(|_| "ok"),
    start.elapsed().as_secs_f64()
  );

  // Reverse-map addr → Lean name (named addrs are anon addrs here).
  let name_of = |addr: &Address| -> String {
    full.named.iter().find(|e| e.value().addr == *addr).map_or_else(
      || format!("<anon {}…>", &addr.hex()[..16]),
      |e| e.key().to_string(),
    )
  };

  let dump = |label: &str, histo: &dashmap::DashMap<Address, u64>| {
    let mut rows: Vec<(Address, u64)> =
      histo.iter().map(|e| (e.key().clone(), *e.value())).collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1));
    let total: u64 = rows.iter().map(|(_, n)| n).sum();
    eprintln!("\n== {label}: {total} total, {} distinct ==", rows.len());
    for (addr, n) in rows.iter().take(top_k) {
      #[allow(clippy::cast_precision_loss)]
      let pct = *n as f64 / total.max(1) as f64 * 100.0;
      eprintln!("  {n:>12} ({pct:>5.1}%)  {}", name_of(addr));
    }
  };

  dump("delta unfolds", &ix_kernel::perf::DELTA_HISTO);
  dump("iota reductions", &ix_kernel::perf::IOTA_HISTO);
  eprintln!(
    "\nNat.succ peels: {}",
    ix_kernel::perf::NAT_SUCC_PEELS.load(Ordering::Relaxed)
  );
}
