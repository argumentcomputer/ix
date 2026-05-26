//! Native re-run of the SP1/Zisk guest's `check_const` loop, used to gather
//! data the zkVM guests cannot surface from inside the proof environment.
//!
//! `crates/kernel/src/lib.rs` short-circuits every `IX_*` env-var read on
//! `target_os = "zkvm"`, so the kernel's perf-counter infrastructure
//! (`crates/kernel/src/perf.rs`) is inert inside SP1/Zisk guests. Run this
//! native binary against the same `.ixe` to read cache hit rates, peak/avg
//! fuel per constant, and a wall-clock baseline. Combine with the SP1
//! cycle-tracker output (see `sp1/host/src/main.rs` and
//! `sp1/guest/src/main.rs`) to attribute zkVM cycles to specific phases.
//!
//!   IX_PERF_COUNTERS=1 cargo run --release --example perf_check -- path.ixe
//!
//! Mirrors `sp1/guest/src/main.rs` (Anon mode; no Meta-mode variant since
//! the cache and fuel behaviour is materially the same and Meta only adds
//! a few percent of cycles in the zkVM).

use std::env;
use std::fs;
use std::time::Instant;

use ix_kernel::id::KId;
use ix_kernel::ingress::ixon_ingress_owned;
use ix_kernel::mode::Anon;
use ix_kernel::tc::TypeChecker;
use ixon::env::Env as IxonEnv;
use ixon::metadata::ConstantMetaInfo;

fn main() {
  env_logger::builder()
    .filter_level(log::LevelFilter::Info)
    .format_timestamp(None)
    .init();
  let path = env::args().nth(1).expect("usage: perf_check <ixe>");
  let bytes = fs::read(&path).expect("read ixe");

  // Collect (KId, pretty-name) pairs so the per-kid log lines line up with
  // the `kid_NNN` labels printed by the SP1 guest's cycle tracker.
  let env = IxonEnv::get(&mut &bytes[..]).expect("decode env");
  let entries: Vec<(KId<Anon>, String)> = env
    .named
    .iter()
    .filter(|e| !matches!(e.value().meta.info, ConstantMetaInfo::Muts { .. }))
    .map(|e| (KId::<Anon>::new(e.value().addr.clone(), ()), e.key().pretty()))
    .collect();
  let kids: Vec<KId<Anon>> = entries.iter().map(|(k, _)| k.clone()).collect();
  eprintln!("[perf_check] env loaded: {} consts", kids.len());
  for (i, (_, name)) in entries.iter().enumerate() {
    eprintln!("  kid_{i:03}  {name}");
  }

  let t_ingress = Instant::now();
  let (mut kenv, _intern) = ixon_ingress_owned::<Anon>(env).expect("ingress");
  eprintln!("[perf_check] ingress:    {:>8.2?}", t_ingress.elapsed());

  let t_check = Instant::now();
  let mut failures = 0u32;
  let mut tc = TypeChecker::new(&mut kenv);
  for kid in &kids {
    if tc.check_const(kid).is_err() {
      failures = failures.saturating_add(1);
    }
  }
  eprintln!(
    "[perf_check] check_const: {:>8.2?} ({} failures)",
    t_check.elapsed(),
    failures
  );
  // Drop the TC first so its borrow on KEnv ends; KEnv's `Drop` is what
  // actually dumps the `PerfCounters` summary when IX_PERF_COUNTERS=1.
  drop(tc);
  drop(kenv);
}
