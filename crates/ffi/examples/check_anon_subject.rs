//! Bounded-run building block for profiling ONE anonymous work item by primary
//! address. Dependencies are lazily ingressed but trusted, exactly as in one
//! work item of `ix check-rs --anon`. This is NOT corpus/closure verification.
//!
//! cargo run --release -p ix-ffi --example check_anon_subject -- FILE.ixe HEX
//!
//! Run under an external timeout/memory limit. IX_MAX_REC_FUEL and the existing
//! kernel diagnostic variables are honored. A fresh process gives a fresh
//! KEnv and avoids carrying worker-history caches between samples.

use std::{
  path::Path, process::ExitCode, sync::atomic::Ordering, time::Instant,
};

use ix_common::address::Address;
use ix_kernel::{
  anon_work::build_anon_work, env::KEnv, id::KId, mode::Anon, tc::TypeChecker,
};
use ixon::env::Env;

// Match the native ix executable, without calling its Lean FFI entrypoints.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn check(path: &str, primary: &Address) -> Result<bool, String> {
  let start = Instant::now();
  let env = Env::get_anon_mmap(Path::new(path))?;
  let load_secs = start.elapsed().as_secs_f64();
  let start = Instant::now();
  let work = build_anon_work(&env)?;
  let item =
    work.iter().find(|item| item.primary() == primary).ok_or_else(|| {
      format!("{} is not a work-item primary address", primary.hex())
    })?;
  let targets = item.targets().len();
  eprintln!(
    "[subject] primary={} targets={targets} scope=subject-only workers=1 fuel_cap_per_member={} load={load_secs:.3}s enumerate={:.3}s",
    primary.hex(),
    ix_kernel::tc::max_rec_fuel(),
    start.elapsed().as_secs_f64()
  );
  let mut kenv = KEnv::<Anon>::new();
  let _ = ix_kernel::profile::take_op_counts();
  let start = Instant::now();
  let (result, last_member_fuel, peak_def_eq_depth) = {
    let mut tc = TypeChecker::new_with_lazy_anon(&mut kenv, &env);
    tc.set_debug_label(format!("#{}", primary.hex()));
    let result = tc.check_const(&KId::new(primary.clone(), ()));
    (result, tc.fuel_used(), tc.def_eq_peak)
  };
  let check_secs = start.elapsed().as_secs_f64();
  let ops = ix_kernel::profile::take_op_counts();
  let aggregate_fuel = ix_kernel::perf::enabled()
    .then(|| kenv.perf.total_rec_fuel_used.load(Ordering::Relaxed));
  let report = serde_json::json!({
    "primary": primary.hex(), "scope": "subject-only", "targets": targets,
    "passed": result.is_ok(), "error": result.as_ref().err().map(ToString::to_string),
    "load_secs": load_secs, "check_secs": check_secs,
    "fuel_cap_per_member": ix_kernel::tc::max_rec_fuel(),
    "last_member_fuel": last_member_fuel,
    // Null unless IX_PERF_COUNTERS is enabled; do not label the final member's
    // budget as the total fuel of a multi-member work item.
    "aggregate_fuel": aggregate_fuel, "last_member_def_eq_peak": peak_def_eq_depth,
    "subst": ops.subst_nodes, "whnf": ops.whnf_calls,
    "def_eq": ops.def_eq_calls, "intern": ops.intern_nodes,
    "nat_arith": ops.nat_arith,
  });
  println!("{report}");
  Ok(result.is_ok())
}

fn main() -> ExitCode {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if args.len() != 2 {
    eprintln!(
      "usage: check_anon_subject FILE.ixe PRIMARY_HEX\nSubject-only profiling: dependencies are trusted, not checked."
    );
    return ExitCode::from(2);
  }
  let Some(primary) = Address::from_hex(&args[1]) else {
    eprintln!("invalid primary address: {}", args[1]);
    return ExitCode::from(2);
  };
  // Match the CLI's dedicated worker stack, not the process main stack.
  let worker = std::thread::Builder::new()
    .name("ix-kernel-subject".to_owned())
    .stack_size(256 * 1024 * 1024)
    .spawn(move || check(&args[0], &primary));
  match worker {
    Ok(worker) => match worker.join() {
      Ok(Ok(true)) => ExitCode::SUCCESS,
      Ok(Ok(false)) => ExitCode::FAILURE,
      Ok(Err(error)) => {
        eprintln!("{error}");
        ExitCode::from(2)
      },
      Err(_) => {
        eprintln!("subject worker panicked");
        ExitCode::from(2)
      },
    },
    Err(error) => {
      eprintln!("cannot start subject worker: {error}");
      ExitCode::from(2)
    },
  }
}
