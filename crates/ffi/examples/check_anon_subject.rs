//! Bounded-run building block for profiling ONE anonymous work item by primary
//! address. Dependencies are lazily ingressed but trusted, exactly as in one
//! work item of `ix check-rs --anon`. This is NOT corpus/closure verification.
//!
//! cargo run --release -p ix-ffi --example check_anon_subject -- FILE.ixe HEX
//! cargo run --release -p ix-ffi --example check_anon_subject -- --resolve FILE.ixe HEX...
//!
//! `--resolve` only enumerates work: map target addresses (including non-primary
//! block members) to their primary, without checking anything or loading names.
//!
//! Run under an external timeout/memory limit. IX_MAX_REC_FUEL and the existing
//! kernel diagnostic variables are honored. A fresh process gives a fresh
//! KEnv and avoids carrying worker-history caches between samples.
//!
//! Diagnostic-only runs: `IX_PERF_COUNTERS=1` prints cache hit rates;
//! `IX_REDUCE_HISTO=1` prints the top 20 delta/iota addresses and totals.
//! `IX_SAME_HEAD_PROFILE=1` reports actual same-head attempts and their fuel.
//! `IX_HOT_MISSES=1` prints miss shapes once at completion; optional
//! `IX_HOT_MISS_CTX=1` includes their context identities.
//! Collection is bounded to 4,096 keys; reported counts are intervals after
//! low-frequency entries are replaced, not exact per-key totals.
//! Reports go to stderr after checking; stdout's subject JSON is unchanged.
//! Leave these flags unset for paired benchmark timings.

use std::{
  collections::{HashMap, HashSet},
  path::Path,
  process::ExitCode,
  sync::atomic::Ordering,
  time::Instant,
};

use ix_common::address::Address;
use ix_kernel::{
  anon_work::{AnonWorkItem, build_anon_work},
  env::KEnv,
  id::KId,
  mode::Anon,
  tc::TypeChecker,
};
use ixon::env::Env;

// Match the native ix executable, without calling its Lean FFI entrypoints.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[derive(Debug, PartialEq, Eq)]
struct ResolvedSubject {
  requested: Address,
  primary: Address,
  targets: usize,
}

fn resolve_subjects(
  work: &[AnonWorkItem],
  requested: &[Address],
) -> Result<Vec<ResolvedSubject>, String> {
  let wanted: HashSet<_> = requested.iter().cloned().collect();
  let mut found = HashMap::new();
  for item in work {
    for target in item.targets() {
      if wanted.contains(target) {
        found.insert(target.clone(), (item.primary(), item.targets().len()));
      }
    }
  }
  requested
    .iter()
    .map(|addr| {
      let (primary, targets) = found.get(addr).ok_or_else(|| {
        format!("{} is not a kernel-checkable target address", addr.hex())
      })?;
      Ok(ResolvedSubject {
        requested: addr.clone(),
        primary: (*primary).clone(),
        targets: *targets,
      })
    })
    .collect()
}

fn run(args: &[String]) -> Result<bool, String> {
  if args.first().is_some_and(|arg| arg == "--resolve") && args.len() >= 3 {
    let requested: Vec<_> = args[2..]
      .iter()
      .map(|arg| {
        Address::from_hex(arg).ok_or_else(|| format!("invalid address: {arg}"))
      })
      .collect::<Result<_, _>>()?;
    let env = Env::get_anon_mmap(Path::new(&args[1]))?;
    let work = build_anon_work(&env)?;
    let resolved = resolve_subjects(&work, &requested)?;
    let rows: Vec<_> = resolved
      .iter()
      .map(|row| {
        serde_json::json!({
          "requested": row.requested.hex(), "primary": row.primary.hex(),
          "targets": row.targets,
        })
      })
      .collect();
    println!(
      "{}",
      serde_json::json!({
        "scope": "index-only", "resolutions": rows,
      })
    );
    return Ok(true);
  }
  if args.len() != 2 || args[0] == "--resolve" {
    return Err("usage: check_anon_subject FILE.ixe PRIMARY_HEX\n       check_anon_subject --resolve FILE.ixe TARGET_HEX...\nSubject-only profiling: dependencies are trusted, not checked.".to_owned());
  }
  let primary = Address::from_hex(&args[1])
    .ok_or_else(|| format!("invalid primary address: {}", args[1]))?;
  check(&args[0], &primary)
}

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
  ix_kernel::perf::same_head::reset();
  let start = Instant::now();
  let (result, last_member_fuel, peak_def_eq_depth, hot_misses) = {
    let mut tc = TypeChecker::new_with_lazy_anon(&mut kenv, &env);
    tc.set_debug_label(format!("#{}", primary.hex()));
    let result = tc.check_const(&KId::new(primary.clone(), ()));
    let fuel = tc.fuel_used();
    let peak = tc.def_eq_peak;
    // TypeChecker has no Drop accounting. Flush the final member explicitly,
    // after capturing its allowance and before discarding the checker.
    tc.finish_constant_accounting();
    (result, fuel, peak, tc.hot_miss_summary())
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
  eprint!("{hot_misses}");
  eprint!("{}", ix_kernel::perf::same_head::summary());
  if ix_kernel::perf::enabled() {
    // The example does not install a log backend, so KEnv's log::info!
    // drop summary would otherwise be invisible. No checker work is rerun.
    eprint!("{}", kenv.perf.summary());
  }
  if ix_kernel::perf::reduce_histo_enabled() {
    print_reductions(
      "delta",
      ix_kernel::perf::DELTA_HISTO
        .iter()
        .map(|entry| (entry.key().clone(), *entry.value()))
        .collect(),
    );
    print_reductions(
      "iota",
      ix_kernel::perf::IOTA_HISTO
        .iter()
        .map(|entry| (entry.key().clone(), *entry.value()))
        .collect(),
    );
    eprintln!(
      "[reduce-histo] nat_succ_peels={}",
      ix_kernel::perf::NAT_SUCC_PEELS.load(Ordering::Relaxed)
    );
  }
  Ok(result.is_ok())
}

const REDUCTION_REPORT_LIMIT: usize = 20;

fn top_reductions(
  mut entries: Vec<(Address, u64)>,
) -> (u128, usize, Vec<(Address, u64)>) {
  let total = entries.iter().map(|(_, n)| u128::from(*n)).sum();
  let distinct = entries.len();
  entries.sort_unstable_by(|(a, x), (b, y)| y.cmp(x).then_with(|| a.cmp(b)));
  entries.truncate(REDUCTION_REPORT_LIMIT);
  (total, distinct, entries)
}

fn print_reductions(label: &str, entries: Vec<(Address, u64)>) {
  let (total, distinct, top) = top_reductions(entries);
  eprintln!(
    "[reduce-histo] {label}: {total} reductions across {distinct} addresses; top {}",
    top.len()
  );
  for (addr, count) in top {
    eprintln!("[reduce-histo] {label} {count} #{}", addr.hex());
  }
}

fn main() -> ExitCode {
  let args: Vec<_> = std::env::args().skip(1).collect();
  // Match the CLI's dedicated worker stack, not the process main stack.
  let worker = std::thread::Builder::new()
    .name("ix-kernel-subject".to_owned())
    .stack_size(256 * 1024 * 1024)
    .spawn(move || run(&args));
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn reduction_report_bounds_rows_but_preserves_complete_totals() {
    let entries: Vec<_> =
      (0..25u64).map(|n| (Address::hash(&n.to_le_bytes()), n + 1)).collect();
    let (total, distinct, top) = top_reductions(entries);
    assert_eq!(total, 325);
    assert_eq!(distinct, 25);
    assert_eq!(top.len(), REDUCTION_REPORT_LIMIT);
    assert_eq!(top.first().unwrap().1, 25);
    assert_eq!(top.last().unwrap().1, 6);
  }

  #[test]
  fn reduction_report_handles_ties_empty_input_and_wide_totals() {
    assert_eq!(top_reductions(Vec::new()), (0, 0, Vec::new()));
    let a = Address::hash(b"a");
    let b = Address::hash(b"b");
    let (total, distinct, top) =
      top_reductions(vec![(b.clone(), u64::MAX), (a.clone(), u64::MAX)]);
    assert_eq!(total, 2 * u128::from(u64::MAX));
    assert_eq!(distinct, 2);
    assert!(top[0].0 < top[1].0);
    assert_eq!(top_reductions(vec![(a, u64::MAX), (b, u64::MAX)]).2, top);
  }

  #[test]
  fn resolves_members_to_primary_preserving_request_order() {
    let a = Address::hash(b"standalone");
    let b = Address::hash(b"primary");
    let c = Address::hash(b"member");
    let work = vec![
      AnonWorkItem::Standalone { addr: a.clone() },
      AnonWorkItem::Block {
        block_addr: Address::hash(b"block"),
        primary: b.clone(),
        targets: vec![b.clone(), c.clone()],
      },
    ];
    let rows =
      resolve_subjects(&work, &[c.clone(), a.clone(), b.clone()]).unwrap();
    assert_eq!(
      rows,
      vec![
        ResolvedSubject { requested: c, primary: b.clone(), targets: 2 },
        ResolvedSubject { requested: a.clone(), primary: a, targets: 1 },
        ResolvedSubject { requested: b.clone(), primary: b, targets: 2 },
      ]
    );
  }

  #[test]
  fn missing_address_is_an_error_not_a_partial_success() {
    let a = Address::hash(b"present");
    let work = vec![AnonWorkItem::Standalone { addr: a.clone() }];
    assert!(resolve_subjects(&work, &[a, Address::hash(b"absent")]).is_err());
  }
}
