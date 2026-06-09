//! Generate a `.ixes` sharding manifest from a `.ixe` env, out of circuit — a
//! standalone equivalent of `ix profile` + `ix shard` that does NOT go through
//! the Lean/FFI layer. Useful for producing a plan to feed the Zisk host's
//! `--shard-plan`, and for iterating the partitioner without a full Lean build.
//!
//! Usage:
//!   cargo run -p ix-kernel --release --example shard_plan -- <env.ixe> \
//!       (--shards N | --max-cycles C) [--cycles-per-heartbeat K] [--out path]
//!
//!   --shards N             partition into exactly N shards.
//!   --max-cycles C         size N to a per-shard guest-cycle budget instead
//!                          (the leaf prover's trace size = what sets peak RAM).
//!   --cycles-per-heartbeat K   heartbeat→cycle conversion (default 208000,
//!                          measured on mergesort; recalibrate per env with one
//!                          `--execute`: a shard's steps ÷ its heartbeats).
//!   --out path             output .ixes (default <env>.ixes).
//!
//! Converting a host-RAM budget to --max-cycles (empirical single-leaf model on
//! this prover: peak_RAM_GB ≈ 45 + 32 × cycles_billions):
//!     max_cycles ≈ (target_peak_GB − 45) / 32 × 1e9
//! e.g. a 256 GB box, ~195 GB safe target (≈50 GB headroom) → --max-cycles 4.5e9
//!
//! Profiles the env with the real kernel (single worker, cache-isolated so
//! heartbeats reflect un-memoized in-circuit cost and every delta-unfold is
//! recorded), aggregates per-constant records into a block profile, partitions,
//! and writes the manifest.

use ix_common::address::Address;
use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
use ix_kernel::profile::{BlockProfile, ProfileBuilder, ProfileSink};
use ix_kernel::shard::{partition_for_cycle_cap, Hypergraph, ShardManifest};
use ix_kernel::tc::TypeChecker;
use ixon::constant::ConstantInfo as CI;
use ixon::env::Env as IxonEnv;

/// Map a constant to its ingress block: a projection's `block` address,
/// otherwise the constant itself (mirrors the FFI profiler's `profile_block_of`).
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

fn block_size(env: &IxonEnv, block: &Address) -> u32 {
  env.get_const_bytes(block).map_or(0, |b| b.len().min(u32::MAX as usize) as u32)
}

/// Parse a count that may use float/scientific notation (e.g. `4.5e9`).
fn parse_count(s: &str) -> u64 {
  let v: f64 = s.parse().unwrap_or_else(|_| {
    eprintln!("error: not a number: {s}");
    std::process::exit(1);
  });
  if v < 0.0 {
    eprintln!("error: must be non-negative: {s}");
    std::process::exit(1);
  }
  v as u64
}

fn usage() -> ! {
  eprintln!(
    "usage: shard_plan <env.ixe> (--shards N | --max-cycles C) \
     [--cycles-per-heartbeat K] [--out path]"
  );
  eprintln!(
    "  --max-cycles is a per-shard guest-cycle budget; convert from RAM via \
     max_cycles ~= (target_peak_GB - 45) / 32 * 1e9  (256 GB box -> ~4.5e9)."
  );
  std::process::exit(1);
}

fn main() {
  // ---- Parse args. ----
  let args: Vec<String> = std::env::args().collect();
  let mut path: Option<String> = None;
  let mut shards: Option<usize> = None;
  let mut max_cycles: Option<u64> = None;
  // Default heartbeat→cycle ratio. Measured across 12 envs: large, shardable
  // envs (>20k hb) cluster at 194–208k whole-env; the per-shard ratio runs
  // higher (less memoization) — mergesort's heaviest shard is ~216k. 215k is
  // that per-shard value (the conservative end for the regime that needs
  // sharding). Tiny envs run lower (~130–160k, cheap arithmetic); a couple of
  // mid envs run ~258k (heavy def-eq) — recalibrate those via --execute.
  let mut cyc_per_hb: u64 = 215_000;
  let mut out: Option<String> = None;
  let mut i = 1;
  while i < args.len() {
    match args[i].as_str() {
      "--shards" => {
        i += 1;
        shards = Some(parse_count(args.get(i).unwrap_or(&String::new())) as usize);
      },
      "--max-cycles" => {
        i += 1;
        max_cycles = Some(parse_count(args.get(i).unwrap_or(&String::new())));
      },
      "--cycles-per-heartbeat" => {
        i += 1;
        cyc_per_hb = parse_count(args.get(i).unwrap_or(&String::new())).max(1);
      },
      "--out" => {
        i += 1;
        out = args.get(i).cloned();
      },
      s if s.starts_with("--") => {
        eprintln!("error: unknown flag {s}");
        usage();
      },
      s if path.is_none() => path = Some(s.to_string()),
      s => {
        eprintln!("error: unexpected argument {s}");
        usage();
      },
    }
    i += 1;
  }
  let Some(path) = path else { usage() };
  if shards.is_some() == max_cycles.is_some() {
    eprintln!("error: pass exactly one of --shards or --max-cycles");
    usage();
  }
  let out = out.unwrap_or_else(|| format!("{path}.ixes"));

  // ---- Profile: run the kernel, recording heartbeats + delta-unfold edges. ----
  let bytes = std::fs::read(&path).expect("read .ixe");
  let env = IxonEnv::get_anon(&mut &bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");

  let mut kenv = KEnv::<Anon>::new();
  kenv.profile_sink = Some(ProfileSink::new(true)); // isolate = sound recording
  let mut failures = 0usize;
  for item in &work {
    let kid = KId::<Anon>::new(item.primary().clone(), ());
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    if tc.check_const(&kid).is_err() {
      failures += 1;
    }
    tc.finish_constant_accounting();
  }
  let sink = kenv.profile_sink.take().expect("profile sink");

  // ---- Aggregate per-constant records into a block-level BlockProfile. ----
  let mut builder = ProfileBuilder::new();
  for (consumer, rec) in &sink.records {
    let cb = block_of(&env, consumer);
    let cs = block_size(&env, &cb);
    builder.block(cb.clone(), rec.fuel, cs, 1);
    for prod in &rec.producers {
      let pb = block_of(&env, prod);
      let ps = block_size(&env, &pb);
      builder.block(pb.clone(), 0, ps, 0);
      builder.delta_edge(cb.clone(), pb);
    }
  }
  let profile: BlockProfile = builder.finish();

  // ---- Choose the partition: explicit N, or sized to a cycle budget. ----
  let (shard_of, n) = match (shards, max_cycles) {
    (Some(n), None) => {
      let h = Hypergraph::from_profile(&profile);
      (h.partition(n, 0.05), n)
    },
    (None, Some(cap)) => {
      let plan = partition_for_cycle_cap(&profile, cap, cyc_per_hb, 0.05);
      let cyc = u128::from(plan.max_shard_heartbeats) * u128::from(cyc_per_hb);
      let floor_cyc =
        u128::from(plan.largest_block_heartbeats) * u128::from(cyc_per_hb);
      eprintln!(
        "budget: max_cycles={cap} → heartbeat_cap={} (@ {cyc_per_hb} cyc/hb) → N={}",
        plan.heartbeat_cap, plan.num_shards,
      );
      eprintln!(
        "  heaviest shard: {} hb (~{cyc} cycles); largest atomic block: {} hb (~{floor_cyc} cycles)",
        plan.max_shard_heartbeats, plan.largest_block_heartbeats,
      );
      if plan.infeasible_atomic_floor {
        eprintln!(
          "  WARNING: the largest atomic (mutual) block alone exceeds --max-cycles — \
           NO shard count can fit it. Split that block upstream (Lean side), raise \
           --max-cycles, or use a bigger box."
        );
      } else if plan.max_shard_heartbeats > plan.heartbeat_cap {
        eprintln!(
          "  note: heaviest shard still over cap at N={} (pinned by the atomic-block \
           floor); more shards won't lower it.",
          plan.num_shards,
        );
      }
      (plan.shard_of, plan.num_shards)
    },
    _ => unreachable!("validated exactly one of --shards / --max-cycles above"),
  };

  // ---- Manifest. ----
  let mut manifest = ShardManifest::build(&profile, &shard_of, n);
  for s in &mut manifest.shards {
    s.assumption_root = ixon::merkle::merkle_root_canonical(&s.foreign_blocks);
  }
  std::fs::write(&out, manifest.to_bytes()).expect("write .ixes manifest");

  eprintln!(
    "profiled {} work items ({failures} failure(s)), {} blocks, {} delta edges → {} shards; wrote {out}",
    work.len(),
    profile.num_blocks(),
    profile.num_edges(),
    manifest.num_shards,
  );
  eprintln!("{}", manifest.summary());
}
