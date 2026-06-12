//! Generate a `.ixes` sharding manifest from a `.ixe` env, out of circuit — a
//! standalone equivalent of `ix profile` + `ix shard` that does NOT go through
//! the Lean/FFI layer. Useful for producing a plan to feed the Zisk host's
//! `--shard-plan`, and for iterating the partitioner without a full Lean build.
//!
//! Usage:
//!   cargo run -p ix-kernel --release --example shard_plan -- <env.ixe> \
//!       [--shards N | --max-cycles C] [--ram-gb G] [--cycles-per-heartbeat K] [--out path]
//!
//! By DEFAULT (no flags) it sizes the shard count automatically from this
//! machine's total RAM (`/proc/meminfo`): RAM → per-shard cycle cap (prover
//! model `peak_RAM_GB ≈ 45 + 32 × cycles_billions`, ~78% of RAM) → cap ÷
//! cycles-per-heartbeat → N from total heartbeats. So you just hand it the
//! `.ixe`; no budget to pick.
//!
//!   --shards N             force exactly N shards (skip the estimate).
//!   --max-cycles C         force a per-shard guest-cycle budget (skip RAM read).
//!   --ram-gb G             override detected RAM (for what-if sizing).
//!   --cycles-per-heartbeat K   heartbeat→cycle conversion (default 215000,
//!                          measured across envs; recalibrate per env with one
//!                          `--execute`: a shard's steps ÷ its heartbeats).
//!   --out path             output .ixes (default <env>.ixes).
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
use ix_kernel::shard::{
  Hypergraph, ShardManifest, cycle_cap_for_ram, partition_for_cycle_cap,
};
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
  env
    .get_const_bytes(block)
    .map_or(0, |b| u32::try_from(b.len()).unwrap_or(u32::MAX))
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
  #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
  // floor semantics intended; sign guarded by the non-negative exit above
  {
    v as u64
  }
}

/// Total RAM in GiB from `/proc/meminfo` (`None` off-Linux / on parse failure).
fn detect_ram_gb() -> Option<f64> {
  let s = std::fs::read_to_string("/proc/meminfo").ok()?;
  let line = s.lines().find(|l| l.starts_with("MemTotal:"))?;
  let kb: f64 = line.split_whitespace().nth(1)?.parse().ok()?;
  Some(kb / 1024.0 / 1024.0)
}

fn usage() -> ! {
  eprintln!(
    "usage: shard_plan <env.ixe> [--shards N | --max-cycles C] \
     [--ram-gb G] [--cycles-per-heartbeat K] [--store-dir dir] [--out path]"
  );
  eprintln!(
    "  default: size N automatically from this machine's RAM (/proc/meminfo).\n  \
     --shards N forces a count; --max-cycles C forces a per-shard cycle budget;\n  \
     --ram-gb G overrides detected RAM.\n  \
     --store-dir dir: store-aware planning — work items whose targets are all\n  \
     covered by the proof store are excluded (not profiled, not partitioned);\n  \
     the manifest covers only NOVEL work. The prover resolves the covered\n  \
     remainder by folding the store's proofs (zisk-host --store-dir)."
  );
  std::process::exit(1);
}

/// The proof store's covered-target set: the union of `proofs/*.cover`
/// (packed 32-byte addresses), exactly as `zisk-host --store-dir` writes them.
fn load_covered(dir: &str) -> std::collections::HashSet<Address> {
  let pdir = std::path::Path::new(dir).join("proofs");
  let mut covered = std::collections::HashSet::new();
  for idx in 0.. {
    let Ok(bytes) = std::fs::read(pdir.join(format!("{idx}.cover"))) else {
      break;
    };
    covered.extend(Address::unpack(&bytes));
  }
  covered
}

fn main() {
  // ---- Parse args. ----
  let args: Vec<String> = std::env::args().collect();
  let mut path: Option<String> = None;
  let mut shards: Option<usize> = None;
  let mut naive = false;
  let mut max_cycles: Option<u64> = None;
  // Default heartbeat→cycle ratio. Measured across 12 envs: large, shardable
  // envs (>20k hb) cluster at 194–208k whole-env; the per-shard ratio runs
  // higher (less memoization) — mergesort's heaviest shard is ~216k. 215k is
  // that per-shard value (the conservative end for the regime that needs
  // sharding). Tiny envs run lower (~130–160k, cheap arithmetic); a couple of
  // mid envs run ~258k (heavy def-eq) — recalibrate those via --execute.
  let mut cyc_per_hb: u64 = 215_000;
  let mut ram_gb: Option<f64> = None;
  let mut store_dir: Option<String> = None;
  let mut out: Option<String> = None;
  let mut i = 1;
  while i < args.len() {
    match args[i].as_str() {
      "--naive" => {
        naive = true;
      },
      "--shards" => {
        i += 1;
        shards = Some(
          usize::try_from(parse_count(args.get(i).unwrap_or(&String::new())))
            .expect("shard count fits usize"),
        );
      },
      "--max-cycles" => {
        i += 1;
        max_cycles = Some(parse_count(args.get(i).unwrap_or(&String::new())));
      },
      "--cycles-per-heartbeat" => {
        i += 1;
        cyc_per_hb = parse_count(args.get(i).unwrap_or(&String::new())).max(1);
      },
      "--ram-gb" => {
        i += 1;
        ram_gb = args.get(i).and_then(|s| s.parse::<f64>().ok());
      },
      "--store-dir" => {
        i += 1;
        store_dir = args.get(i).cloned();
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
  if shards.is_some() && max_cycles.is_some() {
    eprintln!("error: pass at most one of --shards / --max-cycles");
    usage();
  }
  let out = out.unwrap_or_else(|| format!("{path}.ixes"));

  // ---- Store-aware planning: drop work the store already covers. ----
  // A work item is covered iff every target it would certify is in the store
  // (the same rule the prover applies per shard). Covered items are not
  // profiled (no point typechecking them again) and not partitioned — they're
  // resolved at prove time by folding the store's proofs. Covered BLOCKS are
  // also excluded from the hypergraph: a novel→covered delta edge is an
  // assumption discharged at aggregation, not a cut to minimize.
  let covered: std::collections::HashSet<Address> =
    store_dir.as_deref().map(load_covered).unwrap_or_default();
  let covered_item = |item: &ix_kernel::anon_work::AnonWorkItem| -> bool {
    !covered.is_empty()
      && item.proven_targets().iter().all(|t| covered.contains(t))
  };

  // ---- Profile: run the kernel, recording heartbeats + delta-unfold edges. ----
  let bytes = std::fs::read(&path).expect("read .ixe");
  let env =
    IxonEnv::get_anon(&mut &bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");
  let (novel_work, covered_work): (Vec<_>, Vec<_>) =
    work.iter().partition(|item| !covered_item(item));
  // Blocks whose work item is covered — excluded from the hypergraph below.
  let covered_blocks: std::collections::HashSet<Address> =
    covered_work.iter().map(|item| block_of(&env, item.primary())).collect();
  if novel_work.is_empty() {
    eprintln!(
      "nothing to plan: the store covers all {} work items",
      work.len()
    );
    std::process::exit(0);
  }

  let mut kenv = KEnv::<Anon>::new();
  kenv.profile_sink = Some(ProfileSink::new(true)); // isolate = sound recording
  let mut failures = 0usize;
  for item in &novel_work {
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
      if covered_blocks.contains(&pb) {
        continue; // assumption against the store, not a partition edge
      }
      let ps = block_size(&env, &pb);
      builder.block(pb.clone(), 0, ps, 0);
      builder.delta_edge(cb.clone(), pb);
    }
  }
  let profile: BlockProfile = builder.finish();

  // ---- Choose the partition. Default: size N from the machine's RAM (no
  // budget needed). --shards N forces a count; --max-cycles C forces a budget.
  let (shard_of, n, tree) = if let (true, Some(n)) = (naive, shards) {
    // Naive baseline: group blocks into N contiguous (address-sorted) chunks,
    // ignoring the delta graph — to isolate the value of smart grouping. No
    // bisection tree (the prover falls back to a flat fold).
    let nb = profile.num_blocks();
    let chunk = nb.div_ceil(n.max(1)).max(1);
    let shard_of: Vec<u32> = (0..nb)
      .map(|b| {
        u32::try_from((b / chunk).min(n - 1)).expect("shard index fits u32")
      })
      .collect();
    eprintln!("naive grouping into {n} contiguous block chunks");
    (shard_of, n, None)
  } else if let Some(n) = shards {
    let h = Hypergraph::from_profile(&profile);
    let (so, t) = h.partition_with_tree(n, 0.05);
    (so, n, Some(t))
  } else {
    // Per-shard cycle cap: explicit --max-cycles, else derived from RAM.
    let cap = match max_cycles {
      Some(c) => {
        eprintln!("budget: --max-cycles {c}");
        c
      },
      None => {
        let ram = ram_gb.or_else(detect_ram_gb).unwrap_or_else(|| {
          eprintln!("warning: could not read /proc/meminfo; assuming 256 GB (override with --ram-gb)");
          256.0
        });
        let c = cycle_cap_for_ram(ram);
        if c == 0 {
          eprintln!(
            "error: {ram:.0} GB RAM is below the ~45 GB prover base — nothing will \
             prove on this machine."
          );
          std::process::exit(1);
        }
        eprintln!(
          "auto: machine RAM {ram:.0} GB → per-shard cap ~{c} cycles \
           (~78% RAM via prover model peak_GB≈45+32·Bcyc)"
        );
        c
      },
    };
    let plan = partition_for_cycle_cap(&profile, cap, cyc_per_hb, 0.05);
    let cyc = u128::from(plan.max_shard_heartbeats) * u128::from(cyc_per_hb);
    let floor_cyc =
      u128::from(plan.largest_block_heartbeats) * u128::from(cyc_per_hb);
    eprintln!(
      "  total heartbeats {} → heartbeat_cap {} (@ {cyc_per_hb} cyc/hb) → N={}",
      profile.total_heartbeats(),
      plan.heartbeat_cap,
      plan.num_shards,
    );
    eprintln!(
      "  heaviest shard: {} hb (~{cyc} cycles); largest atomic block: {} hb (~{floor_cyc} cycles)",
      plan.max_shard_heartbeats, plan.largest_block_heartbeats,
    );
    if plan.infeasible_atomic_floor {
      eprintln!(
        "  WARNING: the largest atomic (mutual) block alone exceeds the cap — NO \
         shard count can fit it. Split that block upstream (Lean side) or use a \
         bigger box."
      );
    } else if plan.max_shard_heartbeats > plan.heartbeat_cap {
      eprintln!(
        "  note: heaviest shard still over cap at N={} (pinned by the atomic-block \
         floor); more shards won't lower it.",
        plan.num_shards,
      );
    }
    (plan.shard_of, plan.num_shards, Some(plan.tree))
  };

  // ---- Manifest. ----
  let mut manifest = ShardManifest::build(&profile, &shard_of, n);
  if let Some(t) = tree {
    manifest = manifest.with_tree(t);
  }
  for s in &mut manifest.shards {
    s.assumption_root = ixon::merkle::merkle_root_canonical(&s.foreign_blocks);
  }
  std::fs::write(&out, manifest.to_bytes()).expect("write .ixes manifest");

  eprintln!(
    "profiled {} novel work items ({} store-covered skipped, {failures} failure(s)), \
     {} blocks, {} delta edges → {} shards; wrote {out}",
    novel_work.len(),
    covered_work.len(),
    profile.num_blocks(),
    profile.num_edges(),
    manifest.num_shards,
  );
  eprintln!("{}", manifest.summary());
}
