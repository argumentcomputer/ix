//! Generate a `.ixes` sharding manifest from a `.ixe` env, out of circuit — a
//! standalone equivalent of `ix profile` + `ix shard` that does NOT go through
//! the Lean/FFI layer. Useful for producing a plan to feed the Zisk host's
//! `--shard-plan`, and for testing/iterating the partitioner without a full
//! Lean build.
//!
//!   cargo run -p ix-kernel --release --example shard_plan -- <env.ixe> <N> [out.ixes]
//!
//! Profiles the env with the real kernel (single worker, cache-isolated so
//! heartbeats reflect the un-memoized in-circuit cost and every delta-unfold is
//! recorded), aggregates per-constant records into a block-level profile,
//! partitions into `N` shards (recursive balanced min-cut bisection minimizing
//! cross-shard delta ingress), and writes the `.ixes` manifest.

use ix_common::address::Address;
use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
use ix_kernel::profile::{BlockProfile, ProfileBuilder, ProfileSink};
use ix_kernel::shard::{Hypergraph, ShardManifest};
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

fn main() {
  let args: Vec<String> = std::env::args().collect();
  if args.len() < 3 {
    eprintln!("usage: shard_plan <env.ixe> <num_shards> [out.ixes]");
    std::process::exit(1);
  }
  let path = args[1].clone();
  let num_shards: usize = args[2].parse().expect("num_shards must be a positive integer");
  let out = args.get(3).cloned().unwrap_or_else(|| format!("{path}.ixes"));

  let bytes = std::fs::read(&path).expect("read .ixe");
  let env = IxonEnv::get_anon(&mut &bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");

  // ---- Profile: run the kernel, recording heartbeats + delta-unfold edges. ----
  let mut kenv = KEnv::<Anon>::new();
  kenv.profile_sink = Some(ProfileSink::new(true)); // isolate = sound recording
  let mut failures = 0usize;
  for item in &work {
    let kid = KId::<Anon>::new(item.primary().clone(), ());
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    if tc.check_const(&kid).is_err() {
      failures += 1;
    }
    // The TypeChecker is recreated per item, so flush the last constant's record
    // explicitly (no trailing reset would otherwise do it).
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

  // ---- Partition + manifest. ----
  let h = Hypergraph::from_profile(&profile);
  let shard_of = h.partition(num_shards, 0.05);
  let mut manifest = ShardManifest::build(&profile, &shard_of, num_shards);
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
