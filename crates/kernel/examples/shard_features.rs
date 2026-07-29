//! Emit a per-shard feature CSV from a profile + manifest pair, for
//! calibrating the planner's cost model against externally measured shard
//! costs (`ziskemu -X` on dumped shard inputs).
//!
//!   cargo run -p ix-kernel --release --example shard_features -- \
//!     <plan.ixprof> <plan.ixes> [label]
//!
//! Columns: label, shard manifest index, block count, and the per-shard sums
//! of every feature the profile carries (heartbeats, subst, own serialized
//! bytes, constant count) plus the manifest's cross-ingress bytes and the
//! current model's predicted steps.

use ix_common::address::Address;
use ix_kernel::profile::BlockProfile;
use ix_kernel::shard::{
  COST_PER_INGRESS_BYTE, SHARD_COST_FLOOR, ShardManifest, block_step_cost,
};
use rustc_hash::FxHashMap;

fn main() {
  let mut args = std::env::args().skip(1);
  let prof_path =
    args.next().expect("usage: shard_features <ixprof> <ixes> [label]");
  let ixes_path =
    args.next().expect("usage: shard_features <ixprof> <ixes> [label]");
  let label = args.next().unwrap_or_else(|| {
    std::path::Path::new(&ixes_path)
      .file_stem()
      .unwrap()
      .to_string_lossy()
      .into_owned()
  });

  let profile =
    BlockProfile::from_bytes(&std::fs::read(&prof_path).expect("read ixprof"))
      .expect("parse ixprof");
  let manifest =
    ShardManifest::from_bytes(&std::fs::read(&ixes_path).expect("read ixes"))
      .expect("parse ixes");

  let by_addr: FxHashMap<Address, u32> = profile
    .blocks()
    .iter()
    .enumerate()
    .map(|(i, b)| {
      (b.addr.clone(), u32::try_from(i).expect("block ids are u32"))
    })
    .collect();

  println!(
    "label,shard,n_blocks,heartbeats,subst,whnf,def_eq,nat_arith,intern,\
     own_bytes,const_count,cross_ingress,predicted_steps"
  );
  for (idx, s) in manifest.shards.iter().enumerate() {
    let mut hb = 0u64;
    let mut subst = 0u64;
    let mut whnf = 0u64;
    let mut def_eq = 0u64;
    let mut nat_arith = 0u64;
    let mut intern = 0u64;
    let mut bytes = 0u64;
    let mut consts = 0u64;
    let mut block_steps = 0u64;
    for a in &s.blocks {
      let b = profile.block(by_addr[a]);
      hb += b.heartbeats;
      subst += b.subst;
      whnf += b.whnf;
      def_eq += b.def_eq;
      nat_arith += b.nat_arith;
      intern += b.intern;
      bytes += u64::from(b.serialized_size);
      consts += u64::from(b.const_count);
      block_steps += block_step_cost(b);
    }
    debug_assert_eq!(hb, s.heartbeats);
    let predicted = block_steps
      .saturating_add(SHARD_COST_FLOOR)
      .saturating_add(COST_PER_INGRESS_BYTE.saturating_mul(s.cross_ingress));
    println!(
      "{label},{idx},{},{hb},{subst},{whnf},{def_eq},{nat_arith},{intern},\
       {bytes},{consts},{},{predicted}",
      s.blocks.len(),
      s.cross_ingress,
    );
  }
}
