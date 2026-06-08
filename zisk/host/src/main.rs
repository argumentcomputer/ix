//! Partition Anon work items into shards, prove each shard with the
//! leaf guest, then fold all leaf proofs through the aggregation guest
//! into one recursive proof.
//!
//! Accepts one or many `.ixe` inputs in a single invocation. All inputs
//! are proved in the *same* process — the prover is set up once and the
//! GPU/CUDA context stays warm across every input — and every leaf proof
//! (across all inputs and all shards) is folded into a single aggregate
//! proof. This is the batch entry point: pay proofman init + GPU
//! kernel cold-start exactly once, then prove a whole set of constants
//! and aggregate them together.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute --ixe ../nataddcomm.ixe
//! RUST_LOG=info cargo run --release -- --gpu --ixe ../nataddcomm.ixe --ixe ../stringappend.ixe
//! RUST_LOG=info cargo run --release -- --gpu --ixe ../init.ixe --shard-bytes 250000
//! RUST_LOG=info cargo run --release -- --gpu --ixe ../mergesort.ixe --shard-plan ../mergesort.ixe.ixes
//! ```
//!
//! `--shard-plan <manifest.ixes>` is the preferred partitioner: it proves the
//! partition computed offline by `ix profile` + `ix shard` (the kernel
//! profiler's real heartbeat cost model + delta-unfold graph cut). Each
//! manifest shard becomes one closure-injected leaf proof, and the leaves fold
//! into one aggregate. `--shard-consts N` / `--shard-bytes B` are the simpler
//! no-profile fallbacks (partition `build_anon_work` by work-item count or by
//! cumulative serialized-AST cost). Sharding is applied per input. The pipeline
//! ends in aggregation whenever more than one leaf proof is produced — whether
//! from multiple shards of one env, multiple inputs, or both.

use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{bail, Result};
use clap::Parser;
use human_repr::{HumanCount, HumanThroughput};
use ix_kernel::anon_work::{build_anon_work, AnonWorkItem};
use ixon::env::Env as IxonEnv;
use zisk_host::{AGG_PROGRAM, SHARD_PROGRAM};
use zisk_sdk::{
  EmbeddedClient, EmbeddedClientBuilder, EmbeddedOpts, ProverClient, VerboseMode,
  VerifyConstraintsExtension, ZiskStdin,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Run shards in the VM only — no proof generated.
  #[arg(long, conflicts_with = "verify_constraints")]
  execute: bool,

  /// Run the constraint checker without generating a proof (single shard
  /// only).
  #[arg(long)]
  verify_constraints: bool,

  /// Enable GPU-accelerated proving.
  #[arg(long)]
  gpu: bool,

  /// Path to a `.ixe` file. Repeatable: pass `--ixe` multiple times to
  /// prove a batch of inputs in one warm process and aggregate them all
  /// into a single proof. If omitted entirely, one empty `IxonEnv` is
  /// used.
  #[arg(long)]
  ixe: Vec<PathBuf>,

  /// Fixed-count partitioning: maximum work items per shard. `0`
  /// (default) puts the whole env in one shard. Mutually exclusive
  /// with `--shard-bytes`. Applied independently to each input. "Consts"
  /// here is the work-item unit returned by `build_anon_work` — one per
  /// Standalone constant or per Muts block; a single Muts block work
  /// item may cover many target constants in the kernel-check sense.
  #[arg(long, default_value_t = 0, conflicts_with = "shard_bytes")]
  shard_consts: u32,

  /// Cost-based partitioning: pack contiguous work items into shards
  /// until cumulative serialized-AST bytes exceed this budget, then
  /// open a new shard. Bytes are summed via
  /// `LazyConstant::raw_bytes().len()` over each item's `targets()` —
  /// for a Standalone item that's its own body; for a Muts block it's
  /// the sum across all member + ctor projections. Strong proxy for
  /// kernel work, computable without parsing or executing. Applied
  /// independently to each input.
  ///
  /// Doubles as the hard per-item ceiling: any single work item whose
  /// serialized cost exceeds this budget aborts at planning time, with
  /// an error naming the offending item. A would-be-oversized item gets
  /// caught before any prove runs (otherwise it'd silently produce an
  /// over-budget shard that either blows guest RAM or exceeds the
  /// prover's MT-trace ceiling).
  ///
  /// Mutually exclusive with `--shard-consts`.
  #[arg(long)]
  shard_bytes: Option<usize>,

  /// Manifest-driven sharding: prove the partition in a `.ixes` manifest
  /// produced offline by `ix profile <env.ixe>` then
  /// `ix shard <env.ixesp> --shards N`. Each manifest shard becomes one
  /// closure-injected leaf proof — its member blocks' work items, shipped with
  /// only their dependency closure — and the leaves fold into one aggregate.
  /// This is the performant path: the partition is balanced by the kernel
  /// profiler's real per-block heartbeats and cut to minimize cross-shard
  /// delta-unfold ingress, instead of the static `--shard-consts`/`--shard-bytes`
  /// heuristics. Requires exactly one `--ixe` (the env the manifest was built
  /// for); the manifest must cover that env's full work set. Composes with
  /// `--execute` (per-shard cycles) and `--only-shard`.
  #[arg(long, conflicts_with_all = ["shard_consts", "shard_bytes", "store_dir"])]
  shard_plan: Option<PathBuf>,

  /// Print the planned shard partition (range, items, bytes) for every
  /// input and exit. No setup, no execute, no prove. Useful for tuning
  /// `--shard-bytes`.
  #[arg(long)]
  plan: bool,

  /// Tree-fold aggregation arity: each agg-guest invocation verifies at
  /// most this many child proofs. The leaf phase produces N proofs;
  /// the host then folds them in `log_arity(N)` levels until a single
  /// root proof remains. The same agg guest is reused at every level —
  /// `verify_zisk_proof` works on any Zisk proof regardless of which
  /// guest produced it. Arity 16 keeps each agg call's stdin under
  /// ~5 MB (16 × 336 kB), well below Zisk's guest RAM cap. Used only
  /// when more than one leaf proof is produced.
  #[arg(long, default_value_t = 16)]
  agg_arity: u32,

  /// 1-indexed shard to prove from the planned partition; all other
  /// shards are dropped before the leaf phase. Useful for smoke-testing
  /// a specific shard (e.g. the one containing the largest item) without
  /// running the full sweep. Requires exactly one `--ixe` input.
  /// Aggregation is skipped because the run produces a single leaf proof.
  #[arg(long)]
  only_shard: Option<usize>,

  /// Cross-proof reuse store directory. When set (with `--execute`), the
  /// host loads the set of already-proven primary addresses from
  /// `<dir>/proven.bin`, checks only the NOVEL work items of each input
  /// (skipping constants already in the store), and appends the newly
  /// checked primaries back to the store. Demonstrates shards/proofs
  /// avoiding re-checking shared constants. Content-addressed: a constant
  /// has the same primary address across every env.
  #[arg(long)]
  store_dir: Option<PathBuf>,

  /// Disable cross-proof reuse for THIS run while keeping the same reuse/agg
  /// code path. With `--store-dir`, treats the on-disk store as empty: every
  /// work item is novel (0 reused), so the full env is proved + aggregated
  /// from scratch — the "no sharing" baseline. The existing store is neither
  /// consulted (no covering proofs folded) nor overwritten, so a populated
  /// store survives for a back-to-back "with sharing" comparison.
  #[arg(long)]
  no_reuse: bool,

  /// Closure injection (reuse path): ship each leaf guest only the BFS
  /// dependency closure of its checked targets — the constants it certifies
  /// plus their transitive `Constant.refs` and referenced literal blobs —
  /// instead of the whole env. Essential for large envs (Init, 184 MB) that
  /// don't fit the 512 MB guest whole; each shard then pays only its closure's
  /// decode. The committed claim is identical, since subject/assumptions
  /// depend only on the checked targets and their direct refs (all in the
  /// closure). Costs host-side closure computation per shard.
  #[arg(long)]
  closure_inject: bool,

  /// Require a fully closed environment modulo axioms: error BEFORE proving
  /// unless every typing dependency of every constant the batch will certify is
  /// either (a) certified somewhere in this invocation, or (b) already in the
  /// `--store-dir` store (proved by a prior run, re-verified and folded at
  /// aggregation). Axioms are the only permitted residual. Turns "residual =
  /// axioms" from a printed hope into an enforced precondition, so a successful
  /// run yields an unconditional-mod-axioms result rather than a conditional
  /// one with dangling assumptions. Pairs with `--plan` for a no-prove check.
  #[arg(long)]
  require_closed: bool,

  /// Testing knob (reuse path): cap each input to its first N novel work items
  /// before sharding, so you can prove just a few shards of a huge env (e.g.
  /// a couple of Init shards) end-to-end. Everything downstream — targets,
  /// coverage binding, discharge — stays self-consistent on the capped subset.
  #[arg(long)]
  limit_items: Option<usize>,

  /// Cap on resident witness traces during the prove phase, bounding
  /// peak host RAM per shard. Zisk's prover queues witnesses up to this
  /// count before committing them; peak RAM ≈ N × avg-witness-size +
  /// fixed overheads. Zisk's built-in default is 10 (tuned for
  /// large-memory boxes); we default to 5 here as a safer fit for
  /// ~256 GB machines. Override up to 10 on bigger boxes for maximum
  /// parallelism, or down to 3 on smaller ones. See the Zisk section
  /// of the top-level README for a per-RAM recommendation table. Has
  /// no effect on `--execute` / `--verify-constraints` modes.
  #[arg(long, default_value_t = 5)]
  max_witness_stored: usize,
}

/// 112-byte public output of one shard-guest proof.
///
/// First 44 bytes are the original prefix (env_hash, range_start/range_end —
/// or checked-count/0 in reuse mode — and failures). The next 68 bytes are
/// the conditional claim: `subject_root` (canonical merkle root over the
/// certified target addresses), `assumptions_root` (merkle root over their
/// direct refs not certified here), and `checked_count`. Together the roots
/// form `Claim::CheckEnv { root: subject_root, assumptions: assumptions_root }`.
#[derive(Clone, Copy, Debug)]
struct ShardPublics {
  env_hash: [u8; 32],
  range_start: u32,
  range_end: u32,
  failures: u32,
  subject_root: [u8; 32],
  assumptions_root: [u8; 32],
  checked_count: u32,
}

const SHARD_PUBLICS_LEN: usize = 112;

impl ShardPublics {
  fn decode(buf: &[u8; SHARD_PUBLICS_LEN]) -> Self {
    Self {
      env_hash: buf[0..32].try_into().unwrap(),
      range_start: u32::from_le_bytes(buf[32..36].try_into().unwrap()),
      range_end: u32::from_le_bytes(buf[36..40].try_into().unwrap()),
      failures: u32::from_le_bytes(buf[40..44].try_into().unwrap()),
      subject_root: buf[44..76].try_into().unwrap(),
      assumptions_root: buf[76..108].try_into().unwrap(),
      checked_count: u32::from_le_bytes(buf[108..112].try_into().unwrap()),
    }
  }
}

/// One input env, parsed and partitioned into shards. Built once up front
/// so the prove loop can run back-to-back without re-parsing.
struct InputPlan {
  /// Human-readable label for logging (the `.ixe` path or `<empty env>`).
  label: String,
  /// Serialized Ixon env bytes fed to the guest.
  env_bytes: Vec<u8>,
  /// Half-open work-item ranges, one per shard, tiling `[0, total)`.
  shards: Vec<(u32, u32)>,
  /// Total work items in this env.
  total: u32,
  /// Total target constants across this env's work items.
  target_count: usize,
}

fn load_env_bytes(ixe: Option<&PathBuf>) -> Vec<u8> {
  match ixe {
    Some(path) => fs::read(path).expect("read ixe input"),
    None => {
      let env = IxonEnv::new();
      let mut buf = Vec::new();
      env.put(&mut buf).expect("env.put");
      buf
    },
  }
}

/// Partition `[0, total)` into half-open ranges of at most
/// `shard_consts` items each. `shard_consts == 0` or `>= total`
/// returns one shard.
fn plan_shards(total: u32, shard_consts: u32) -> Vec<(u32, u32)> {
  if shard_consts == 0 || shard_consts >= total {
    return vec![(0, total)];
  }
  let mut out = Vec::with_capacity(total.div_ceil(shard_consts) as usize);
  let mut start = 0u32;
  while start < total {
    let end = (start + shard_consts).min(total);
    out.push((start, end));
    start = end;
  }
  out
}

/// Structural cost estimate for one work item, in serialized-AST bytes.
///
/// For a Standalone item that's the byte length of its primary const;
/// for a Muts block it's the sum across all member + ctor projections.
/// Reads `LazyConstant::raw_bytes().len()` (O(1) per target) — no parse,
/// no allocation.
///
/// Why bytes are a usable proxy for kernel cycles: body size scales with
/// AST node count, which scales with WHNF / infer / def-eq work; Muts
/// block weight scales with member count, which is exactly how many
/// projections the kernel walks. Doesn't capture cross-shard cache
/// sharing or pathological def-eq blowups, but correlates well enough
/// to drive packing.
fn item_cost_bytes(env: &IxonEnv, item: &AnonWorkItem) -> usize {
  item
    .targets()
    .iter()
    .filter_map(|addr| env.consts.get(addr).map(|lc| lc.value().raw_bytes().len()))
    .sum()
}

/// Greedy left-to-right contiguous bin-packing by structural cost.
///
/// Walks work items in order, accumulating into the current shard until
/// adding the next item would exceed `shard_bytes`. Single items larger
/// than `shard_bytes` are an error — they'd produce an over-budget
/// shard that the prover may not handle, and the caller should know
/// before running.
fn plan_shards_by_cost(
  work: &[AnonWorkItem],
  env: &IxonEnv,
  shard_bytes: usize,
) -> Result<Vec<(u32, u32)>> {
  let mut out: Vec<(u32, u32)> = Vec::new();
  let mut current_start: u32 = 0;
  let mut current_bytes: usize = 0;
  for (i, item) in work.iter().enumerate() {
    let s = item_cost_bytes(env, item);
    if s > shard_bytes {
      bail!(
        "work item {i} exceeds --shard-bytes ({} > {}); raise the \
         budget or accept that this env can't be sharded under it",
        s.human_count_bytes(),
        shard_bytes.human_count_bytes(),
      );
    }
    let i = i as u32;
    if current_bytes > 0 && current_bytes + s > shard_bytes {
      out.push((current_start, i));
      current_start = i;
      current_bytes = 0;
    }
    current_bytes += s;
  }
  if current_start < work.len() as u32 {
    out.push((current_start, work.len() as u32));
  }
  Ok(out)
}

/// Parse one input env and partition it into shards. When `print_plan`
/// is set, emit the per-shard breakdown (range, items, bytes).
fn plan_input(
  ixe: Option<&PathBuf>,
  shard_consts: u32,
  shard_bytes: Option<usize>,
  print_plan: bool,
) -> Result<InputPlan> {
  let label =
    ixe.map(|p| p.display().to_string()).unwrap_or_else(|| "<empty env>".to_string());
  let env_bytes = load_env_bytes(ixe);
  let env = IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");
  let total: u32 = work.len().try_into().expect("work-item count fits in u32");
  let target_count: usize = work.iter().map(|item| item.targets().len()).sum();
  let shards = match shard_bytes {
    Some(budget) => plan_shards_by_cost(&work, &env, budget)?,
    None => plan_shards(total, shard_consts),
  };
  println!(
    "input {label}: {total} work items ({target_count} target constants), \
     {} shard(s)",
    shards.len(),
  );
  if print_plan {
    for (i, &(s, e)) in shards.iter().enumerate() {
      let bytes: usize =
        (s..e).map(|idx| item_cost_bytes(&env, &work[idx as usize])).sum();
      println!(
        "  [{:>3}/{:>3}] range [{s:>5}, {e:>5})  items={:>5}  bytes={}",
        i + 1,
        shards.len(),
        e - s,
        bytes.human_count_bytes(),
      );
    }
  }
  Ok(InputPlan { label, env_bytes, shards, total, target_count })
}

/// Load the cross-proof reuse store: the set of already-proven primary
/// addresses (as raw 32-byte keys) from `<dir>/proven.bin`. Missing file →
/// empty set.
fn load_store(dir: &std::path::Path) -> std::collections::HashSet<[u8; 32]> {
  use ix_common::address::Address;
  let mut set = std::collections::HashSet::default();
  if let Ok(bytes) = fs::read(dir.join("proven.bin")) {
    for a in Address::unpack(&bytes) {
      set.insert(*a.as_bytes());
    }
  }
  set
}

/// Persist the reuse store (sorted, packed) to `<dir>/proven.bin`.
fn save_store(dir: &std::path::Path, set: &std::collections::HashSet<[u8; 32]>) -> Result<()> {
  fs::create_dir_all(dir)?;
  let mut addrs: Vec<[u8; 32]> = set.iter().copied().collect();
  addrs.sort_unstable();
  let mut buf = Vec::with_capacity(addrs.len() * 32);
  for a in &addrs {
    buf.extend_from_slice(a);
  }
  fs::write(dir.join("proven.bin"), buf)?;
  Ok(())
}

/// Append a leaf proof to the on-disk proof store: `proofs/<n>.proof` holds the
/// blob, `proofs/<n>.cover` the packed 32-byte addresses it certifies. Reuse
/// resolution pulls these back to *verify* (not trust) the reused constants.
fn append_proof(
  dir: &std::path::Path,
  proof: &[u8],
  covered: &[[u8; 32]],
) -> Result<()> {
  let pdir = dir.join("proofs");
  fs::create_dir_all(&pdir)?;
  let idx = (0..)
    .find(|n| !pdir.join(format!("{n}.proof")).exists())
    .expect("free proof index");
  fs::write(pdir.join(format!("{idx}.proof")), proof)?;
  let mut cov = Vec::with_capacity(covered.len() * 32);
  for a in covered {
    cov.extend_from_slice(a);
  }
  fs::write(pdir.join(format!("{idx}.cover")), cov)?;
  Ok(())
}

/// Load the proof store: `(blob, covered-set)` per stored leaf proof.
fn load_proof_index(
  dir: &std::path::Path,
) -> Vec<(Vec<u8>, std::collections::HashSet<[u8; 32]>)> {
  let pdir = dir.join("proofs");
  let mut out = Vec::new();
  let mut idx = 0usize;
  loop {
    let pf = pdir.join(format!("{idx}.proof"));
    if !pf.exists() {
      break;
    }
    let blob = match fs::read(&pf) {
      Ok(b) => b,
      Err(_) => break,
    };
    let mut cov: std::collections::HashSet<[u8; 32]> = std::collections::HashSet::default();
    if let Ok(cb) = fs::read(pdir.join(format!("{idx}.cover"))) {
      for chunk in cb.chunks_exact(32) {
        let mut a = [0u8; 32];
        a.copy_from_slice(chunk);
        cov.insert(a);
      }
    }
    out.push((blob, cov));
    idx += 1;
  }
  out
}

/// Build the 3-slice leaf-guest stdin: range + env bytes + reuse check-list.
///
/// `check_list` is a packed list of primary addresses (`Address::pack`) to
/// check; empty means "range mode" (use `[start,end)`). A non-empty list puts
/// the guest in reuse mode, checking only those work items.
fn leaf_stdin(start: u32, end: u32, env_bytes: &[u8], check_list: &[u8]) -> ZiskStdin {
  let stdin = ZiskStdin::new();
  let mut range_buf = [0u8; 8];
  range_buf[0..4].copy_from_slice(&start.to_le_bytes());
  range_buf[4..8].copy_from_slice(&end.to_le_bytes());
  stdin.write_slice(&range_buf);
  stdin.write_slice(env_bytes);
  stdin.write_slice(check_list);
  stdin
}

/// Build the aggregation-guest stdin: the allowed program-vk set (count +
/// 32-byte vks) the agg guest pins each child against, then the proof blobs
/// (count + `Vec<u8>`s).
fn agg_stdin(allowed_vks: &[Vec<u8>], proofs: &[Vec<u8>]) -> ZiskStdin {
  let stdin = ZiskStdin::new();
  stdin.write(&(allowed_vks.len() as u32));
  for vk in allowed_vks {
    stdin.write(vk);
  }
  stdin.write(&(proofs.len() as u32));
  for bytes in proofs {
    stdin.write(bytes);
  }
  stdin
}

/// Extract a proof's 32-byte program vk: v0.18 lays the proof out as u64
/// words `[minimal(1)][n_publics(1)][program_vk(4)]…`, so the program vk is
/// bytes `[16..48)` (words 2..6). Used both to derive the allowed-vk set the
/// agg guest pins against and to key the proof store.
fn program_vk(proof: &[u8]) -> Vec<u8> {
  proof.get(16..48).map(|s| s.to_vec()).unwrap_or_default()
}

/// The distinct program vks across a set of proofs (the allowed set to pin the
/// agg guest against — typically {SHARD_VK} or {SHARD_VK, AGG_VK}).
fn distinct_vks(proofs: &[Vec<u8>]) -> Vec<Vec<u8>> {
  let mut out: Vec<Vec<u8>> = Vec::new();
  for p in proofs {
    let vk = program_vk(p);
    if !out.contains(&vk) {
      out.push(vk);
    }
  }
  out
}

/// Build a closure sub-env: serialize only the BFS dependency closure of
/// `roots` (their transitive `Constant.refs` plus referenced literal blobs),
/// copying each constant's GENUINE bytes via `store_const_lazy` so the guest's
/// per-const integrity check (`hash(bytes) == addr`) and the env merkle root
/// still hold. The guest decodes this instead of the whole env, so a shard
/// pays only its closure's decode — essential for Init (184 MB doesn't fit the
/// 512 MB guest whole). Empty `anon_hints` (no metadata section) is
/// performance-only: ingress falls back to `Regular(0)`, so the typecheck
/// result — and thus the committed claim — is unchanged. External refs (not in
/// `source`) are omitted and remain open assumptions, exactly as in whole-env.
/// The full dependency-closure address set of `roots`: their transitive Expr
/// `refs` PLUS each projection's structural `block: Address`. A refs-only walk
/// (`bfs_refs`) misses the block — projections (IPrj/CPrj/RPrj/DPrj) point at
/// their Muts block via a struct field, not the Expr ref table — so the kernel
/// couldn't resolve the projection and would spuriously fail. The returned set
/// includes constant AND referenced-blob addresses (external refs absent from
/// `source` are included as addresses but have no bytes to copy).
fn closure_addrs(
  source: &IxonEnv,
  roots: &[ix_common::address::Address],
) -> std::collections::HashSet<ix_common::address::Address> {
  use std::collections::{HashSet, VecDeque};

  use ix_common::address::Address;
  use ix_kernel::ingress::{
    anon_ctor_proj_addr, anon_defn_proj_addr, anon_indc_proj_addr,
    anon_recr_proj_addr,
  };
  use ixon::constant::{ConstantInfo as CI, MutConst as MC};

  let proj_block = |info: &CI| -> Option<Address> {
    match info {
      CI::IPrj(p) => Some(p.block.clone()),
      CI::CPrj(p) => Some(p.block.clone()),
      CI::RPrj(p) => Some(p.block.clone()),
      CI::DPrj(p) => Some(p.block.clone()),
      _ => None,
    }
  };

  let mut closure: HashSet<Address> = HashSet::default();
  let mut queue: VecDeque<Address> = VecDeque::new();
  let mut push = |closure: &mut HashSet<Address>, q: &mut VecDeque<Address>, a: Address| {
    if closure.insert(a.clone()) {
      q.push_back(a);
    }
  };
  for r in roots {
    push(&mut closure, &mut queue, r.clone());
  }
  while let Some(addr) = queue.pop_front() {
    if let Some(c) = source.get_const(&addr) {
      // 1. Expr-level refs.
      for r in &c.refs {
        push(&mut closure, &mut queue, r.clone());
      }
      // 2. A projection → its Muts block (structural, not in `refs`).
      if let Some(b) = proj_block(&c.info) {
        push(&mut closure, &mut queue, b);
      }
      // 3. A Muts block → ALL its member + constructor projection entries.
      // Ingressing a block (`ingress_anon_block`) computes these projection
      // addresses and requires them present, even when nothing references them
      // directly via `refs`. Mirror `build_anon_work`'s enumeration so the
      // sub-env carries them (else the guest fails with "computed CPrj address
      // … not present in env").
      if let CI::Muts(members) = &c.info {
        for (i, m) in members.iter().enumerate() {
          let i = i as u64;
          let member_addr = match m {
            MC::Defn(_) => anon_defn_proj_addr(&addr, i),
            MC::Indc(_) => anon_indc_proj_addr(&addr, i),
            MC::Recr(_) => anon_recr_proj_addr(&addr, i),
          };
          push(&mut closure, &mut queue, member_addr);
          if let MC::Indc(ind) = m {
            for cidx in 0..ind.ctors.len() as u64 {
              push(&mut closure, &mut queue, anon_ctor_proj_addr(&addr, i, cidx));
            }
          }
        }
      }
    }
  }
  closure
}

/// Serialized byte size of the constant or blob at `addr` in `source` (0 if
/// external/absent) — the contribution `addr` makes to an injected sub-env.
fn addr_bytes(source: &IxonEnv, addr: &ix_common::address::Address) -> usize {
  source
    .get_const_bytes(addr)
    .map(|b| b.len())
    .or_else(|| source.get_blob(addr).map(|b| b.len()))
    .unwrap_or(0)
}

/// Build a closure sub-env from a precomputed closure address set: copy each
/// constant's GENUINE bytes (`store_const_lazy`) and referenced blobs, then
/// serialize. Integrity (`hash(bytes) == addr`) and the env merkle root hold
/// because the bytes are copied verbatim; empty `anon_hints` is performance-
/// only (ingress falls back to `Regular(0)`), so the committed claim is
/// unchanged. Essential for envs that don't fit the guest whole (Init, 184 MB).
fn build_sub_env(
  source: &IxonEnv,
  roots: &[ix_common::address::Address],
) -> Result<Vec<u8>> {
  let closure = closure_addrs(source, roots);
  let mut sub = IxonEnv::new();
  for addr in &closure {
    if let Some(bytes) = source.get_const_bytes(addr) {
      sub.store_const_lazy(addr.clone(), bytes);
    } else if let Some(blob) = source.get_blob(addr) {
      sub.store_blob(blob);
    }
    // else: external ref absent from `source` — omit; stays an open assumption.
    // Carry the constant's reducibility hint so the guest reproduces vanilla
    // kernel behavior. `get_anon` normally harvests hints from the Named
    // section, which this sub-env drops; without them the kernel forces
    // `Regular(0)` and does extra def-eq work (the ~30% check overhead).
    if let Some(h) = source.anon_hints.get(addr) {
      sub.anon_hints.insert(addr.clone(), *h);
    }
  }
  let mut buf = Vec::new();
  sub.put(&mut buf).map_err(|e| anyhow::anyhow!("sub-env serialize: {e}"))?;
  Ok(buf)
}

/// Closure-aware shard packing for the reuse path: greedily group consecutive
/// novel work items into contiguous `(start, end)` ranges whose UNION closure
/// (what the guest decodes under closure injection) stays under `budget` bytes
/// — the real constraint once closures are injected, vs. the whole env. Shared
/// deps within a group are counted once, so items with overlapping closures
/// pack tightly. Aborts if a single item's own closure exceeds `budget`.
fn plan_chunks_by_closure(
  source: &IxonEnv,
  items: &[&AnonWorkItem],
  budget: usize,
) -> Result<Vec<(usize, usize)>> {
  use std::collections::HashSet;

  use ix_common::address::Address;

  let mut ranges = Vec::new();
  let mut start = 0usize;
  let mut cur: HashSet<Address> = HashSet::default();
  let mut cur_bytes = 0usize;
  for i in 0..items.len() {
    let roots = items[i].proven_targets();
    let item_closure = closure_addrs(source, &roots);
    let item_alone: usize = item_closure.iter().map(|a| addr_bytes(source, a)).sum();
    if item_alone > budget {
      bail!(
        "work item {i} (primary {}…) closure is {} > budget {} — raise --shard-bytes",
        &items[i].primary().hex()[..16],
        item_alone.human_count_bytes(),
        budget.human_count_bytes(),
      );
    }
    let delta: usize =
      item_closure.iter().filter(|a| !cur.contains(*a)).map(|a| addr_bytes(source, a)).sum();
    if i > start && cur_bytes + delta > budget {
      ranges.push((start, i));
      start = i;
      cur.clear();
      cur.extend(item_closure.iter().cloned());
      cur_bytes = item_alone;
    } else {
      for a in &item_closure {
        if cur.insert(a.clone()) {
          cur_bytes += addr_bytes(source, a);
        }
      }
    }
  }
  if start < items.len() {
    ranges.push((start, items.len()));
  }
  Ok(ranges)
}

/// Core of the closure check, factored out for testing: given parsed inputs
/// and the store, return `(missing, checked, axioms)` where `missing` is the
/// list of `(label, dangling-ref)` typing dependencies that are neither
/// certified in-batch nor in the store nor a literal blob. `checked` is the
/// number of constants inspected; `axioms` how many are `Axio` declarations.
fn find_missing_deps(
  parsed: &[(String, IxonEnv, Vec<AnonWorkItem>)],
  store: &std::collections::HashSet<[u8; 32]>,
) -> (Vec<(String, ix_common::address::Address)>, usize, usize) {
  use std::collections::HashSet;

  use ix_common::address::Address;
  use ixon::constant::ConstantInfo;

  // certified = every target the batch will prove ∪ the store.
  let mut certified: HashSet<[u8; 32]> = store.clone();
  for (_, _, work) in parsed {
    for w in work {
      for t in w.proven_targets() {
        certified.insert(*t.as_bytes());
      }
    }
  }

  // Every non-blob ref of every certified constant must be in `certified`.
  let mut missing: Vec<(String, Address)> = Vec::new();
  let mut axioms = 0usize;
  let mut checked = 0usize;
  for (label, env, work) in parsed {
    for w in work {
      for t in w.proven_targets() {
        let Some(c) = env.get_const(&t) else { continue };
        if matches!(&c.info, ConstantInfo::Axio(_)) {
          axioms += 1;
        }
        checked += 1;
        for r in &c.refs {
          if env.get_blob(r).is_some() {
            continue;
          }
          if !certified.contains(r.as_bytes()) {
            missing.push((label.clone(), r.clone()));
          }
        }
      }
    }
  }
  (missing, checked, axioms)
}

/// Pre-flight closure check for `--require-closed`. Bails unless every typing
/// dependency of every constant the batch will certify is itself either
/// (a) certified somewhere in this batch (any input's work items), or (b)
/// already in the on-disk `store` (a prior proof — re-verified and folded at
/// aggregation). Axioms need no special case: they are themselves work items,
/// so they land in (a) as certified declarations, and their inhabitation is the
/// irreducible "modulo axioms" residual. Literal blob refs (Nat/Str data) are
/// well-typed by construction and never count.
///
/// Sound under the store-closure invariant: a constant enters the store only
/// via a run, so if every run uses `--require-closed` the store is itself
/// closed and (b) holds transitively. Store entries' own refs aren't re-checked
/// here (their definitions live in other envs), but aggregation re-verifies the
/// covering proofs that certified them.
fn check_inputs_closed(
  inputs: &[Option<PathBuf>],
  store: &std::collections::HashSet<[u8; 32]>,
) -> Result<()> {
  // Parse every input once: (label, env, work).
  let parsed: Vec<(String, IxonEnv, Vec<AnonWorkItem>)> = inputs
    .iter()
    .map(|ixe| {
      let label = ixe
        .as_ref()
        .map(|p| p.display().to_string())
        .unwrap_or_else(|| "<empty env>".to_string());
      let bytes = load_env_bytes(ixe.as_ref());
      let env =
        IxonEnv::get_anon(&mut &bytes[..]).expect("invalid Ixon environment");
      let work = build_anon_work(&env).expect("build_anon_work");
      (label, env, work)
    })
    .collect();

  let (mut missing, checked, axioms) = find_missing_deps(&parsed, store);

  if !missing.is_empty() {
    missing.sort_by(|a, b| a.1.as_bytes().cmp(b.1.as_bytes()));
    missing.dedup_by(|a, b| a.1 == b.1);
    let shown: Vec<String> = missing
      .iter()
      .take(8)
      .map(|(l, r)| format!("{}… (referenced in {l})", &r.hex()[..16]))
      .collect();
    bail!(
      "env not closed modulo axioms: {} dangling dependenc{} — neither proved \
       in this batch nor present in the store. Prove the providing env first \
       (e.g. add --ixe init.ixe, or populate the store), then retry. Sample:\n  {}",
      missing.len(),
      if missing.len() == 1 { "y" } else { "ies" },
      shown.join("\n  "),
    );
  }

  println!(
    "closure check OK: {checked} constants closed modulo {axioms} axiom(s) — \
     every dependency is proved in-batch or already in the store",
  );
  Ok(())
}

/// The canonical subject root a leaf guest commits for a chunk that certifies
/// `cover` (its `covered()` target addresses): `merkle_root_canonical` over the
/// addresses, exactly as the guest computes it. Used host-side to re-derive the
/// expected per-child subject *from the env* (not from the proof) so the final
/// aggregate's committed subject can be checked against the env it should cover.
fn subject_of_cover(cover: &[[u8; 32]]) -> ix_common::address::Address {
  use ix_common::address::Address;
  let leaves: Vec<Address> =
    cover.iter().map(|b| Address::from_slice(b).expect("cover address")).collect();
  ixon::merkle::merkle_root_canonical(&leaves).unwrap_or_else(ixon::merkle::zero_address)
}

/// Fold per-child subject roots with the same left-associative `merkle_join`
/// the agg guest applies over its verified children (in fold order). A single
/// child folds to itself (matching the leaf-direct case where no agg runs).
fn fold_subjects(subjects: &[ix_common::address::Address]) -> ix_common::address::Address {
  let mut acc: Option<ix_common::address::Address> = None;
  for s in subjects {
    acc = Some(match acc {
      None => s.clone(),
      Some(p) => ixon::merkle::merkle_join(&p, s),
    });
  }
  acc.unwrap_or_else(ixon::merkle::zero_address)
}

/// Partition `n` items into chunks of at most `arity` each, avoiding
/// any chunk of size exactly 1 (which would make agg-of-1 a no-op).
/// When the trailing remainder is 1, it's merged into the previous
/// chunk so the smallest chunk produced is size 2. Returns half-open
/// `(start, end)` index ranges.
fn tree_partition(n: usize, arity: usize) -> Vec<(usize, usize)> {
  if n <= arity {
    return vec![(0, n)];
  }
  let mut ranges: Vec<(usize, usize)> = Vec::new();
  let mut i = 0;
  while i + arity <= n {
    ranges.push((i, i + arity));
    i += arity;
  }
  let remainder = n - i;
  if remainder == 1 {
    // Merge the singleton into the previous chunk so the agg guest
    // never gets called with just one proof (which would be agg-of-1
    // pure overhead).
    let last = ranges.last_mut().expect("at least one full chunk");
    last.1 = n;
  } else if remainder > 0 {
    ranges.push((i, n));
  }
  ranges
}

/// Host-side coherence check for one input's shard proofs: every shard
/// must carry the same `env_hash`, the ranges must tile `[0, total)`
/// exactly, and failures are summed. Returns this input's failure count.
/// (The agg guest can't yet parse leaf publics from the proof blob, so
/// this is enforced here.)
fn check_input_coherence(label: &str, publics: &[ShardPublics], total: u32) -> Result<u32> {
  let env_hash = publics[0].env_hash;
  let mut failures: u32 = 0;
  let mut expected_start: u32 = 0;
  for (i, p) in publics.iter().enumerate() {
    if p.env_hash != env_hash {
      bail!("input {label}: leaf {i} env_hash mismatch with leaf 0");
    }
    if p.range_start != expected_start {
      bail!(
        "input {label}: leaf {i} range_start = {} but expected {expected_start} \
         (non-tiling shards)",
        p.range_start,
      );
    }
    expected_start = p.range_end;
    failures = failures.saturating_add(p.failures);
  }
  if expected_start != total {
    bail!(
      "input {label}: leaves cover [0, {expected_start}) but env has {total} work items"
    );
  }
  Ok(failures)
}

fn build_client(gpu: bool, max_witness_stored: Option<usize>) -> Result<EmbeddedClient> {
  // Default executor (Emulator), NOT `ExecutorKind::Assembly`. Empirically
  // Assembly + multi-program setup is broken: calling `client.setup`
  // for a second program re-initializes the ASM microservices and
  // leaves the first program's ROM histogram empty, so subsequent
  // proves panic at `state-machines/rom/src/rom.rs:178` with
  // "index out of bounds: len 0". The v0.18 upstream aggregation
  // example (`~/zisk/examples/aggregation/host/src/main.rs`) also uses
  // the default Emulator executor.
  //
  // `minimal_memory()` deliberately NOT enabled — per upstream CLI
  // docs ("Reduce memory footprint during proving at the cost of
  // speed"). We have ~94 GB of free GPU memory, so the speed
  // trade-off is the wrong direction for this hardware.
  let mut opts = EmbeddedOpts::default();
  if let Some(n) = max_witness_stored {
    opts = opts.max_witness_stored(n);
  }
  let mut builder: EmbeddedClientBuilder =
    ProverClient::embedded().with_embedded_opts(opts);
  if gpu {
    builder = builder.gpu();
  }
  builder.build()
}

/// The ingress *block* address a work item belongs to — the key the manifest
/// (and the profiler) uses. For a Muts block the work item's `primary` is a
/// member projection, whose `block` field is the block address; for a standalone
/// constant the primary is the block. Mirrors the profiler's `profile_block_of`.
fn work_block_addr(
  env: &IxonEnv,
  item: &AnonWorkItem,
) -> ix_common::address::Address {
  use ixon::constant::ConstantInfo as CI;
  let primary = item.primary();
  match env.get_const(primary) {
    Some(c) => match &c.info {
      CI::IPrj(p) => p.block.clone(),
      CI::CPrj(p) => p.block.clone(),
      CI::RPrj(p) => p.block.clone(),
      CI::DPrj(p) => p.block.clone(),
      _ => primary.clone(),
    },
    None => primary.clone(),
  }
}

/// Map each manifest shard to the work items whose ingress block it owns.
/// Returns one `Vec<&AnonWorkItem>` per manifest shard (aligned to
/// `manifest.shards`, possibly empty). A manifest "block" address is exactly a
/// work item's block address ([`work_block_addr`]), so the map is 1:1. Errors if
/// the manifest does not cover the env's full work set — a stale or mismatched
/// manifest would otherwise silently drop constants from the aggregate.
fn group_work_by_manifest<'a>(
  env: &IxonEnv,
  work: &'a [AnonWorkItem],
  manifest: &ix_kernel::shard::ShardManifest,
) -> Result<Vec<Vec<&'a AnonWorkItem>>> {
  use std::collections::HashMap;

  use ix_common::address::Address;

  let mut by_primary: HashMap<Address, usize> = HashMap::with_capacity(work.len());
  for (i, w) in work.iter().enumerate() {
    by_primary.insert(work_block_addr(env, w), i);
  }
  let mut assigned = vec![false; work.len()];
  let mut groups: Vec<Vec<&AnonWorkItem>> =
    Vec::with_capacity(manifest.shards.len());
  let mut unknown_blocks = 0usize;
  for shard in &manifest.shards {
    let mut g: Vec<&AnonWorkItem> = Vec::with_capacity(shard.blocks.len());
    for b in &shard.blocks {
      match by_primary.get(b) {
        Some(&i) if !assigned[i] => {
          assigned[i] = true;
          g.push(&work[i]);
        },
        Some(_) => {}, // block listed twice across shards — keep the first
        None => unknown_blocks += 1,
      }
    }
    groups.push(g);
  }
  let uncovered = assigned.iter().filter(|a| !**a).count();
  if uncovered > 0 {
    bail!(
      "manifest covers only {} of {} work items ({uncovered} uncovered) — the \
       manifest was built for a different or stale env; re-run `ix profile` + \
       `ix shard` on this .ixe",
      work.len() - uncovered,
      work.len(),
    );
  }
  if unknown_blocks > 0 {
    println!(
      "  note: {unknown_blocks} manifest block(s) have no work item in this env (ignored)"
    );
  }
  Ok(groups)
}

/// Prove a `.ixes` manifest partition: one closure-injected leaf proof per
/// (non-empty) manifest shard, folded into a single aggregate whose committed
/// subject is bound to the env. Honors `--execute` (per-shard VM cycles) and
/// `--only-shard k` (prove just shard k). The agg program is set up lazily,
/// only when more than one leaf is produced.
async fn run_shard_plan(
  client: &EmbeddedClient,
  plan: &InputPlan,
  manifest_path: &std::path::Path,
  args: &Args,
) -> Result<()> {
  use std::collections::HashSet;

  use ix_common::address::Address;
  use ix_kernel::shard::ShardManifest;

  let env =
    IxonEnv::get_anon(&mut &plan.env_bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");

  let mbytes = fs::read(manifest_path)
    .map_err(|e| anyhow::anyhow!("read manifest {}: {e}", manifest_path.display()))?;
  let manifest = ShardManifest::from_bytes(&mbytes)
    .map_err(|e| anyhow::anyhow!("parse manifest {}: {e}", manifest_path.display()))?;
  let groups = group_work_by_manifest(&env, &work, &manifest)?;

  // Select (manifest-index, items) to prove: every non-empty shard, or just the
  // one named by --only-shard.
  let selected: Vec<(usize, &Vec<&AnonWorkItem>)> = match args.only_shard {
    Some(k) => {
      if k == 0 || k > groups.len() {
        bail!("--only-shard {k} out of range; manifest has {} shard(s)", groups.len());
      }
      vec![(k - 1, &groups[k - 1])]
    },
    None => groups.iter().enumerate().filter(|(_, g)| !g.is_empty()).collect(),
  };
  if selected.iter().all(|(_, g)| g.is_empty()) {
    bail!("nothing to prove: selected manifest shard(s) are empty");
  }

  println!(
    "shard-plan {}: {} work items, manifest {} shard(s), cross-ingress total {}; proving {} leaf(s)",
    plan.label,
    work.len(),
    manifest.num_shards,
    (manifest.total_cross_ingress as usize).human_count_bytes(),
    selected.len(),
  );
  for &(idx, g) in &selected {
    let si = &manifest.shards[idx];
    println!(
      "  shard {idx:>3}: {:>5} work items  heartbeats={}  own={}  cross_ingress={}",
      g.len(),
      si.heartbeats,
      (si.own_size as usize).human_count_bytes(),
      (si.cross_ingress as usize).human_count_bytes(),
    );
  }

  // Per-shard guest input: explicit primary check-list + closure-injected
  // sub-env (ship only this shard's dependency closure, never the whole env).
  let build_inputs = |g: &[&AnonWorkItem]| -> Result<(Vec<u8>, Vec<u8>, Vec<[u8; 32]>)> {
    let primaries: Vec<Address> = g.iter().map(|w| w.primary().clone()).collect();
    let check_list = Address::pack(&primaries);
    let roots: Vec<Address> = g.iter().flat_map(|w| w.proven_targets()).collect();
    let cover: Vec<[u8; 32]> = roots.iter().map(|a| *a.as_bytes()).collect();
    let sub_env = build_sub_env(&env, &roots)?;
    Ok((check_list, sub_env, cover))
  };

  // ---- Execute mode: run each shard in the VM for cycles (no proof). ----
  if args.execute {
    let mut total_steps = 0u64;
    let mut total_failures = 0u32;
    for &(idx, g) in &selected {
      let (check_list, sub_env, _cover) = build_inputs(g)?;
      let stdin = leaf_stdin(0, 0, &sub_env, &check_list);
      let result = client.execute(&SHARD_PROGRAM, stdin).run()?.await?;
      let mut buf = [0u8; SHARD_PUBLICS_LEN];
      result.get_public_values_slice(&mut buf);
      let publics = ShardPublics::decode(&buf);
      let cycles = result.get_execution_steps();
      total_steps += cycles;
      total_failures = total_failures.saturating_add(publics.failures);
      println!(
        "  [shard {idx}] {} work items, failures={}, cycles={cycles}",
        g.len(),
        publics.failures,
      );
    }
    println!("total cycles: {total_steps}, failures: {total_failures}");
    if total_failures > 0 {
      bail!("kernel typecheck produced {total_failures} failure(s)");
    }
    return Ok(());
  }

  // ---- Prove mode: one closure-injected leaf per shard. ----
  let mut leaf_proofs: Vec<Vec<u8>> = Vec::with_capacity(selected.len());
  let mut leaf_subjects: Vec<Address> = Vec::with_capacity(selected.len());
  let mut covered_union: HashSet<[u8; 32]> = HashSet::default();
  let mut total_leaf_ms = 0u64;
  let mut total_failures = 0u32;
  let mut last_leaf_result = None;
  let mut shard_vk: Vec<u8> = Vec::new();
  let leaf_start = Instant::now();
  for &(idx, g) in &selected {
    let (check_list, sub_env, cover) = build_inputs(g)?;
    println!(
      "  [shard {idx}] proving {} work items; closure sub-env {} vs whole env {} ({:.0}%)",
      g.len(),
      sub_env.len().human_count_bytes(),
      plan.env_bytes.len().human_count_bytes(),
      100.0 * sub_env.len() as f64 / plan.env_bytes.len().max(1) as f64,
    );
    let stdin = leaf_stdin(0, 0, &sub_env, &check_list);
    let result = client.prove(&SHARD_PROGRAM, stdin).run()?.await?;
    let mut buf = [0u8; SHARD_PUBLICS_LEN];
    result.get_public_values_slice(&mut buf);
    let publics = ShardPublics::decode(&buf);
    total_failures = total_failures.saturating_add(publics.failures);
    let leaf_ms = result.get_proving_time();
    total_leaf_ms += leaf_ms;
    let blob = result.get_proof_bytes()?;
    if shard_vk.is_empty() {
      shard_vk = program_vk(&blob);
    }
    println!(
      "    failures={}, prove {:.2}s, {} steps",
      publics.failures,
      leaf_ms as f64 / 1000.0,
      result.get_execution_steps(),
    );
    // Bind each leaf: its committed subject must equal the env-derived merkle
    // root over the constants it certified. A guest that proved a different set
    // than the manifest assigned would commit a different root and fail here.
    let expected = subject_of_cover(&cover);
    if *expected.as_bytes() != publics.subject_root {
      bail!(
        "shard {idx}: committed subject {}… ≠ env-derived {}… — guest certified a \
         different set than the manifest assigned",
        Address::from_slice(&publics.subject_root)
          .map(|a| a.hex()[..16].to_string())
          .unwrap_or_default(),
        expected.hex()[..16].to_string(),
      );
    }
    covered_union.extend(cover.iter().copied());
    leaf_subjects.push(expected);
    leaf_proofs.push(blob);
    last_leaf_result = Some(result);
  }
  let leaf_wall = leaf_start.elapsed();

  // Full-env coverage: the union of all leaves must cover every work item's
  // targets (skipped under --only-shard, which proves a single shard).
  if args.only_shard.is_none() {
    let grand: HashSet<[u8; 32]> =
      work.iter().flat_map(|w| w.proven_targets()).map(|a| *a.as_bytes()).collect();
    let miss = grand.iter().filter(|t| !covered_union.contains(*t)).count();
    if miss > 0 {
      bail!("coverage gap: {miss} env target(s) not covered by any shard leaf");
    }
  }

  // ---- Aggregate: tree-fold the leaves, mirroring the merkle subject fold so
  // the root's committed subject can be bound to the env. ----
  let arity = (args.agg_arity as usize).max(2);
  let (final_size, agg_ms, verify_ms, root_committed, expected_final) =
    if leaf_proofs.len() == 1 {
      let leaf = last_leaf_result.expect("single leaf");
      let final_size = leaf.get_proof_bytes()?.len();
      let vstart = Instant::now();
      leaf.verify()?;
      // Per-leaf binding above already pinned the subject; fold of 1 = itself.
      (final_size, 0u64, vstart.elapsed().as_millis() as u64, leaf_subjects[0].clone(), leaf_subjects[0].clone())
    } else {
      if shard_vk.is_empty() {
        bail!("no shard vk available to pin the aggregation");
      }
      client.setup(&AGG_PROGRAM).run()?.await?;
      let mut cur_proofs = leaf_proofs;
      let mut cur_subjects = leaf_subjects;
      let mut total_agg_ms = 0u64;
      let mut level = 1usize;
      let mut root_result: Option<_> = None;
      while cur_proofs.len() > 1 {
        let ranges = tree_partition(cur_proofs.len(), arity);
        println!(
          "  [agg L{level}] folding {} proofs into {} (arity {arity})",
          cur_proofs.len(),
          ranges.len(),
        );
        let mut next_proofs: Vec<Vec<u8>> = Vec::with_capacity(ranges.len());
        let mut next_subjects: Vec<Address> = Vec::with_capacity(ranges.len());
        let mut last_result = None;
        for &(s, e) in &ranges {
          let allowed = distinct_vks(&cur_proofs[s..e]);
          let astart = Instant::now();
          let result =
            client.prove(&AGG_PROGRAM, agg_stdin(&allowed, &cur_proofs[s..e])).run()?.await?;
          total_agg_ms += result.get_proving_time();
          println!(
            "    [{s}..{e}] {} proofs → prove {:.2}s (wall {:.2}s)",
            e - s,
            result.get_proving_time() as f64 / 1000.0,
            astart.elapsed().as_secs_f64(),
          );
          next_proofs.push(result.get_proof_bytes()?);
          // Mirror the guest's left-associative merkle_join over this chunk.
          next_subjects.push(fold_subjects(&cur_subjects[s..e]));
          last_result = Some(result);
        }
        cur_proofs = next_proofs;
        cur_subjects = next_subjects;
        root_result = last_result;
        level += 1;
      }
      let root = root_result.expect("tree-fold produced a root");
      let final_size = root.get_proof_bytes()?.len();
      let mut fbuf = [0u8; SHARD_PUBLICS_LEN];
      root.get_public_values_slice(&mut fbuf);
      let committed = ShardPublics::decode(&fbuf).subject_root;
      let vstart = Instant::now();
      root.verify()?;
      let committed_addr = Address::from_slice(&committed)
        .unwrap_or_else(|_| ixon::merkle::zero_address());
      (final_size, total_agg_ms, vstart.elapsed().as_millis() as u64, committed_addr, cur_subjects[0].clone())
    };

  // Bind the aggregate's committed subject to the env-derived fold.
  if root_committed != expected_final {
    bail!(
      "subject-binding failed: aggregate commits {}… but the env requires {}… — \
       the folded proofs do not cover this env",
      root_committed.hex()[..16].to_string(),
      expected_final.hex()[..16].to_string(),
    );
  }

  println!(
    "shard-plan done: {} leaf(s) ({:.2}s wall, {:.2}s sum) + agg {:.2}s → final proof {}; \
     verify {:.3}s; subject bound to env ({}… over {} target(s))",
    selected.len(),
    leaf_wall.as_secs_f64(),
    total_leaf_ms as f64 / 1000.0,
    agg_ms as f64 / 1000.0,
    final_size.human_count_bytes(),
    verify_ms as f64 / 1000.0,
    expected_final.hex()[..16].to_string(),
    covered_union.len(),
  );
  if total_failures > 0 {
    bail!("kernel typecheck produced {total_failures} failure(s) (proof still verifies)");
  }
  Ok(())
}

#[tokio::main]
async fn main() -> Result<()> {
  zisk_sdk::setup_logger(VerboseMode::Info);

  let args = Args::parse();

  // Collect inputs. No `--ixe` → a single empty env (back-compat).
  let inputs: Vec<Option<PathBuf>> =
    if args.ixe.is_empty() { vec![None] } else { args.ixe.iter().cloned().map(Some).collect() };

  // `--only-shard` and `--verify-constraints` are single-shard debug
  // tools; they don't compose with a multi-input batch.
  if inputs.len() > 1 && args.only_shard.is_some() {
    bail!("--only-shard requires exactly one --ixe input");
  }
  if inputs.len() > 1 && args.verify_constraints {
    bail!("--verify-constraints requires exactly one --ixe input");
  }
  // `--shard-plan` is per-env: the manifest covers one specific env's full work
  // set, so a batch of inputs has no single manifest to apply.
  if args.shard_plan.is_some() && inputs.len() > 1 {
    bail!("--shard-plan requires exactly one --ixe input (the env the manifest was built for)");
  }

  // ---- Plan every input up front (parse + shard). ----
  let print_plan = args.plan || args.shard_bytes.is_some();
  let mut plans: Vec<InputPlan> = Vec::with_capacity(inputs.len());
  for ixe in &inputs {
    plans.push(plan_input(ixe.as_ref(), args.shard_consts, args.shard_bytes, print_plan)?);
  }

  // `--only-shard` narrows the (single) input's shard list.
  if let Some(only) = args.only_shard {
    let plan = &mut plans[0];
    let num = plan.shards.len();
    if only == 0 || only > num {
      bail!("--only-shard {only} out of range; have {num} shard(s)");
    }
    let (s, e) = plan.shards[only - 1];
    println!("only-shard: proving shard {only}/{num} of {} range [{s}, {e})", plan.label);
    plan.shards = vec![(s, e)];
  }

  // Pre-flight closure gate: bail before any proving if the batch isn't a
  // closed env modulo axioms. Runs in `--plan` mode too, so `--plan
  // --require-closed` is a fast no-prove closure check.
  if args.require_closed {
    let store = match (&args.store_dir, args.no_reuse) {
      (Some(dir), false) => load_store(dir),
      _ => std::collections::HashSet::default(),
    };
    check_inputs_closed(&inputs, &store)?;
  }

  if args.plan {
    return Ok(());
  }

  // Grand totals across the whole batch.
  let grand_total_items: u32 = plans.iter().map(|p| p.total).sum();
  let grand_target_count: usize = plans.iter().map(|p| p.target_count).sum();
  let total_leaves: usize = plans.iter().map(|p| p.shards.len()).sum();

  let client = build_client(args.gpu, Some(args.max_witness_stored))?;
  client.setup(&SHARD_PROGRAM).run()?.await?;
  // Skip agg-guest setup unless we'll produce more than one leaf proof.
  // The reuse path (store_dir) sets up the agg program itself (it folds a
  // different set of proofs); skip the normal-path setup for it here.
  let need_agg = !args.execute
    && !args.verify_constraints
    && args.store_dir.is_none()
    && args.shard_plan.is_none()
    && total_leaves > 1;
  if need_agg {
    client.setup(&AGG_PROGRAM).run()?.await?;
  }

  // ---- Manifest-driven sharding (the offline profiler/partitioner plan). ----
  // Prove the `.ixes` partition: one closure-injected leaf per manifest shard,
  // folded into one aggregate. Sets up the agg program itself (lazily, only
  // when >1 shard). Returns when done — does not fall through to the
  // range-based execute/leaf paths below.
  if let Some(manifest_path) = &args.shard_plan {
    run_shard_plan(&client, &plans[0], manifest_path, &args).await?;
    return Ok(());
  }

  // ---- Cross-proof reuse (execute only): check only NOVEL constants. ----
  //
  // Load the proven-primaries store, and for each input check only the work
  // items whose primary isn't already in the store. Constants proven by an
  // earlier input/run are skipped (their well-typedness is an assumption
  // resolved at the store layer). Content-addressing makes the primary the
  // shared key across envs. After a clean run, the novel primaries are added
  // to the store. Demonstrates shards/proofs avoiding re-checking shared
  // constants.
  if let Some(store_dir) = &args.store_dir {
    use std::collections::HashSet;

    use ix_common::address::Address;

    // Reuse works in both modes: `--execute` checks novel constants in the VM;
    // otherwise it PROVES only the novel constants (skipping ones already in
    // the store) and folds the novel leaf proofs into one aggregate proof.
    let prove_mode = !args.execute;
    let chunk = if args.shard_consts > 0 { args.shard_consts as usize } else { 300 };
    // `--shard-bytes B` selects closure-aware sizing (pack until a chunk's
    // injected-closure bytes hit B), which only makes sense when injecting —
    // so it implies closure injection. `--closure-inject` alone injects with
    // the default count-based chunking. Either way the guest gets a sub-env.
    let inject = args.closure_inject || args.shard_bytes.is_some();

    // The store records certified TARGET addresses (not just primaries) so a
    // novel constant's direct refs can be resolved against it. `--no-reuse`
    // forces an empty store so every item is novel (the "no sharing" baseline)
    // without touching the real one on disk.
    let mut store =
      if args.no_reuse { HashSet::default() } else { load_store(store_dir) };
    let store_start = store.len();
    let hx = |b: &[u8; 32]| {
      Address::from_slice(b).map(|a| a.hex()[..16].to_string()).unwrap_or_default()
    };

    let mut grand_checked: u64 = 0;
    let mut grand_reused: u64 = 0;
    let mut total_steps: u64 = 0; // execute-mode cycles
    let mut total_leaf_ms: u64 = 0; // prove-mode leaf proving time
    let mut total_failures: u32 = 0;
    let mut all_refs: HashSet<[u8; 32]> = HashSet::default();
    // Novel leaf proofs produced this run (prove mode), folded + verified.
    let mut leaf_proof_bytes: Vec<Vec<u8>> = Vec::new();
    // The covered-target set behind each novel leaf, in the SAME order as
    // `leaf_proof_bytes` — lets the host re-derive each child's expected
    // subject root from the env for the final coverage-binding check.
    let mut leaf_covers: Vec<Vec<[u8; 32]>> = Vec::new();
    // Each novel leaf's COMMITTED subject root, captured at prove time (same
    // order). Re-reading `get_public_values_slice` on a stored result yields
    // zeros, so the single-leaf binding check reads from here.
    let mut leaf_committed_subjects: Vec<[u8; 32]> = Vec::new();
    // Every target address this run's aggregate must end up covering (novel +
    // reused), to assert the final combined subject is complete over the env.
    let mut grand_targets: HashSet<[u8; 32]> = HashSet::default();
    let mut last_leaf_result = None;
    // In-circuit resolution state: the store's EXISTING leaf proofs (loaded
    // before we append this run's), the reused constants we must resolve by
    // VERIFYING a covering store proof, and the shard program vk to pin.
    let stored_leaves =
      if prove_mode && !args.no_reuse { load_proof_index(store_dir) } else { Vec::new() };
    let mut all_reused_covered: HashSet<[u8; 32]> = HashSet::default();
    let mut shard_vk: Vec<u8> = Vec::new();

    for plan in &plans {
      let env =
        IxonEnv::get_anon(&mut &plan.env_bytes[..]).expect("invalid Ixon environment");
      let work = build_anon_work(&env).expect("build_anon_work");
      // A work item is reused iff its primary is already certified.
      let mut novel_items: Vec<&AnonWorkItem> =
        work.iter().filter(|w| !store.contains(w.primary().as_bytes())).collect();
      // Testing: cap to the first N novel items so a few shards of a huge env
      // can be proved end-to-end without proving all 171 (Init).
      if let Some(n) = args.limit_items {
        novel_items.truncate(n);
      }
      let reused_items = work.len() - novel_items.len();
      grand_reused += reused_items as u64;
      if novel_items.is_empty() {
        println!("  [{}] {} work items: all reused — skipped", plan.label, work.len());
        continue;
      }

      // `consts`-key addresses this input newly certifies.
      let mut novel_targets: HashSet<[u8; 32]> = HashSet::default();
      for w in &novel_items {
        for t in w.proven_targets() {
          novel_targets.insert(*t.as_bytes());
        }
      }
      grand_targets.extend(novel_targets.iter().copied());

      // Reused work items' covered targets — these must be DISCHARGED by
      // verifying a store proof that covers them (not trusted).
      for w in work.iter().filter(|w| store.contains(w.primary().as_bytes())) {
        for t in w.proven_targets() {
          all_reused_covered.insert(*t.as_bytes());
        }
      }

      // Dependency refs of the novel set; those not in the store / not certified
      // now stay OPEN assumptions of the conditional `CheckEnv` claim. A
      // `Constant.refs` entry can point at either another CONSTANT (a genuine
      // typing obligation) or a literal DATA blob (the bytes behind an
      // `Expr::Nat`/`Expr::Str` — e.g. the numbers 0, 1). Literals are
      // well-typed by construction and content-addressing pins their bytes, so
      // they are NOT assumptions; skip any ref that resolves to a blob.
      let mut open_now = 0u64;
      for w in &novel_items {
        for t in w.proven_targets() {
          if let Some(c) = env.get_const(&t) {
            for r in &c.refs {
              if env.get_blob(r).is_some() {
                continue; // literal/data blob, not a typing assumption
              }
              let rb = r.as_bytes();
              all_refs.insert(*rb);
              if !store.contains(rb) && !novel_targets.contains(rb) {
                open_now += 1;
              }
            }
          }
        }
      }

      // Chunk novel WORK ITEMS so each guest run stays under the ~512 MB wall.
      // In prove mode each leaf proof is stored with the consts it certifies,
      // so a future run can resolve them by verification.
      let mut input_cycles: u64 = 0;
      let mut input_leaf_ms: u64 = 0;
      let mut input_failures: u32 = 0;
      let mut first_subject = [0u8; 32];
      let mut first_assumptions = [0u8; 32];
      // Closure-aware sizing when `--shard-bytes` is set (pack until a chunk's
      // injected-closure bytes hit the budget); otherwise fixed work-item count.
      let chunk_ranges: Vec<(usize, usize)> = if let Some(b) = args.shard_bytes {
        plan_chunks_by_closure(&env, &novel_items, b)?
      } else {
        (0..novel_items.len())
          .step_by(chunk)
          .map(|s| (s, (s + chunk).min(novel_items.len())))
          .collect()
      };
      for (ci, &(cs, ce)) in chunk_ranges.iter().enumerate() {
        let nc = &novel_items[cs..ce];
        let primaries: Vec<Address> = nc.iter().map(|w| w.primary().clone()).collect();
        let check_list = Address::pack(&primaries);
        // Closure injection: ship the guest only this chunk's dependency
        // closure, not the whole env. The committed claim is invariant —
        // subject/assumptions depend only on the checked targets and their
        // direct refs, all present in the closure — so this only shrinks the
        // guest's decode, essential for envs that don't fit whole (Init).
        let sub_env: Option<Vec<u8>> = if inject {
          let roots: Vec<Address> = nc.iter().flat_map(|w| w.proven_targets()).collect();
          Some(build_sub_env(&env, &roots)?)
        } else {
          None
        };
        if let Some(se) = &sub_env {
          println!(
            "  [shard {}] {} work items; closure sub-env {} vs whole env {} ({:.0}%)",
            ci,
            nc.len(),
            se.len().human_count_bytes(),
            plan.env_bytes.len().human_count_bytes(),
            100.0 * se.len() as f64 / plan.env_bytes.len().max(1) as f64,
          );
        }
        let env_slice: &[u8] = sub_env.as_deref().unwrap_or(&plan.env_bytes);
        let stdin = leaf_stdin(0, 0, env_slice, &check_list);
        let mut buf = [0u8; SHARD_PUBLICS_LEN];
        // Targets this shard certifies — used by both the proof index and the
        // per-shard store update below.
        let chunk_covered: Vec<[u8; 32]> =
          nc.iter().flat_map(|w| w.proven_targets()).map(|a| *a.as_bytes()).collect();
        if prove_mode {
          let result = client.prove(&SHARD_PROGRAM, stdin).run()?.await?;
          result.get_public_values_slice(&mut buf);
          input_leaf_ms += result.get_proving_time();
          let blob = result.get_proof_bytes()?;
          if shard_vk.is_empty() {
            shard_vk = program_vk(&blob);
          }
          if !args.no_reuse {
            append_proof(store_dir, &blob, &chunk_covered)?;
          }
          leaf_proof_bytes.push(blob);
          leaf_covers.push(chunk_covered.clone());
          let mut subj = [0u8; 32];
          subj.copy_from_slice(&buf[44..76]);
          leaf_committed_subjects.push(subj);
          last_leaf_result = Some(result);
        } else {
          let result = client.execute(&SHARD_PROGRAM, stdin).run()?.await?;
          result.get_public_values_slice(&mut buf);
          input_cycles += result.get_execution_steps();
        }
        let publics = ShardPublics::decode(&buf);
        input_failures = input_failures.saturating_add(publics.failures);
        // Bank this shard's certified targets into the store IMMEDIATELY and
        // persist, rather than waiting until the whole input (or batch) is
        // done. So a re-run / resume skips already-proven shards and never
        // redoes their work, and a later input sees this shard's constants as
        // reused as soon as it lands. Gate on the shard verifying clean.
        if !args.no_reuse && publics.failures == 0 {
          for t in &chunk_covered {
            store.insert(*t);
          }
          save_store(store_dir, &store)?;
        }
        if ci == 0 {
          first_subject = publics.subject_root;
          first_assumptions = publics.assumptions_root;
        }
      }
      total_steps += input_cycles;
      total_leaf_ms += input_leaf_ms;
      total_failures = total_failures.saturating_add(input_failures);
      grand_checked += novel_targets.len() as u64;
      let n_chunks = chunk_ranges.len();
      let work_note = if prove_mode {
        format!("leaf-prove {:.2}s", (input_leaf_ms as f64) / 1000.0)
      } else {
        format!("cycles={input_cycles}")
      };
      println!(
        "  [{}] {} items: {reused_items} reused, {} novel ({} targets) / {n_chunks} chunk(s); \
         failures={input_failures}, {work_note}; open assumptions: {open_now}; \
         claim[chunk0] CheckEnv{{ subject={}…, assumptions={}… }}",
        plan.label,
        work.len(),
        novel_items.len(),
        novel_targets.len(),
        hx(&first_subject),
        hx(&first_assumptions),
      );
      // Note: targets are banked per-shard above (immediately after each shard
      // verifies clean), so there's no end-of-input insert here — a partially
      // failed input still keeps its clean shards' constants in the store.
    }
    // Per-shard `save_store` already persisted every clean shard; this final
    // write is a harmless backstop. `--no-reuse` is a read-only baseline and
    // never persists (it would clobber the populated store the comparison run
    // depends on).
    if !args.no_reuse {
      save_store(store_dir, &store)?;
    }
    let open: usize = all_refs.iter().filter(|r| !store.contains(*r)).count();
    println!(
      "reuse summary: {grand_reused} work items reused, {grand_checked} targets certified; \
       store {store_start} → {} targets",
      store.len(),
    );
    println!(
      "open assumptions (refs not yet in store): {open} — resolve by proving their providers \
       (e.g. init) into the store; residual = axioms",
    );

    if total_failures > 0 {
      bail!("kernel typecheck produced {total_failures} failure(s)");
    }

    if prove_mode {
      // ---- In-circuit resolution ----
      // Verify (don't trust) the reused constants: pull the store's leaf proofs
      // that cover them and fold them WITH this run's novel leaves. The agg
      // guest verifies each, pins its program vk to SHARD_VK, and folds the
      // claims — so the aggregate cryptographically attests the full env,
      // reused parts included.
      let covering: Vec<(Vec<u8>, std::collections::HashSet<[u8; 32]>)> = stored_leaves
        .iter()
        .filter(|(_, cov)| cov.iter().any(|a| all_reused_covered.contains(a)))
        .map(|(blob, cov)| (blob.clone(), cov.clone()))
        .collect();
      let n_novel = leaf_proof_bytes.len();
      let n_cover = covering.len();

      // ---- Final soundness check: bind the aggregate's subject to the env ----
      // The agg commits `subject = merkle_join`-fold of its children's subject
      // roots (each read from a *verified* child proof). On its own that only
      // attests "these verified shard proofs cover SOME constants". To pin
      // *which* env, the host re-derives the expected per-child subject root
      // FROM THE ENV (each child's `covered()` set → `merkle_root_canonical`),
      // folds them in the same order, and (a) asserts every env target is
      // covered by some folded child, then (b) checks the final proof's
      // committed subject equals this env-derived root. A swapped-in
      // verified-but-unrelated proof would change the committed root and fail.
      grand_targets.extend(all_reused_covered.iter().copied());
      let mut child_subjects: Vec<Address> = Vec::with_capacity(n_novel + n_cover);
      let mut covered_union: HashSet<[u8; 32]> = HashSet::default();
      for cov in &leaf_covers {
        child_subjects.push(subject_of_cover(cov));
        covered_union.extend(cov.iter().copied());
      }
      for (_, cov) in &covering {
        let v: Vec<[u8; 32]> = cov.iter().copied().collect();
        child_subjects.push(subject_of_cover(&v));
        covered_union.extend(cov.iter().copied());
      }
      let expected_subject = fold_subjects(&child_subjects);
      let expected_bytes = *expected_subject.as_bytes();
      let uncovered =
        grand_targets.iter().filter(|t| !covered_union.contains(*t)).count();
      if uncovered > 0 {
        bail!(
          "coverage gap: {uncovered} env target(s) not covered by any folded proof — \
           the aggregate would not attest the full env"
        );
      }

      let mut fold = leaf_proof_bytes;
      fold.extend(covering.into_iter().map(|(b, _)| b));
      let total_fold = fold.len();

      // Assert the final proof's committed subject root matches the env-derived
      // fold. `committed` comes from the captured leaf publics (single-leaf) or
      // the fresh agg result's publics (fold) — never a re-read of a stored
      // result, which yields zeros.
      let assert_subject_bound = |committed: [u8; 32]| -> Result<()> {
        if committed != expected_bytes {
          bail!(
            "subject-binding failed: final proof commits subject {}… but the env \
             requires {}… — the folded proofs do not cover this env",
            hx(&committed),
            hx(&expected_bytes),
          );
        }
        Ok(())
      };

      if total_fold == 0 {
        println!("nothing novel to prove (fully reused) — no proof generated");
      } else if total_fold == 1 {
        // One leaf, no reused-covering proof to fold in — verify it directly.
        let leaf = last_leaf_result.expect("single leaf");
        let final_size = leaf.get_proof_bytes()?.len();
        let vstart = Instant::now();
        leaf.verify()?;
        assert_subject_bound(leaf_committed_subjects[0])?;
        println!(
          "resolved fold: 1 novel leaf + 0 reused-covering proofs; leaf-prove {:.2}s; \
           final proof size {}; verify {:.3}s; subject bound to env ({}… over {} target(s))",
          (total_leaf_ms as f64) / 1000.0,
          final_size.human_count_bytes(),
          vstart.elapsed().as_secs_f64(),
          hx(&expected_bytes),
          grand_targets.len(),
        );
      } else {
        // Single-level fold over novel leaves + the reused-covering store
        // proofs (all SHARD_VK), vk-pinned in-circuit.
        if shard_vk.is_empty() {
          bail!("no shard vk available to pin the aggregation");
        }
        client.setup(&AGG_PROGRAM).run()?.await?;
        let allowed = vec![shard_vk.clone()];
        let agg_start = Instant::now();
        let result =
          client.prove(&AGG_PROGRAM, agg_stdin(&allowed, &fold)).run()?.await?;
        let agg_ms = result.get_proving_time();
        let final_size = result.get_proof_bytes()?.len();
        let mut fbuf = [0u8; SHARD_PUBLICS_LEN];
        result.get_public_values_slice(&mut fbuf);
        let agg_committed = ShardPublics::decode(&fbuf).subject_root;
        let vstart = Instant::now();
        result.verify()?;
        assert_subject_bound(agg_committed)?;
        println!(
          "resolved fold: {n_novel} novel leaves + {n_cover} reused-covering proof(s) \
           → 1 agg (each vk-pinned to SHARD_VK); leaf-prove {:.2}s + agg {:.2}s (wall {:.2}s); \
           final proof size {}; verify {:.3}s; subject bound to env ({}… over {} target(s))",
          (total_leaf_ms as f64) / 1000.0,
          (agg_ms as f64) / 1000.0,
          agg_start.elapsed().as_secs_f64(),
          final_size.human_count_bytes(),
          vstart.elapsed().as_secs_f64(),
          hx(&expected_bytes),
          grand_targets.len(),
        );
      }
    } else {
      println!("total cycles: {total_steps}");
    }
    return Ok(());
  }

  // ---- Execute path: run every shard of every input in the VM. ----
  if args.execute {
    let mut total_steps: u64 = 0;
    let mut total_exec_ms: u64 = 0;
    let mut total_failures: u32 = 0;
    for plan in &plans {
      let num_shards = plan.shards.len();
      for (i, &(start, end)) in plan.shards.iter().enumerate() {
        let stdin = leaf_stdin(start, end, &plan.env_bytes, &[]);
        let result = client.execute(&SHARD_PROGRAM, stdin).run()?.await?;
        let mut buf = [0u8; SHARD_PUBLICS_LEN];
        result.get_public_values_slice(&mut buf);
        let publics = ShardPublics::decode(&buf);
        let cycles = result.get_execution_steps();
        total_steps += cycles;
        total_exec_ms += result.get_execution_time();
        total_failures = total_failures.saturating_add(publics.failures);
        println!(
          "  [{} shard {}/{num_shards}] range [{start}, {end}), failures={}, cycles={cycles}",
          plan.label,
          i + 1,
          publics.failures,
        );
      }
    }
    let total_exec = Duration::from_millis(total_exec_ms);
    let throughput =
      grand_target_count as f64 / total_exec.as_secs_f64().max(f64::EPSILON);
    println!("failures: {total_failures}");
    println!("cycles: {total_steps}");
    println!("inputs: {}", plans.len());
    println!("work items: {grand_total_items}");
    println!("target constants: {grand_target_count}");
    println!(
      "exec time: {:.3}s, throughput: {}",
      total_exec.as_secs_f64(),
      throughput.human_throughput("consts"),
    );
    if total_failures > 0 {
      bail!("kernel typecheck produced {total_failures} failure(s)");
    }
    return Ok(());
  }

  if args.verify_constraints {
    // Guaranteed single input by the guard above.
    let plan = &plans[0];
    if plan.shards.len() != 1 {
      bail!("--verify-constraints requires a single shard (got {})", plan.shards.len());
    }
    let (start, end) = plan.shards[0];
    let stdin = leaf_stdin(start, end, &plan.env_bytes, &[]);
    client.verify_constraints(&SHARD_PROGRAM, stdin).run()?.await?;
    println!("constraints verified");
    return Ok(());
  }

  // ---- Leaf phase: one proof per shard, across every input. ----
  //
  // All proofs are produced in this one process, so the GPU kernels and
  // proofman state stay warm from the first shard through the last.
  let mut leaf_proof_bytes: Vec<Vec<u8>> = Vec::with_capacity(total_leaves);
  let mut total_leaf_ms: u64 = 0;
  let mut total_failures: u32 = 0;
  // Keep the final leaf's result handle for the single-leaf path so it can
  // `.verify()` directly with no aggregation.
  let mut last_leaf_result = None;
  let leaf_phase_start = Instant::now();
  for plan in &plans {
    let num_shards = plan.shards.len();
    let mut input_publics: Vec<ShardPublics> = Vec::with_capacity(num_shards);
    for (i, &(start, end)) in plan.shards.iter().enumerate() {
      println!(
        "  [{} leaf {}/{num_shards}] range [{start}, {end}) — proving...",
        plan.label,
        i + 1,
      );
      let stdin = leaf_stdin(start, end, &plan.env_bytes, &[]);
      let result = client.prove(&SHARD_PROGRAM, stdin).run()?.await?;
      let mut buf = [0u8; SHARD_PUBLICS_LEN];
      result.get_public_values_slice(&mut buf);
      let publics = ShardPublics::decode(&buf);
      let leaf_ms = result.get_proving_time();
      total_leaf_ms += leaf_ms;
      println!(
        "    failures={}, prove time {:.2}s, {} steps",
        publics.failures,
        (leaf_ms as f64) / 1000.0,
        result.get_execution_steps(),
      );
      leaf_proof_bytes.push(result.get_proof_bytes()?);
      input_publics.push(publics);
      last_leaf_result = Some(result);
    }
    // Per-input coherence: this input's shards must tile its own env.
    total_failures = total_failures
      .saturating_add(check_input_coherence(&plan.label, &input_publics, plan.total)?);
  }
  let leaf_phase_wall = leaf_phase_start.elapsed();
  let total_leaf_size: usize = leaf_proof_bytes.iter().map(Vec::len).sum();
  println!(
    "leaf phase: {total_leaves} proofs across {} input(s), {:.2}s wall, {:.2}s sum, \
     leaf-bytes total {}",
    plans.len(),
    leaf_phase_wall.as_secs_f64(),
    (total_leaf_ms as f64) / 1000.0,
    total_leaf_size.human_count_bytes(),
  );

  // ---- Aggregation phase: tree-fold every leaf into one proof. ----
  //
  // The agg guest verifies a list of Zisk proofs via `verify_zisk_proof`
  // and is mode-agnostic: it works on both leaf proofs and on its own
  // recursive output, and on leaves from different envs. Tree fan-in is
  // set so each agg invocation reads only `arity` proofs (~5 MB stdin at
  // 16×336 kB), well under the guest RAM cap. We loop levels until exactly
  // one proof remains.
  let arity: usize = args.agg_arity as usize;
  let (final_size, agg_steps, agg_ms, verify_ms) = if total_leaves > 1 {
    let mut current: Vec<Vec<u8>> = leaf_proof_bytes;
    let mut total_agg_steps: u64 = 0;
    let mut total_agg_ms: u64 = 0;
    let mut level: usize = 1;
    // Hold the result handle from the *last* agg call at the *last*
    // level — that's the root and we need its `.verify()`.
    let mut root_result: Option<_> = None;
    while current.len() > 1 {
      let ranges = tree_partition(current.len(), arity);
      let n_chunks = ranges.len();
      println!(
        "  [agg L{level}] folding {} proofs into {n_chunks} (arity {arity})",
        current.len(),
      );
      let mut next: Vec<Vec<u8>> = Vec::with_capacity(n_chunks);
      let mut last_result_this_level = None;
      for (i, &(s, e)) in ranges.iter().enumerate() {
        // Allowed vks = the distinct program vks of the proofs being folded
        // (SHARD_VK at the leaf level; AGG_VK at higher levels). The agg guest
        // pins each child to one of these and commits them.
        let allowed = distinct_vks(&current[s..e]);
        let stdin = agg_stdin(&allowed, &current[s..e]);
        let agg_start = Instant::now();
        let result = client.prove(&AGG_PROGRAM, stdin).run()?.await?;
        let ms = result.get_proving_time();
        let steps = result.get_execution_steps();
        total_agg_steps += steps;
        total_agg_ms += ms;
        println!(
          "    [{}/{n_chunks}] {} proofs → {steps} steps, prove {:.2}s (wall {:.2}s)",
          i + 1,
          e - s,
          (ms as f64) / 1000.0,
          agg_start.elapsed().as_secs_f64(),
        );
        next.push(result.get_proof_bytes()?);
        last_result_this_level = Some(result);
      }
      current = next;
      root_result = last_result_this_level;
      level += 1;
    }
    let root = root_result.expect("tree-fold produced no result");
    let final_size = root.get_proof_bytes()?.len();
    let verify_start = Instant::now();
    root.verify()?;
    let verify_ms = verify_start.elapsed().as_millis() as u64;
    (final_size, total_agg_steps, total_agg_ms, verify_ms)
  } else {
    let leaf = last_leaf_result.expect("single-leaf path must have a leaf result");
    let final_size = leaf.get_proof_bytes()?.len();
    let verify_start = Instant::now();
    leaf.verify()?;
    let verify_ms = verify_start.elapsed().as_millis() as u64;
    (final_size, 0u64, 0u64, verify_ms)
  };

  let total_prove_ms = total_leaf_ms + agg_ms;
  let throughput = grand_target_count as f64
    / Duration::from_millis(total_prove_ms).as_secs_f64().max(f64::EPSILON);
  println!("failures: {total_failures}");
  println!("inputs: {}", plans.len());
  println!("work items: {grand_total_items}");
  println!("target constants: {grand_target_count}");
  println!("leaves: {total_leaves}");
  println!(
    "total prove time: {:.2}s (leaves {:.2}s + agg {:.2}s)",
    (total_prove_ms as f64) / 1000.0,
    (total_leaf_ms as f64) / 1000.0,
    (agg_ms as f64) / 1000.0,
  );
  println!("prove throughput: {}", throughput.human_throughput("consts"));
  println!("final proof size: {}", final_size.human_count_bytes());
  if total_leaves > 1 {
    println!("final proof steps: {agg_steps}");
  }
  println!("verify time: {:.3}s", (verify_ms as f64) / 1000.0);
  if total_failures > 0 {
    bail!("kernel typecheck produced {total_failures} failure(s) (proof still verifies)");
  }
  Ok(())
}

#[cfg(test)]
mod closure_tests {
  use std::collections::{HashMap, HashSet};

  use ix_common::address::Address;
  use ix_kernel::anon_work::build_anon_work;
  use ixon::env::Env as IxonEnv;

  use super::find_missing_deps;

  /// A self-contained env is closed (no missing deps); removing a foundational
  /// work item from the certified set must make at least one dependent's ref
  /// dangle. Gated on `IX_TEST_IXE`.
  #[test]
  fn closure_detects_missing_dep() {
    let Ok(path) = std::env::var("IX_TEST_IXE") else {
      eprintln!("IX_TEST_IXE unset — skipping closure_detects_missing_dep");
      return;
    };
    let bytes = std::fs::read(&path).expect("read IX_TEST_IXE");
    let env = IxonEnv::get_anon(&mut &bytes[..]).expect("get_anon");
    let work = build_anon_work(&env).expect("build_anon_work");
    let store = HashSet::new();

    // A bundled `.ixe` is self-contained → closed modulo axioms.
    let full = vec![("full".to_string(), env, work)];
    let (missing, checked, axioms) = find_missing_deps(&full, &store);
    assert!(
      missing.is_empty(),
      "expected a self-contained env to be closed, got {} missing",
      missing.len()
    );
    eprintln!("closed: {checked} constants, {axioms} axioms, 0 missing");

    // Find the most-referenced target, drop the work item that certifies it,
    // and confirm the dangling dependency is now detected.
    let (_, env2, mut work2) = full.into_iter().next().unwrap();
    let mut indeg: HashMap<Address, usize> = HashMap::new();
    for w in &work2 {
      for t in w.proven_targets() {
        if let Some(c) = env2.get_const(&t) {
          for r in &c.refs {
            if env2.get_blob(r).is_none() {
              *indeg.entry(r.clone()).or_insert(0) += 1;
            }
          }
        }
      }
    }
    let hottest = indeg
      .into_iter()
      .max_by_key(|(_, n)| *n)
      .map(|(a, _)| a)
      .expect("env has at least one dependency edge");
    work2.retain(|w| !w.proven_targets().iter().any(|t| *t == hottest));

    let holed = vec![("holed".to_string(), env2, work2)];
    let (missing2, _, _) = find_missing_deps(&holed, &store);
    assert!(
      missing2.iter().any(|(_, r)| *r == hottest),
      "dropping the hottest target should surface it as a missing dep"
    );
    eprintln!(
      "removing hottest target {}… surfaced {} dangling ref(s)",
      &hottest.hex()[..16],
      missing2.len()
    );
  }
}
