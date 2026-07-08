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

use anyhow::{Result, bail};
use clap::Parser;
use human_repr::{HumanCount, HumanThroughput};
use ix_bench::{
  EXIT_REJECTED, Rejection, Status, collect_consts, peak_rss_bytes, write_row,
};
use ix_kernel::anon_work::{
  AnonWorkItem, block_of_addr, build_anon_work, build_sub_env, work_block_addr,
};
use ixon::env::Env as IxonEnv;
use zisk_host::{AGG_PROGRAM, SHARD_PROGRAM};
use zisk_sdk::{
  EmbeddedClient, EmbeddedClientBuilder, EmbeddedOpts, ProverClient,
  VerboseMode, VerifyConstraintsExtension, ZiskStdin,
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

  /// Use the Emulator executor instead of the default Assembly executor.
  /// Assembly is the default: it is markedly faster at trace generation
  /// (measured ~4-6x on EXECUTE, ~11x on COMPUTE_MINIMAL_TRACE) and is the
  /// prerequisite for the hints stream. Pass `--emulator` to opt back into
  /// the Emulator (e.g. to debug, or on a box without the memlock rlimit the
  /// ASM executor's MAP_LOCKED mmaps require). See the multi-program
  /// setup-ordering note on `build_client`.
  #[arg(long)]
  emulator: bool,

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
  /// `ix shard <env.ixprof>`. Each manifest shard becomes one
  /// closure-injected leaf proof — its member blocks' work items, shipped with
  /// only their dependency closure — and the leaves fold into one aggregate.
  /// This is the performant path: the partition is balanced by the kernel
  /// profiler's real per-block heartbeats and cut to minimize cross-shard
  /// delta-unfold ingress, instead of the static `--shard-consts`/`--shard-bytes`
  /// heuristics. Requires exactly one `--ixe` (the env the manifest was built
  /// for); the manifest must cover that env's full work set. Composes with
  /// `--execute` (per-shard cycles), `--only-shard`, and `--store-dir`
  /// (cross-run proof reuse).
  #[arg(long, conflicts_with_all = ["shard_consts", "shard_bytes"])]
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

  /// Cross-run proof store directory (requires `--shard-plan`). A manifest
  /// shard whose certified targets are ALL already covered by stored proofs is
  /// not re-proven: the covering stored proofs are folded into the aggregate
  /// instead, where the agg guest VERIFIES them (vk-pinned, witness-checked)
  /// — reuse by verification, never by trust. Freshly proven shards are
  /// appended to the store (`proofs/<n>.{proof,cover,asm}`) as they complete,
  /// so an interrupted run resumes where it left off. Content-addressed: a
  /// constant has the same address across every env, so proofs are shared
  /// between envs too.
  #[arg(long)]
  store_dir: Option<PathBuf>,

  /// Disable cross-run reuse for THIS run while keeping the same code path.
  /// With `--store-dir`, treats the on-disk store as empty: every shard is
  /// novel, the full env is proved + aggregated from scratch — the "no
  /// sharing" baseline. The existing store is neither consulted nor
  /// overwritten, so a populated store survives for a back-to-back
  /// comparison.
  #[arg(long)]
  no_reuse: bool,

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

  /// Dump the selected shard's guest stdin (range + closure sub-env +
  /// check-list) to this file and exit, instead of executing/proving. Pairs
  /// with `--shard-plan` (+ `--only-shard` to pick which shard) to produce an
  /// `input.bin` for standalone profiling: `ziskemu -e <guest.elf> -i input.bin
  /// -X -S` or `cargo-zisk run -i input.bin -p summary`.
  #[arg(long)]
  dump_input: Option<PathBuf>,

  /// Comma-separated Lean names to check (each: closure sub-env → one leaf).
  #[arg(
    long,
    value_delimiter = ',',
    conflicts_with_all = ["shard_plan", "only_shard", "store_dir"]
  )]
  consts: Vec<String>,

  /// Additional names from a file (one per line, `#` comments); unions with --consts.
  #[arg(long, conflicts_with_all = ["shard_plan", "only_shard", "store_dir"])]
  consts_file: Option<PathBuf>,

  /// With --consts/--consts-file: check each subject only, trusting its deps.
  // Validated in main (not clap `requires = "consts"`): names may come from
  // --consts-file alone, which a clap-level `requires` would wrongly reject.
  #[arg(long)]
  skip_deps: bool,

  /// Write per-constant results JSON `{ "<name>": { … } }` (accumulated across names).
  /// With `--shard-plan --execute` it instead gets one env-level row (totals +
  /// per-shard cycles breakdown).
  #[arg(long)]
  json: Option<PathBuf>,

  /// Benchmark key for the env-level row `--shard-plan --execute --json`
  /// writes (e.g. the CamelCase env slug CI uses). Defaults to the manifest
  /// file stem.
  #[arg(long, requires = "shard_plan")]
  json_name: Option<String>,

  /// Enable tracing-texray; with --json, per-phase spans are written to <json>.spans.
  #[arg(long)]
  texray: bool,
}

/// Fail FAST on a guest typecheck failure: a rejected constant rejects the
/// whole workload, so bail before spending cycles (or proofs) on the
/// remaining shards — mirroring the OOM kill, which also cancels the rest.
/// Callers with a `--json` row in flight write it with `status: rejected`
/// BEFORE calling this; `main` maps the typed error to `EXIT_REJECTED`.
fn reject_failures(publics: &ShardPublics, ctx: &str) -> Result<()> {
  if publics.failures > 0 {
    return Err(
      Rejection { failures: publics.failures.into(), ctx: ctx.to_string() }
        .into(),
    );
  }
  Ok(())
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
  /// Number of targets the guest certified. Decoded for layout completeness;
  /// the host derives counts from the manifest/work sets instead.
  #[allow(dead_code)]
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
    .filter_map(|addr| {
      env.consts.get(addr).map(|lc| lc.value().raw_bytes().len())
    })
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
  let label = ixe
    .map(|p| p.display().to_string())
    .unwrap_or_else(|| "<empty env>".to_string());
  let env_bytes = load_env_bytes(ixe);
  let env =
    IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");
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

/// One stored leaf proof: the blob plus the claim preimages behind its
/// committed roots — the certified target set (subject) and the assumption
/// set, both sorted + deduped. The preimages are exactly what mode-1
/// aggregation needs as discharge witness, so a stored proof folds like any
/// other child: verified in-circuit, never trusted.
struct StoredProof {
  blob: Vec<u8>,
  subjects: Vec<ix_common::address::Address>,
  assumptions: Vec<ix_common::address::Address>,
}

/// Append a leaf proof to the on-disk store: `proofs/<n>.proof` holds the
/// blob, `<n>.cover` the packed certified target addresses, `<n>.asm` the
/// packed assumption addresses. The proofs directory is the store's single
/// source of truth — the covered set is derived from the `.cover` files.
fn append_proof(
  dir: &std::path::Path,
  proof: &[u8],
  covered: &[ix_common::address::Address],
  assumptions: &[ix_common::address::Address],
) -> Result<()> {
  use ix_common::address::Address;
  let pdir = dir.join("proofs");
  fs::create_dir_all(&pdir)?;
  let idx = (0..)
    .find(|n| !pdir.join(format!("{n}.proof")).exists())
    .expect("free proof index");
  fs::write(pdir.join(format!("{idx}.proof")), proof)?;
  fs::write(pdir.join(format!("{idx}.cover")), Address::pack(covered))?;
  fs::write(pdir.join(format!("{idx}.asm")), Address::pack(assumptions))?;
  Ok(())
}

/// Load the proof store. Entries missing the `.asm` witness file (written by
/// a pre-discharge host) are skipped with a note — without the assumption
/// preimages they cannot be folded as mode-1 children.
fn load_proof_index(dir: &std::path::Path) -> Vec<StoredProof> {
  use ix_common::address::Address;
  let pdir = dir.join("proofs");
  let mut out = Vec::new();
  for idx in 0.. {
    let pf = pdir.join(format!("{idx}.proof"));
    let Ok(blob) = fs::read(&pf) else { break };
    let Ok(cov) = fs::read(pdir.join(format!("{idx}.cover"))) else { break };
    let Ok(asm) = fs::read(pdir.join(format!("{idx}.asm"))) else {
      println!(
        "  store: skipping {idx}.proof (no .asm witness; re-prove to refresh)"
      );
      continue;
    };
    let mut subjects: Vec<Address> = Address::unpack(&cov).collect();
    subjects.sort_unstable();
    subjects.dedup();
    let mut assumptions: Vec<Address> = Address::unpack(&asm).collect();
    assumptions.sort_unstable();
    assumptions.dedup();
    out.push(StoredProof { blob, subjects, assumptions });
  }
  out
}

/// Build the 3-slice leaf-guest stdin: range + env bytes + reuse check-list.
///
/// `check_list` is a packed list of primary addresses (`Address::pack`) to
/// check; empty means "range mode" (use `[start,end)`). A non-empty list puts
/// the guest in reuse mode, checking only those work items.
fn leaf_stdin(
  start: u32,
  end: u32,
  env_bytes: &[u8],
  check_list: &[u8],
) -> ZiskStdin {
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
/// Build the agg guest's stdin. `witness = None` selects mode 0 (legacy join
/// fold). `witness = Some(per-child (subject set, assumption set))` selects
/// mode 1 (set discharge): the guest verifies each list's canonical root
/// against the child's committed publics, then discharges assumptions proven
/// by sibling subjects. Witness order must match `proofs` order.
fn agg_stdin(
  allowed_vks: &[Vec<u8>],
  proofs: &[Vec<u8>],
  witness: Option<&[(Vec<u8>, Vec<u8>)]>,
) -> ZiskStdin {
  let stdin = ZiskStdin::new();
  stdin.write(&u32::from(witness.is_some())); // mode
  stdin.write(&(allowed_vks.len() as u32));
  for vk in allowed_vks {
    stdin.write(vk);
  }
  stdin.write(&(proofs.len() as u32));
  for bytes in proofs {
    stdin.write(bytes);
  }
  if let Some(w) = witness {
    assert_eq!(w.len(), proofs.len(), "witness/proof count mismatch");
    for (s_blob, a_blob) in w {
      stdin.write(s_blob);
      stdin.write(a_blob);
    }
  }
  stdin
}

/// Mirror of the leaf guest's assumption rule (`zisk/guest/src/main.rs`): the
/// direct `Constant.refs` of every checked target that are neither in the
/// checked set nor data blobs — the constants the leaf *assumes* well-typed.
/// Computed against the full env; the guest computes it against the injected
/// sub-env, whose constants are byte-identical, so the sets agree. Returned
/// sorted + deduped (a set; `merkle_root_canonical` is dedup-invariant).
fn leaf_assumptions(
  env: &IxonEnv,
  targets: &[ix_common::address::Address],
) -> Vec<ix_common::address::Address> {
  let mut checked = targets.to_vec();
  checked.sort_unstable();
  checked.dedup();
  let mut out = Vec::new();
  for t in targets {
    if let Some(c) = env.get_const(t) {
      for r in &c.refs {
        if checked.binary_search(r).is_err() && env.get_blob(r).is_none() {
          out.push(r.clone());
        }
      }
    }
  }
  out.sort_unstable();
  out.dedup();
  out
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
  let leaves: Vec<Address> = cover
    .iter()
    .map(|b| Address::from_slice(b).expect("cover address"))
    .collect();
  ixon::merkle::merkle_root_canonical(&leaves)
    .unwrap_or_else(ixon::merkle::zero_address)
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
fn check_input_coherence(
  label: &str,
  publics: &[ShardPublics],
  total: u32,
) -> Result<u32> {
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

fn build_client(gpu: bool, asm: bool) -> Result<EmbeddedClient> {
  // Executor choice. The default is the Assembly executor (`asm = true`,
  // i.e. no `--emulator`): it is markedly faster at trace generation and is
  // the prerequisite for the hints stream. It historically broke under our
  // multi-program flow — calling `client.setup` for a second program
  // re-initializes the ASM microservices and leaves the first program's ROM
  // histogram empty, so a subsequent prove of the first program panics at
  // `state-machines/rom/src/rom.rs:178` ("index out of bounds: len 0").
  //
  // The fix is ordering-based: never set up the agg program *before* the
  // leaves are proven. The `--shard-plan` path already does this
  // (`run_shard_plan` sets up AGG only after the leaf loop), and the upfront
  // agg setup in `main` is gated to the Emulator (`--emulator`), with Assembly
  // deferring it to after the leaf loop. Validated: a 2-shard multi-program
  // prove that previously panicked now completes and verifies.
  //
  // `minimal_memory()` deliberately NOT enabled — per upstream CLI
  // docs ("Reduce memory footprint during proving at the cost of
  // speed"). We have ~94 GB of free GPU memory, so the speed
  // trade-off is the wrong direction for this hardware.
  // Zisk's default embedded opts (witness cap 10).
  let opts = EmbeddedOpts::default();
  let mut builder: EmbeddedClientBuilder =
    ProverClient::embedded().with_embedded_opts(opts);
  if asm {
    builder = builder.assembly();
  }
  if gpu {
    builder = builder.gpu();
  }
  builder.build()
}

/// Check a single constant chosen by Lean NAME (one iteration of `--consts`).
/// Resolve name → constant address via the env's `named` metadata, map to its
/// ingress block's work item, and ship its closure sub-env. By default the
/// check-list is the ENTIRE closure (full-closure typecheck); with
/// `--skip-deps` it is just the subject (deps trusted). Honors `--dump-input`
/// (write stdin for ziskemu), `--execute` (cycles), and plain prove (single
/// leaf, subject-bound + verified). No aggregation — it's one leaf.
async fn run_constant(
  client: &EmbeddedClient,
  plan: &InputPlan,
  name: &str,
  args: &Args,
) -> Result<()> {
  use ix_common::address::Address;

  // Resolve the Lean name → constant address via the full env's metadata
  // (`get_anon` discards `named`, so load the full env just for the lookup).
  let full =
    IxonEnv::get(&mut &plan.env_bytes[..]).expect("invalid Ixon environment");
  let target: Address = full
    .named
    .iter()
    .find(|e| e.key().to_string() == name)
    .map(|e| e.value().addr.clone())
    .ok_or_else(|| {
      anyhow::anyhow!("no constant named {name:?} in {}", plan.label)
    })?;

  // The name's work item is the one whose ingress block owns it — works for a
  // standalone const (block == itself) and a member of a Muts block (block ==
  // the mutual container, checked atomically).
  let env = IxonEnv::get_anon(&mut &plan.env_bytes[..])
    .expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");
  let block = block_of_addr(&env, &target);
  let item = work
    .iter()
    .find(|w| work_block_addr(&env, w) == block)
    .ok_or_else(|| {
      anyhow::anyhow!(
        "{name:?} resolved to block {}… but no work item covers it",
        &block.hex()[..16]
      )
    })?;

  // Closure sub-env (the named constant's transitive deps), faulted in lazily
  // by the guest.
  let roots: Vec<Address> = item.proven_targets();
  let sub_env = build_sub_env(&env, &roots).map_err(|e| anyhow::anyhow!(e))?;

  // Check-list: full-closure by default (every work item in the sub-env is
  // re-checked, deps included), or subject-only under `--skip-deps` (just the
  // named constant's primary; deps trusted).
  let (check_list, cover, checked) = if args.skip_deps {
    let cover: Vec<[u8; 32]> = roots.iter().map(|a| *a.as_bytes()).collect();
    (Address::pack(&[item.primary().clone()]), cover, 1usize)
  } else {
    let env_sub =
      IxonEnv::get_anon(&mut &sub_env[..]).expect("invalid sub-env");
    let work_sub = build_anon_work(&env_sub).expect("build_anon_work sub");
    let primaries: Vec<Address> =
      work_sub.iter().map(|w| w.primary().clone()).collect();
    let cover: Vec<[u8; 32]> = work_sub
      .iter()
      .flat_map(|w| w.proven_targets())
      .map(|a| *a.as_bytes())
      .collect();
    let n = work_sub.len();
    (Address::pack(&primaries), cover, n)
  };
  println!(
    "constant {name}{}: block {}… ({} work item(s) checked, {} target const(s)); closure sub-env {} vs whole env {} ({:.0}%)",
    if args.skip_deps { " [skip-deps]" } else { " [full-closure]" },
    &block.hex()[..16],
    checked,
    roots.len(),
    sub_env.len().human_count_bytes(),
    plan.env_bytes.len().human_count_bytes(),
    100.0 * sub_env.len() as f64 / plan.env_bytes.len().max(1) as f64,
  );

  // ---- Dump mode: write stdin for `ziskemu`/`cargo-zisk run -i`. ----
  if let Some(dump) = &args.dump_input {
    let stdin = leaf_stdin(0, 0, &sub_env, &check_list);
    stdin
      .save(dump)
      .map_err(|e| anyhow::anyhow!("save {}: {e}", dump.display()))?;
    println!("dumped input → {}", dump.display());
    return Ok(());
  }

  let stdin = leaf_stdin(0, 0, &sub_env, &check_list);

  // ---- Execute mode: cycles only, no proof. ----
  if args.execute {
    let t0 = Instant::now();
    let result = client.execute(&SHARD_PROGRAM, stdin).run()?.await?;
    let execute_secs = t0.elapsed().as_secs_f64();
    tracing_texray::json_sink::record_manual("zisk/execute", execute_secs);
    let mut buf = [0u8; SHARD_PUBLICS_LEN];
    result.get_public_values_slice(&mut buf);
    let publics = ShardPublics::decode(&buf);
    let cycles = result.get_execution_steps();
    println!("cycles: {cycles}, failures: {}", publics.failures);
    if let Some(path) = &args.json {
      let tput =
        if execute_secs > 0.0 { cycles as f64 / execute_secs } else { 0.0 };
      let status =
        if publics.failures > 0 { Status::Rejected } else { Status::Ok };
      write_row(
        path,
        name,
        status,
        serde_json::json!({
          "cycles": cycles,
          "execute-time": (execute_secs * 1e6).round() / 1e6,
          "throughput": tput.round(),
          // The execute phase's RSS high-water — the only phase this cell
          // has, so the name stays bare (phases separate at the testbed).
          "peak-rss": peak_rss_bytes(),
        }),
      )?;
    }
    reject_failures(&publics, &format!("constant {name}"))?;
    return Ok(());
  }

  // ---- Prove mode: single leaf, bind subject to the env, verify. ----
  let result = client.prove(&SHARD_PROGRAM, stdin).run()?.await?;
  let mut buf = [0u8; SHARD_PUBLICS_LEN];
  result.get_public_values_slice(&mut buf);
  let publics = ShardPublics::decode(&buf);
  let leaf_ms = result.get_proving_time();
  tracing_texray::json_sink::record_manual(
    "zisk/prove",
    leaf_ms as f64 / 1000.0,
  );
  let expected = subject_of_cover(&cover);
  if *expected.as_bytes() != publics.subject_root {
    bail!(
      "committed subject {}… ≠ env-derived {}… — guest certified a different set",
      Address::from_slice(&publics.subject_root)
        .map(|a| a.hex()[..16].to_string())
        .unwrap_or_default(),
      &expected.hex()[..16],
    );
  }
  let vstart = Instant::now();
  result.verify()?;
  println!(
    "constant {name}: failures={}, prove {:.2}s ({} steps), verify {:.3}s; \
     subject bound ({}… over {} target(s))",
    publics.failures,
    leaf_ms as f64 / 1000.0,
    result.get_execution_steps(),
    vstart.elapsed().as_secs_f64(),
    &expected.hex()[..16],
    roots.len(),
  );
  if let Some(path) = &args.json {
    let status =
      if publics.failures > 0 { Status::Rejected } else { Status::Ok };
    write_row(
      path,
      name,
      status,
      serde_json::json!({
        "prove-time": (leaf_ms as f64).round() / 1000.0,
        "steps": result.get_execution_steps(),
        "peak-rss": peak_rss_bytes(),
      }),
    )?;
  }
  // Proof still verifies on rejection — the guest certifies "checked, with
  // failures" — but a rejected constant must land as a red row, not a metric.
  reject_failures(&publics, &format!("constant {name}"))?;
  Ok(())
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
  covered_by_store: &std::collections::HashSet<[u8; 32]>,
) -> Result<Vec<Vec<&'a AnonWorkItem>>> {
  use std::collections::HashMap;

  use ix_common::address::Address;

  let mut by_primary: HashMap<Address, usize> =
    HashMap::with_capacity(work.len());
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
  // Every work item must be either assigned to a manifest shard or fully
  // covered by the proof store (a store-aware manifest deliberately omits
  // covered work; the prover resolves it by folding the store's proofs).
  let unaccounted = work
    .iter()
    .enumerate()
    .filter(|(i, w)| {
      !assigned[*i]
        && !w
          .proven_targets()
          .iter()
          .all(|t| covered_by_store.contains(t.as_bytes()))
    })
    .count();
  if unaccounted > 0 {
    bail!(
      "{unaccounted} of {} work items are neither in the manifest nor covered \
       by the proof store — the manifest was built for a different or stale \
       env (or a different store); re-run the planner on this .ixe",
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

/// Host mirror of the agg guest's mode-1 discharge: union the children's
/// subject and assumption sets, then drop every assumption proven by the union
/// subject. Returns `(union_subjects, outstanding_assumptions)`, both sorted
/// and deduped. Must stay in lockstep with the guest (`zisk/agg-guest`).
fn discharge(
  subjects: &[&[ix_common::address::Address]],
  assumptions: &[&[ix_common::address::Address]],
) -> (Vec<ix_common::address::Address>, Vec<ix_common::address::Address>) {
  let mut union_s: Vec<_> = subjects.concat();
  let mut union_a: Vec<_> = assumptions.concat();
  union_s.sort_unstable();
  union_s.dedup();
  union_a.sort_unstable();
  union_a.dedup();
  let outstanding =
    union_a.into_iter().filter(|a| union_s.binary_search(a).is_err()).collect();
  (union_s, outstanding)
}

/// Prove a `.ixes` manifest partition: one closure-injected leaf proof per
/// (non-empty) manifest shard, folded along the manifest's bisection tree into
/// a single aggregate whose committed subject is bound to the env. Honors
/// `--execute` (per-shard VM cycles) and `--only-shard k` (prove just shard k).
/// The agg program is set up lazily, only when more than one leaf is produced.
/// Manifests without a bisection tree (written before it existed) are
/// rejected when aggregation is needed — regenerate with the current planner.
async fn run_shard_plan(
  client: &EmbeddedClient,
  plan: &InputPlan,
  manifest_path: &std::path::Path,
  args: &Args,
) -> Result<()> {
  use std::collections::HashSet;

  use ix_common::address::Address;
  use ix_kernel::shard::{FoldOp, ShardManifest, agg_plan};

  let env = IxonEnv::get_anon(&mut &plan.env_bytes[..])
    .expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");

  let mbytes = fs::read(manifest_path).map_err(|e| {
    anyhow::anyhow!("read manifest {}: {e}", manifest_path.display())
  })?;
  let manifest = ShardManifest::from_bytes(&mbytes).map_err(|e| {
    anyhow::anyhow!("parse manifest {}: {e}", manifest_path.display())
  })?;

  // ---- Cross-run reuse store (loaded before grouping: a store-aware manifest
  // omits covered work, which grouping accepts only when the store accounts
  // for it). ----
  let write_store = args.store_dir.is_some() && !args.no_reuse;
  let stored: Vec<StoredProof> = match (&args.store_dir, args.no_reuse) {
    (Some(dir), false) => load_proof_index(dir),
    _ => Vec::new(),
  };
  let covered_by_store: HashSet<[u8; 32]> = stored
    .iter()
    .flat_map(|p| p.subjects.iter().map(|a| *a.as_bytes()))
    .collect();

  let groups =
    group_work_by_manifest(&env, &work, &manifest, &covered_by_store)?;

  // Select (manifest-index, items) to prove: every non-empty shard, or just the
  // one named by --only-shard.
  let selected: Vec<(usize, &Vec<&AnonWorkItem>)> = match args.only_shard {
    Some(k) => {
      if k == 0 || k > groups.len() {
        bail!(
          "--only-shard {k} out of range; manifest has {} shard(s)",
          groups.len()
        );
      }
      vec![(k - 1, &groups[k - 1])]
    },
    None => groups.iter().enumerate().filter(|(_, g)| !g.is_empty()).collect(),
  };
  if selected.iter().all(|(_, g)| g.is_empty()) {
    bail!("nothing to prove: selected manifest shard(s) are empty");
  }

  // ---- Cross-run reuse: prove only what the store doesn't cover. ----
  // A manifest shard is reused iff EVERY target it would certify is covered by
  // stored proofs; partially-covered shards re-prove whole (the shard is the
  // proof unit). Work the manifest omits entirely (store-aware planning) is
  // covered by construction. Everything this run must certify but won't prove
  // — reused shards plus unmanifested work — is resolved by folding the
  // covering stored proofs, which the agg guest verifies in-circuit.
  let shard_targets = |g: &[&AnonWorkItem]| -> Vec<Address> {
    g.iter().flat_map(|w| w.proven_targets()).collect()
  };
  let (novel, reused): (Vec<_>, Vec<_>) =
    selected.iter().copied().partition(|(_, g)| {
      !shard_targets(g).iter().all(|t| covered_by_store.contains(t.as_bytes()))
    });
  // Targets this run answers for: just the selected shard under --only-shard
  // (a smoke test), otherwise the whole env's work set.
  let needed: HashSet<[u8; 32]> = if args.only_shard.is_some() {
    selected
      .iter()
      .flat_map(|(_, g)| shard_targets(g))
      .map(|a| *a.as_bytes())
      .collect()
  } else {
    work
      .iter()
      .flat_map(|w| w.proven_targets())
      .map(|a| *a.as_bytes())
      .collect()
  };
  let novel_targets: HashSet<[u8; 32]> = novel
    .iter()
    .flat_map(|(_, g)| shard_targets(g))
    .map(|a| *a.as_bytes())
    .collect();
  // Seed: stored proofs contributing a needed target the novel shards won't
  // certify. Fixpoint: an included proof's own assumptions may be covered by
  // OTHER stored proofs (from the run that proved it) — fold those too, so a
  // closed store yields an unconditional claim even cross-env. Terminates:
  // every round includes at least one more proof or stops.
  let mut included = vec![false; stored.len()];
  for (i, p) in stored.iter().enumerate() {
    included[i] = p.subjects.iter().any(|a| {
      needed.contains(a.as_bytes()) && !novel_targets.contains(a.as_bytes())
    });
  }
  loop {
    let included_subjects: HashSet<[u8; 32]> = stored
      .iter()
      .zip(&included)
      .filter(|(_, inc)| **inc)
      .flat_map(|(p, _)| p.subjects.iter().map(|a| *a.as_bytes()))
      .collect();
    let open: HashSet<[u8; 32]> = stored
      .iter()
      .zip(&included)
      .filter(|(_, inc)| **inc)
      .flat_map(|(p, _)| p.assumptions.iter().map(|a| *a.as_bytes()))
      .filter(|a| !novel_targets.contains(a) && !included_subjects.contains(a))
      .collect();
    let mut grew = false;
    for (i, p) in stored.iter().enumerate() {
      if !included[i] && p.subjects.iter().any(|s| open.contains(s.as_bytes()))
      {
        included[i] = true;
        grew = true;
      }
    }
    if !grew {
      break;
    }
  }
  let covering: Vec<&StoredProof> = stored
    .iter()
    .zip(&included)
    .filter(|(_, inc)| **inc)
    .map(|(p, _)| p)
    .collect();

  println!(
    "shard-plan {}: {} work items, manifest {} shard(s), cross-ingress total {}; \
     proving {} leaf(s), {} reused via {} stored proof(s)",
    plan.label,
    work.len(),
    manifest.num_shards,
    (manifest.total_cross_ingress as usize).human_count_bytes(),
    novel.len(),
    reused.len(),
    covering.len(),
  );
  for &(idx, g) in &selected {
    let si = &manifest.shards[idx];
    let status =
      if novel.iter().any(|&(i, _)| i == idx) { "novel " } else { "reused" };
    println!(
      "  shard {idx:>3} [{status}]: {:>5} work items  heartbeats={}  own={}  cross_ingress={}",
      g.len(),
      si.heartbeats,
      (si.own_size as usize).human_count_bytes(),
      (si.cross_ingress as usize).human_count_bytes(),
    );
  }

  // Per-shard guest input: explicit primary check-list + closure-injected
  // sub-env (ship only this shard's dependency closure, never the whole env),
  // plus the cover (target addresses) for the host-side claim bindings.
  type LeafInputs = (
    Vec<u8>,       // packed primary check-list
    Vec<u8>,       // serialized closure sub-env
    Vec<[u8; 32]>, // cover: certified target addresses
  );
  let build_inputs = |g: &[&AnonWorkItem]| -> Result<LeafInputs> {
    let primaries: Vec<Address> =
      g.iter().map(|w| w.primary().clone()).collect();
    let check_list = Address::pack(&primaries);
    let roots: Vec<Address> =
      g.iter().flat_map(|w| w.proven_targets()).collect();
    let cover: Vec<[u8; 32]> = roots.iter().map(|a| *a.as_bytes()).collect();
    let sub_env =
      build_sub_env(&env, &roots).map_err(|e| anyhow::anyhow!(e))?;
    Ok((check_list, sub_env, cover))
  };

  // ---- Dump mode: write the selected shard's guest stdin to a file (for
  // standalone profiling with `ziskemu`/`cargo-zisk run -i`), then exit. ----
  if let Some(dump) = &args.dump_input {
    let (idx, g) = selected.first().expect("a selected shard");
    let (check_list, sub_env, _cover) = build_inputs(g)?;
    let stdin = leaf_stdin(0, 0, &sub_env, &check_list);
    stdin
      .save(dump)
      .map_err(|e| anyhow::anyhow!("save {}: {e}", dump.display()))?;
    println!(
      "dumped shard {idx} input ({} work items, sub-env {}) → {}",
      g.len(),
      sub_env.len().human_count_bytes(),
      dump.display(),
    );
    return Ok(());
  }

  // ---- Execute mode: run each novel shard in the VM for cycles (no proof);
  // store-covered shards have nothing to execute. With `--json`, one
  // env-level row (keyed by `--json-name`, default the manifest stem)
  // carries the totals plus a per-shard cycles breakdown under
  // `shard-cycles` — the CI benchmark's per-shard tracking. ----
  if args.execute {
    let t0 = Instant::now();
    let mut total_steps = 0u64;
    let mut max_shard_cycles = 0u64;
    let mut max_shard_peak: Option<u64> = None;
    let mut shard_cycles = serde_json::Map::new();
    let mut shard_time = serde_json::Map::new();
    let mut shard_peak_rss = serde_json::Map::new();
    // Fail FAST on a rejected shard (skip the rest), but still write the
    // row — with the shards measured so far — as `status: rejected`.
    let mut rejection: Option<Rejection> = None;
    for &(idx, g) in &novel {
      let (check_list, sub_env, _cover) = build_inputs(g)?;
      let stdin = leaf_stdin(0, 0, &sub_env, &check_list);
      // Windowed RAM high-water: reset before each shard so the per-shard
      // peaks are independent; the env row's peak-rss is their max.
      tracing_texray::rss_sampler::reset_peak_tree_rss();
      let result = client.execute(&SHARD_PROGRAM, stdin).run()?.await?;
      let mut buf = [0u8; SHARD_PUBLICS_LEN];
      result.get_public_values_slice(&mut buf);
      let publics = ShardPublics::decode(&buf);
      let cycles = result.get_execution_steps();
      let exec_secs = result.get_execution_time() as f64 / 1000.0;
      let peak = peak_rss_bytes();
      total_steps += cycles;
      max_shard_cycles = max_shard_cycles.max(cycles);
      max_shard_peak = max_shard_peak.max(peak);
      // 1-based zero-padded keys: matches --only-shard's numbering and keeps
      // the flattened bencher measure list (`shard-cycles:<k>`, …) sorted.
      let key = format!("{:02}", idx + 1);
      shard_cycles.insert(key.clone(), serde_json::json!(cycles));
      shard_time.insert(key.clone(), serde_json::json!(exec_secs));
      if let Some(p) = peak {
        shard_peak_rss.insert(key, serde_json::json!(p));
      }
      println!(
        "  [shard {idx}] {} work items, failures={}, cycles={cycles}, \
         {exec_secs:.1}s, peak {}",
        g.len(),
        publics.failures,
        peak.map_or("?".to_string(), |p| format!(
          "{:.2} GiB",
          p as f64 / (1 << 30) as f64
        )),
      );
      if publics.failures > 0 {
        rejection = Some(Rejection {
          failures: publics.failures.into(),
          ctx: format!("shard {idx}"),
        });
        break;
      }
    }
    let execute_secs = t0.elapsed().as_secs_f64();
    tracing_texray::json_sink::record_manual("zisk/execute", execute_secs);
    println!(
      "total cycles: {total_steps}, failures: {}",
      rejection.as_ref().map_or(0, |r| r.failures)
    );
    if let Some(path) = &args.json {
      let name = args.json_name.clone().unwrap_or_else(|| {
        manifest_path
          .file_stem()
          .map(|s| s.to_string_lossy().into_owned())
          .unwrap_or_else(|| "env".to_string())
      });
      let tput = if execute_secs > 0.0 {
        total_steps as f64 / execute_secs
      } else {
        0.0
      };
      let status =
        if rejection.is_some() { Status::Rejected } else { Status::Ok };
      write_row(
        path,
        &name,
        status,
        serde_json::json!({
          "cycles": total_steps,
          "shards": novel.len(),
          "max-shard-cycles": max_shard_cycles,
          "execute-time": (execute_secs * 1e6).round() / 1e6,
          "throughput": tput.round(),
          // Max over the per-shard windows == the run's execution-phase
          // high-water (setup RAM excluded by the resets above).
          "peak-rss": max_shard_peak,
          "shard-cycles": shard_cycles,
          "shard-time": shard_time,
          "shard-peak-rss": shard_peak_rss,
        }),
      )?;
    }
    if let Some(r) = rejection {
      return Err(r.into());
    }
    return Ok(());
  }

  // ---- Prove mode: one closure-injected leaf per shard. ----
  let mut leaf_proofs: Vec<Vec<u8>> = Vec::with_capacity(selected.len());
  // Per-leaf claim preimages (sorted, deduped): the certified target set and
  // the assumption set behind the leaf's committed roots. Supplied to the agg
  // guest as discharge witness and mirrored host-side for the final binding.
  let mut leaf_subject_sets: Vec<Vec<Address>> =
    Vec::with_capacity(selected.len());
  let mut leaf_assumption_sets: Vec<Vec<Address>> =
    Vec::with_capacity(selected.len());
  // Shard id (manifest index == bisection-tree leaf id) of each proven leaf, so
  // the aggregation can fold along the manifest's bisection tree.
  let mut leaf_ids: Vec<u32> = Vec::with_capacity(selected.len());
  let mut covered_union: HashSet<[u8; 32]> = HashSet::default();
  let mut total_leaf_ms = 0u64;
  let mut total_failures = 0u32;
  let mut last_leaf_result = None;
  let leaf_start = Instant::now();
  for &(idx, g) in &novel {
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
    println!(
      "    failures={}, prove {:.2}s, {} steps",
      publics.failures,
      leaf_ms as f64 / 1000.0,
      result.get_execution_steps(),
    );
    reject_failures(&publics, &format!("shard {idx}"))?;
    // Bind each leaf: its committed subject must equal the env-derived merkle
    // root over the constants it certified. A guest that proved a different set
    // than the manifest assigned would commit a different root and fail here.
    let mut targets: Vec<Address> = cover
      .iter()
      .map(|b| Address::from_slice(b).expect("cover address"))
      .collect();
    let expected = ixon::merkle::merkle_root_canonical(&targets)
      .unwrap_or_else(ixon::merkle::zero_address);
    if *expected.as_bytes() != publics.subject_root {
      bail!(
        "shard {idx}: committed subject {}… ≠ env-derived {}… — guest certified a \
         different set than the manifest assigned",
        Address::from_slice(&publics.subject_root)
          .map(|a| a.hex()[..16].to_string())
          .unwrap_or_default(),
        &expected.hex()[..16],
      );
    }
    // Record the leaf's claim preimages and check the assumptions mirror NOW
    // (a divergence would otherwise only surface as a witness-root panic deep
    // inside the agg guest, after the leaf proving time is already spent).
    let asm_set = leaf_assumptions(&env, &targets);
    let asm_expected = ixon::merkle::merkle_root_canonical(&asm_set)
      .unwrap_or_else(ixon::merkle::zero_address);
    if *asm_expected.as_bytes() != publics.assumptions_root {
      bail!(
        "shard {idx}: committed assumptions root ≠ host mirror — the host's \
         leaf_assumptions rule diverges from the guest's",
      );
    }
    targets.sort_unstable();
    targets.dedup();
    // Bank the clean shard immediately: an interrupted run resumes with this
    // shard reused instead of re-proven.
    if write_store && publics.failures == 0 {
      append_proof(
        args.store_dir.as_ref().expect("write_store implies store_dir"),
        &blob,
        &targets,
        &asm_set,
      )?;
    }
    leaf_subject_sets.push(targets);
    leaf_assumption_sets.push(asm_set);
    covered_union.extend(cover.iter().copied());
    leaf_proofs.push(blob);
    leaf_ids.push(idx as u32);
    last_leaf_result = Some(result);
  }
  let leaf_wall = leaf_start.elapsed();

  // Full-env coverage: the union of all folded children — novel leaves plus
  // covering stored proofs — must cover every work item's targets (skipped
  // under --only-shard, which proves a single shard).
  for p in &covering {
    covered_union.extend(p.subjects.iter().map(|a| *a.as_bytes()));
  }
  if args.only_shard.is_none() {
    let grand: HashSet<[u8; 32]> = work
      .iter()
      .flat_map(|w| w.proven_targets())
      .map(|a| *a.as_bytes())
      .collect();
    let miss = grand.iter().filter(|t| !covered_union.contains(*t)).count();
    if miss > 0 {
      bail!(
        "coverage gap: {miss} env target(s) not covered by any folded proof"
      );
    }
  }

  // ---- Aggregate: fold all children — novel leaves along the manifest's
  // bisection tree (pruned to the shards proven this run), covering stored
  // proofs as extra children of a synthesized tail fold — into one verified
  // root. Mode-1 commitments are canonical SETS, so the fold shape never
  // changes the final claim; the tree only places discharge at the lowest
  // common ancestors. Stored proofs MUST pass through at least one agg call:
  // that in-circuit verification is what makes reuse trustless. ----
  let arity = (args.agg_arity as usize).max(2);
  let (final_size, agg_ms, verify_ms, root_committed, expected_final) =
    if leaf_proofs.len() == 1 && covering.is_empty() {
      let leaf = last_leaf_result.expect("single leaf");
      let final_size = leaf.get_proof_bytes()?.len();
      let vstart = Instant::now();
      leaf.verify()?;
      // Per-leaf binding above already pinned the subject; fold of 1 = itself.
      let subject = ixon::merkle::merkle_root_canonical(&leaf_subject_sets[0])
        .unwrap_or_else(ixon::merkle::zero_address);
      (
        final_size,
        0u64,
        vstart.elapsed().as_millis() as u64,
        subject.clone(),
        subject,
      )
    } else {
      // Slot-producing op list, in post order (children precede parents).
      // Each op yields one slot: the node's proof plus its claim preimages —
      // the certified subject SET and outstanding assumption SET (sorted +
      // deduped) — feeding the next level's discharge witness + host mirror.
      enum Op {
        NovelLeaf(u32),
        Stored(usize),
        Agg(Vec<usize>),
      }
      let mut ops: Vec<Op> = Vec::new();
      match leaf_ids.len() {
        0 => {},
        1 => ops.push(Op::NovelLeaf(leaf_ids[0])),
        _ => {
          let Some(full_tree) = &manifest.tree else {
            bail!(
              "manifest has no bisection tree (written by an older planner) — \
               regenerate the .ixes with the current `shard_plan`"
            );
          };
          let present: HashSet<u32> = leaf_ids.iter().copied().collect();
          let tree = full_tree
            .prune(&|id| present.contains(&id))
            .expect("≥1 proven leaf is in the tree");
          for op in agg_plan(&tree, arity) {
            ops.push(match op {
              FoldOp::Leaf(id) => Op::NovelLeaf(id),
              FoldOp::Agg(c) => Op::Agg(c),
            });
          }
        },
      }
      // The forest's roots so far (slot indices): the novel fold's root (if
      // any) plus one slot per covering stored proof.
      let mut current: Vec<usize> =
        if ops.is_empty() { Vec::new() } else { vec![ops.len() - 1] };
      for k in 0..covering.len() {
        ops.push(Op::Stored(k));
        current.push(ops.len() - 1);
      }
      // Tail fold: reduce the forest to ONE root, `arity` children per agg.
      // Runs at least one agg whenever stored proofs are present (even a
      // single stored proof folds through an agg-of-1 — nothing else this run
      // verifies it).
      let mut planned_aggs =
        ops.iter().filter(|o| matches!(o, Op::Agg(_))).count();
      while current.len() > 1 || planned_aggs == 0 {
        let mut next = Vec::with_capacity(current.len().div_ceil(arity));
        for chunk in current.chunks(arity) {
          ops.push(Op::Agg(chunk.to_vec()));
          planned_aggs += 1;
          next.push(ops.len() - 1);
        }
        current = next;
      }

      client.setup(&AGG_PROGRAM).run()?.await?;
      let id_to_idx: std::collections::HashMap<u32, usize> =
        leaf_ids.iter().copied().enumerate().map(|(i, id)| (id, i)).collect();
      println!(
        "  [agg] folding {} novel leaf/leaves + {} stored proof(s) (arity {arity}, {planned_aggs} agg node(s))",
        leaf_proofs.len(),
        covering.len(),
      );
      let mut slot_proof: Vec<Vec<u8>> = Vec::with_capacity(ops.len());
      let mut slot_subj: Vec<Vec<Address>> = Vec::with_capacity(ops.len());
      let mut slot_asm: Vec<Vec<Address>> = Vec::with_capacity(ops.len());
      let mut total_agg_ms = 0u64;
      let mut root_result: Option<_> = None;
      for op in &ops {
        match op {
          Op::NovelLeaf(id) => {
            let i = id_to_idx[id]; // present by construction (tree pruned)
            slot_proof.push(leaf_proofs[i].clone());
            slot_subj.push(leaf_subject_sets[i].clone());
            slot_asm.push(leaf_assumption_sets[i].clone());
          },
          Op::Stored(k) => {
            let p = covering[*k];
            slot_proof.push(p.blob.clone());
            slot_subj.push(p.subjects.clone());
            slot_asm.push(p.assumptions.clone());
          },
          Op::Agg(children) => {
            let proofs: Vec<Vec<u8>> =
              children.iter().map(|&c| slot_proof[c].clone()).collect();
            // Mode-1 witness: each child's subject/assumption preimages, in
            // the same order as `proofs`. The guest verifies them against the
            // children's committed roots, so they are untrusted inputs here.
            let witness: Vec<(Vec<u8>, Vec<u8>)> = children
              .iter()
              .map(|&c| {
                (Address::pack(&slot_subj[c]), Address::pack(&slot_asm[c]))
              })
              .collect();
            let allowed = distinct_vks(&proofs);
            let astart = Instant::now();
            let result = client
              .prove(&AGG_PROGRAM, agg_stdin(&allowed, &proofs, Some(&witness)))
              .run()?
              .await?;
            total_agg_ms += result.get_proving_time();
            let (union_s, outstanding) = discharge(
              &children
                .iter()
                .map(|&c| slot_subj[c].as_slice())
                .collect::<Vec<_>>(),
              &children
                .iter()
                .map(|&c| slot_asm[c].as_slice())
                .collect::<Vec<_>>(),
            );
            println!(
              "    agg {} → prove {:.2}s (wall {:.2}s); subjects {} assumptions {} → outstanding {}",
              proofs.len(),
              result.get_proving_time() as f64 / 1000.0,
              astart.elapsed().as_secs_f64(),
              union_s.len(),
              children.iter().map(|&c| slot_asm[c].len()).sum::<usize>(),
              outstanding.len(),
            );
            slot_proof.push(result.get_proof_bytes()?);
            slot_subj.push(union_s);
            slot_asm.push(outstanding);
            root_result = Some(result);
          },
        }
      }
      let root = root_result.expect("tree fold produced a root agg");
      let final_size = root.get_proof_bytes()?.len();
      let mut fbuf = [0u8; SHARD_PUBLICS_LEN];
      root.get_public_values_slice(&mut fbuf);
      let fpub = ShardPublics::decode(&fbuf);
      let vstart = Instant::now();
      root.verify()?;
      let committed_addr = Address::from_slice(&fpub.subject_root)
        .unwrap_or_else(|_| ixon::merkle::zero_address());
      // Root subject = canonical merkle root over the UNION of certified
      // targets — a set commitment, independent of fold shape.
      let root_subj = slot_subj.last().expect("root subject set");
      let expected = ixon::merkle::merkle_root_canonical(root_subj)
        .unwrap_or_else(ixon::merkle::zero_address);
      // Bind the root's outstanding-assumptions root to the host mirror, and
      // report closure: an empty outstanding set means the aggregate claim is
      // UNCONDITIONAL (every cross-shard obligation was discharged in-circuit).
      let root_asm = slot_asm.last().expect("root assumption set");
      let asm_expected = ixon::merkle::merkle_root_canonical(root_asm)
        .unwrap_or_else(ixon::merkle::zero_address);
      if *asm_expected.as_bytes() != fpub.assumptions_root {
        bail!("aggregate assumptions root ≠ host mirror — discharge diverged");
      }
      if root_asm.is_empty() {
        println!(
          "  [agg] all assumptions discharged — final claim is unconditional"
        );
      } else {
        println!(
          "  [agg] {} outstanding assumption(s) remain (refs not proven by any folded shard)",
          root_asm.len(),
        );
      }
      (
        final_size,
        total_agg_ms,
        vstart.elapsed().as_millis() as u64,
        committed_addr,
        expected,
      )
    };

  // Bind the aggregate's committed subject to the env-derived fold.
  if root_committed != expected_final {
    bail!(
      "subject-binding failed: aggregate commits {}… but the env requires {}… — \
       the folded proofs do not cover this env",
      &root_committed.hex()[..16],
      &expected_final.hex()[..16],
    );
  }

  println!(
    "shard-plan done: {} novel leaf/leaves + {} stored ({:.2}s wall, {:.2}s sum) + agg {:.2}s → final proof {}; \
     verify {:.3}s; subject bound to env ({}… over {} target(s))",
    novel.len(),
    covering.len(),
    leaf_wall.as_secs_f64(),
    total_leaf_ms as f64 / 1000.0,
    agg_ms as f64 / 1000.0,
    final_size.human_count_bytes(),
    verify_ms as f64 / 1000.0,
    &expected_final.hex()[..16],
    covered_union.len(),
  );
  if total_failures > 0 {
    return Err(
      Rejection {
        failures: total_failures.into(),
        ctx: "aggregate (proof still verifies)".to_string(),
      }
      .into(),
    );
  }
  Ok(())
}

#[tokio::main]
async fn main() -> std::process::ExitCode {
  match run().await {
    Ok(()) => std::process::ExitCode::SUCCESS,
    Err(e) => {
      eprintln!("error: {e:#}");
      if e.downcast_ref::<Rejection>().is_some() {
        // Reserved exit code: rejection rows are on disk; the caller needs
        // no log parsing to tell "kernel said no" from an infra failure.
        std::process::ExitCode::from(EXIT_REJECTED)
      } else {
        std::process::ExitCode::FAILURE
      }
    },
  }
}

async fn run() -> Result<()> {
  zisk_sdk::setup_logger(VerboseMode::Info);

  let args = Args::parse();

  // Start the process-tree RSS sampler so `peak_rss_bytes()` reflects the ASM
  // microservices' memory, and point the per-phase timing sink at the drill-down
  // file if requested. Both are independent of the SDK's global tracing logger.
  //
  // TODO(spans): the sink only receives the coarse `zisk/execute` / `zisk/prove`
  // phases we `record_manual` below. For a finer drill-down (setup, trace-gen,
  // per-microservice), install a TeXRay subscriber and examine the zisk-sdk's
  // own tracing spans — which requires composing it with the SDK's global logger
  // (`zisk_sdk::setup_logger`), currently the sole subscriber.
  tracing_texray::rss_sampler::start(std::time::Duration::from_millis(50));
  // With --texray + --json, per-phase span timings land at `<json>.spans` as
  // JSON Lines — the CI drill-down input.
  if args.texray {
    if let Some(json) = args.json.as_ref().and_then(|p| p.to_str()) {
      let _ = tracing_texray::json_sink::to_file(&format!("{json}.spans"));
    }
  }

  // Collect inputs. No `--ixe` → a single empty env (back-compat).
  let inputs: Vec<Option<PathBuf>> = if args.ixe.is_empty() {
    vec![None]
  } else {
    args.ixe.iter().cloned().map(Some).collect()
  };

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
    bail!(
      "--shard-plan requires exactly one --ixe input (the env the manifest was built for)"
    );
  }
  // Named constants (from --consts and/or --consts-file) select from one env.
  let consts = collect_consts(&args.consts, args.consts_file.as_deref())?;
  if !consts.is_empty() && inputs.len() > 1 {
    bail!("--consts/--consts-file requires exactly one --ixe input");
  }
  if consts.is_empty() && args.skip_deps {
    bail!("--skip-deps requires constants via --consts or --consts-file");
  }
  if consts.is_empty() && args.json.is_some() && args.shard_plan.is_none() {
    bail!(
      "--json requires constants via --consts/--consts-file, or --shard-plan"
    );
  }

  // ---- Plan every input up front (parse + shard). ----
  let print_plan = args.plan || args.shard_bytes.is_some();
  let mut plans: Vec<InputPlan> = Vec::with_capacity(inputs.len());
  for ixe in &inputs {
    plans.push(plan_input(
      ixe.as_ref(),
      args.shard_consts,
      args.shard_bytes,
      print_plan,
    )?);
  }

  // `--only-shard` narrows the (single) input's shard list. Skip for the
  // manifest path — there `--only-shard` selects a *manifest* shard and is
  // handled inside `run_shard_plan`, not against the range-based plan here.
  if let Some(only) = args.only_shard.filter(|_| args.shard_plan.is_none()) {
    let plan = &mut plans[0];
    let num = plan.shards.len();
    if only == 0 || only > num {
      bail!("--only-shard {only} out of range; have {num} shard(s)");
    }
    let (s, e) = plan.shards[only - 1];
    println!(
      "only-shard: proving shard {only}/{num} of {} range [{s}, {e})",
      plan.label
    );
    plan.shards = vec![(s, e)];
  }

  // The store composes with manifest-driven sharding only: shard granularity
  // is the reuse unit, and the discharge fold is what verifies stored proofs.
  if args.store_dir.is_some() && args.shard_plan.is_none() {
    bail!("--store-dir requires --shard-plan (reuse is per manifest shard)");
  }

  // Pre-flight closure gate: bail before any proving if the batch isn't a
  // closed env modulo axioms. Runs in `--plan` mode too, so `--plan
  // --require-closed` is a fast no-prove closure check.
  if args.require_closed {
    let covered = match (&args.store_dir, args.no_reuse) {
      (Some(dir), false) => {
        let mut set = std::collections::HashSet::default();
        for p in load_proof_index(dir) {
          set.extend(p.subjects.iter().map(|a| *a.as_bytes()));
        }
        set
      },
      _ => std::collections::HashSet::default(),
    };
    check_inputs_closed(&inputs, &covered)?;
  }

  if args.plan {
    return Ok(());
  }

  // Grand totals across the whole batch.
  let grand_total_items: u32 = plans.iter().map(|p| p.total).sum();
  let grand_target_count: usize = plans.iter().map(|p| p.target_count).sum();
  let total_leaves: usize = plans.iter().map(|p| p.shards.len()).sum();

  let client = build_client(args.gpu, !args.emulator)?;
  client.setup(&SHARD_PROGRAM).run()?.await?;
  // Skip agg-guest setup unless we'll produce more than one leaf proof.
  // The shard-plan path sets up the agg program itself, after its leaves.
  //
  // Under the Assembly executor (the default) this upfront agg setup is
  // *harmful*: it re-initializes the ASM microservices and clobbers SHARD's
  // ROM histogram, so the subsequent leaf proves panic in `rom.rs`. We defer
  // the agg setup to after the leaf loop (see the agg-fold below). Only the
  // Emulator (`--emulator`) keeps the upfront setup — it has no microservice
  // state to clobber.
  let need_agg = !args.execute
    && !args.verify_constraints
    && args.shard_plan.is_none()
    && total_leaves > 1;
  if need_agg && args.emulator {
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

  // ---- Named constants (no manifest/range). Loops one leaf per name. ----
  if !consts.is_empty() {
    for name in &consts {
      run_constant(&client, &plans[0], name, &args).await?;
    }
    return Ok(());
  }

  // ---- Execute path: run every shard of every input in the VM. ----
  if args.execute {
    let mut total_steps: u64 = 0;
    let mut total_exec_ms: u64 = 0;
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
        println!(
          "  [{} shard {}/{num_shards}] range [{start}, {end}), failures={}, cycles={cycles}",
          plan.label,
          i + 1,
          publics.failures,
        );
        reject_failures(
          &publics,
          &format!("{} shard {}/{num_shards}", plan.label, i + 1),
        )?;
      }
    }
    let total_exec = Duration::from_millis(total_exec_ms);
    let throughput =
      grand_target_count as f64 / total_exec.as_secs_f64().max(f64::EPSILON);
    println!("failures: 0");
    println!("cycles: {total_steps}");
    println!("inputs: {}", plans.len());
    println!("work items: {grand_total_items}");
    println!("target constants: {grand_target_count}");
    println!(
      "exec time: {:.3}s, throughput: {}",
      total_exec.as_secs_f64(),
      throughput.human_throughput("consts"),
    );
    return Ok(());
  }

  if args.verify_constraints {
    // Guaranteed single input by the guard above.
    let plan = &plans[0];
    if plan.shards.len() != 1 {
      bail!(
        "--verify-constraints requires a single shard (got {})",
        plan.shards.len()
      );
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
      reject_failures(
        &publics,
        &format!("{} leaf {}/{num_shards}", plan.label, i + 1),
      )?;
      leaf_proof_bytes.push(result.get_proof_bytes()?);
      input_publics.push(publics);
      last_leaf_result = Some(result);
    }
    // Per-input coherence: this input's shards must tile its own env.
    total_failures = total_failures.saturating_add(check_input_coherence(
      &plan.label,
      &input_publics,
      plan.total,
    )?);
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
    // Under the Assembly executor (the default) the upfront agg setup in `main`
    // was skipped (it would have clobbered SHARD's ROM histogram before the
    // leaf proves). Now that every leaf is proven, set up the agg program here
    // — the last `setup` before the agg proves, so the ASM microservices hold
    // AGG's ROM. The Emulator already did this setup upfront.
    if !args.emulator {
      client.setup(&AGG_PROGRAM).run()?.await?;
    }
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
        let stdin = agg_stdin(&allowed, &current[s..e], None);
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
    let leaf =
      last_leaf_result.expect("single-leaf path must have a leaf result");
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
    return Err(
      Rejection {
        failures: total_failures.into(),
        ctx: "batch (proof still verifies)".to_string(),
      }
      .into(),
    );
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

#[cfg(test)]
mod cli_tests {
  use clap::Parser;

  use super::Args;

  fn parse(argv: &[&str]) -> Args {
    Args::try_parse_from(
      std::iter::once("zisk-host").chain(argv.iter().copied()),
    )
    .expect("parse ok")
  }
  fn parse_err(argv: &[&str]) -> String {
    Args::try_parse_from(
      std::iter::once("zisk-host").chain(argv.iter().copied()),
    )
    .unwrap_err()
    .to_string()
  }

  #[test]
  fn consts_splits_on_comma() {
    let a = parse(&["--consts", "Nat.add_comm,Nat.succ,String.append"]);
    assert_eq!(a.consts, vec!["Nat.add_comm", "Nat.succ", "String.append"]);
  }

  #[test]
  fn consts_repeatable_and_comma_lists_stack() {
    let a = parse(&["--consts", "a", "--consts", "b,c"]);
    assert_eq!(a.consts, vec!["a", "b", "c"]);
  }

  #[test]
  fn skip_deps_and_json_parse_with_consts_file_only() {
    // --skip-deps/--json need names, but names may come from --consts-file
    // alone — clap must accept the parse (main validates after
    // collect_consts).
    let a = parse(&[
      "--consts-file",
      "names.txt",
      "--skip-deps",
      "--json",
      "out.json",
    ]);
    assert!(a.skip_deps);
    assert_eq!(a.json.as_deref(), Some(std::path::Path::new("out.json")));
  }

  #[test]
  fn consts_conflicts_with_shard_plan() {
    let s = parse_err(&["--consts", "a", "--shard-plan", "p.ixes"]);
    assert!(s.contains("shard-plan") || s.contains("shard_plan"));
  }

  #[test]
  fn consts_conflicts_with_only_shard() {
    let s = parse_err(&["--consts", "a", "--only-shard", "1"]);
    assert!(s.contains("only-shard") || s.contains("only_shard"));
  }

  #[test]
  fn collect_unions_and_dedups() {
    // Grammar/union behavior is tested in ix-bench; this pins the Args
    // plumbing (comma splitting stacked with a file) end to end.
    let dir = std::env::temp_dir();
    let path = dir.join("zisk_host_cli_test_consts.txt");
    std::fs::write(&path, "a\nb\n# comment\n  c  \n\na\n").expect("write");
    let a =
      parse(&["--consts", "a,d", "--consts-file", path.to_str().unwrap()]);
    let got = ix_bench::collect_consts(&a.consts, a.consts_file.as_deref())
      .expect("collect");
    assert_eq!(got, vec!["a", "d", "b", "c"]);
    let _ = std::fs::remove_file(&path);
  }
}
