//! Drive the SP1 guest: load an Ixon environment, execute (or prove) the
//! kernel typecheck over it.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute
//! RUST_LOG=info cargo run --release -- --execute --ixe ../../minimal.ixe
//! WITHOUT_VK_VERIFICATION=1 RUST_LOG=info cargo run --release  # prove (compressed)
//! # prove a single constant out of a large env (Anon-only):
//! WITHOUT_VK_VERIFICATION=1 RUST_LOG=info cargo run --release -- --ixe ../../init.ixe --only-const Nat.add_comm
//! ```
//!
//! Proving (any non-`--execute` run) requires `WITHOUT_VK_VERIFICATION=1` in
//! the environment: the guest hashes via the patched BLAKE3's `BLAKE3_COMPRESS`
//! precompile, whose recursion shapes aren't in the SP1 prover's bundled
//! `vk_map.bin`, so without the bypass proving aborts with `vk not allowed`.
//! The `experimental` sp1-sdk feature (see `Cargo.toml`) honors the variable on
//! both the prover and the light-node verifier. Drop once `vk_map.bin` is
//! regenerated with the new chip. `--execute` does not need it.

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{Result, bail};
use clap::Parser;
use human_repr::{HumanCount, HumanThroughput};
use ix_kernel::anon_work::{
  block_of_addr, build_anon_work, build_sub_env, work_block_addr,
};
use ixon::env::Env as IxonEnv;
use sp1_sdk::{
  Elf, ProveRequest, Prover, ProverClient, ProvingKey, SP1Stdin, include_elf,
};

pub const GUEST_ELF: Elf = include_elf!("sp1-guest");

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Run the program in the VM only - no proof.
  #[arg(long)]
  execute: bool,

  /// Run the kernel in Meta mode (preserves names + dup-level-param-name
  /// check). Default is Anon mode, which matches Aiur's `kernel_check_test`
  /// semantics. Both modes prove the same structural typecheck; Meta is
  /// strictly more constrained but slightly more expensive.
  #[arg(long)]
  meta: bool,

  /// Path to a `.ixe` file produced by `lake exe ix compile`. If omitted, an
  /// empty `IxonEnv` is used.
  #[arg(long)]
  ixe: Option<PathBuf>,

  /// Check a single constant selected by its Lean NAME (e.g. "Nat.add_comm").
  /// The name resolves through the env's `named` metadata to its ingress
  /// block's work item; the guest receives only that block's closure sub-env
  /// plus a one-item check-list, so one constant can be proved out of a large
  /// env without shipping (or typechecking) the whole thing. Anon-only
  /// (incompatible with `--meta`). Requires `--ixe`.
  #[arg(long)]
  only_const: Option<String>,
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

/// Count the kernel-checked target addresses for human-readable output.
/// Mirrors the in-guest enumeration so the printed count matches what
/// the guest actually proves over.
///
/// Anon: `Env::get_anon` (skip metadata) + `build_anon_work` over
/// `env.consts` — same enumeration `rs_kernel_check_anon` and the
/// guest both use.
///
/// Meta: `Env::get` (need `env.named`) + `checkable_addrs()` — same
/// `env.named` walk the Meta guest does.
fn count_checkable(env_bytes: &[u8], meta_mode: bool) -> usize {
  if meta_mode {
    IxonEnv::get(&mut &env_bytes[..])
      .expect("invalid Ixon environment")
      .checkable_addrs()
      .len()
  } else {
    let env =
      IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");
    build_anon_work(&env)
      .expect("build_anon_work")
      .iter()
      .map(|item| item.targets().len())
      .sum()
  }
}

/// Resolve `--only-const <name>` to the guest inputs for that one constant:
/// a closure sub-env and a one-item check-list selecting its work item. The
/// name resolves through the full env's `named` metadata to a constant address,
/// which maps to the `build_anon_work` item whose ingress block owns it
/// (standalone → itself; a mutual-block member → the whole block, checked
/// atomically). Returns `(sub_env_bytes, check_list, target_count)`. Anon-only
/// — the work-item model doesn't apply to Meta's `env.named` walk.
fn only_const_inputs(
  full_env_bytes: &[u8],
  name: &str,
) -> Result<(Vec<u8>, Vec<u8>, usize)> {
  use ix_common::address::Address;

  // `get_anon` discards `named`, so load the full env once just for the lookup.
  let full =
    IxonEnv::get(&mut &full_env_bytes[..]).expect("invalid Ixon environment");
  let target: Address = full
    .named
    .iter()
    .find(|e| e.key().to_string() == name)
    .map(|e| e.value().addr.clone())
    .ok_or_else(|| anyhow::anyhow!("no constant named {name:?} in env"))?;

  let env = IxonEnv::get_anon(&mut &full_env_bytes[..])
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

  let check_list = Address::pack(&[item.primary().clone()]);
  let roots: Vec<Address> = item.proven_targets();
  let sub_env = build_sub_env(&env, &roots).map_err(|e| anyhow::anyhow!(e))?;
  println!(
    "only-const {name}: block {}… ({} target const(s)); closure sub-env {} vs whole env {} ({:.0}%)",
    &block.hex()[..16],
    roots.len(),
    sub_env.len().human_count_bytes(),
    full_env_bytes.len().human_count_bytes(),
    100.0 * sub_env.len() as f64 / full_env_bytes.len().max(1) as f64,
  );
  Ok((sub_env, check_list, roots.len()))
}

#[tokio::main]
async fn main() -> Result<()> {
  sp1_sdk::utils::setup_logger();

  let args = Args::parse();
  let whole_env_bytes = load_env_bytes(args.ixe.as_ref());

  // `--only-const` ships a closure sub-env + a one-item check-list (Anon only);
  // otherwise the whole env ships with an empty check-list (= check everything).
  let (env_bytes, check_list, const_count) =
    if let Some(name) = &args.only_const {
      if args.meta {
        bail!("--only-const is Anon-only and cannot be combined with --meta");
      }
      only_const_inputs(&whole_env_bytes, name)?
    } else {
      let cc = count_checkable(&whole_env_bytes, args.meta);
      (whole_env_bytes, Vec::new(), cc)
    };

  // Three guest inputs, in order:
  //   1. 1-byte mode flag (0 = Anon / 1 = Meta).
  //   2. Serialized Ixon env (whole env, or a closure sub-env under
  //      `--only-const`). Anon enumerates work in-guest via
  //      `ix_kernel::anon_work::build_anon_work`; Meta walks `env.named`.
  //   3. Check-list of packed primary addresses (`--only-const`), or empty
  //      to check every work item.
  let mut stdin = SP1Stdin::new();
  stdin.write::<u8>(&u8::from(args.meta));
  stdin.write_vec(env_bytes);
  stdin.write_vec(check_list);

  let client = ProverClient::from_env().await;

  if args.execute {
    let exec_start = Instant::now();
    let (output, report) =
      client.execute(GUEST_ELF, stdin).await.expect("execute");
    let exec_duration = exec_start.elapsed();
    let failures = u32::from_le_bytes(
      output.as_slice()[..4].try_into().expect("output too short"),
    );
    let throughput =
      const_count as f64 / exec_duration.as_secs_f64().max(f64::EPSILON);
    println!("failures: {failures}");
    // Conditional-claim public output (Anon mode): failures(4) +
    // subject_root(32) + assumptions_root(32) + checked_count(4) + env_hash(32).
    let o = output.as_slice();
    if o.len() >= 104 {
      let hex8 = |b: &[u8]| {
        b.iter().take(8).map(|x| format!("{x:02x}")).collect::<String>()
      };
      let checked = u32::from_le_bytes(o[68..72].try_into().unwrap());
      println!(
        "claim: CheckEnv {{ subject={}…, assumptions={}… }} (checked={checked})",
        hex8(&o[4..36]),
        hex8(&o[36..68]),
      );
    }
    println!("cycles: {}", report.total_instruction_count());
    println!("constants: {const_count}");
    println!(
      "exec time: {:.3}s, throughput: {}",
      exec_duration.as_secs_f64(),
      throughput.human_throughput("consts"),
    );
    // `ExecutionReport`'s `Display` lists opcode counts (RISC-V mix), syscall
    // counts (precompile usage; expected zero for the current guest), and
    // — when the SDK is built with the `profiling` feature — the
    // accumulated `cycle-tracker-report-*` totals emitted by the guest.
    // Together with `crates/kernel/examples/perf_check.rs` (native cache /
    // fuel counters), this is the entry point for profiling SP1 cycles.
    println!("---- ExecutionReport ----");
    println!("{report}");
    if failures > 0 {
      bail!("kernel typecheck produced {failures} failure(s)");
    }
    return Ok(());
  }

  let pk = client.setup(GUEST_ELF).await.expect("setup");
  let start = Instant::now();
  // Requires `WITHOUT_VK_VERIFICATION=1` in the env: the guest's BLAKE3_COMPRESS
  // precompile shapes aren't in the prover's bundled `vk_map.bin`, so otherwise
  // this aborts with `vk not allowed`. The `experimental` feature honors the
  // var (see the module doc header and `Cargo.toml`). `--execute` doesn't.
  let proof = client.prove(&pk, stdin).compressed().await.expect("prove");
  let prove_duration = start.elapsed();
  let throughput =
    const_count as f64 / prove_duration.as_secs_f64().max(f64::EPSILON);
  // `SP1ProofWithPublicValues::bytes()` is the onchain-verifier encoding
  // (Plonk/Groth16 only) and panics on Compressed. Use bincode's size
  // count to match what the SDK's `.save()` writes, without allocating the
  // multi-MB serialized proof just to measure its length.
  let proof_size = usize::try_from(bincode::serialized_size(&proof)?)?;
  println!("proof generated in {:.2}s", prove_duration.as_secs_f64());
  println!("constants: {const_count}");
  println!("prove throughput: {}", throughput.human_throughput("consts"));
  println!("proof size: {}", proof_size.human_count_bytes());

  let verify_start = Instant::now();
  client.verify(&proof, pk.verifying_key(), None).expect("verify");
  let verify_duration = verify_start.elapsed();
  println!("proof verified in {:.3}s", verify_duration.as_secs_f64());
  Ok(())
}
