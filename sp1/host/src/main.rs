//! Drive the SP1 guest: load an Ixon environment, execute (or prove) the
//! kernel typecheck over it.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute
//! RUST_LOG=info cargo run --release -- --execute --ixe ../../minimal.ixe
//! RUST_LOG=info cargo run --release           # prove (compressed)
//! ```

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{bail, Result};
use clap::Parser;
use human_repr::{HumanCount, HumanThroughput};
use ix_kernel::anon_work::build_anon_work;
use ixon::env::Env as IxonEnv;
use sp1_sdk::{
  include_elf, Elf, ProveRequest, Prover, ProverClient, ProvingKey, SP1Stdin,
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
    let env = IxonEnv::get_anon(&mut &env_bytes[..])
      .expect("invalid Ixon environment");
    build_anon_work(&env)
      .expect("build_anon_work")
      .iter()
      .map(|item| item.targets().len())
      .sum()
  }
}

#[tokio::main]
async fn main() -> Result<()> {
  sp1_sdk::utils::setup_logger();

  let args = Args::parse();
  let env_bytes = load_env_bytes(args.ixe.as_ref());
  let const_count = count_checkable(&env_bytes, args.meta);

  // Two guest inputs, in order:
  //   1. 1-byte mode flag (0 = Anon / 1 = Meta).
  //   2. Serialized Ixon env. Anon enumerates work in-guest via
  //      `ix_kernel::anon_work::build_anon_work`; Meta walks
  //      `env.named` after deserialization.
  let mut stdin = SP1Stdin::new();
  stdin.write::<u8>(&u8::from(args.meta));
  stdin.write_vec(env_bytes);

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
      let hex8 = |b: &[u8]| b.iter().take(8).map(|x| format!("{x:02x}")).collect::<String>();
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
  let proof = client
    .prove(&pk, stdin)
    .compressed()
    .await
    .expect("prove");
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
  client
    .verify(&proof, pk.verifying_key(), None)
    .expect("verify");
  let verify_duration = verify_start.elapsed();
  println!("proof verified in {:.3}s", verify_duration.as_secs_f64());
  Ok(())
}
