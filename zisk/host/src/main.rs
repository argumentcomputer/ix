//! Drive the Zisk guest: load an Ixon environment, execute (or prove) the
//! kernel typecheck over it.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute
//! RUST_LOG=info cargo run --release -- --execute --ixe ../minimal.ixe
//! RUST_LOG=info cargo run --release                  # CPU prove
//! RUST_LOG=info cargo run --release -- --gpu         # GPU prove
//! ```

use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{bail, Result};
use clap::Parser;
use human_repr::{HumanCount, HumanThroughput};
use ix_kernel::anon_work::build_anon_work;
use ixon::env::Env as IxonEnv;
use zisk_host::PROGRAM;
use zisk_sdk::{
  EmbeddedClient, EmbeddedClientBuilder, ExecutorKind, ProverClient, VerboseMode,
  VerifyConstraintsExtension, ZiskStdin,
};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Run the program in the VM only — no proof.
  #[arg(long, conflicts_with = "verify_constraints")]
  execute: bool,

  /// Run the constraint checker without generating a proof.
  #[arg(long)]
  verify_constraints: bool,

  /// Enable GPU-accelerated proving. Requires a CUDA-capable build of the
  /// Zisk SDK / proofman (the default since v0.17.0 unless `cpu-only` is set).
  #[arg(long)]
  gpu: bool,

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

fn build_client(gpu: bool) -> Result<EmbeddedClient> {
  let mut builder: EmbeddedClientBuilder =
    ProverClient::embedded().executor(ExecutorKind::Assembly);
  if gpu {
    builder = builder.gpu();
  }
  builder.build()
}

#[tokio::main]
async fn main() -> Result<()> {
  zisk_sdk::setup_logger(VerboseMode::Info);

  let args = Args::parse();
  let env_bytes = load_env_bytes(args.ixe.as_ref());
  let const_count = count_checkable(&env_bytes, args.meta);

  // Two stdin slices, in order:
  //   1. 1-byte mode flag (0 = Anon / 1 = Meta).
  //   2. Serialized Ixon env bytes. Anon enumerates work in-guest via
  //      `ix_kernel::anon_work::build_anon_work`; Meta walks
  //      `env.named` after deserialization.
  let stdin = ZiskStdin::new();
  stdin.write_slice(&[u8::from(args.meta)]);
  stdin.write_slice(&env_bytes);

  let client = build_client(args.gpu)?;

  client.upload(&PROGRAM).run()?;
  client.setup(&PROGRAM).run()?.await?;

  if args.execute {
    let result = client
      .execute(&PROGRAM, stdin)
      .executor(ExecutorKind::Assembly)
      .run()?
      .await?;
    let mut buf = [0u8; 4];
    result.get_public_values_slice(&mut buf);
    let failures = u32::from_le_bytes(buf);
    let exec_duration =
      Duration::from_millis(result.get_execution_time());
    let throughput =
      const_count as f64 / exec_duration.as_secs_f64().max(f64::EPSILON);
    println!("failures: {failures}");
    println!("cycles: {}", result.get_execution_steps());
    println!("constants: {const_count}");
    println!(
      "exec time: {:.3}s, throughput: {}",
      exec_duration.as_secs_f64(),
      throughput.human_throughput("consts"),
    );
    if failures > 0 {
      bail!("kernel typecheck produced {failures} failure(s)");
    }
    return Ok(());
  }

  if args.verify_constraints {
    client.verify_constraints(&PROGRAM, stdin).run()?.await?;
    println!("constraints verified");
    return Ok(());
  }

  let start = Instant::now();
  let result = client
    .prove(&PROGRAM, stdin)
    .executor(ExecutorKind::Assembly)
    .run()?
    .await?;
  let duration = Duration::from_millis(result.get_proving_time());
  let mut buf = [0u8; 4];
  result.get_public_values_slice(&mut buf);
  let failures = u32::from_le_bytes(buf);
  let throughput =
    const_count as f64 / duration.as_secs_f64().max(f64::EPSILON);
  let proof_size = result.get_proof_bytes().len();
  println!("failures: {failures}");
  println!("constants: {const_count}");
  println!(
    "proof generated in {:.2}s (wall {:.2}s, {} steps)",
    duration.as_secs_f64(),
    start.elapsed().as_secs_f64(),
    result.get_execution_steps()
  );
  println!("prove throughput: {}", throughput.human_throughput("consts"));
  println!("proof size: {}", proof_size.human_count_bytes());

  let verify_start = Instant::now();
  result.verify()?;
  let verify_duration = verify_start.elapsed();
  println!("proof verified in {:.3}s", verify_duration.as_secs_f64());
  if failures > 0 {
    bail!("kernel typecheck produced {failures} failure(s) (proof still verifies)");
  }

  Ok(())
}
