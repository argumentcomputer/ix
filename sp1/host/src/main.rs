//! Drive the SP1 guest: load an Ixon environment, execute (or prove) the
//! kernel typecheck over it.
//!
//! ```shell
//! RUST_LOG=info cargo run --release -- --execute
//! RUST_LOG=info cargo run --release -- --execute --ixe ../../minimal.ixe
//! WITHOUT_VK_VERIFICATION=1 RUST_LOG=info cargo run --release  # prove (compressed)
//! # prove a single constant out of a large env (Anon-only):
//! WITHOUT_VK_VERIFICATION=1 RUST_LOG=info cargo run --release -- --ixe ../../init.ixe --consts Nat.add_comm
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
use ix_bench::{
  EXIT_REJECTED, Rejection, Status, collect_consts, peak_rss_bytes, write_row,
};
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
  /// Execute in the VM only — no proof.
  #[arg(long)]
  execute: bool,

  /// Run the kernel in Meta mode (default: Anon). Meta preserves names.
  #[arg(long)]
  meta: bool,

  /// Path to a `.ixe` (default: empty env).
  #[arg(long)]
  ixe: Option<PathBuf>,

  /// Comma-separated Lean names to check (Anon-only; each is one guest run).
  #[arg(long, value_delimiter = ',')]
  consts: Vec<String>,

  /// Additional names from a file (one per line, `#` comments); unions with --consts.
  #[arg(long)]
  consts_file: Option<PathBuf>,

  /// With --consts/--consts-file: check each subject only, trusting its deps.
  // Validated in main (not clap `requires = "consts"`): names may come from
  // --consts-file alone, which a clap-level `requires` would wrongly reject.
  #[arg(long)]
  skip_deps: bool,

  /// Write per-constant results JSON `{ "<name>": { … } }` (accumulated across --consts).
  #[arg(long)]
  json: Option<PathBuf>,

  /// Enable tracing-texray; with --json, per-phase spans are written to <json>.spans.
  #[arg(long)]
  texray: bool,
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

/// Resolve one `--consts` name to the guest inputs for that constant: its
/// closure sub-env and a check-list. The name resolves through the full env's
/// `named` metadata to a constant address, which maps to the `build_anon_work`
/// item whose ingress block owns it (standalone → itself; a mutual-block member
/// → the whole block, checked atomically). The check-list is the ENTIRE closure
/// (full-closure typecheck) by default, or just the subject when `skip_deps` is
/// set. Returns `(sub_env_bytes, check_list, checked_count)`. Anon-only — the
/// work-item model doesn't apply to Meta's `env.named` walk.
fn constant_inputs(
  full_env_bytes: &[u8],
  name: &str,
  skip_deps: bool,
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

  let roots: Vec<Address> = item.proven_targets();
  let sub_env = build_sub_env(&env, &roots).map_err(|e| anyhow::anyhow!(e))?;

  // Check-list: full-closure by default (every work item in the sub-env), or
  // subject-only under `--skip-deps` (just the named constant's primary).
  let (check_list, checked) = if skip_deps {
    (Address::pack(&[item.primary().clone()]), 1usize)
  } else {
    let env_sub =
      IxonEnv::get_anon(&mut &sub_env[..]).expect("invalid sub-env");
    let work_sub = build_anon_work(&env_sub).expect("build_anon_work sub");
    let primaries: Vec<Address> =
      work_sub.iter().map(|w| w.primary().clone()).collect();
    let n = work_sub.len();
    (Address::pack(&primaries), n)
  };
  println!(
    "constant {name}{}: block {}… ({} work item(s) checked, {} target const(s)); closure sub-env {} vs whole env {} ({:.0}%)",
    if skip_deps { " [skip-deps]" } else { " [full-closure]" },
    &block.hex()[..16],
    checked,
    roots.len(),
    sub_env.len().human_count_bytes(),
    full_env_bytes.len().human_count_bytes(),
    100.0 * sub_env.len() as f64 / full_env_bytes.len().max(1) as f64,
  );
  Ok((sub_env, check_list, checked))
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
        std::process::ExitCode::from(EXIT_REJECTED as u8)
      } else {
        std::process::ExitCode::FAILURE
      }
    },
  }
}

async fn run() -> Result<()> {
  sp1_sdk::utils::setup_logger();

  let args = Args::parse();

  // Start the process-tree RSS sampler (accurate peak RAM) and point the
  // per-phase timing sink at the drill-down file if requested — both
  // independent of the SDK's global tracing logger.
  //
  // TODO(spans): the sink only receives the coarse `sp1/execute` / `sp1/prove`
  // phases we `record_manual` below. For a finer drill-down, install a TeXRay
  // subscriber and examine the sp1-sdk's own tracing spans — which requires
  // composing it with the SDK's global logger (`sp1_sdk::utils::setup_logger`),
  // currently the sole subscriber.
  tracing_texray::rss_sampler::start(std::time::Duration::from_millis(50));
  // With --texray + --json, per-phase span timings land at `<json>.spans` as
  // JSON Lines — the CI drill-down input.
  if args.texray {
    if let Some(json) = args.json.as_ref().and_then(|p| p.to_str()) {
      let _ = tracing_texray::json_sink::to_file(&format!("{json}.spans"));
    }
  }

  let whole_env_bytes = load_env_bytes(args.ixe.as_ref());
  let client = ProverClient::from_env().await;
  let consts = collect_consts(&args.consts, args.consts_file.as_deref())?;
  if !consts.is_empty() && args.meta {
    bail!("--consts is Anon-only and cannot be combined with --meta");
  }
  if consts.is_empty() && args.skip_deps {
    bail!("--skip-deps requires constants via --consts or --consts-file");
  }

  if consts.is_empty() {
    run_one(&client, &args, &whole_env_bytes, None).await?;
  } else {
    for name in &consts {
      run_one(&client, &args, &whole_env_bytes, Some(name)).await?;
    }
  }
  Ok(())
}

async fn run_one<C: Prover + Sync>(
  client: &C,
  args: &Args,
  whole_env_bytes: &[u8],
  name: Option<&str>,
) -> Result<()> {
  // A name ships a closure sub-env + a check-list (Anon only); otherwise the
  // whole env ships with an empty check-list (= check everything).
  let (env_bytes, check_list, const_count) = match name {
    Some(n) => constant_inputs(whole_env_bytes, n, args.skip_deps)?,
    None => {
      let cc = count_checkable(whole_env_bytes, args.meta);
      (whole_env_bytes.to_vec(), Vec::new(), cc)
    },
  };

  // Three guest inputs, in order:
  //   1. 1-byte mode flag (0 = Anon / 1 = Meta).
  //   2. Serialized Ixon env (whole env, or a closure sub-env under --consts).
  //   3. Check-list of packed primary addresses (--consts), or empty for all.
  let mut stdin = SP1Stdin::new();
  stdin.write::<u8>(&u8::from(args.meta));
  stdin.write_vec(env_bytes);
  stdin.write_vec(check_list);

  if args.execute {
    let exec_start = Instant::now();
    let (output, report) =
      client.execute(GUEST_ELF, stdin).await.expect("execute");
    let exec_duration = exec_start.elapsed();
    tracing_texray::json_sink::record_manual(
      "sp1/execute",
      exec_duration.as_secs_f64(),
    );
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
    // Together with the kernel's native perf counters
    // (`crates/kernel/src/perf.rs`, `IX_PERF_COUNTERS=1`), this is the entry
    // point for profiling SP1 cycles.
    println!("---- ExecutionReport ----");
    println!("{report}");
    if let Some(path) = &args.json {
      let cycles = report.total_instruction_count();
      let secs = exec_duration.as_secs_f64();
      let tput = if secs > 0.0 { cycles as f64 / secs } else { 0.0 };
      let key =
        name.map(|s| s.to_string()).unwrap_or_else(|| "env".to_string());
      let status = if failures > 0 { Status::Rejected } else { Status::Ok };
      write_row(
        path,
        &key,
        status,
        serde_json::json!({
          "cycles": cycles,
          "execute-time": (secs * 1e6).round() / 1e6,
          "throughput": tput.round(),
          // The execute phase's RSS high-water — the only phase this cell
          // has, so the name stays bare (phases separate at the testbed).
          "peak-rss": peak_rss_bytes(),
        }),
      )?;
    }
    if failures > 0 {
      return Err(
        Rejection {
          failures: failures.into(),
          ctx: name.map_or_else(|| "env".to_string(), |s| s.to_string()),
        }
        .into(),
      );
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
  tracing_texray::json_sink::record_manual(
    "sp1/prove",
    prove_duration.as_secs_f64(),
  );
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
  if let Some(path) = &args.json {
    let key = name.map(|s| s.to_string()).unwrap_or_else(|| "env".to_string());
    write_row(
      path,
      &key,
      Status::Ok,
      serde_json::json!({
        "prove-time": (prove_duration.as_secs_f64() * 1e6).round() / 1e6,
        "peak-rss": peak_rss_bytes(),
      }),
    )?;
  }
  Ok(())
}

#[cfg(test)]
mod cli_tests {
  use clap::Parser;

  use super::Args;

  fn parse(argv: &[&str]) -> Args {
    Args::try_parse_from(
      std::iter::once("sp1-host").chain(argv.iter().copied()),
    )
    .expect("parse ok")
  }

  #[test]
  fn consts_splits_on_comma() {
    let a = parse(&["--consts", "Nat.add_comm,Nat.succ"]);
    assert_eq!(a.consts, vec!["Nat.add_comm", "Nat.succ"]);
  }

  #[test]
  fn consts_repeatable_and_comma_lists_stack() {
    let a = parse(&["--consts", "a", "--consts", "b,c"]);
    assert_eq!(a.consts, vec!["a", "b", "c"]);
  }

  #[test]
  fn skip_deps_parses_with_consts_file_only() {
    // Names may come from --consts-file alone; clap must accept the parse
    // (main validates after collect_consts).
    let a = parse(&["--consts-file", "names.txt", "--skip-deps"]);
    assert!(a.skip_deps);
  }

  #[test]
  fn json_alone_ok() {
    // sp1-host's --json is not gated on --consts (keys by "env" when no name).
    let a = parse(&["--json", "out.json"]);
    assert_eq!(a.json.as_deref(), Some(std::path::Path::new("out.json")));
  }

  #[test]
  fn consts_file_alone_ok() {
    let a = parse(&["--consts-file", "names.txt"]);
    assert_eq!(
      a.consts_file.as_deref(),
      Some(std::path::Path::new("names.txt"))
    );
  }

  #[test]
  fn collect_unions_and_dedups() {
    // Grammar/union behavior is tested in ix-bench; this pins the Args
    // plumbing (comma splitting stacked with a file) end to end.
    let path = std::env::temp_dir().join("sp1_host_cli_test_consts.txt");
    std::fs::write(&path, "a\nb\n# comment\n  c  \n\na\n").expect("write");
    let a =
      parse(&["--consts", "a,d", "--consts-file", path.to_str().unwrap()]);
    let got = ix_bench::collect_consts(&a.consts, a.consts_file.as_deref())
      .expect("collect");
    assert_eq!(got, vec!["a", "d", "b", "c"]);
    let _ = std::fs::remove_file(&path);
  }
}
