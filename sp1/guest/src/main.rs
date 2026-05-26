//! SP1 guest binary: prove that every kernel-checkable constant in a
//! serialized Ixon environment typechecks under the Ix kernel.
//!
//! Input (two reads, in order):
//!   1. `u8`: kernel mode flag (0 = Anon default, 1 = Meta) via `read::<u8>`.
//!   2. `Vec<u8>`: Ixon-serialized environment via `read_vec`.
//!
//! Output (via `sp1_zkvm::io::commit`):
//!   - `u32`: count of constants that failed typechecking (0 = all pass).
//!
//! Anon mode enumerates the work set in-guest via
//! [`ix_kernel::anon_work::build_anon_work`] — the same enumeration
//! that drives `rs_kernel_check_anon` in `crates/ffi/src/kernel.rs`.
//! The proof commits to "every kernel-checkable constant in this env
//! typechecks," matching Aiur's `kernel_check_test` semantics.
//!
//! Meta mode walks `env.named` for the kid set (preserves Lean names
//! + runs the dup-level-param-name check); slightly more constrained
//! and slightly more expensive in cycles.
//!
//! Both modes typecheck the same underlying structural set; they
//! differ only in which metadata fields the kernel carries through
//! `KEnv<M>`.

#![no_main]
sp1_zkvm::entrypoint!(main);

use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::ingress::ixon_ingress_owned;
use ix_kernel::mode::{Anon, Meta};
use ix_kernel::tc::TypeChecker;
use ixon::env::Env as IxonEnv;
use ixon::metadata::ConstantMetaInfo;

// SP1's cycle tracker (gated by the SDK `profiling` feature on the host
// side — see `sp1/host/Cargo.toml`) consumes `println!`s of the form
// `cycle-tracker-report-{start,end}: <name>` from stdout and accumulates
// total cycles per label across all invocations of that label. Each
// `println!` is a single `syscall_write`, so per-iteration brackets in
// hot loops add measurable overhead — keep these at coarse phase
// boundaries. To get per-constant cycle attribution (e.g. for a one-off
// "which `kid_NNN` dominates?" investigation), temporarily wrap the
// `tc.check_const(kid)` call below in the same pair of `println!`s; pair
// the output with `crates/kernel/examples/perf_check.rs` to map indices
// to constant names.
macro_rules! tic { ($name:expr) => { println!("cycle-tracker-report-start: {}", $name) } }
macro_rules! toc { ($name:expr) => { println!("cycle-tracker-report-end: {}", $name) } }

pub fn main() {
  let meta_mode: u8 = sp1_zkvm::io::read();
  let env_bytes: Vec<u8> = sp1_zkvm::io::read_vec();

  let failures = if meta_mode == 1 {
    // ---- Meta mode: full env load + eager ingress ----
    //
    // `ixon_ingress_inner` walks `env.named` to enumerate work items,
    // so we need the full env (with the metadata sections intact).
    tic!("ixon_decode_env");
    let env =
      IxonEnv::get(&mut &env_bytes[..]).expect("invalid Ixon environment");
    toc!("ixon_decode_env");

    let mut kids: Vec<KId<Meta>> = Vec::with_capacity(env.named.len());
    kids.extend(
      env
        .named
        .iter()
        .filter(|e| !matches!(e.value().meta.info, ConstantMetaInfo::Muts { .. }))
        .map(|e| KId::<Meta>::new(e.value().addr.clone(), e.key().clone())),
    );

    tic!("ingress");
    let (mut kenv, _intern) =
      ixon_ingress_owned::<Meta>(env).expect("ingress failed");
    toc!("ingress");

    let mut failures: u32 = 0;
    tic!("check_const_loop");
    let mut tc = TypeChecker::new(&mut kenv);
    for kid in &kids {
      if tc.check_const(kid).is_err() {
        failures = failures.saturating_add(1);
      }
    }
    toc!("check_const_loop");
    failures
  } else {
    // ---- Anon mode: get_anon + lazy on-demand ingress ----
    //
    // `Env::get_anon` parses-and-discards the metadata sections
    // (named/names/comms) so the steady-state env carries only
    // `consts`/`blobs`/`anon_hints`. `build_anon_work` enumerates the
    // canonical kernel-checkable work set from `env.consts` alone
    // (no metadata) — same logic the FFI's `rs_kernel_check_anon`
    // uses. Each `tc.check_const(primary)` either typechecks one
    // standalone or drives the kernel's block coordination to cover
    // every member + ctor of a Muts block.
    tic!("ixon_decode_env");
    let env =
      IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");
    toc!("ixon_decode_env");

    tic!("build_anon_work");
    let work = build_anon_work(&env).expect("build_anon_work");
    toc!("build_anon_work");

    let mut kenv = KEnv::<Anon>::new();
    let mut failures: u32 = 0;
    tic!("check_const_loop");
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    for item in &work {
      let kid = KId::<Anon>::new(item.primary().clone(), ());
      if tc.check_const(&kid).is_err() {
        failures = failures.saturating_add(1);
      }
    }
    toc!("check_const_loop");
    failures
  };

  sp1_zkvm::io::commit(&failures);
}
