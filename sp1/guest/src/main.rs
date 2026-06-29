//! SP1 guest binary: prove that every kernel-checkable constant in a
//! serialized Ixon environment typechecks under the Ix kernel.
//!
//! Input (three reads, in order):
//!   1. `u8`: kernel mode flag (0 = Anon default, 1 = Meta) via `read::<u8>`.
//!   2. `Vec<u8>`: Ixon-serialized environment via `read_vec`.
//!   3. `Vec<u8>`: optional check-list — a packed set of primary addresses
//!      (`Address::pack`) to check in Anon mode. Empty ⇒ whole env; non-empty
//!      ⇒ check exactly those work items (the `--only-const` path, where the
//!      host ships a closure sub-env plus the one targeted primary). Mirrors
//!      the Zisk leaf guest's reuse-mode selection.
//!
//! Output (via `sp1_zkvm::io::commit_slice`, fixed 104-byte layout):
//!   - `u32` failures (offset 0; 0 = all pass)
//!   - `[u8; 32]` subject_root  — canonical merkle root over the consts
//!     this proof certified (Anon mode; zero in Meta)
//!   - `[u8; 32]` assumptions_root — merkle root over their direct refs not
//!     certified here (the conditional claim's external assumptions)
//!   - `u32` checked_count
//!   - `[u8; 32]` env_hash
//!
//! `(subject_root, assumptions_root)` form `Claim::CheckEnv { root, assumptions }`
//! — the same content-addressed conditional claim the Zisk leaf guest emits.
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

use ix_common::address::Address;
use ix_kernel::anon_work::{AnonWorkItem, build_anon_work};
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::ingress::ixon_ingress_owned;
use ix_kernel::mode::{Anon, Meta};
use ix_kernel::tc::TypeChecker;
use ixon::env::Env as IxonEnv;
use ixon::merkle::{merkle_root_canonical, zero_address};
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
// the output with a native `check_const` run over the same anon-work order
// to map indices to constant names.
macro_rules! tic {
  ($name:expr) => {
    println!("cycle-tracker-report-start: {}", $name)
  };
}
macro_rules! toc {
  ($name:expr) => {
    println!("cycle-tracker-report-end: {}", $name)
  };
}

pub fn main() {
  let meta_mode: u8 = sp1_zkvm::io::read();
  let env_bytes: Vec<u8> = sp1_zkvm::io::read_vec();
  // Optional check-list: a packed set of primary addresses to check (Anon
  // mode). Empty ⇒ whole env. Ignored in Meta mode (the host forbids
  // `--only-const` there).
  let check_list: Vec<u8> = sp1_zkvm::io::read_vec();
  // `Address::hash` is blake3 via the precompile shim (same path the kernel
  // uses) — binds the proof to the exact env payload.
  let env_hash: [u8; 32] = *Address::hash(&env_bytes).as_bytes();

  // Conditional-claim outputs: populated in Anon mode (the claim/resolution
  // path, mirroring the Zisk leaf guest); left zero in Meta mode.
  let mut subject_root = zero_address();
  let mut assumptions_root = zero_address();
  let mut checked_count: u32 = 0;

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
        .filter(|e| {
          !matches!(e.value().meta.info, ConstantMetaInfo::Muts { .. })
        })
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

    // Empty check-list ⇒ whole env. Non-empty ⇒ check exactly the work items
    // whose primary is in the set (the `--only-const` path). `Address` orders
    // by raw bytes, so sort + binary_search is correct — mirrors the Zisk leaf
    // guest's reuse-mode selection.
    let items_to_check: Vec<&AnonWorkItem> = if check_list.is_empty() {
      work.iter().collect()
    } else {
      let mut want: Vec<Address> = Address::unpack(&check_list).collect();
      want.sort_unstable();
      work
        .iter()
        .filter(|it| want.binary_search(it.primary()).is_ok())
        .collect()
    };

    let mut kenv = KEnv::<Anon>::new();
    let mut failures: u32 = 0;
    let mut checked_covered: Vec<Address> = Vec::new();
    tic!("check_const_loop");
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    for item in &items_to_check {
      let kid = KId::<Anon>::new(item.primary().clone(), ());
      if tc.check_const(&kid).is_err() {
        failures = failures.saturating_add(1);
      }
      // Certify in `consts`-key space (block addr + projections) — the same
      // address space `Constant.refs` use, so the assumption set and its
      // cross-proof resolution line up.
      checked_covered.extend(item.proven_targets());
    }
    toc!("check_const_loop");

    // ---- Conditional claim: CheckEnv { subject, assumptions } ----
    //
    // subject     = canonical merkle root over the consts certified here.
    // assumptions = canonical merkle root over their DIRECT refs not
    //   certified here — this whole-env proof's external dependencies
    //   (ultimately the declared axioms). Mirrors the Zisk leaf guest so
    //   both backends emit the same content-addressed claim.
    //
    //   A `Constant.refs` entry points at either another CONSTANT (a genuine
    //   typing obligation) or a literal DATA blob (the bytes behind an
    //   `Expr::Nat`/`Expr::Str` — e.g. the numbers 0, 1). Literals are
    //   well-typed by construction with content-pinned bytes, so they are NOT
    //   assumptions; skip refs that resolve to a blob (must match Zisk).
    tic!("claim_roots");
    checked_count = checked_covered.len() as u32;
    subject_root =
      merkle_root_canonical(&checked_covered).unwrap_or_else(zero_address);
    let mut sorted = checked_covered.clone();
    sorted.sort_unstable();
    sorted.dedup();
    let mut assumptions: Vec<Address> = Vec::new();
    for t in &checked_covered {
      if let Some(c) = env.get_const(t) {
        for r in &c.refs {
          if sorted.binary_search(r).is_err() && env.get_blob(r).is_none() {
            assumptions.push(r.clone());
          }
        }
      }
    }
    assumptions_root =
      merkle_root_canonical(&assumptions).unwrap_or_else(zero_address);
    toc!("claim_roots");
    failures
  };

  // Fixed 104-byte public output: failures(4) + subject_root(32) +
  // assumptions_root(32) + checked_count(4) + env_hash(32). `failures` stays
  // at offset 0 so existing readers keep working.
  let mut out = Vec::with_capacity(104);
  out.extend_from_slice(&failures.to_le_bytes());
  out.extend_from_slice(subject_root.as_bytes());
  out.extend_from_slice(assumptions_root.as_bytes());
  out.extend_from_slice(&checked_count.to_le_bytes());
  out.extend_from_slice(&env_hash);
  sp1_zkvm::io::commit_slice(&out);
}
