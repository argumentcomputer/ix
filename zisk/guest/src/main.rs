//! Zisk guest binary: prove that every kernel-checkable constant in a
//! serialized Ixon environment typechecks under the Ix kernel.
//!
//! Input (two `ziskos::io::read_input_slice` slices, in order):
//!   1. `[u8; 1]`: kernel mode flag. `0` = Anon (default, matches Aiur's
//!      `kernel_check_test` semantics: structural typecheck only).
//!      `1` = Meta (preserves names + runs the dup-level-param-name check).
//!   2. `Vec<u8>`: Ixon-serialized environment (`ixon::env::Env::get` format).
//!
//! Output (via `ziskos::io::commit`):
//!   - `u32`: count of constants that failed typechecking (0 = all pass).
//!
//! Anon mode enumerates the work set in-guest via
//! [`ix_kernel::anon_work::build_anon_work`] — the same enumeration
//! that drives `rs_kernel_check_anon` in `crates/ffi/src/kernel.rs`.
//! The proof commits to "every kernel-checkable constant in this env
//! typechecks," matching Aiur's `kernel_check_test` semantics.

#![no_main]
ziskos::entrypoint!(main);

use ix_kernel::anon_work::build_anon_work;
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::ingress::ixon_ingress_owned;
use ix_kernel::mode::{Anon, Meta};
use ix_kernel::tc::TypeChecker;
use ixon::env::Env as IxonEnv;
use ixon::metadata::ConstantMetaInfo;

fn main() {
  let mode_slice: &[u8] = ziskos::io::read_input_slice();
  let meta_mode = mode_slice.first().copied().unwrap_or(0) == 1;

  let env_bytes: &[u8] = ziskos::io::read_input_slice();

  let failures = if meta_mode {
    // ---- Meta mode: full env load + eager ingress ----
    //
    // `ixon_ingress_inner` walks `env.named` to enumerate work items,
    // so we need the full env (with the metadata sections intact).
    let env =
      IxonEnv::get(&mut &env_bytes[..]).expect("invalid Ixon environment");

    let mut kids: Vec<KId<Meta>> = Vec::with_capacity(env.named.len());
    kids.extend(
      env
        .named
        .iter()
        .filter(|e| !matches!(e.value().meta.info, ConstantMetaInfo::Muts { .. }))
        .map(|e| KId::<Meta>::new(e.value().addr.clone(), e.key().clone())),
    );

    let (mut kenv, _intern) =
      ixon_ingress_owned::<Meta>(env).expect("ingress failed");
    let mut failures: u32 = 0;
    let mut tc = TypeChecker::new(&mut kenv);
    for kid in &kids {
      if tc.check_const(kid).is_err() {
        failures = failures.saturating_add(1);
      }
    }
    failures
  } else {
    // ---- Anon mode: get_anon + lazy on-demand ingress ----
    //
    // `Env::get_anon` parses-and-discards the metadata sections so
    // the steady-state env carries only `consts`/`blobs`/`anon_hints`.
    // `build_anon_work` enumerates the canonical kernel-checkable
    // work set from `env.consts` alone (no metadata) — same logic
    // the FFI's `rs_kernel_check_anon` uses. Each
    // `tc.check_const(primary)` either typechecks one standalone or
    // drives the kernel's block coordination to cover every member +
    // ctor of a Muts block.
    let env =
      IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");

    let work = build_anon_work(&env).expect("build_anon_work");

    let mut kenv = KEnv::<Anon>::new();
    let mut failures: u32 = 0;
    let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
    for item in &work {
      let kid = KId::<Anon>::new(item.primary().clone(), ());
      if tc.check_const(&kid).is_err() {
        failures = failures.saturating_add(1);
      }
    }
    failures
  };

  ziskos::io::commit(&failures);
}
