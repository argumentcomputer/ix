//! Zisk leaf guest: typecheck work items `[range_start, range_end)`
//! of the canonical `build_anon_work` enumeration against a serialized
//! Ixon environment.
//!
//! Input (two `ziskos::io::read_input_slice` slices):
//!   1. `[u8; 8]` `range_start: u32 || range_end: u32` little-endian.
//!      `(0, 0)` means "whole env" (range = `[0, total)`).
//!   2. `Vec<u8>` Ixon-serialized environment (`ixon::env::Env::get`).
//!
//! Output committed via `ziskos::io::commit*`:
//!   - `[u8; 32]` blake3 hash of the env bytes — binds the proof to the
//!     exact env payload; aggregation can require this matches across
//!     leaves.
//!   - `u32` `range_start`, `u32` `range_end`, `u32` failure count.
//!
//! `Env::get_anon` parses-and-discards metadata, so the steady-state
//! env carries only `consts`/`blobs`/`anon_hints`. `build_anon_work`
//! enumerates the canonical kernel-checkable work set from `env.consts`
//! — the same enumeration `rs_kernel_check_anon` uses. Each
//! `tc.check_const(primary)` either typechecks one standalone or drives
//! the kernel's block coordination across a Muts block's members + ctors.

#![no_main]
ziskos::entrypoint!(main);

use ix_common::address::Address;
use ix_kernel::anon_work::{build_anon_work, AnonWorkItem};
use ix_kernel::env::KEnv;
use ix_kernel::id::KId;
use ix_kernel::mode::Anon;
use ix_kernel::tc::TypeChecker;
use ixon::env::Env as IxonEnv;
use ixon::merkle::{merkle_root_canonical, zero_address};

fn main() {
  let range_slice: &[u8] = ziskos::io::read_input_slice();
  let range_start: u32 = range_slice
    .get(..4)
    .and_then(|b| b.try_into().ok())
    .map(u32::from_le_bytes)
    .unwrap_or(0);
  let range_end: u32 = range_slice
    .get(4..8)
    .and_then(|b| b.try_into().ok())
    .map(u32::from_le_bytes)
    .unwrap_or(0);

  let env_bytes: &[u8] = ziskos::io::read_input_slice();
  // `Address::hash` is blake3 routed through the precompile shim (same
  // path the kernel uses everywhere) — no extra dep needed.
  let env_hash: [u8; 32] = *Address::hash(env_bytes).as_bytes();

  // Slice 3: cross-proof reuse selector — a packed list of primary
  // addresses (`Address::pack`) the host wants checked. When empty, fall
  // back to contiguous-range mode (shard/whole-env). When non-empty, check
  // exactly the work items whose primary is in the set: the host ships only
  // the NOVEL constants (those not already in the proof store), so shared
  // constants proven by an earlier proof are skipped here. Their
  // well-typedness becomes an assumption resolved at the store/aggregation
  // layer (content-addressed: same constant ⇒ same primary across envs).
  let check_slice: &[u8] = ziskos::io::read_input_slice();

  let env = IxonEnv::get_anon(&mut &env_bytes[..]).expect("invalid Ixon environment");
  let work = build_anon_work(&env).expect("build_anon_work");
  let total = work.len() as u32;

  // Decide which work items to check, then check them — recording every
  // checked target address so we can emit a conditional claim binding the
  // proof to exactly what it certified. `field_a`/`field_b` preserve the
  // original 44-byte prefix: range mode reports [start, end); reuse mode
  // reports [checked_count, 0).
  let (items_to_check, field_a, field_b): (Vec<&AnonWorkItem>, u32, u32) =
    if check_slice.is_empty() {
      let (start, end) = resolve_range(range_start, range_end, total);
      (work[start as usize..end as usize].iter().collect(), start, end)
    } else {
      // Reuse mode: check only work items whose primary is in the set.
      // `Address` orders by raw bytes, so sort + binary_search is correct.
      let mut want: Vec<Address> = Address::unpack(check_slice).collect();
      want.sort_unstable();
      let items: Vec<&AnonWorkItem> =
        work.iter().filter(|it| want.binary_search(it.primary()).is_ok()).collect();
      (items, 0, 0) // field_a filled in below once checked_count is known
    };
  let reuse_mode = !check_slice.is_empty();

  let mut kenv = KEnv::<Anon>::new();
  let mut failures: u32 = 0;
  let mut checked_targets: Vec<Address> = Vec::new();
  let mut tc = TypeChecker::<Anon>::new_with_lazy_anon(&mut kenv, &env);
  for item in &items_to_check {
    let kid = KId::<Anon>::new(item.primary().clone(), ());
    if tc.check_const(&kid).is_err() {
      failures = failures.saturating_add(1);
    }
    // Certify in `consts`-key space (block addr + projections), matching
    // the address space `Constant.refs` use, so the assumption set and its
    // cross-proof resolution line up exactly.
    checked_targets.extend(item.proven_targets());
  }
  let checked_count = checked_targets.len() as u32;

  // ---- Conditional claim (full-soundness binding) ----
  //
  // subject  = canonical merkle root over the target addresses this proof
  //            CERTIFIED as well-typed.
  // assumptions = canonical merkle root over those targets' DIRECT refs
  //            that are NOT certified here — the constants this proof
  //            assumes are well-typed. The aggregation/`Contains` circuit
  //            resolves each assumption leaf against another proof's
  //            subject (recursively), bottoming out at axioms.
  // Together these are `Claim::CheckEnv { root: subject, assumptions }` —
  // content-addressed, no proof-layer namespace.
  let subject_root =
    merkle_root_canonical(&checked_targets).unwrap_or_else(zero_address);

  // Assumption set = (union of direct refs of checked targets) \ checked,
  // EXCLUDING literal/data blobs. A `Constant.refs` entry points at either
  // another CONSTANT (a real "this must be well-typed" obligation) or a
  // literal blob — the bytes behind an `Expr::Nat`/`Expr::Str` (e.g. the
  // numbers 0, 1). Literals are well-typed by construction and their bytes
  // are pinned by content-addressing, so they are NOT assumptions to
  // resolve. Filtering them keeps the assumption tree to genuine constant
  // obligations (e.g. `Nat.add_comm` becomes correctly unconditional).
  let mut checked_sorted = checked_targets.clone();
  checked_sorted.sort_unstable();
  checked_sorted.dedup();
  let mut assumptions: Vec<Address> = Vec::new();
  for t in &checked_targets {
    if let Some(c) = env.get_const(t) {
      for r in &c.refs {
        if checked_sorted.binary_search(r).is_err() && env.get_blob(r).is_none() {
          assumptions.push(r.clone());
        }
      }
    }
  }
  let assumptions_root =
    merkle_root_canonical(&assumptions).unwrap_or_else(zero_address);

  // In reuse mode, report the checked count in field_a (field_b stays 0).
  let field_a = if reuse_mode { checked_count } else { field_a };

  // Fixed 112-byte payload. First 44 bytes are the original prefix
  // (env_hash, field_a, field_b, failures) so the existing range/coherence
  // path is unchanged; the next 68 bytes carry the conditional claim
  // (subject root, assumptions root, checked count).
  ziskos::io::commit_slice(&env_hash);
  ziskos::io::commit_slice(&field_a.to_le_bytes());
  ziskos::io::commit_slice(&field_b.to_le_bytes());
  ziskos::io::commit_slice(&failures.to_le_bytes());
  ziskos::io::commit_slice(subject_root.as_bytes());
  ziskos::io::commit_slice(assumptions_root.as_bytes());
  ziskos::io::commit_slice(&checked_count.to_le_bytes());
}

/// Resolve the requested work-item range. `(0, 0)` is treated as "whole
/// env". Otherwise `end` is clamped to `total` and `start` to `end`.
fn resolve_range(start: u32, end: u32, total: u32) -> (u32, u32) {
  if start == 0 && end == 0 {
    return (0, total);
  }
  let end = end.min(total);
  let start = start.min(end);
  (start, end)
}
