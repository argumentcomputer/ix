//! Zisk aggregation guest (in-circuit assumption resolution).
//!
//! Verifies N child proofs and *binds* them: it reads each verified child's
//! committed claim (program vk + subject/assumptions roots) out of its
//! exposed publics, **pins** the program vk to an allowed set (so a child can
//! only be a real shard/agg proof, not an attacker's trivial program), and
//! combines the children's claims. The reused constants are thus *verified*,
//! not trusted.
//!
//! Two combination modes, selected by the first stdin word:
//!
//! - **Mode 0 (join fold, legacy)**: subjects and assumptions are folded as
//!   opaque roots with left-associative `merkle_join`. O(1) per child, but
//!   assumptions are never discharged — a child's assumption survives to the
//!   final root even when a sibling's subject proves it.
//!
//! - **Mode 1 (set discharge)**: the host supplies, per child, the *preimage
//!   address lists* behind its subject and assumptions roots as untrusted
//!   witness. The guest re-derives each list's canonical merkle root and
//!   asserts it equals the child's committed root (so forged lists cannot
//!   pass), then computes
//!     `subject     = canonical( ∪ subjects )`
//!     `assumptions = canonical( ∪ assumptions ∖ ∪ subjects )`
//!   — every assumption proven by any sibling is **discharged** here, at the
//!   lowest level of the aggregation tree where producer and consumer meet.
//!   When the whole env is folded, the final assumptions root collapses to
//!   the zero sentinel (no outstanding obligations): an *unconditional*
//!   claim. Mode-1 outputs are canonical set commitments, so agg-of-agg
//!   witness verification is uniform at every level.
//!
//! Input (bincode-framed via `ziskos::io::read`):
//!   1. `u32` mode (0 or 1).
//!   2. `u32` num_vks, then that many `Vec<u8>` (32-byte) ALLOWED program vks.
//!      POSITIONAL CONVENTION: index 0 is the LEAF (shard) vk; every index
//!      ≥ 1 is an aggregation vk. The order is load-bearing and committed
//!      (the id below hashes the concatenation in order), so an external
//!      verifier that checks the id against the known-good [SHARD_VK,
//!      AGG_VK] hash also pins the convention.
//!   3. `u32` num_proofs, then that many `Vec<u8>` proof blobs.
//!   4. Mode 1 only: per child, `Vec<u8>` packed subject addresses then
//!      `Vec<u8>` packed assumption addresses (32 bytes each, any order —
//!      the canonical root sorts and dedups).
//!
//! Per-child checks, on top of proof verification: the program vk must be in
//! the allowed set; the committed `failures` word (slot 10) must be 0 — an
//! aggregate must never launder a kernel-rejected constant into a
//! `failures=0` root; and a child that is itself an aggregate (vk index ≥ 1)
//! must commit THIS instance's vks id — without that recursive pin, an
//! agg-of-1 built against a rogue allowed set (containing an arbitrary
//! program's vk) would fold under an honest-looking root, since only its
//! program vk (the shared AGG vk) is checked here.
//!
//! Output (committed, leaf-COMPATIBLE 112-byte layout so an aggregate is
//! parseable exactly like a leaf — enabling agg-of-agg):
//!   - [0..32)   blake3(allowed vks)   (id; the leaf's `env_hash` slot)
//!   - [32..36)  num_proofs            (field_a)
//!   - [36..40)  mode                  (field_b)
//!   - [40..44)  0                     (failures; every child asserted 0)
//!   - [44..76)  combined subject root
//!   - [76..108) combined assumptions root (mode 1: post-discharge)
//!   - [108..112) num_proofs           (checked_count)
//!
//! Zisk proof word layout (as `&[u64]`; unchanged v0.18 → v1.0.0-alpha,
//! re-verified against v1.0.0-alpha leaf proofs):
//!   [minimal(1)][n_publics(1)][program_vk(4)][zisk_publics(64)][proof…][vk(4)]
//! so program_vk = words[2..6]; the leaf's committed publics occupy the
//! zisk_publics region (one u32 slot per word, low 32 bits) starting at
//! words[6]. Subject = leaf slots 11..19, assumptions = slots 19..27.

#![no_main]
ziskos::entrypoint!(main);

extern crate alloc;
use alloc::vec::Vec;

use ix_common::address::Address;
use ixon::merkle::{merkle_join, merkle_root_canonical, zero_address};

/// Reconstruct a 32-byte address committed at leaf-publics `slot_start`
/// (8 consecutive u32 slots). `words` is the whole proof as u64 words; the
/// zisk_publics region begins at word index 6, one u32 slot per word.
fn read_pub_addr(words: &[u64], slot_start: usize) -> Address {
  let mut b = [0u8; 32];
  for j in 0..8 {
    let w = words[6 + slot_start + j] as u32; // low 32 bits = the committed u32 slot
    b[j * 4..j * 4 + 4].copy_from_slice(&w.to_le_bytes());
  }
  Address::from_slice(&b).expect("publics address")
}

fn main() {
  // 0. Combination mode.
  let mode: u32 = ziskos::io::read();
  assert!(mode <= 1, "unknown aggregation mode {mode}");

  // 1. Allowed program vks.
  let num_vks: u32 = ziskos::io::read();
  let mut allowed: Vec<[u64; 4]> = Vec::with_capacity(num_vks as usize);
  let mut allowed_bytes: Vec<u8> = Vec::with_capacity(num_vks as usize * 32);
  for _ in 0..num_vks {
    let vk: Vec<u8> = ziskos::io::read();
    let mut w = [0u64; 4];
    for j in 0..4 {
      w[j] = u64::from_le_bytes(vk[j * 8..j * 8 + 8].try_into().expect("vk word"));
    }
    allowed.push(w);
    allowed_bytes.extend_from_slice(&vk);
  }
  let vks_id = Address::hash(&allowed_bytes);

  // 2. Verify + bind each child proof, collecting its committed roots.
  let num_proofs: u32 = ziskos::io::read();
  let mut child_roots: Vec<(Address, Address)> =
    Vec::with_capacity(num_proofs as usize);
  for i in 0..num_proofs {
    let proof: Vec<u8> = ziskos::io::read();
    let valid = unsafe { ziskos::zisklib::verify_zisk_proof_c(proof.as_ptr(), proof.len()) };
    if !valid {
      panic!("child proof {i} verification failed");
    }
    // Parse the proof's u64 words via a copy (the deserialized `Vec<u8>` may
    // not be 8-aligned for a direct `align_to`).
    let words: Vec<u64> = proof
      .chunks_exact(8)
      .map(|c| u64::from_le_bytes(c.try_into().expect("u64 chunk")))
      .collect();
    // Pin the program vk (words[2..6]) to the allowed set — without this, the
    // committed publics carry no meaning (any valid proof of any program
    // would pass).
    let vk = [words[2], words[3], words[4], words[5]];
    let Some(vk_idx) = allowed.iter().position(|a| *a == vk) else {
      panic!("child proof {i}: program vk not in allowed set");
    };
    // A child that is itself an aggregate must have pinned its own children
    // against THIS allowed set (uniform down the tree): its committed id
    // (slots 0..8) is blake3(its allowed vks), which must equal ours.
    if vk_idx >= 1 && read_pub_addr(&words, 0) != vks_id {
      panic!("child proof {i}: aggregate child pinned a different vk set");
    }
    // Never fold a failed leaf: this instance commits failures=0, so a
    // nonzero child failures word would otherwise be erased from the claim.
    let failures = words[6 + 10] as u32;
    if failures != 0 {
      panic!("child proof {i}: committed failures={failures}");
    }
    let s = read_pub_addr(&words, 11);
    let a = read_pub_addr(&words, 19);
    child_roots.push((s, a));
  }

  // 3. Combine the children's claims.
  let (subject, assumptions) = if mode == 0 {
    // Join fold: opaque-root composition, no discharge.
    let mut subject: Option<Address> = None;
    let mut assumptions: Option<Address> = None;
    for (s, a) in &child_roots {
      subject = Some(match subject {
        None => s.clone(),
        Some(p) => merkle_join(&p, s),
      });
      assumptions = Some(match assumptions {
        None => a.clone(),
        Some(p) => merkle_join(&p, a),
      });
    }
    (
      subject.unwrap_or_else(zero_address),
      assumptions.unwrap_or_else(zero_address),
    )
  } else {
    // Set discharge: verify each child's witness preimages against its
    // committed roots, then resolve assumptions against sibling subjects.
    let mut subj_union: Vec<Address> = Vec::new();
    let mut asm_union: Vec<Address> = Vec::new();
    for (i, (s_root, a_root)) in child_roots.iter().enumerate() {
      let s_blob: Vec<u8> = ziskos::io::read();
      let a_blob: Vec<u8> = ziskos::io::read();
      let s_list: Vec<Address> = Address::unpack(&s_blob).collect();
      let a_list: Vec<Address> = Address::unpack(&a_blob).collect();
      // The witness is untrusted: its canonical root must reproduce the
      // root the (verified) child committed, or the lists are forged.
      let s_check = merkle_root_canonical(&s_list).unwrap_or_else(zero_address);
      if s_check != *s_root {
        panic!("child {i}: subject witness does not match committed root");
      }
      let a_check = merkle_root_canonical(&a_list).unwrap_or_else(zero_address);
      if a_check != *a_root {
        panic!("child {i}: assumptions witness does not match committed root");
      }
      subj_union.extend(s_list);
      asm_union.extend(a_list);
    }
    subj_union.sort_unstable();
    subj_union.dedup();
    asm_union.sort_unstable();
    asm_union.dedup();
    // Discharge: an assumption proven by any child's subject is resolved.
    let outstanding: Vec<Address> = asm_union
      .into_iter()
      .filter(|a| subj_union.binary_search(a).is_err())
      .collect();
    (
      merkle_root_canonical(&subj_union).unwrap_or_else(zero_address),
      merkle_root_canonical(&outstanding).unwrap_or_else(zero_address),
    )
  };

  // Leaf-compatible 112-byte layout (see module docs).
  ziskos::io::commit_slice(vks_id.as_bytes());
  ziskos::io::commit_slice(&num_proofs.to_le_bytes());
  ziskos::io::commit_slice(&mode.to_le_bytes());
  ziskos::io::commit_slice(&0u32.to_le_bytes());
  ziskos::io::commit_slice(subject.as_bytes());
  ziskos::io::commit_slice(assumptions.as_bytes());
  ziskos::io::commit_slice(&num_proofs.to_le_bytes());
}
