//! Zisk aggregation guest (in-circuit assumption resolution).
//!
//! Verifies N child proofs and *binds* them: it reads each verified child's
//! committed claim (program vk + subject/assumptions roots) out of its
//! exposed publics, **pins** the program vk to an allowed set (so a child can
//! only be a real shard/agg proof, not an attacker's trivial program), and
//! folds the subjects/assumptions with the same canonical merkle ops the leaf
//! guest uses. The reused constants are thus *verified*, not trusted.
//!
//! Input (bincode-framed via `ziskos::io::read`):
//!   1. `u32` num_vks, then that many `Vec<u8>` (32-byte) ALLOWED program vks
//!      (e.g. [SHARD_VK] for a single-level fold; [SHARD_VK, AGG_VK] for
//!      tree-fold). Committed so an external verifier checks them against the
//!      real program vks.
//!   2. `u32` num_proofs, then that many `Vec<u8>` proof blobs.
//!
//! Output (committed, leaf-COMPATIBLE 112-byte layout so an aggregate is
//! parseable exactly like a leaf — enabling agg-of-agg):
//!   - [0..32)   blake3(allowed vks)   (id; the leaf's `env_hash` slot)
//!   - [32..36)  num_proofs            (field_a)
//!   - [36..40)  0                     (field_b)
//!   - [40..44)  0                     (failures)
//!   - [44..76)  combined subject root (merkle_join of children's subjects)
//!   - [76..108) combined assumptions root
//!   - [108..112) num_proofs           (checked_count)
//!
//! v0.18 proof word layout (as `&[u64]`):
//!   [minimal(1)][n_publics(1)][program_vk(4)][zisk_publics(64)][proof…][vk(4)]
//! so program_vk = words[2..6]; the leaf's committed publics occupy the
//! zisk_publics region (one u32 slot per word, low 32 bits) starting at
//! words[6]. Subject = leaf slots 11..19, assumptions = slots 19..27.

#![no_main]
ziskos::entrypoint!(main);

extern crate alloc;
use alloc::vec::Vec;

use ix_common::address::Address;
use ixon::merkle::{merkle_join, zero_address};

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

  // 2. Verify + bind each child proof.
  let num_proofs: u32 = ziskos::io::read();
  let mut subject: Option<Address> = None;
  let mut assumptions: Option<Address> = None;
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
    if !allowed.iter().any(|a| *a == vk) {
      panic!("child proof {i}: program vk not in allowed set");
    }
    let s = read_pub_addr(&words, 11);
    let a = read_pub_addr(&words, 19);
    subject = Some(match subject {
      None => s,
      Some(p) => merkle_join(&p, &s),
    });
    assumptions = Some(match assumptions {
      None => a,
      Some(p) => merkle_join(&p, &a),
    });
  }

  let subject = subject.unwrap_or_else(zero_address);
  let assumptions = assumptions.unwrap_or_else(zero_address);
  let vks_id = Address::hash(&allowed_bytes);

  // Leaf-compatible 112-byte layout (see module docs).
  ziskos::io::commit_slice(vks_id.as_bytes());
  ziskos::io::commit_slice(&num_proofs.to_le_bytes());
  ziskos::io::commit_slice(&0u32.to_le_bytes());
  ziskos::io::commit_slice(&0u32.to_le_bytes());
  ziskos::io::commit_slice(subject.as_bytes());
  ziskos::io::commit_slice(assumptions.as_bytes());
  ziskos::io::commit_slice(&num_proofs.to_le_bytes());
}
