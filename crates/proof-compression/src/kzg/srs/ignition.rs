//! Import Ignition transcripts using an independently trusted source manifest.
//!
//! A transcript's embedded checksum establishes integrity, not ceremony
//! provenance. The caller pins a manifest of complete source-file digests;
//! inspecting local downloads only produces a candidate for that trust decision.
//! Import checks all pinned file bytes and the retained powers, then publishes
//! a prefix cache atomically. Cache loads require the import receipt separately.
//! Ignition's shifted basis starts at `tau * G1`, with public degree `M - 1`
//! for `M` published entries, independent of the retained prefix.

mod admission;
mod cache;
mod points;
mod source;

pub use admission::IgnitionAdmission;
#[cfg(test)]
pub(crate) use admission::{test_admission, test_admission_cache};
pub use cache::{
  IgnitionCacheIdentity, load_ignition_cache, load_ignition_cache_with_identity,
};
pub use source::{
  Contribution, SHIFTED_TAU_BASIS, SOURCE_FORMAT, SourceManifest, Transcript,
  inspect_ignition_source, read_source_manifest,
};

use super::super::curve::{Fr, G1Affine, G1Projective, G2Affine, PairingCurve};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field, PrimeField, Zero};
use std::{io, path::Path};

pub const MAX_G1_POINTS: usize = 100_800_000;
pub const MAX_PREFIX_LEN: usize = 1 << 26;
pub const IGNITION_MANIFEST_URL: &str =
  "https://aztec-ignition.s3.amazonaws.com/MAIN%20IGNITION/manifest.json";
pub const FINAL_POSITION: u32 = 197;
pub const FINAL_ADDRESS: &str = "0xa57ec000b7fb9ea9b0119efdee0b8f15f895c2f3";
pub const PREDECESSOR_POSITION: u32 = 196;
pub const PREDECESSOR_ADDRESS: &str =
  "0x9c3f372a2aacc0d7272f56a4664311b7647b0031";

#[derive(Clone, Copy, Debug)]
struct Anchors {
  g1: [G1Affine; 2],
  tau_g2: G2Affine,
  contribution_g2: G2Affine,
}

fn invalid(
  message: impl Into<Box<dyn std::error::Error + Send + Sync>>,
) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message)
}

fn validate_prefix(prefix_len: usize, total: usize) -> io::Result<()> {
  if prefix_len < 2
    || !prefix_len.is_power_of_two()
    || prefix_len > MAX_PREFIX_LEN
    || prefix_len > total
  {
    return Err(invalid("invalid Ignition prefix length"));
  }
  Ok(())
}

fn validate_anchors(anchors: &Anchors) -> io::Result<()> {
  if anchors.g1.iter().any(|point| {
    point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
  }) || [anchors.tau_g2, anchors.contribution_g2].iter().any(|point| {
    point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
  }) {
    return Err(invalid("invalid Ignition anchor"));
  }
  if !PairingCurve::multi_pairing(
    [anchors.g1[0], -G1Affine::generator()],
    [G2Affine::generator(), anchors.tau_g2],
  )
  .is_zero()
  {
    return Err(invalid(
      "Ignition first power does not match its shifted basis",
    ));
  }
  if !PairingCurve::multi_pairing(
    [anchors.g1[1], -anchors.g1[0]],
    [G2Affine::generator(), anchors.tau_g2],
  )
  .is_zero()
  {
    return Err(invalid("Ignition anchors are not successive powers"));
  }
  Ok(())
}

/// Authenticate complete local source files and create a reusable prefix cache.
///
/// `trusted_source_manifest` is the BLAKE3 of independently trusted manifest
/// bytes, not a digest read from the same untrusted download. All selected
/// transcript files are hashed, including bytes beyond the retained prefix.
/// An optional predecessor is checked against its own pinned files and powers,
/// followed by a contribution-link pairing. This is not a replay of the full
/// ceremony or verification of participant signatures. Memory is bounded by
/// chunks; the destination must not exist.
pub fn import_ignition_transcripts(
  source_root: &Path,
  source_manifest: &Path,
  trusted_source_manifest: [u8; 32],
  cache: &Path,
  prefix_len: usize,
) -> io::Result<IgnitionCacheIdentity> {
  let manifest =
    read_source_manifest(source_manifest, trusted_source_manifest)?;
  validate_prefix(prefix_len, manifest.num_g1_points as usize)?;
  let mut output = cache::CacheWriter::create(
    cache,
    prefix_len,
    manifest.public_setup()?,
    trusted_source_manifest,
  )?;
  let previous = if let Some(previous) = &manifest.predecessor {
    let mut progression = ProgressionCheck::new(
      trusted_source_manifest,
      prefix_len,
      previous.position,
    );
    let anchors = source::stream_contribution(
      source_root,
      &manifest,
      previous,
      prefix_len,
      |points| progression.absorb(points),
    )?;
    validate_anchors(&anchors)?;
    progression.verify(&anchors)?;
    Some(anchors)
  } else {
    None
  };
  let mut progression = ProgressionCheck::new(
    trusted_source_manifest,
    prefix_len,
    manifest.contribution.position,
  );
  let anchors = source::stream_contribution(
    source_root,
    &manifest,
    &manifest.contribution,
    prefix_len,
    |points| {
      progression.absorb(points)?;
      output.push(points)
    },
  )?;
  validate_anchors(&anchors)?;
  progression.verify(&anchors)?;
  if let Some(previous) = previous
    && !PairingCurve::multi_pairing(
      [anchors.g1[0], -previous.g1[0]],
      [G2Affine::generator(), anchors.contribution_g2],
    )
    .is_zero()
  {
    return Err(invalid(
      "Ignition contribution does not follow its predecessor",
    ));
  }
  output.finish(&anchors)
}

struct ProgressionCheck {
  r: Fr,
  next_power: Fr,
  previous: Option<G1Affine>,
  low: G1Projective,
  high: G1Projective,
  expected: usize,
  seen: usize,
}

impl ProgressionCheck {
  fn new(source_manifest: [u8; 32], prefix_len: usize, position: u32) -> Self {
    let mut hash = blake3::Hasher::new();
    hash.update(b"ix/bn254/ignition-prefix-progression/v1");
    hash.update(&source_manifest);
    hash.update(&(prefix_len as u64).to_le_bytes());
    hash.update(&position.to_le_bytes());
    let mut reader = hash.finalize_xof();
    let r = loop {
      let mut wide = [0; 64];
      reader.fill(&mut wide);
      let candidate = Fr::from_le_bytes_mod_order(&wide);
      if !candidate.is_zero() {
        break candidate;
      }
    };
    Self {
      r,
      next_power: Fr::ONE,
      previous: None,
      low: G1Projective::zero(),
      high: G1Projective::zero(),
      expected: prefix_len,
      seen: 0,
    }
  }

  fn absorb(&mut self, points: &[G1Affine]) -> io::Result<()> {
    if points.is_empty() {
      return Ok(());
    }
    self.seen = self
      .seen
      .checked_add(points.len())
      .filter(|seen| *seen <= self.expected)
      .ok_or_else(|| invalid("too many Ignition prefix points"))?;
    if let Some(previous) = self.previous {
      // Adjacency across transcript and chunk boundaries is part of the relation.
      self.low += previous * self.next_power;
      self.high += points[0] * self.next_power;
      self.next_power *= self.r;
    }
    if points.len() > 1 {
      let scalars: Vec<_> = (1..points.len())
        .map(|_| {
          let scalar = self.next_power;
          self.next_power *= self.r;
          scalar
        })
        .collect();
      self.low += G1Projective::msm(&points[..points.len() - 1], &scalars)
        .expect("equal lengths");
      self.high +=
        G1Projective::msm(&points[1..], &scalars).expect("equal lengths");
    }
    self.previous = points.last().copied();
    Ok(())
  }

  fn verify(self, anchors: &Anchors) -> io::Result<()> {
    if self.seen != self.expected {
      return Err(invalid("incomplete Ignition prefix"));
    }
    if !PairingCurve::multi_pairing(
      [self.high.into_affine(), (-self.low).into_affine()],
      [G2Affine::generator(), anchors.tau_g2],
    )
    .is_zero()
    {
      return Err(invalid("Ignition prefix is not one tau progression"));
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests;
