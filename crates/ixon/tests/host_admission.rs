//! Cross-language host transport vectors. Parsing is not semantic admission.

use ix_common::address::Address;
use ixon::host_admission::{Kind, Policy, Statement};
use ixon::merkle::merkle_root_canonical;

const VECTORS: &str =
  include_str!("../../../Tests/Fixtures/host-admission-v1/vectors.tsv");

fn address(byte: u8) -> Address {
  Address::from_slice(&[byte; 32]).unwrap()
}

fn sample(name: &str) -> Statement {
  let (kind, spec, binding, content, main) = match name {
    "logical" => (Kind::Logical, 0, 1, 0, None),
    "logical_main" => (Kind::Logical, 1, 0, 1, Some(0)),
    "tier_empty_logical" => (
      Kind::Tiered { logical_root: None, tier_root: Some(address(0)) },
      0,
      0,
      0,
      None,
    ),
    "tier_both" => (
      Kind::Tiered {
        logical_root: Some(address(0)),
        tier_root: Some(address(1)),
      },
      1,
      0,
      0,
      Some(1),
    ),
    _ => panic!("unknown vector {name}"),
  };
  Statement {
    kind,
    host_spec_digest: address(spec),
    binding_hash: address(binding),
    content_root: address(content),
    main: main.map(address),
    policy: Policy::NoExternalArtifactAssumptions,
  }
}

fn unhex(text: &str) -> Vec<u8> {
  assert_eq!(text.len() % 2, 0);
  (0..text.len())
    .step_by(2)
    .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
    .collect()
}

#[test]
fn independent_codec_and_merkle_vectors() {
  let mut counts = (0, 0);
  for line in VECTORS.lines().filter(|line| !line.starts_with('#')) {
    let row: Vec<_> = line.split('\t').collect();
    match row.as_slice() {
      ["statement", name, hash, hex] => {
        let expected = sample(name);
        let raw = unhex(hex);
        assert_eq!(expected.to_bytes(), raw);
        assert_eq!(Statement::decode(&raw).unwrap(), expected);
        assert_eq!(expected.address().hex(), *hash);
        counts.0 += 1;
      },
      ["merkle", ids, hash] => {
        let leaves = if *ids == "-" {
          vec![]
        } else {
          ids.split(',').map(|id| address(id.parse().unwrap())).collect()
        };
        let root = merkle_root_canonical(&leaves);
        assert_eq!(root.map_or_else(|| "none".to_owned(), |r| r.hex()), *hash);
        counts.1 += 1;
      },
      _ => panic!("invalid vector row: {line}"),
    }
  }
  assert_eq!(counts, (4, 8));
}

#[test]
fn strict_envelope_and_option_tags() {
  for name in ["logical", "logical_main", "tier_empty_logical", "tier_both"] {
    let raw = sample(name).to_bytes();
    for end in 0..raw.len() {
      assert!(Statement::decode(&raw[..end]).is_err());
    }
    let mut trailing = raw.clone();
    trailing.push(0);
    assert!(Statement::decode(&trailing).is_err());
    for (index, value) in [(0, 0xe5), (4, 2), (5, 3), (6, 2), (7, 1), (104, 2)]
    {
      let mut bad = raw.clone();
      bad[index] = value;
      assert!(Statement::decode(&bad).is_err());
    }
  }
  let left = sample("tier_empty_logical");
  let mut right = left.clone();
  right.kind = Kind::Tiered {
    logical_root: Some(address(0)),
    tier_root: Some(address(0)),
  };
  assert_ne!(left.to_bytes(), right.to_bytes());
  assert_ne!(left.address(), right.address());
}
