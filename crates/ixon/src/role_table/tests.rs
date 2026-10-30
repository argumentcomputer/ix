use super::*;

fn addr(seed: u8) -> Address {
  Address::from_slice(&std::array::from_fn::<_, 32, _>(|i| {
    seed.wrapping_add(u8::try_from(i).unwrap())
  }))
  .unwrap()
}

// Independently construct Rust values; do not derive expectations by decoding.
fn cases() -> Vec<(String, RoleTable)> {
  let mut cases = vec![
    (
      "empty-0".into(),
      RoleTable { version: 0, bound: vec![], evidence: vec![] },
    ),
    (
      "empty-255".into(),
      RoleTable { version: 255, bound: vec![], evidence: vec![] },
    ),
    (
      "all-roles".into(),
      RoleTable {
        version: 2,
        bound: Role::ALL.iter().map(|r| (*r, addr(r.index()))).collect(),
        evidence: vec![],
      },
    ),
    (
      "wire-only".into(),
      RoleTable {
        version: 0,
        bound: vec![(Role::Nat, addr(7)), (Role::NatZero, addr(7))],
        evidence: vec![
          (Role::Eq, vec![Evidence::DefEq, Evidence::Proof(addr(241))]),
          (Role::SorryAx, vec![]),
        ],
      },
    ),
    (
      "evidence-255".into(),
      RoleTable {
        version: 2,
        bound: vec![],
        evidence: vec![(
          Role::NatDiv,
          (0..255)
            .map(|i| {
              if i % 2 == 0 {
                Evidence::DefEq
              } else {
                Evidence::Proof(addr(i))
              }
            })
            .collect(),
        )],
      },
    ),
  ];
  for r in Role::ALL {
    cases.push((
      format!("role-{}", r.lean_name()),
      RoleTable {
        version: r.index(),
        bound: vec![(r, addr(r.index()))],
        evidence: vec![],
      },
    ));
  }
  cases
}

fn unhex(hex: &str) -> Vec<u8> {
  assert_eq!(hex.len() % 2, 0);
  hex
    .as_bytes()
    .as_chunks::<2>()
    .0
    .iter()
    .map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(), 16).unwrap())
    .collect()
}

#[test]
fn lean_interoperability_both_directions() {
  let lines: Vec<_> =
    include_str!("../../../../Tests/Fixtures/ixon-v4/role-table.tsv")
      .lines()
      .filter(|l| !l.starts_with('#') && !l.is_empty())
      .collect();
  let cases = cases();
  assert_eq!(cases.len(), 5 + Role::ALL.len());
  assert_eq!(lines.len(), cases.len());
  for ((name, table), line) in cases.iter().zip(lines) {
    let (label, hex) = line.split_once('\t').unwrap();
    assert_eq!(name, label);
    let lean_bytes = unhex(hex);
    assert_eq!(table.to_bytes().unwrap(), lean_bytes, "Rust encode: {name}");
    assert_eq!(
      RoleTable::from_bytes(&lean_bytes).unwrap(),
      *table,
      "Lean decode: {name}"
    );
  }
  for (i, role) in Role::ALL.iter().enumerate() {
    assert_eq!(usize::from(role.index()), i);
    assert_eq!(Role::from_index(role.index()), Some(*role));
  }
  for i in (Role::ALL.len() as u8)..=255 {
    assert_eq!(Role::from_index(i), None);
  }
}

#[test]
fn rejects_all_truncations_and_trailing_bytes() {
  for (name, table) in cases() {
    let bytes = table.to_bytes().unwrap();
    for len in 0..bytes.len() {
      assert!(
        RoleTable::from_bytes(&bytes[..len]).is_err(),
        "{name}: prefix {len}"
      );
    }
    for suffix in [vec![0], vec![0xe8, 3, 0, 0, 0]] {
      let mut extended = bytes.clone();
      extended.extend(suffix);
      assert!(
        RoleTable::from_bytes(&extended).is_err(),
        "{name}: trailing bytes"
      );
    }
  }
}

#[test]
fn rejects_malformed_tags_roles_and_ordering() {
  let unknown = Role::ALL.len() as u8;
  for bytes in [
    vec![0xe8, 2, 2, 0, 0],                // old profile tag
    vec![0xe4, 3, 2, 0, 0],                // env tag
    vec![0xe8, 3, 2, 0, 1, unknown, 0],    // unknown evidence role
    vec![0xe8, 3, 2, 0, 1, 0, 1, 2],       // unknown evidence tag
    vec![0xe8, 3, 2, 0, 2, 1, 0, 0, 0],    // descending evidence
    vec![0xe8, 3, 2, 0, 2, 0, 0, 0, 0],    // duplicate evidence role
  ] {
    assert!(RoleTable::from_bytes(&bytes).is_err(), "{bytes:?}");
  }
  for roles in [[unknown, unknown + 1], [1, 0], [0, 0]] {
    let mut bytes = vec![0xe8, 3, 2, 2];
    for r in roles {
      bytes.push(r);
      bytes.extend_from_slice(addr(0).as_bytes());
    }
    bytes.push(0);
    assert!(RoleTable::from_bytes(&bytes).is_err());
  }
}

#[test]
fn writer_refuses_noncanonical_tables_without_repairing_them() {
  let empty = RoleTable { version: 2, bound: vec![], evidence: vec![] };
  for roles in [[Role::NatZero, Role::Nat], [Role::Nat, Role::Nat]] {
    let table = RoleTable {
      bound: roles.iter().map(|r| (*r, addr(0))).collect(),
      ..empty.clone()
    };
    assert!(table.to_bytes().is_err());
    let table = RoleTable {
      evidence: roles.iter().map(|r| (*r, vec![])).collect(),
      ..empty.clone()
    };
    assert!(table.to_bytes().is_err());
  }
  for table in [
    RoleTable { bound: vec![(Role::Nat, addr(0)); 256], ..empty.clone() },
    RoleTable { evidence: vec![(Role::Nat, vec![]); 256], ..empty.clone() },
    RoleTable {
      evidence: vec![(Role::Nat, vec![Evidence::DefEq; 256])],
      ..empty
    },
  ] {
    assert!(table.to_bytes().is_err());
  }
}
