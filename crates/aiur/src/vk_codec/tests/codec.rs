// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Transport actual full keys and adversarial v5 bytes to the total Lean codec.

use super::*;
use multi_stark::system::CircuitInputs;
use std::{fs, io};

fn parameters() -> (CommitmentParameters, FriParameters) {
  (
    CommitmentParameters { log_blowup: 1, cap_height: 0 },
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    },
  )
}

fn record(
  nodes: Vec<Node<Val>>,
  zeros: Vec<NodeId>,
  lookups: Vec<Lookup<NodeId>>,
  group: usize,
  maximum: usize,
) -> Vec<u8> {
  let circuit = Circuit {
    graph: ConstraintGraph {
      nodes,
      zeros,
      lookups,
      degrees: vec![],
      lookup_prefix_len: 0,
      max_constraint_degree: 0,
    },
    main_width: 1,
    preprocessed: None,
    preprocessed_width: 1,
    preprocessed_height: 256,
    lookup_group_size: group,
    max_constraint_degree: maximum,
    num_lookups: 0,
    stage_2_width: 0,
    num_publics: 8,
    constraint_count: 0,
  };
  let mut bytes = vec![];
  encode_circuit(&mut bytes, &circuit);
  bytes
}

fn key(records: &[Vec<u8>], commitment: Option<&[u8]>) -> Vec<u8> {
  let mut bytes = vec![];
  for parameter in [1, 0, 0, 1, 64, 0, 0] {
    push_u16(&mut bytes, parameter);
  }
  push_u16(&mut bytes, records.len());
  for record in records {
    bytes.extend_from_slice(record);
  }
  match commitment {
    None => bytes.push(0),
    Some(digests) => {
      assert_eq!(digests.len() % 32, 0);
      bytes.push(1);
      push_u16(&mut bytes, digests.len() / 32);
      bytes.extend_from_slice(digests);
    },
  }
  for index in 0..records.len() {
    push_u16(&mut bytes, if commitment.is_some() { index } else { 65535 });
  }
  bytes
}

fn every_tag_record() -> Vec<u8> {
  let mut nodes = vec![
    Node::Const(Val::ZERO),
    Node::Const(Val::ONE),
    Node::Const(Val::from_u64(65535)),
    Node::Const(Val::from_u64(65536)),
    Node::Const(-Val::ONE),
    Node::Public(7),
    Node::IsFirstRow,
    Node::IsLastRow,
    Node::IsTransition,
    Node::Add(NodeId(1), NodeId(6)),
    Node::Sub(NodeId(9), NodeId(2)),
    Node::Mul(NodeId(9), NodeId(10)),
    Node::Neg(NodeId(11)),
  ];
  for source in [Source::Preprocessed, Source::Main, Source::Stage2] {
    for offset in [RowOffset::Current, RowOffset::Next] {
      nodes.push(Node::Var(ColRef { source, offset, index: 0 }));
    }
  }
  record(
    nodes,
    vec![NodeId(12), NodeId(17), NodeId(18)],
    vec![Lookup { multiplicity: NodeId(1), args: vec![NodeId(9)] }],
    1,
    2,
  )
}

fn cases() -> Vec<Vec<u8>> {
  let (cp, fp) = parameters();
  let actual = graph_tests::graph_system();
  let mut cases = vec![to_bytes(&actual, cp, fp)];
  for inputs in [vec![], vec![CircuitInputs::default()]] {
    let system = System::new(AiurConfig::new(cp, fp), inputs).0;
    cases.push(to_bytes(&system, cp, fp));
  }
  let every_tag = every_tag_record();
  let mut small = vec![
    key(&[], None),
    key(&[], Some(&[])),
    key(std::slice::from_ref(&every_tag), None),
    key(std::slice::from_ref(&every_tag), Some(&[7; 32])),
    key(&[every_tag.clone(), every_tag.clone()], Some(&[19; 64])),
  ];
  // Constants that the decoder reduces or accepts in a nonminimal tag.
  for value in [0, 1, 65535, 65536, Val::ORDER_U64, u64::MAX] {
    let mut record = record(vec![Node::Const(Val::ONE)], vec![], vec![], 1, 1);
    record.splice(13..16, std::iter::once(1).chain(value.to_le_bytes()));
    small.push(key(&[record], None));
  }
  cases.extend(small.iter().cloned());
  for bytes in &small {
    // Every truncation and every trailing-byte value, including zeros.
    cases.extend((0..bytes.len()).map(|end| bytes[..end].to_vec()));
    for suffix in 0..=255 {
      let mut extended = bytes.clone();
      extended.push(suffix);
      cases.push(extended);
    }
  }
  let mutations = key(&[every_tag], Some(&[7; 32]));
  for offset in 14..mutations.len() {
    for value in [0, 1, 15, 16, 255] {
      let mut bytes = mutations.clone();
      bytes[offset] = value;
      cases.push(bytes);
    }
  }
  let leaf = Node::Const(Val::ONE);
  for group in [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 255] {
    for count in [0, 1, 2, 3, 7, 8, 9, 16, 17] {
      let lookups =
        vec![Lookup { multiplicity: NodeId(0), args: vec![] }; count];
      cases.push(key(&[record(vec![leaf], vec![], lookups, group, 1)], None));
    }
  }
  for node in [
    Node::Add(NodeId(0), NodeId(1)),
    Node::Sub(NodeId(1), NodeId(0)),
    Node::Mul(NodeId(0), NodeId(65535)),
    Node::Neg(NodeId(1)),
    Node::Public(8),
    Node::Public(255),
  ] {
    cases.push(key(&[record(vec![leaf, node], vec![], vec![], 1, 1)], None));
  }
  for source in [Source::Preprocessed, Source::Main, Source::Stage2] {
    for offset in [RowOffset::Current, RowOffset::Next] {
      for index in [0, 1, 2, 65535] {
        let var = Node::Var(ColRef { source, offset, index });
        for lookups in
          [vec![], vec![Lookup { multiplicity: NodeId(1), args: vec![] }]]
        {
          cases
            .push(key(&[record(vec![var, leaf], vec![], lookups, 1, 1)], None));
        }
      }
    }
  }
  for invalid in [1, 65535] {
    cases.push(key(
      &[record(vec![leaf], vec![NodeId(invalid)], vec![], 1, 1)],
      None,
    ));
    for lookup in [
      Lookup { multiplicity: NodeId(invalid), args: vec![] },
      Lookup { multiplicity: NodeId(0), args: vec![NodeId(invalid)] },
    ] {
      cases.push(key(&[record(vec![leaf], vec![], vec![lookup], 1, 1)], None));
    }
  }
  for maximum in [0, 1, 2, 65535] {
    cases.push(key(
      &[record(vec![Node::IsFirstRow], vec![], vec![], 1, maximum)],
      None,
    ));
  }
  let mut nodes = vec![Node::IsFirstRow];
  for index in 0..32 {
    nodes.push(Node::Mul(NodeId(index), NodeId(index)));
  }
  cases.push(key(&[record(nodes.clone(), vec![], vec![], 1, 1)], None));
  nodes.pop();
  for group in 1..=8 {
    let lookup = Lookup { multiplicity: NodeId(31), args: vec![NodeId(31)] };
    cases.push(key(
      &[record(nodes.clone(), vec![], vec![lookup; group], group, 1)],
      None,
    ));
  }
  // The largest serialized degree is valid, even though this decoder does
  // not check the chosen PCS's quotient budget (System::new does).
  nodes.truncate(16);
  let mut root = 15;
  for power in (0..15).rev() {
    nodes.push(Node::Mul(NodeId(root), NodeId(power)));
    root += 1;
  }
  let mut maximum = record(nodes, vec![NodeId(root)], vec![], 8, 65535);
  maximum[0..4].copy_from_slice(&[255; 4]);
  maximum[4..8].copy_from_slice(&[255; 4]);
  cases.push(key(&[maximum], Some(&[255; 32])));
  cases
}

fn write_nat(out: &mut Vec<u8>, value: usize) {
  out.extend_from_slice(&(value as u64).to_le_bytes());
}

fn write_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
  write_nat(out, bytes.len());
  out.extend_from_slice(bytes);
}

#[test]
fn rejects_invalid_commitment_cap_sizes_without_panicking() {
  for count in [0, 3, 5, 7] {
    let bytes = key(&[], Some(&vec![0; count * 32]));
    let decoded = std::panic::catch_unwind(|| from_bytes(&bytes));
    assert!(decoded.is_ok(), "invalid cap size must return an error");
    assert!(decoded.unwrap().is_err(), "invalid cap size must be rejected");
  }
}

#[test]
fn key_codec_snapshot() -> io::Result<()> {
  let cases = cases();
  let mut out = b"Aiur key codec v1\n".to_vec();
  write_nat(&mut out, cases.len());
  let mut accepted = 0;
  let mut noncanonical = 0;
  let mut circuits = 0;
  for bytes in &cases {
    write_bytes(&mut out, bytes);
    match from_bytes(bytes) {
      Err(_) => out.push(0),
      Ok((system, cp, fp)) => {
        out.push(1);
        accepted += 1;
        let canonical = to_bytes(&system, cp, fp);
        noncanonical += usize::from(canonical != *bytes);
        write_bytes(&mut out, &canonical);
        write_nat(&mut out, system.circuits.len());
        for circuit in system.circuits {
          circuits += 1;
          for value in [
            circuit.main_width,
            circuit.preprocessed_width,
            circuit.preprocessed_height,
            circuit.max_constraint_degree,
            circuit.lookup_group_size,
            circuit.stage_2_width,
            circuit.num_publics,
            circuit.constraint_count,
            circuit.graph.lookup_prefix_len,
            circuit.graph.max_constraint_degree as usize,
          ] {
            write_nat(&mut out, value);
          }
          write_nat(&mut out, circuit.graph.degrees.len());
          for degree in circuit.graph.degrees {
            write_nat(&mut out, degree as usize);
          }
        }
      },
    }
  }
  assert!(accepted > 100 && noncanonical >= 5 && circuits > 100);
  if let Ok(path) = std::env::var("IX_KEY_CODEC_SNAPSHOT") {
    fs::write(path, out)?;
  }
  println!(
    "key codec: {} cases, {accepted} accepted, {noncanonical} noncanonical, {circuits} circuits",
    cases.len(),
  );
  Ok(())
}
