use super::*;
use crate::{
  hash::pack_bytes,
  ixby::bits::{fill_words, read_words},
};
use flock_prover::{circuit::builder::GateType, union::UnionInstance};
fn data(n: usize) -> Vec<u8> {
  (0..n).map(|i| (i.wrapping_mul(197) ^ (i >> 9)) as u8).collect()
}
fn eval(g: &CommitmentBridgeGate, input: &[F128]) -> Vec<F128> {
  let mut out = Vec::new();
  g.eval(input, &(), &mut out);
  out
}
fn batches(
  domain: ArtifactDomain,
  bytes: &[u8],
  parent: [F128; 2],
  setup: &CompiledCommitmentBridge,
) -> Vec<CommitmentBridgeAdvice> {
  let mut walk = CommitmentBridgeWitness::new(domain, bytes, parent).unwrap();
  let mut result: Vec<CommitmentBridgeAdvice> = Vec::new();
  while let Some(a) = walk.next_batch().unwrap() {
    setup.check_advice(&a).unwrap();
    if let Some(p) = result.last() {
      assert_eq!(p.statement.shared(), a.statement.shared());
      assert_eq!(p.statement.final_state(), a.statement.initial());
    }
    result.push(a);
  }
  assert_eq!(result.len(), (bytes.len() + 48).div_ceil(1024));
  let mut whole = *result[0].statement.words();
  whole[8] = result.last().unwrap().statement.final_state();
  CommitmentBridgeStatement::from_words(&whole)
    .unwrap()
    .check_complete()
    .unwrap();
  result
}
#[test]
fn bridge_covers_empty_padding_and_prefix_shift_at_every_chunk_boundary() {
  let parent = [F128::new(17, 31), F128::new(123, 456)];
  for domain in
    [ArtifactDomain::Program, ArtifactDomain::Input, ArtifactDomain::Output]
  {
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    for n in [0, 1, 975, 976, 977, 1023, 1024, 1025, 2048, 2049, 3077] {
      let bytes = data(n);
      let batch = batches(domain, &bytes, parent, &setup);
      let mut message = b"IxBy/commit/v0\0".to_vec();
      message.push(domain as u8);
      for p in parent {
        message.extend(p.lo.to_le_bytes());
        message.extend(p.hi.to_le_bytes());
      }
      message.extend(&bytes);
      let h = blake3::hash(&message);
      assert_eq!(
        batch[0].statement.words()[5..7],
        [pack_bytes(&h.as_bytes()[..16]), pack_bytes(&h.as_bytes()[16..])]
      );
      if n == 2049 && domain == ArtifactDomain::Program {
        for at in [
          0,
          1,
          3,
          5,
          7,
          8,
          8 + 64,
          8 + 92,
          8 + 2 * 92,
          8 + 3 * 92,
          8 + 3 * 92 + 30,
        ] {
          let mut bad = batch[1].clone();
          bad.private[at] += F128::ONE;
          assert!(setup.check_advice(&bad).is_err(), "private {at}");
        }
        let union =
          UnionInstance::new(&setup.shape.registry, setup.shape.counts.clone());
        eprintln!(
          "commitment bridge M={} dense={}",
          union.dense_m(),
          union.dense_words()
        );
      }
    }
  }
}
#[test]
fn bridge_controls_and_transformed_words_have_exact_rows_and_padding() {
  for op in [CommitmentBridgeOp::Control, CommitmentBridgeOp::Copy] {
    let g = CommitmentBridgeGate::new(3, ArtifactDomain::Output, op).unwrap();
    let table = g.r1cs();
    let mut rows = Vec::new();
    let inputs = if op == CommitmentBridgeOp::Control {
      [0u64, 976, 977, 1024, 2048, (1 << 24) - 48, 1 << 24]
        .into_iter()
        .flat_map(|n| {
          [0, (n + 47) >> 10]
            .map(move |i| vec![F128::new(n, 0), F128::new(i, 0)])
        })
        .collect::<Vec<_>>()
    } else {
      [0, 1, 16384]
        .into_iter()
        .flat_map(|index| {
          [0, 1].map(move |next| {
            let mut row =
              (0..132).map(|i| F128::new(i, !i)).collect::<Vec<_>>();
            row[0] = F128::new(index, 0);
            row[3] = F128::new(next, 0);
            row
          })
        })
        .collect()
    };
    for input in &inputs {
      let out = eval(&g, input);
      assert_eq!(out.last(), Some(&F128::ZERO));
      if op == CommitmentBridgeOp::Control {
        let n = input[0].lo;
        let i = input[1].lo;
        let last = n.saturating_sub(1) >> 10;
        assert_eq!(
          &out[..7],
          &[
            i.saturating_sub(1),
            i.min(last),
            last,
            n + 48,
            i + 1,
            u64::from(i <= last),
            (n + 47) >> 10
          ]
          .map(|v| F128::new(v, 0))
        );
      } else {
        for (i, value) in out.iter().take(64).enumerate() {
          let expected = if input[0] == F128::ZERO {
            match i {
              0 => pack_bytes(&ArtifactDomain::Output.prefix()),
              1 => input[1],
              2 => input[2],
              _ => input[4 + i - 3],
            }
          } else if i < 3 {
            input[4 + 61 + i]
          } else if input[3] == F128::ONE {
            input[68 + i - 3]
          } else {
            F128::ZERO
          };
          assert_eq!(*value, expected);
        }
      }
      let mut bits = vec![false; table.n()];
      g.plan().fill_row(&mut bits[..g.plan().k()], |b| fill_words(input, b));
      assert!(table.satisfies(&bits));
      assert_eq!(read_words(&bits, input.len(), out.len()), out);
      for at in input.len()..input.len() + out.len() {
        for bit in [0, 63, 64, 127] {
          bits[128 * at + bit] ^= true;
          assert!(!table.satisfies(&bits));
          bits[128 * at + bit] ^= true;
        }
      }
      rows.push(CommitmentBridgeRow(input.clone()));
    }
    for at in
      if op == CommitmentBridgeOp::Control { vec![0, 1] } else { vec![0, 3] }
    {
      let mut bad = inputs[0].clone();
      bad[at].hi = 1;
      assert_eq!(eval(&g, &bad).last(), Some(&F128::ONE));
    }
    let rows = rows.into_iter().take(7).collect::<Vec<_>>();
    crate::ixby::test_support::padding(
      g.plan(),
      &rows,
      |r, b| fill_words(&r.0, b),
      |dst| g.generate_witness_into(&rows, dst),
    );
  }
}
const CHILD: &str = "IXBY_COMMITMENT_BRIDGE_VERIFY_CHILD";
const TEST: &str = "ixby::ixbf_decode::paged::commitment_bridge::tests::bridges_prove_fresh_and_reject_recomputed_prefixes";
fn fresh_verify(
  domain: ArtifactDomain,
  statement: &CommitmentBridgeStatement,
  proof: &[u8],
) {
  use std::{
    io::Write,
    process::{Command, Stdio},
  };
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", TEST, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env(CHILD, (domain as u8).to_string())
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for v in statement.words() {
    stdin.write_all(&v.lo.to_le_bytes()).unwrap();
    stdin.write_all(&v.hi.to_le_bytes()).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  assert!(
    output.status.success(),
    "{}{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
}
#[test]
#[ignore = "real raw/prefixed BLAKE3 proofs, isolated verifier and recomputed hostile prefix rows"]
fn bridges_prove_fresh_and_reject_recomputed_prefixes() {
  use flock_prover::prover::UnionSlotProverInput;
  use std::{io::Read, time::Instant};
  if let Ok(domain) = std::env::var(CHILD) {
    let domain = match domain.as_str() {
      "1" => ArtifactDomain::Program,
      "2" => ArtifactDomain::Input,
      "3" => ArtifactDomain::Output,
      _ => panic!("domain"),
    };
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    let mut bytes = Vec::new();
    std::io::stdin()
      .take(8 * 1024 * 1024 + 16 * PUBLIC_WORDS as u64 + 1)
      .read_to_end(&mut bytes)
      .unwrap();
    assert!(bytes.len() >= 16 * PUBLIC_WORDS);
    let expected = bytes[..16 * PUBLIC_WORDS]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|v| pack_bytes(v))
      .collect::<Vec<_>>();
    setup
      .verify(
        &CommitmentBridgeStatement::from_words(&expected).unwrap(),
        &bytes[16 * PUBLIC_WORDS..],
      )
      .unwrap();
    return;
  }
  let parent = [F128::new(17, 31), F128::new(123, 456)];
  for domain in
    [ArtifactDomain::Program, ArtifactDomain::Input, ArtifactDomain::Output]
  {
    let start = Instant::now();
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    let setup_time = start.elapsed();
    let batch = batches(domain, &data(1024), parent, &setup);
    for (i, a) in batch.iter().enumerate() {
      let start = Instant::now();
      let proof = setup.prove(a).unwrap();
      let elapsed = start.elapsed();
      setup.verify(&a.statement, &proof).unwrap();
      fresh_verify(domain, &a.statement, &proof);
      eprintln!(
        "commitment {domain:?} chunk {i}: proof={} setup={setup_time:?} witness+prove={elapsed:?} fresh passed",
        proof.len()
      );
      if i == 0 {
        for at in 0..PUBLIC_WORDS {
          let mut bad = *a.statement.words();
          bad[at] += F128::ONE;
          if let Ok(statement) = CommitmentBridgeStatement::from_words(&bad) {
            assert!(setup.verify(&statement, &proof).is_err());
          }
        }
        let mut bad = proof.clone();
        bad.push(0);
        assert!(setup.verify(&a.statement, &bad).is_err());
        let mut bad = proof.clone();
        bad[0] ^= 1;
        assert!(setup.verify(&a.statement, &bad).is_err());
      }
    }
    if domain != ArtifactDomain::Program {
      continue;
    }
    for attack in 0..6 {
      let index = usize::from(attack >= 4);
      let a = &batch[index];
      let witness = setup.witness(a).unwrap();
      let op = usize::from(attack >= 2);
      let (slot, g) = &setup.emission.gates[op];
      let mut rows = witness.rows::<CommitmentBridgeGate>(*slot).to_vec();
      match attack {
        0 => rows[0].0[0].lo += 1,
        1 => rows[0].0[1].lo += 1,
        2 => rows[0].0[1] += F128::ONE,
        3 => rows[0].0[4] += F128::ONE,
        4 => rows[0].0[65] += F128::ONE,
        5 => rows[0].0[3] += F128::ONE,
        _ => unreachable!(),
      }
      assert_eq!(
        eval(g, &rows[0].0).last(),
        Some(&F128::ZERO),
        "attack {attack}"
      );
      let gate = g.clone();
      let table = gate.r1cs();
      let mut inputs =
        setup.drivers.iter().map(|d| d.prover(&witness)).collect::<Vec<_>>();
      inputs[setup.shape.registry_slot(*slot)] = UnionSlotProverInput::in_place(
        move |dst| gate.generate_witness_into(&rows, dst),
        table.csc_lincheck_circuit(),
      );
      let proof = setup.prove_rows(&witness, inputs).unwrap();
      let err = setup.verify(&a.statement, &proof).unwrap_err();
      assert!(
        format!("{err:?}").contains("Wiring"),
        "attack {attack}: {err:?}"
      );
      eprintln!("commitment bridge attack {attack} rejected at Wiring");
    }
  }
}
#[test]
#[ignore = "complete original program/input/output commitment bridge circuits; set IXBY_PAGED_PROGRAM/INPUT/OUTPUT"]
fn original_artifacts_complete_commitment_bridge_circuits() {
  let mut parent = [F128::new(17, 31), F128::new(123, 456)];
  let mut program = parent;
  for (domain, var) in [
    (ArtifactDomain::Program, "IXBY_PAGED_PROGRAM"),
    (ArtifactDomain::Input, "IXBY_PAGED_INPUT"),
    (ArtifactDomain::Output, "IXBY_PAGED_OUTPUT"),
  ] {
    if domain != ArtifactDomain::Program {
      parent = program;
    }
    let bytes = std::fs::read(std::env::var_os(var).expect(var)).unwrap();
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    let start = std::time::Instant::now();
    let batch = batches(domain, &bytes, parent, &setup);
    eprintln!(
      "original {domain:?}: bytes={} bridge circuits={} elapsed={:?}",
      bytes.len(),
      batch.len(),
      start.elapsed()
    );
    if domain == ArtifactDomain::Program {
      program = batch[0].statement.words()[5..7].try_into().unwrap();
    }
    for index in [0, batch.len() - 1] {
      let proof = setup.prove(&batch[index]).unwrap();
      fresh_verify(domain, &batch[index].statement, &proof);
      eprintln!(
        "original {domain:?} bridge {index}: proof={} fresh passed",
        proof.len()
      );
      if batch.len() == 1 {
        break;
      }
    }
  }
}
