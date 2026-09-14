// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

use super::*;

/// Supply function rows directly, with only the rank-zero byte requests.
/// This deliberately does not use the executor or its hint implementations.
fn supplied_proof(
  system: &AiurSystem,
  claim: &[G],
  input: &[G],
  auxiliaries_after_rank: &[G],
) -> AiurProof {
  let traces = system
    .circuit_shapes()
    .iter()
    .enumerate()
    .map(|(index, shape)| {
      let height = if index == 0 { 4 } else { shape.preprocessed_height };
      let mut rows = vec![G::ZERO; height * shape.main_width];
      if index == 0 {
        rows[..input.len()].copy_from_slice(input);
        rows[input.len()] = G::ONE; // selector
        rows[input.len() + 1] = G::ONE; // public return multiplicity
        let start = input.len() + 8; // selector, multiplicity, six rank bytes
        assert_eq!(start + auxiliaries_after_rank.len(), shape.main_width);
        rows[start..shape.main_width].copy_from_slice(auxiliaries_after_rank);
      } else if index == system.toplevel.circuits.len() + 1 {
        rows[6] = G::from_u8(3); // three rank-byte pairs (0, 0)
      }
      RowMajorMatrix::new(rows, shape.main_width)
    })
    .collect();
  let witness = SystemWitness::from_stage_1(traces, &system.system);
  system.system.prove(&system.key, claim, witness)
}

fn pack_word(bytes: &[G]) -> G {
  assert_eq!(bytes.len(), 4);
  bytes.iter().enumerate().fold(G::ZERO, |sum, (index, byte)| {
    sum + *byte * G::from_u64(1 << (8 * index))
  })
}

/// All unconstrained operations can receive arbitrary per-row advice.
/// The u32 carries are virtual expressions and therefore are still pinned.
/// I/O writes, key insertion and debugging do not constrain these rows.
#[test]
fn supplied_advice_has_relational_semantics() {
  let function = Function {
    body: Block {
      ops: vec![
        Op::IOGetInfo(0, vec![]),
        Op::IORead(0, 1, 2),
        Op::UnconstrainedBigUintDivMod(0, 1),
        Op::UnconstrainedGToBytes(0),
        Op::UnconstrainedGInverse(0),
        Op::Call(1, vec![0], 1, true),
        Op::UnconstrainedU32Add(vec![0, 1, 2, 3], vec![4, 5, 6, 7]),
        Op::UnconstrainedU32Add3(
          vec![0, 1, 2, 3],
          vec![4, 5, 6, 7],
          vec![8, 9, 10, 11],
        ),
        Op::IOSetInfo(0, vec![], 1, 2),
        Op::IOWrite(0, vec![12, 13]),
        Op::Debug("advice effects".into(), Some(vec![14, 15])),
      ],
      ctrl: Ctrl::Return(0, (12..38).collect()),
    },
    layout: FunctionLayout {
      input_size: 12,
      selectors: 1,
      auxiliaries: 31,
      lookups: 4,
    },
    entry: true,
    constrained: true,
  };
  let callee = Function {
    body: Block {
      ops: vec![Op::Const(G::ZERO)],
      ctrl: Ctrl::Return(0, vec![1]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 7,
      lookups: 4,
    },
    entry: false,
    constrained: false,
  };
  let (cp, fp) = test_parameters();
  let system = AiurSystem::build(
    with_singleton_circuits(vec![function, callee], vec![]),
    cp,
    fp,
  );
  let input: Vec<_> = (1..=12).map(G::from_u64).collect();
  // Even the advice called "bytes" is outside the byte range. The bare
  // hints impose no range check; a caller must add one when required.
  let advice: Vec<_> = (300..324).map(G::from_u64).collect();
  let mut output = advice[..20].to_vec();
  let inverse_2_32 = G::from_u64(0xffff_fffe_0000_0002);
  let x = pack_word(&input[..4]);
  let y = pack_word(&input[4..8]);
  let z = pack_word(&input[8..12]);
  output.push((x + y - pack_word(&advice[16..20])) * inverse_2_32);
  output.extend_from_slice(&advice[20..24]);
  output.push((x + y + z - pack_word(&advice[20..24])) * inverse_2_32);
  let mut claim = vec![function_channel(), G::ZERO];
  claim.extend_from_slice(&input);
  claim.extend_from_slice(&output);
  let proof = supplied_proof(&system, &claim, &input, &advice);
  system.verify(&claim, &proof).expect("unchecked advice is permitted");

  // A changed public carry is not supplied by this same local computation.
  *claim.last_mut().unwrap() += G::ONE;
  let proof = supplied_proof(&system, &claim, &input, &advice);
  assert!(system.verify(&claim, &proof).is_err());
}

#[test]
fn checked_inverse_advice_rejects_incorrect_value() {
  let function = Function {
    body: Block {
      ops: vec![
        Op::UnconstrainedGInverse(0),
        Op::Mul(0, 1),
        Op::Const(G::ONE),
        Op::AssertEq(vec![2], vec![3], None),
      ],
      ctrl: Ctrl::Return(0, vec![1]),
    },
    layout: FunctionLayout {
      input_size: 1,
      selectors: 1,
      auxiliaries: 9,
      lookups: 4,
    },
    entry: true,
    constrained: true,
  };
  let (cp, fp) = test_parameters();
  let system =
    AiurSystem::build(with_singleton_circuits(vec![function], vec![]), cp, fp);
  let input = [G::from_u8(3)];
  let wrong = G::from_u8(4);
  let claim = [function_channel(), G::ZERO, input[0], wrong];
  let proof =
    supplied_proof(&system, &claim, &input, &[wrong, input[0] * wrong]);
  assert!(system.verify(&claim, &proof).is_err());
  let (claim, proof) = system.prove(0, &input, &mut empty_io_buffer());
  system.verify(&claim, &proof).expect("checked honest inverse must verify");
}
