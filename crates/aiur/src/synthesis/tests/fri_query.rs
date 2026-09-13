// Copyright (c) 2026 Argument Computer Corporation.
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Record the real FRI verifier's private query routine through its public
//! folding strategy hook, with honest PCS proofs and the concrete MMCS.

use super::*;
use multi_stark::{
  config::StarkGenericConfig,
  p3_field::{BasedVectorSpace, Field, HornerIter, PrimeField64, TwoAdicField},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  types::{Challenger, ExtMmcs, ExtVal, Mmcs, Pcs, Val},
};
use p3_blake3::Blake3;
use p3_challenger::{
  CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger,
};
use p3_commit::{Mmcs as MmcsTrait, Pcs as PcsTrait};
use p3_fri::{
  BatchMultiOpening, FriFoldingStrategy, FriParameters as NativeParameters,
  TwoAdicFriFolding, verifier::verify_fri,
};
use p3_symmetric::{
  CompressionFunctionFromHasher, MerkleCap, SerializingHasher,
};
use p3_util::reverse_bits_len;
use std::{cell::RefCell, io, marker::PhantomData};

type Dft = <AiurConfig as StarkGenericConfig>::Dft;
type Commitment = MerkleCap<Val, [u8; 32]>;
type NativeFolding = TwoAdicFriFolding<
  Vec<BatchMultiOpening<Val, Mmcs>>,
  <Mmcs as MmcsTrait<Val>>::Error,
>;

struct FoldCall {
  index: usize,
  height: usize,
  log_arity: usize,
  challenge: ExtVal,
  values: Vec<ExtVal>,
  result: ExtVal,
}

#[derive(Default)]
struct RecordingFolding(RefCell<Vec<FoldCall>>);

impl FriFoldingStrategy<Val, ExtVal> for RecordingFolding {
  type InputProof = Vec<BatchMultiOpening<Val, Mmcs>>;
  type InputError = <Mmcs as MmcsTrait<Val>>::Error;

  fn extra_query_index_bits(&self) -> usize {
    let native: NativeFolding = TwoAdicFriFolding(PhantomData);
    <NativeFolding as FriFoldingStrategy<Val, ExtVal>>::extra_query_index_bits(
      &native,
    )
  }

  fn fold_row(
    &self,
    index: usize,
    height: usize,
    log_arity: usize,
    challenge: ExtVal,
    evals: impl Iterator<Item = ExtVal>,
  ) -> ExtVal {
    let values: Vec<_> = evals.collect();
    let native: NativeFolding = TwoAdicFriFolding(PhantomData);
    let result = <NativeFolding as FriFoldingStrategy<Val, ExtVal>>::fold_row(
      &native,
      index,
      height,
      log_arity,
      challenge,
      values.iter().copied(),
    );
    self.0.borrow_mut().push(FoldCall {
      index,
      height,
      log_arity,
      challenge,
      values,
      result,
    });
    result
  }

  fn fold_matrix<M: Matrix<ExtVal>>(
    &self,
    challenge: ExtVal,
    log_arity: usize,
    matrix: M,
  ) -> Vec<ExtVal> {
    let native: NativeFolding = TwoAdicFriFolding(PhantomData);
    <NativeFolding as FriFoldingStrategy<Val, ExtVal>>::fold_matrix(
      &native, challenge, log_arity, matrix,
    )
  }
}

#[derive(Clone)]
struct RecordingChallenger {
  inner: Challenger,
  fields: Vec<Val>,
  indices: Vec<(usize, usize)>,
}

impl CanObserve<Val> for RecordingChallenger {
  fn observe(&mut self, value: Val) {
    self.inner.observe(value);
  }
}

impl CanObserve<Commitment> for RecordingChallenger {
  fn observe(&mut self, value: Commitment) {
    self.inner.observe(value);
  }
}

impl CanSample<Val> for RecordingChallenger {
  fn sample(&mut self) -> Val {
    let value = self.inner.sample();
    self.fields.push(value);
    value
  }
}

impl CanSample<ExtVal> for RecordingChallenger {
  fn sample(&mut self) -> ExtVal {
    self.sample_algebra_element()
  }
}

impl CanSampleBits<usize> for RecordingChallenger {
  fn sample_bits(&mut self, bits: usize) -> usize {
    let value = self.inner.sample_bits(bits);
    self.indices.push((bits, value));
    value
  }
}

impl FieldChallenger<Val> for RecordingChallenger {}

impl GrindingChallenger for RecordingChallenger {
  type Witness = Val;

  fn grind(&mut self, bits: usize) -> Val {
    self.inner.grind(bits)
  }
}

fn nat(out: &mut Vec<u8>, value: usize) {
  out.extend(u64::try_from(value).unwrap().to_le_bytes());
}

fn field(out: &mut Vec<u8>, value: Val) {
  out.extend(value.as_canonical_u64().to_le_bytes());
}

fn extension(out: &mut Vec<u8>, value: ExtVal) {
  for &coordinate in value.as_basis_coefficients_slice() {
    field(out, coordinate);
  }
}

fn extensions(out: &mut Vec<u8>, values: &[ExtVal]) {
  nat(out, values.len());
  for &value in values {
    extension(out, value);
  }
}

fn query_point(bits: usize, index: usize) -> Val {
  Val::two_adic_generator(bits)
    .exp_u64(u64::try_from(reverse_bits_len(index, bits)).unwrap())
}

fn layout(index: usize, final_bits: usize) -> Vec<Vec<usize>> {
  let offsets = match index {
    0 => vec![vec![0]],
    1 => vec![vec![2]],
    2 => vec![vec![6, 2], vec![2, 0]],
    _ => vec![vec![3, 6], vec![3]],
  };
  offsets
    .into_iter()
    .map(|batch| {
      batch
        .into_iter()
        .map(|bits| bits + final_bits + usize::from(final_bits != 0))
        .collect()
    })
    .collect()
}

fn polynomial(seed: usize, bits: usize, column: usize) -> Vec<Val> {
  (0..1 << bits)
    .map(|index| Val::from_usize(seed * 101 + column * 29 + index * 13 + 1))
    .collect()
}

#[test]
fn fri_query_snapshot() -> io::Result<()> {
  let mut out = b"Aiur native FRI query chains v1\n".to_vec();
  let mut cases = 0;
  let mut total_queries = 0;
  let mut total_rounds = 0;
  let mut total_calls = 0;
  for blowup in 1..=2 {
    for final_bits in 0..=2 {
      for max_arity in 1..=4 {
        for layout_index in 0..4 {
          let logs = layout(layout_index, final_bits);
          let queries = 1 + layout_index + final_bits;
          let global_bits =
            logs.iter().flatten().copied().max().unwrap() + blowup;
          let mmcs = Mmcs::new(
            SerializingHasher::new(Blake3),
            CompressionFunctionFromHasher::new(Blake3),
            0,
          );
          let parameters = NativeParameters {
            log_blowup: blowup,
            log_final_poly_len: final_bits,
            max_log_arity: max_arity,
            num_queries: queries,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
            mmcs: ExtMmcs::new(mmcs.clone()),
          };
          let pcs = Pcs::new(Dft::default(), mmcs.clone(), parameters.clone());
          let sources: Vec<Vec<Vec<Vec<Val>>>> = logs
            .iter()
            .enumerate()
            .map(|(batch, matrices)| {
              matrices
                .iter()
                .enumerate()
                .map(|(matrix, &bits)| {
                  (0..2 + matrix)
                    .map(|column| {
                      polynomial(cases + batch * 7 + matrix, bits, column)
                    })
                    .collect()
                })
                .collect()
            })
            .collect();
          let (commits, data): (Vec<_>, Vec<_>) = logs
            .iter()
            .zip(&sources)
            .map(|(matrices, sources)| {
              let evaluations = matrices.iter().zip(sources).map(|(&bits, columns)| {
                let domain = <Pcs as PcsTrait<ExtVal, Challenger>>::natural_domain_for_degree(&pcs, 1 << bits);
                let mut values = Vec::new();
                for point in Val::two_adic_generator(bits).powers().take(1 << bits) {
                  values.extend(columns.iter().map(|p| p.iter().copied().horner::<Val, _>(point)));
                }
                (domain, RowMajorMatrix::new(values, columns.len()))
              });
              <Pcs as PcsTrait<ExtVal, Challenger>>::commit(&pcs, evaluations)
            })
            .unzip();
          let mut prefix =
            Challenger::from_hasher(b"ix/fri-query-corpus/v1".to_vec(), Blake3);
          prefix.observe_slice(&commits);
          let zeta: ExtVal = prefix.sample_algebra_element();
          let mut points = vec![zeta];
          if layout_index % 2 == 1 {
            points
              .push(zeta + ExtVal::new([Val::from_u64(19), Val::from_u64(3)]));
          }
          let requests = data
            .iter()
            .zip(&logs)
            .map(|(data, matrices)| {
              (data, matrices.iter().map(|_| points.clone()).collect())
            })
            .collect();
          let (opened, proof) = pcs.open(requests, &mut prefix.clone());
          let claims: Vec<_> = commits.into_iter().zip(&logs).zip(&opened).map(|((commit, matrices), opened)| {
            let matrices = matrices.iter().zip(opened).map(|(&bits, values)| {
              let domain = <Pcs as PcsTrait<ExtVal, Challenger>>::natural_domain_for_degree(&pcs, 1 << bits);
              (domain, points.iter().copied().zip(values.iter().cloned()).collect())
            }).collect();
            (commit, matrices)
          }).collect();
          let ordinary =
            pcs.verify(claims.clone(), &proof, &mut prefix.clone());
          assert!(ordinary.is_ok(), "ordinary PCS case {cases}: {ordinary:?}");
          // The PCS caller absorbs every claimed evaluation before it
          // enters verify_fri. Preserve that exact prefix for the recorder.
          for values in opened.iter().flatten().flatten() {
            prefix.observe_algebra_slice(values);
          }
          let folding = RecordingFolding::default();
          let mut challenger = RecordingChallenger {
            inner: prefix,
            fields: vec![],
            indices: vec![],
          };
          verify_fri(
            &folding,
            &parameters,
            &proof,
            &mut challenger,
            &claims,
            &mmcs,
          )
          .unwrap();
          let rounds = proof.commit_phase_openings.len();
          assert_eq!(challenger.fields.len(), 2 * (rounds + 1));
          assert_eq!(challenger.indices.len(), queries);
          let random: Vec<_> = challenger
            .fields
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| ExtVal::new([pair[0], pair[1]]))
            .collect();
          let calls = folding.0.into_inner();
          assert_eq!(calls.len(), queries * rounds);
          for value in
            [blowup, final_bits, max_arity, queries, layout_index, global_bits]
          {
            nat(&mut out, value);
          }
          nat(&mut out, logs.len());
          for (batch, (matrices, columns)) in
            logs.iter().zip(&sources).enumerate()
          {
            nat(&mut out, matrices.len());
            for (matrix, (&bits, columns)) in
              matrices.iter().zip(columns).enumerate()
            {
              nat(&mut out, bits);
              nat(&mut out, columns.len());
              for polynomial in columns {
                nat(&mut out, polynomial.len());
                for &coefficient in polynomial {
                  field(&mut out, coefficient);
                }
              }
              for (&point, values) in points.iter().zip(&opened[batch][matrix])
              {
                let expected: Vec<_> = columns
                  .iter()
                  .map(|p| p.iter().copied().map(ExtVal::from).horner(point))
                  .collect();
                assert_eq!(*values, expected);
              }
            }
          }
          extensions(&mut out, &points);
          for batch in &opened {
            for matrix in batch {
              for point in matrix {
                extensions(&mut out, point);
              }
            }
          }
          for (batch, opened_batch) in proof.input_openings.iter().enumerate() {
            for (query, &(width, index)) in
              challenger.indices.iter().enumerate()
            {
              assert_eq!(width, global_bits);
              for (matrix, row) in
                opened_batch.opened_values[query].iter().enumerate()
              {
                let height = logs[batch][matrix] + blowup;
                let point = Val::GENERATOR
                  * query_point(height, index >> (global_bits - height));
                let expected: Vec<_> = sources[batch][matrix]
                  .iter()
                  .map(|p| p.iter().copied().horner(point))
                  .collect();
                assert_eq!(*row, expected);
                nat(&mut out, row.len());
                for &value in row {
                  field(&mut out, value);
                }
              }
            }
          }
          extensions(&mut out, &random);
          for &(width, index) in &challenger.indices {
            nat(&mut out, width);
            nat(&mut out, index);
          }
          nat(&mut out, rounds);
          for round in &proof.commit_phase_openings {
            nat(&mut out, usize::from(round.log_arity));
            for siblings in &round.sibling_values {
              extensions(&mut out, siblings);
            }
          }
          extensions(&mut out, &proof.final_poly);
          nat(&mut out, calls.len());
          for call in &calls {
            for value in [call.index, call.height, call.log_arity] {
              nat(&mut out, value);
            }
            extension(&mut out, call.challenge);
            extensions(&mut out, &call.values);
            extension(&mut out, call.result);
          }
          for (query, &(_, index)) in challenger.indices.iter().enumerate() {
            let final_index = if rounds == 0 {
              index
            } else {
              calls[(query + 1) * rounds - 1].index
            };
            let value: ExtVal = proof
              .final_poly
              .iter()
              .copied()
              .horner(query_point(global_bits, final_index));
            nat(&mut out, final_index);
            extension(&mut out, value);
          }
          cases += 1;
          total_queries += queries;
          total_rounds += rounds;
          total_calls += calls.len();
        }
      }
    }
  }
  for value in [cases, total_queries, total_rounds, total_calls] {
    nat(&mut out, value);
  }
  if let Ok(path) = std::env::var("IX_FRI_QUERY_SNAPSHOT") {
    std::fs::write(path, out)?;
  }
  println!(
    "Native FRI query chains: {cases} proofs, {total_queries} queries, {total_rounds} rounds, {total_calls} fold calls"
  );
  Ok(())
}
