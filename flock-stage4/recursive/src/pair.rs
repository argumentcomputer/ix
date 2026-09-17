use crate::backend::{NativeBuilder, NativeGraph};
use crate::*;
use anyhow::{Result, ensure};
use flock_prover::{
  field::F128,
  matrix_fold::{
    JaggedClaim, JaggedRowWeight, JaggedTable, MatrixClaim, Weight,
  },
  pcs::jagged::JaggedParams,
};
use ix_stage4_trace::{F128MatrixSideV1, F128StaticMatrixIdV1};
use ixby_flock::ixby::{
  io::PublicWord, ixbf_decode::stream::batch::CompiledGrammarBatch,
};
use ixby_stage4_exec::{
  CompiledFlockReplay, CompiledGrammarBatchReplay, FlockVerifierSetup,
  GrammarBatchReplayWitness, compile_grammar_batch_replay,
};
use std::collections::HashMap;

const APPLICATION_WORDS: usize = 63;

/// A two-child parser relation. This is a setup/compiler, not a proof.
/// Its application output is one source identity and the full outer endpoints.
pub struct GrammarPairRelation<'a> {
  pub(crate) replay: CompiledGrammarBatchReplay<'a>,
  pub(crate) graph: NativeGraph,
  roots: Vec<RootClaim>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RootWeight {
  low: Vec<usize>,
  point: Vec<usize>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum RootJaggedWeight {
  Eq(usize, Vec<usize>),
  Combo(Vec<(usize, u32)>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
enum RootClaim {
  Matrix(F128StaticMatrixIdV1, RootWeight, RootWeight, usize),
  Structure(Vec<usize>, Vec<usize>, usize),
  Jagged(RootJaggedWeight, Vec<usize>, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePairCensus {
  pub variables: usize,
  pub arithmetic_operations: usize,
  pub packed_arithmetic_rows: usize,
  pub bit_packing_rows: usize,
  pub blake3_compressions: usize,
  pub equality_links: usize,
  pub fixed_words: usize,
  pub application_words: usize,
  pub root_advice_words: usize,
  pub root_claims: usize,
  pub required_row_variables: usize,
}

impl<'a> GrammarPairRelation<'a> {
  pub fn compile(setup: &'a CompiledGrammarBatch) -> Result<Self> {
    let replay = compile_grammar_batch_replay(setup)?;
    let mut b = NativeBuilder::new(true);
    let roots = emit_pair(&mut b, &replay, None)?;
    Ok(Self { replay, graph: b.graph, roots })
  }
  pub fn census(&self) -> NativePairCensus {
    let arithmetic = self.graph.macs.len().div_ceil(gates::MACS_PER_ROW);
    let max_rows = arithmetic
      .max(self.graph.packs.len())
      .max(self.graph.compressions.len())
      .max(1);
    NativePairCensus {
      variables: self.graph.variables,
      arithmetic_operations: self.graph.macs.len(),
      packed_arithmetic_rows: arithmetic,
      bit_packing_rows: self.graph.packs.len(),
      blake3_compressions: self.graph.compressions.len(),
      equality_links: self.graph.equalities.len(),
      fixed_words: self.graph.constants.len(),
      application_words: APPLICATION_WORDS,
      root_advice_words: self.graph.published.len() - APPLICATION_WORDS,
      root_claims: self.roots.len(),
      required_row_variables: max_rows.next_power_of_two().ilog2() as usize,
    }
  }
  pub fn replay(&self) -> &CompiledGrammarBatchReplay<'a> {
    &self.replay
  }

  pub(crate) fn advice(
    &self,
    children: [&GrammarBatchReplayWitness; 2],
  ) -> Result<NativeBuilder> {
    ensure!(
      children.iter().all(|child| child.identity() == self.replay.identity()),
      "child replay setup identity"
    );
    let mut b = NativeBuilder::new(false);
    let roots = emit_pair(&mut b, &self.replay, Some(children))?;
    ensure!(
      b.graph == self.graph && roots == self.roots,
      "native recursive graph differs from proof-free setup"
    );
    b.check().map_err(|e| anyhow::anyhow!("native recursive advice: {e}"))?;
    let public =
      b.graph.published.iter().map(|&i| b.values[i]).collect::<Vec<_>>();
    self.check_roots(&public)?;
    Ok(b)
  }

  pub(crate) fn check_roots(&self, public: &[F128]) -> Result<()> {
    ensure!(
      public.len() == self.graph.published.len(),
      "recursive root public width"
    );
    let setup = self.replay.setup();
    let shape = setup.verifier_shape();
    let structure =
      flock_prover::circuit::SigmaAssertion::matrix(&shape.circuit);
    let pcs = self.replay.merged_pcs();
    let params = JaggedParams::from_heights(
      &pcs.jagged_heights,
      pcs.row_variables as usize,
      setup.pcs_params().m - 7,
    );
    let jagged = JaggedTable::from_params(&params);
    let words = |indices: &[usize]| {
      indices.iter().map(|&i| public[i]).collect::<Vec<_>>()
    };
    let weight =
      |w: &RootWeight| Weight::low_eq(words(&w.low), words(&w.point));
    for (index, root) in self.roots.iter().enumerate() {
      let valid = match root {
        RootClaim::Matrix(id, row, column, value) => {
          ensure!(
            id.registry_digest == shape.registry.digest(),
            "recursive root registry"
          );
          let ty = &shape.registry.boolean_types()
            [usize::try_from(id.table).expect("compiled table index")];
          let matrix = match id.side {
            F128MatrixSideV1::A => &ty.a_0,
            F128MatrixSideV1::B => &ty.b_0,
          };
          MatrixClaim {
            row: weight(row),
            col: weight(column),
            value: public[*value],
          }
          .check_direct(matrix)
        },
        RootClaim::Structure(row, column, value) => MatrixClaim {
          row: Weight::eq(words(row)),
          col: Weight::eq(words(column)),
          value: public[*value],
        }
        .check_direct(&structure),
        RootClaim::Jagged(row, column, value) => {
          let row = match row {
            RootJaggedWeight::Eq(scale, point) => {
              JaggedRowWeight::Eq(public[*scale], words(point))
            },
            RootJaggedWeight::Combo(terms) => JaggedRowWeight::Combo(
              terms
                .iter()
                .map(|&(coefficient, address)| (public[coefficient], address))
                .collect(),
            ),
          };
          JaggedClaim { row, col: words(column), value: public[*value] }
            .check_direct(&jagged)
        },
      };
      ensure!(valid, "recursive root claim {index} rejected");
    }
    Ok(())
  }
}

pub(crate) struct ChildWires {
  pub(crate) application: Vec<F128VariablesV1>,
  pub(crate) algebra: F128AlgebraCircuitOutputV1,
  pub(crate) wiring: F128WiringCircuitOutputV1,
  pub(crate) multipoint: F128MultipointTwistedAssistCircuitOutputV1,
}

fn emit_pair(
  b: &mut NativeBuilder,
  replay: &CompiledGrammarBatchReplay<'_>,
  advice: Option<[&GrammarBatchReplayWitness; 2]>,
) -> Result<Vec<RootClaim>> {
  let left = emit_child(b, replay, advice.map(|v| v[0]))?;
  let right = emit_child(b, replay, advice.map(|v| v[1]))?;
  for i in 0..3 {
    enforce_f128_equal(
      b,
      &left.application[i],
      &right.application[i],
      ConstraintPhase::Statement,
    );
  }
  for i in 0..30 {
    enforce_f128_equal(
      b,
      &left.application[33 + i],
      &right.application[3 + i],
      ConstraintPhase::Statement,
    );
  }
  let application = left.application[..33]
    .iter()
    .chain(&right.application[33..])
    .map(|v| v.word(b))
    .collect::<Vec<_>>();
  ensure!(application.len() == APPLICATION_WORDS, "pair application width");
  b.graph.published = application;
  let mut public = b
    .graph
    .published
    .iter()
    .enumerate()
    .map(|(i, &word)| (word, i))
    .collect::<HashMap<_, _>>();
  let mut roots = Vec::new();
  for child in [left, right] {
    for claim in child.algebra.deferred_matrix_claims {
      let row = root_weight(b, &mut public, &claim.row);
      let column = root_weight(b, &mut public, &claim.column);
      let value = publish(b, &mut public, &claim.value);
      roots.push(RootClaim::Matrix(claim.matrix, row, column, value));
    }
    for claim in child.wiring.circuit_structure_claims {
      ensure!(
        claim.matrix.circuit_digest
          == replay.setup().verifier_shape().circuit.digest(),
        "structure setup digest"
      );
      let row = publish_many(b, &mut public, &claim.row_point);
      let column = publish_many(b, &mut public, &claim.column_point);
      let value = publish(b, &mut public, &claim.value);
      roots.push(RootClaim::Structure(row, column, value));
    }
    for claim in child.multipoint.jagged_assertion.claims {
      let row = match claim.row {
        F128JaggedRowWeightVariablesV1::Eq { scale, point } => {
          RootJaggedWeight::Eq(
            publish(b, &mut public, &scale),
            publish_many(b, &mut public, &point),
          )
        },
        F128JaggedRowWeightVariablesV1::Combo { terms } => {
          RootJaggedWeight::Combo(
            terms
              .iter()
              .map(|term| {
                (publish(b, &mut public, &term.coefficient), term.address)
              })
              .collect(),
          )
        },
      };
      let column = publish_many(b, &mut public, &claim.column_point);
      let value = publish(b, &mut public, &claim.value);
      roots.push(RootClaim::Jagged(row, column, value));
    }
  }
  Ok(roots)
}
fn root_weight(
  b: &mut NativeBuilder,
  public: &mut HashMap<usize, usize>,
  weight: &F128StructuredWeightVariablesV1,
) -> RootWeight {
  RootWeight {
    low: publish_many(b, public, &weight.low),
    point: publish_many(b, public, &weight.point),
  }
}
fn publish_many(
  b: &mut NativeBuilder,
  public: &mut HashMap<usize, usize>,
  values: &[F128VariablesV1],
) -> Vec<usize> {
  values.iter().map(|v| publish(b, public, v)).collect()
}
fn publish(
  b: &mut NativeBuilder,
  public: &mut HashMap<usize, usize>,
  value: &F128VariablesV1,
) -> usize {
  let word = value.word(b);
  *public.entry(word).or_insert_with(|| {
    let index = b.graph.published.len();
    b.graph.published.push(word);
    index
  })
}

pub(crate) fn emit_child<S: FlockVerifierSetup>(
  b: &mut NativeBuilder,
  replay: &CompiledFlockReplay<S>,
  advice: Option<&GrammarBatchReplayWitness>,
) -> Result<ChildWires> {
  let mut profile = profile::Profile::graph("child", b);
  let setup = replay.setup();
  let public_values =
    advice.map(|v| v.public_values().to_vec()).unwrap_or_else(|| {
      setup
        .public_template()
        .words()
        .iter()
        .map(|word| match word {
          PublicWord::Fixed(value) => bytes(*value),
          PublicWord::Output(_) => [0; 16],
        })
        .collect()
    });
  let public = public_values
    .into_iter()
    .map(|v| alloc_f128_private(b, v, ConstraintPhase::Statement))
    .collect::<Result<Vec<_>, _>>()?;
  profile.stage("statement_allocate", b);
  let observed = advice
    .map(|v| v.transcript().observed_values().to_vec())
    .unwrap_or_else(|| vec![[0; 16]; replay.observed_values()]);
  let payloads =
    advice.map(|v| v.transcript().byte_payloads().to_vec()).unwrap_or_else(
      || replay.payload_lengths().iter().map(|&n| vec![0; n]).collect(),
    );
  let challenges = advice
    .map(|v| v.transcript().challenges().to_vec())
    .unwrap_or_else(|| vec![[0; 16]; replay.challenges()]);
  let trace = advice
    .map(|v| v.transcript().chained_blake3())
    .unwrap_or(replay.transcript());
  let transcript = constrain_chained_blake3_transcript(
    b,
    trace,
    &observed,
    &payloads,
    &challenges,
  )?;
  profile.stage("transcript", b);
  let constants = [
    (0, setup.verifier_shape().registry.digest().to_vec()),
    (
      1,
      setup
        .verifier_shape()
        .counts
        .iter()
        .flat_map(|&count| (count as u64).to_le_bytes())
        .collect(),
    ),
    (3, setup.verifier_shape().circuit.digest().to_vec()),
  ];
  for (index, bytes) in constants {
    bind_bytes(b, &transcript.byte_payloads[index], &bytes)?;
  }
  let digest = public_digest(b, &public);
  for (i, &word) in digest.iter().enumerate() {
    let actual = b.pack(transcript.byte_payloads[4][i].bit_expressions());
    b.equal(actual, word);
  }
  profile.stage("statement_bind", b);
  let wiring_private = advice
    .map(|v| v.wiring().private_values().to_vec())
    .unwrap_or_else(|| vec![[0; 16]; 2]);
  let wiring = constrain_f128_wiring(
    b,
    replay.wiring(),
    F128WiringCircuitInputsV1 {
      public_values: &public,
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      private_values: &wiring_private,
    },
  )?;
  profile.stage("wiring", b);
  let boolean_private = advice
    .map(|v| v.transcript().f128_private_values().to_vec())
    .unwrap_or_else(|| {
      vec![[0; 16]; replay.boolean().deferred_matrix_claims.len()]
    });
  let boolean_private = boolean_private
    .into_iter()
    .map(|v| alloc_f128_private(b, v, ConstraintPhase::Lincheck))
    .collect::<Result<Vec<_>, _>>()?;
  let algebra = constrain_f128_algebra_trace_deferred(
    b,
    replay.boolean(),
    F128AlgebraCircuitInputsV1 {
      public_values: &public,
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      private_values: &boolean_private,
    },
  )?;
  profile.stage("boolean_algebra", b);
  let mut packed_direct = Vec::new();
  if let Some(trace) = replay.element() {
    let inputs = F128AlgebraCircuitInputsV1 {
      public_values: &public,
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      private_values: &[],
    };
    let output = constrain_f128_algebra_trace(b, trace, inputs)?;
    let mut constants = std::collections::BTreeMap::new();
    for claim in replay.element_claims() {
      let point = claim
        .point
        .iter()
        .map(|&reference| {
          resolve_reference(
            b,
            reference,
            ConstraintPhase::Pcs,
            inputs,
            &output.operations,
            &mut constants,
          )
        })
        .collect::<Result<Vec<_>, _>>()?;
      let value = resolve_reference(
        b,
        claim.value,
        ConstraintPhase::Pcs,
        inputs,
        &output.operations,
        &mut constants,
      )?;
      packed_direct.push(F128PackedDirectClaimVariablesV1 { point, value });
    }
  }
  packed_direct.extend(wiring.gather_claims.iter().cloned());
  profile.stage("element_algebra", b);
  let frontend = constrain_f128_merged_pcs_frontend(
    b,
    replay.merged_pcs(),
    F128MergedPcsFrontendCircuitInputsV1 {
      public_values: &public,
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      private_values: &boolean_private,
      algebra_operations: &algebra.operations,
      byte_payloads: &transcript.byte_payloads,
      packed_direct_claims: &packed_direct,
    },
  )?;
  profile.stage("opening_frontend", b);
  let multipoint_private =
    advice.map(|v| v.multipoint().private_values().to_vec()).unwrap_or_else(
      || vec![[0; 16]; replay.multipoint().jagged_claim_private_values.len()],
    );
  let multipoint = constrain_f128_multipoint_twisted_assist(
    b,
    replay.multipoint(),
    F128MultipointTwistedAssistCircuitInputsV1 {
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      private_values: &multipoint_private,
      frontend: &frontend,
    },
  )?;
  profile.stage("opening_multipoint", b);
  let inner_census = replay.inner().census();
  let inner_values =
    advice.map(|v| v.inner().private_values().to_vec()).unwrap_or_else(|| {
      vec![
        [0; 16];
        usize::try_from(inner_census.opened_values)
          .expect("compiled opened-value count")
      ]
    });
  let inner_digests =
    advice.map(|v| v.inner().private_digests().to_vec()).unwrap_or_else(|| {
      vec![
        [0; 32];
        usize::try_from(inner_census.path_digests)
          .expect("compiled path count")
      ]
    });
  constrain_f128_inner_ligerito(
    b,
    replay.inner(),
    F128InnerLigeritoCircuitInputsV1 {
      observed_values: &transcript.observed_values,
      challenges: &transcript.challenges,
      byte_payloads: &transcript.byte_payloads,
      private_values: &inner_values,
      private_digests: &inner_digests,
      frontend: &frontend,
    },
  )?;
  profile.stage("opening_inner", b);
  let mut application =
    vec![public[0].clone(); setup.public_template().outputs()];
  for (word, value) in setup.public_template().words().iter().zip(&public) {
    if let PublicWord::Output(index) = word {
      application[*index] = value.clone();
    }
  }
  profile.stage("application", b);
  Ok(ChildWires { application, algebra, wiring, multipoint })
}

pub(crate) fn bind_bytes(
  b: &mut NativeBuilder,
  words: &[F128TranscriptWordV1],
  bytes: &[u8],
) -> Result<()> {
  ensure!(
    words.len() == bytes.len().div_ceil(16),
    "recursive constant payload width"
  );
  for (word, chunk) in words.iter().zip(bytes.chunks(16)) {
    let mut padded = [0; 16];
    padded[..chunk.len()].copy_from_slice(chunk);
    let actual = b.pack(word.bit_expressions());
    let expected = b.constant(ixby_flock::hash::pack_bytes(&padded));
    b.equal(actual, expected);
  }
  Ok(())
}

/// Flock's public vector digest is a non-root chunk hash followed by a linear
/// chain of non-root parent hashes, exactly `union::publics_digest`.
fn public_digest(
  b: &mut NativeBuilder,
  public: &[F128VariablesV1],
) -> [usize; 2] {
  let iv =
    ixby_flock::hash::pack8(&ixby_flock::hash::IV).map(|v| b.constant(v));
  let zero = b.constant(F128::ZERO);
  let mut result = None;
  for chunk in public.chunks(64) {
    let mut cv = iv;
    let blocks = chunk.len().div_ceil(4);
    for (index, block) in chunk.chunks(4).enumerate() {
      let mut input = [zero; 7];
      input[..2].copy_from_slice(&cv);
      for (i, value) in block.iter().enumerate() {
        input[2 + i] = value.word(b);
      }
      let flags = u32::from(index == 0) | (2 * u32::from(index + 1 == blocks));
      input[6] = b.constant(ixby_flock::hash::pack_params(
        0,
        u32::try_from(block.len() * 16).expect("block at most 64 bytes"),
        flags,
      ));
      cv = b.compress(input)[..2].try_into().unwrap();
    }
    result = Some(if let Some(previous) = result {
      let previous: [usize; 2] = previous;
      let params = b.constant(ixby_flock::hash::pack_params(0, 64, 4));
      b.compress([iv[0], iv[1], previous[0], previous[1], cv[0], cv[1], params])
        [..2]
        .try_into()
        .unwrap()
    } else {
      cv
    });
  }
  result.expect("nonempty parser public vector")
}

#[cfg(test)]
mod tests;
