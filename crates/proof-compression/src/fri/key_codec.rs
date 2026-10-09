//! Versioned verifier-only transport; no prover matrices are serialized.
use p3_blake3::Blake3;
use p3_symmetric::CryptographicHasher;
use serde::{Deserialize, Serialize};

use super::plan::VerifierError;
use super::plan::VerifierKey;
use super::plan::validate_circuit;
use multi_stark::graph::ConstraintGraph;
use multi_stark::system::Circuit;
use multi_stark::system::System;
use multi_stark::types::Commitment;
use multi_stark::types::CommitmentParameters;
use multi_stark::types::FriParameters;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;

#[derive(Serialize, Deserialize)]
struct CircuitData {
  graph: ConstraintGraph<Val>,
  metadata: [usize; 8],
}
#[derive(Serialize, Deserialize)]
struct KeyData {
  version: u32,
  commitment: [usize; 2],
  fri: [usize; 5],
  circuits: Vec<CircuitData>,
  preprocessing: Option<Commitment>,
  indices: Vec<Option<usize>>,
}

impl VerifierKey {
  /// Canonical versioned encoding for trusted key transport and fingerprints.
  pub fn to_bytes(&self) -> Result<Vec<u8>, VerifierError> {
    let s = self.system();
    let fp = s.config.fri_parameters();
    use multi_stark::config::StarkGenericConfig;
    let data = KeyData {
      version: 1,
      commitment: [s.config.log_blowup(), s.config.cap_height()],
      fri: [
        fp.log_final_poly_len,
        fp.max_log_arity,
        fp.num_queries,
        fp.commit_proof_of_work_bits,
        fp.query_proof_of_work_bits,
      ],
      circuits: s
        .circuits
        .iter()
        .map(|c| CircuitData {
          graph: c.graph.clone(),
          metadata: [
            c.main_width,
            c.preprocessed_width,
            c.preprocessed_height,
            c.num_lookups,
            c.stage_2_width,
            c.num_publics,
            c.lookup_group_size,
            c.max_constraint_degree,
          ],
        })
        .collect(),
      preprocessing: s.preprocessed_commit.clone(),
      indices: s.preprocessed_indices.clone(),
    };
    bincode::serde::encode_to_vec(data, bincode::config::standard())
      .map_err(|e| VerifierError::Encoding(e.to_string()))
  }

  /// Decode a trusted key, with a 256 MiB decoding budget. Trust/authentication
  /// remains the caller's responsibility. Profile validation is still required.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, VerifierError> {
    let (data, used): (KeyData, usize) = bincode::serde::decode_from_slice(
      bytes,
      bincode::config::standard().with_limit::<268435456>(),
    )
    .map_err(|e| VerifierError::Encoding(e.to_string()))?;
    if used != bytes.len() || data.version != 1 {
      return Err(VerifierError::Profile("key version/trailing bytes"));
    }
    if data.commitment[0] > 31
      || data.commitment[1] != 0
      || data.fri[0] != 0
      || data.fri[1] != 1
      || data.fri[2] == 0
      || data.fri[3] >= 64
      || data.fri[4] >= 64
    {
      return Err(VerifierError::Unsupported("serialized key protocol"));
    }
    let mut circuits = Vec::with_capacity(data.circuits.len());
    for (index, c) in data.circuits.into_iter().enumerate() {
      let [
        main_width,
        preprocessed_width,
        preprocessed_height,
        num_lookups,
        stage_2_width,
        num_publics,
        lookup_group_size,
        max_constraint_degree,
      ] = c.metadata;
      if !(1..=multi_stark::lookup::MAX_LOOKUP_GROUP)
        .contains(&lookup_group_size)
      {
        return Err(VerifierError::Circuit {
          index,
          field: "lookup group size",
        });
      }
      let count = num_lookups
        .max(1)
        .div_ceil(lookup_group_size)
        .checked_mul(2)
        .and_then(|n| c.graph.zeros.len().checked_add(n))
        .ok_or(VerifierError::Profile("constraint count overflow"))?;
      let circuit = Circuit {
        graph: c.graph,
        main_width,
        preprocessed: None,
        preprocessed_width,
        preprocessed_height,
        num_lookups,
        stage_2_width,
        num_publics,
        lookup_group_size,
        constraint_count: count,
        max_constraint_degree,
      };
      validate_circuit(&circuit, index)?;
      circuits.push(circuit);
    }
    let key = Self::new(System {
      config: GoldilocksBlake3Config::new(
        CommitmentParameters {
          log_blowup: data.commitment[0],
          cap_height: data.commitment[1],
        },
        FriParameters {
          log_final_poly_len: data.fri[0],
          max_log_arity: data.fri[1],
          num_queries: data.fri[2],
          commit_proof_of_work_bits: data.fri[3],
          query_proof_of_work_bits: data.fri[4],
        },
      ),
      circuits,
      preprocessed_commit: data.preprocessing,
      preprocessed_indices: data.indices,
    });
    let system = key.system();
    if system.preprocessed_indices.len() != system.circuits.len() {
      return Err(VerifierError::Profile("preprocessing map length"));
    }
    let mut slot = 0;
    for (index, c) in system.circuits.iter().enumerate() {
      let expected = if c.preprocessed_width == 0 {
        if c.preprocessed_height != 0 {
          return Err(VerifierError::Circuit {
            index,
            field: "unexpected preprocessing height",
          });
        }
        None
      } else {
        if !c.preprocessed_height.is_power_of_two() {
          return Err(VerifierError::Circuit {
            index,
            field: "preprocessing height",
          });
        }
        let current = slot;
        slot += 1;
        Some(current)
      };
      if system.preprocessed_indices[index] != expected {
        return Err(VerifierError::Circuit {
          index,
          field: "preprocessing matrix order",
        });
      }
    }
    if (slot == 0 && system.preprocessed_commit.is_some())
      || (slot != 0
        && system.preprocessed_commit.as_ref().map(|c| c.roots().len())
          != Some(1))
    {
      return Err(VerifierError::Profile("preprocessing commitment"));
    }
    if key.to_bytes()? != bytes {
      return Err(VerifierError::Profile("noncanonical key encoding"));
    }
    Ok(key)
  }

  pub fn fingerprint(&self) -> Result<[u8; 32], VerifierError> {
    Ok(Blake3.hash_iter(
      b"multi-stark/verifier-key/v1".iter().copied().chain(self.to_bytes()?),
    ))
  }
}
