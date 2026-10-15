use super::*;
use shape::Shape;

const FRONTEND_VERSION: &[u8] = b"init-kzg-recursive/frontend/v1";

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub(crate) enum ClaimSlot {
  Constant(Scalar),
  PublicU64,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub(crate) struct ClaimSchema {
  pub(super) rows: Vec<Vec<ClaimSlot>>,
  pub(super) public_locations: Vec<(usize, usize)>,
}

impl ClaimSchema {
  pub(crate) fn from_claims(
    claims: &[Vec<Scalar>],
    public_locations: &[(usize, usize)],
  ) -> Result<Self, String> {
    let mut seen = std::collections::BTreeSet::new();
    for &(row, column) in public_locations {
      if claims.get(row).and_then(|values| values.get(column)).is_none() {
        return Err("public claim location out of bounds".into());
      }
      if !seen.insert((row, column)) {
        return Err("duplicate public claim location".into());
      }
    }
    let rows = claims
      .iter()
      .enumerate()
      .map(|(row, values)| {
        values
          .iter()
          .enumerate()
          .map(|(column, &value)| {
            if seen.contains(&(row, column)) {
              ClaimSlot::PublicU64
            } else {
              ClaimSlot::Constant(value)
            }
          })
          .collect()
      })
      .collect();
    let schema = Self { rows, public_locations: public_locations.to_vec() };
    schema.validate(claims)?;
    Ok(schema)
  }

  pub(super) fn validate(&self, claims: &[Vec<Scalar>]) -> Result<(), String> {
    if claims.len() != self.rows.len()
      || claims
        .iter()
        .zip(&self.rows)
        .any(|(values, slots)| values.len() != slots.len())
    {
      return Err("claim dimensions differ from the statement schema".into());
    }
    for (values, slots) in claims.iter().zip(&self.rows) {
      for (&value, slot) in values.iter().zip(slots) {
        match slot {
          ClaimSlot::Constant(expected) if value != *expected => {
            return Err(
              "constant claim differs from the statement schema".into(),
            );
          },
          ClaimSlot::PublicU64
            if value.canonical_limbs_le()[1..]
              .iter()
              .any(|&limb| limb != 0) =>
          {
            return Err("public claim does not fit in u64".into());
          },
          _ => {},
        }
      }
    }
    Ok(())
  }

  #[cfg(test)]
  pub(super) fn public_values(&self, claims: &[Vec<Scalar>]) -> Vec<Scalar> {
    self
      .public_locations
      .iter()
      .map(|&(row, column)| claims[row][column])
      .collect()
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
pub(crate) struct LayoutPolicy {
  pub namespace: Scalar,
  pub max_computation_height: usize,
  pub max_table_height: usize,
}

impl LayoutPolicy {
  pub(super) fn legacy() -> Self {
    Self {
      namespace: Scalar::from_u8(94),
      max_computation_height: 1 << 29,
      max_table_height: 1 << 29,
    }
  }

  fn validate(self) -> Result<(), String> {
    if [self.max_computation_height, self.max_table_height]
      .iter()
      .any(|&height| height < 2 || !height.is_power_of_two())
    {
      return Err("layout caps must be nontrivial powers of two".into());
    }
    Ok(())
  }
}

pub(crate) struct Plan<'a> {
  pub(super) profile: Profile<'a>,
  pub(super) shape: Shape,
  pub(super) claims: ClaimSchema,
  pub(super) layout: LayoutPolicy,
  pub(super) identity: [u8; 32],
}

impl<'a> Plan<'a> {
  pub(crate) fn new(
    system: &'a System<KzgConfig>,
    logs: &[u8],
    claims: ClaimSchema,
    layout: LayoutPolicy,
  ) -> Result<Self, String> {
    if system.preprocessed_indices.len() != system.circuits.len()
      || system
        .preprocessed_indices
        .iter()
        .enumerate()
        .any(|(i, &index)| index != Some(i))
    {
      return Err(
        "wrapper requires one fixed matrix per circuit in canonical order"
          .into(),
      );
    }
    let params = system.config.pcs().verifier_params();
    let profile = Profile {
      circuits: &system.circuits,
      fixed: system
        .preprocessed_commit
        .as_ref()
        .ok_or("missing fixed commitment")?,
      transcript_seed: system.config.transcript_seed(),
      transcript_kind: system.config.transcript_kind(),
      generator: params.g1[0],
      g2: params.g2,
      tau_g2: params.tau_g2,
      max_log_degree: system.config.max_log_degree(),
    };
    let plan = Self::from_profile(&profile, logs, claims, layout)?;
    for (circuit, &log) in system.circuits.iter().zip(logs) {
      let quotient = circuit.quotient_degree();
      if quotient > system.config.max_quotient_degree()
        || usize::from(log) + quotient.ilog2() as usize
          > system.config.max_log_quotient_domain()
      {
        return Err(
          "circuit quotient exceeds the authenticated configuration".into(),
        );
      }
    }
    Ok(plan)
  }

  pub(super) fn from_profile(
    profile: &Profile<'a>,
    logs: &[u8],
    claims: ClaimSchema,
    layout: LayoutPolicy,
  ) -> Result<Self, String> {
    if profile.transcript_kind != crate::kzg::TranscriptKind::Blake3 {
      return Err(
        "recursive circuit requires a BLAKE3 inner transcript".into(),
      );
    }
    layout.validate()?;
    let shape = Shape::new(profile, logs)?;
    for point in profile
      .fixed
      .0
      .iter()
      .flatten()
      .chain(std::iter::once(&profile.generator))
    {
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("invalid fixed G1 verifier point".into());
      }
    }
    for point in [profile.g2, profile.tau_g2] {
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("invalid G2 verifier point".into());
      }
    }
    let identity = identity(profile, &shape, &claims, layout)?;
    Ok(Self { profile: *profile, shape, claims, layout, identity })
  }

  pub(crate) fn identity(&self) -> [u8; 32] {
    self.identity
  }

  pub(crate) fn count(&self) -> Result<Counts, String> {
    construct(&self.profile, &self.shape, &self.claims, Builder::counting())
      .map(|construction| construction.counts())
  }

  pub(crate) fn validate_compact_len(
    &self,
    bytes: usize,
  ) -> Result<(), String> {
    if bytes != self.shape.checked_compact_len()? {
      return Err(
        "compact proof length differs from the verifier profile".into(),
      );
    }
    Ok(())
  }

  pub(crate) fn build(
    &self,
    proof: &Proof<KzgConfig>,
    claims: &[Vec<Scalar>],
  ) -> Result<Built, String> {
    self.validate_request(proof, claims)?;
    let Compiled { circuit, bindings } = self.compile()?;
    let request = bindings.request_inputs(self.identity(), proof, claims)?;
    Ok(Built {
      circuit,
      inputs: request.inputs,
      points: request.points,
      pairing_outputs: bindings.pairing_outputs,
      pairing_keys: bindings.pairing_keys,
      terms: bindings.terms,
    })
  }

  pub(crate) fn compile(&self) -> Result<Compiled, String> {
    let construction =
      construct(&self.profile, &self.shape, &self.claims, Builder::new())?;
    let compiled = construction.finish(self);
    let layout = compiled
      .circuit
      .multi_stark_layout()
      .map_err(|error| error.to_string())?;
    if layout.main_heights.len() != 1
      || layout.main_height > self.layout.max_computation_height
    {
      return Err(
        "recursive computation does not fit one admitted trace".into(),
      );
    }
    let table_rows =
      compiled.circuit.tables().iter().try_fold(0usize, |sum, table| {
        sum.checked_add(table.rows().len()).ok_or("merged table size overflow")
      })?;
    let table_height = table_rows
      .max(2)
      .checked_next_power_of_two()
      .ok_or("merged table height overflow")?;
    if table_height > self.layout.max_table_height
      || !layout.custom_traces.is_empty()
    {
      return Err(
        "recursive tables do not fit one admitted merged table".into(),
      );
    }
    Ok(compiled)
  }

  pub(crate) fn validate_request(
    &self,
    proof: &Proof<KzgConfig>,
    claims: &[Vec<Scalar>],
  ) -> Result<(), String> {
    self.shape.validate(proof)?;
    self.claims.validate(claims)
  }
}

fn identity(
  profile: &Profile<'_>,
  shape: &Shape,
  claims: &ClaimSchema,
  layout: LayoutPolicy,
) -> Result<[u8; 32], String> {
  let mut hash = blake3::Hasher::new();
  hash.update(FRONTEND_VERSION);
  hash.update(b"one-computation-and-merged-table/v1");
  let parameters = (
    profile.transcript_seed,
    profile.max_log_degree,
    shape,
    claims,
    layout,
    (0..profile.circuits.len()).collect::<Vec<_>>(),
  );
  hash.update(
    &bincode::serde::encode_to_vec(parameters, bincode::config::standard())
      .map_err(|error| error.to_string())?,
  );
  for circuit in profile.circuits {
    let metadata = (
      &circuit.graph,
      circuit.main_width,
      circuit.preprocessed_width,
      circuit.preprocessed_height,
      circuit.num_lookups,
      circuit.stage_2_width,
      circuit.num_publics,
      circuit.lookup_group_size,
      circuit.constraint_count,
      circuit.max_constraint_degree,
    );
    let bytes =
      bincode::serde::encode_to_vec(metadata, bincode::config::standard())
        .map_err(|error| error.to_string())?;
    hash.update(&(bytes.len() as u64).to_le_bytes());
    hash.update(&bytes);
  }
  let mut points = vec![];
  profile
    .fixed
    .0
    .serialize_compressed(&mut points)
    .map_err(|error| error.to_string())?;
  profile
    .generator
    .serialize_compressed(&mut points)
    .map_err(|error| error.to_string())?;
  profile
    .g2
    .serialize_compressed(&mut points)
    .map_err(|error| error.to_string())?;
  profile
    .tau_g2
    .serialize_compressed(&mut points)
    .map_err(|error| error.to_string())?;
  hash.update(&(points.len() as u64).to_le_bytes());
  hash.update(&points);
  Ok(*hash.finalize().as_bytes())
}
