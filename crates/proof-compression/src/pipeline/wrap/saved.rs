use super::super::{
  setup::{BINDING_FILE, FIRST_SEED, SetupClass},
  statement,
};
use crate::{
  kzg::{KzgCommitment, KzgConfig, Scalar, compact::FixedProofCodec},
  recursive::native_verifier::{ClaimSchema, Plan},
};
#[cfg(test)]
use multi_stark::traits::Field;
use multi_stark::{
  prover::Proof,
  system::{Circuit, System},
};
use serde::de::DeserializeOwned;
use std::{collections::BTreeMap, fs, path::Path, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(serde::Deserialize)]
struct Manifest {
  widths: Vec<usize>,
  heights: Vec<usize>,
  claims: Vec<Vec<Scalar>>,
}

fn read_recorded(
  dir: &Path,
  name: &str,
  hashes: &mut BTreeMap<String, String>,
) -> Result<Vec<u8>> {
  let bytes = fs::read(dir.join(name))?;
  hashes.insert(name.into(), blake3::hash(&bytes).to_hex().to_string());
  Ok(bytes)
}

fn load<T: DeserializeOwned>(
  dir: &Path,
  name: &str,
  hashes: &mut BTreeMap<String, String>,
) -> Result<T> {
  let bytes = read_recorded(dir, name, hashes)?;
  let (result, used) =
    bincode::serde::decode_from_slice(&bytes, bincode::config::standard())?;
  if used != bytes.len() {
    return Err("trailing metadata".into());
  }
  Ok(result)
}

#[cfg(test)]
pub(super) fn layout() -> crate::recursive::native_verifier::LayoutPolicy {
  super::super::stages::construct::recursive_layout()
}

pub(super) fn claim_schema(claims: &[Vec<Scalar>]) -> Result<ClaimSchema> {
  let public =
    super::super::stages::statement::Statement::from_claims(claims, 18)?
      .locations;
  Ok(ClaimSchema::from_claims(claims, &public)?)
}

struct Input {
  system: System<KzgConfig>,
  proof: Proof<KzgConfig>,
  claims: Vec<Vec<Scalar>>,
  logs: Vec<u8>,
  proof_bytes: Vec<u8>,
  input_blake3: BTreeMap<String, String>,
  setup_identity: [u8; 32],
  development_srs: bool,
  load_seconds: f64,
}

impl Input {
  fn plan(&self) -> Result<Plan<'_>> {
    super::super::stages::construct::recursive_plan(
      &self.system,
      &self.logs,
      claim_schema(&self.claims)?,
    )
  }

  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/load_input"
  )]
  fn load(dir: &Path, config: &super::super::WorkerConfig) -> Result<Self> {
    let start = Instant::now();
    let mut input_blake3 = BTreeMap::new();
    let manifest: Manifest = load(dir, "manifest.bin", &mut input_blake3)?;
    let count = manifest.heights.len();
    let height =
      *manifest.heights.iter().max().ok_or("empty recursive profile")?;
    // The partition count follows the outer FRI proof's layout; the trace
    // height is the supported profile's. Profile identity is bound separately
    // through the profile id and the application's bundled verifier.
    if ![1 << 24, 1 << 25].contains(&height)
      || count < super::super::first::MIN_PARTITIONS
      || manifest.widths.len() != count
      || manifest.widths.contains(&0)
      || manifest.heights.iter().any(|h| *h < 2 || !h.is_power_of_two())
    {
      return Err("unsupported partition profile".into());
    }
    let statement = statement::from_rows(&manifest.claims)?;
    if manifest.claims
      != super::super::first::expected_claims(count, &statement)
    {
      return Err("claim rows differ from the statement and anchors".into());
    }
    eprintln!("Loading authenticated verifier parameters and saved proof");
    let proof_dir = if dir.join("kzg").is_dir() {
      dir.join("kzg")
    } else {
      dir.to_path_buf()
    };
    let setup = config.setup.for_stage(FIRST_SEED, height)?;
    setup.check_binding(dir, height, 2)?;
    let setup_id = setup.identity(height, 2)?;
    if read_recorded(dir, BINDING_FILE, &mut input_blake3)? != setup_id {
      return Err("setup binding changed while loading saved metadata".into());
    }
    let config = setup.config(height, 2, true)?;
    let mut circuits = vec![];
    let mut commitment = KzgCommitment(vec![]);
    for i in 0..count {
      let (circuit, mut part): (Circuit<Scalar>, KzgCommitment) =
        load(&proof_dir, &format!("setup-{i}.bin"), &mut input_blake3)?;
      if circuit.preprocessed_height != manifest.heights[i]
        || circuit.main_width != manifest.widths[i]
        || circuit.preprocessed.is_some()
        || part.0.len() != 1
      {
        return Err("inconsistent setup metadata".into());
      }
      circuits.push(circuit);
      commitment.0.append(&mut part.0);
    }
    let system = System {
      config,
      circuits,
      preprocessed_commit: Some(commitment),
      preprocessed_indices: (0..count).map(Some).collect(),
    };
    let logs: Vec<_> = manifest
      .heights
      .iter()
      .map(|h| u8::try_from(h.ilog2()).unwrap())
      .collect();
    let plan = super::super::stages::construct::recursive_plan(
      &system,
      &logs,
      claim_schema(&manifest.claims)?,
    )?;
    let proof_bytes =
      read_recorded(&proof_dir, "proof.compact.bin", &mut input_blake3)?;
    plan.validate_compact_len(proof_bytes.len())?;
    let proof = FixedProofCodec::new(&system, &logs)?.decode(&proof_bytes)?;
    plan.validate_request(&proof, &manifest.claims)?;
    let refs: Vec<_> = manifest.claims.iter().map(Vec::as_slice).collect();
    system
      .verify_multiple_claims(&refs, &proof)
      .map_err(|e| format!("native verification: {e:?}"))?;
    eprintln!(
      "Saved {}-byte proof verifies natively: {:?}",
      proof_bytes.len(),
      start.elapsed()
    );
    Ok(Self {
      system,
      proof,
      claims: manifest.claims,
      logs,
      proof_bytes,
      input_blake3,
      setup_identity: setup_id,
      development_srs: setup.class() == SetupClass::Development,
      load_seconds: start.elapsed().as_secs_f64(),
    })
  }
}

pub(crate) fn check(
  dir: &Path,
  report: &Path,
  stage: Option<&Path>,
  config: &super::super::WorkerConfig,
) -> Result<()> {
  let start = Instant::now();
  let input = Input::load(dir, config)?;
  let build_start = Instant::now();
  let plan = input.plan()?;
  let fixed_profile = plan.identity();
  let built = tracing::info_span!("compression/build_circuit")
    .in_scope(|| plan.build(&input.proof, &input.claims))?;
  let build_seconds = build_start.elapsed().as_secs_f64();
  let witness_start = Instant::now();
  let assignment =
    tracing::info_span!("compression/witness").in_scope(|| built.assign())?;
  let witness_seconds = witness_start.elapsed().as_secs_f64();
  let stats = built.circuit.stats();
  let result = serde_json::json!({
    "gates": stats.gates,
    "lookups": stats.lookups,
    "values": stats.values,
    "rows": stats.gates + stats.lookups + stats.publics + 1,
    "public_values": stats.publics,
    "pairing_points": built.pairing_keys.len(),
    "msm_terms": built.msm_terms,
    "witness_seconds": witness_seconds,
    "circuit_satisfied": true,
    "external_pairings_pass": true,
    "outer_proof_generated": false,
    "input_proof_bytes": input.proof_bytes.len(),
    "input_proof_blake3": blake3::hash(&input.proof_bytes).to_hex().to_string(),
    "input_blake3": input.input_blake3,
    "setup_id": blake3::Hash::from_bytes(input.setup_identity).to_hex().to_string(),
    "frontend_identity": blake3::Hash::from_bytes(fixed_profile).to_hex().to_string(),
    "load_and_native_verify_seconds": input.load_seconds,
    "build_seconds": build_seconds,
    "total_seconds": start.elapsed().as_secs_f64(),
    "development_srs": input.development_srs,
    "scope": "Full saved first-stage KZG proof checked by recursive constraints and external pairings; no outer proof yet",
  });
  fs::write(report, serde_json::to_vec_pretty(&result)?)?;
  println!("{}", serde_json::to_string_pretty(&result)?);
  if let Some(stage) = stage {
    let statement = statement::from_rows(&input.claims)?;
    super::outer::stage(
      built,
      assignment,
      stage,
      &fixed_profile,
      &statement,
      config,
    )?;
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::Srs;
  use crate::recursive::native_verifier::LayoutPolicy;
  use crate::pipeline::init_claim;
  use crate::pipeline::setup::SetupSource;
  use multi_stark::traits::Algebra;
  use multi_stark::{
    expr::Expr,
    lookup::Lookup,
    system::{CircuitInputs, ProverKey, SystemWitness},
  };
  use p3_matrix::dense::RowMajorMatrix;
  use std::sync::Arc;

  fn input(
    system: System<KzgConfig>,
    key: &ProverKey<KzgConfig>,
    words: [u64; 18],
  ) -> Input {
    let claims: Vec<_> = std::iter::once(0)
      .chain(words)
      .enumerate()
      .map(|(index, value)| {
        vec![
          Scalar::from_u8(93),
          Scalar::ONE,
          Scalar::from_usize(index),
          Scalar::from_u64(value),
        ]
      })
      .collect();
    let main = RowMajorMatrix::new(
      words.into_iter().map(Scalar::from_u64).collect::<Vec<_>>().repeat(4),
      18,
    );
    let refs: Vec<_> = claims.iter().map(Vec::as_slice).collect();
    let proof = system.prove_multiple_claims(
      key,
      &refs,
      SystemWitness::from_stage_1(vec![main], &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    let proof_bytes =
      FixedProofCodec::new(&system, &[2]).unwrap().encode(&proof).unwrap();
    Input {
      system,
      proof,
      claims,
      logs: vec![2],
      proof_bytes,
      input_blake3: BTreeMap::new(),
      setup_identity: [0; 32],
      development_srs: true,
      load_seconds: 0.0,
    }
  }

  #[test]
  fn saved_plan_excludes_public_words_and_binds_constants_and_layout() {
    let config = KzgConfig::new(
      Arc::new(Srs::unsafe_dev_setup(8, b"saved-plan-fixture")),
      2,
    );
    let definition = CircuitInputs {
      main_width: 18,
      preprocessed: Some(RowMajorMatrix::new_col(vec![
        Scalar::ONE,
        Scalar::ZERO,
        Scalar::ZERO,
        Scalar::ZERO,
      ])),
      constraints: (0..18)
        .map(|i| Expr::main_next(i) - Expr::main(i))
        .collect(),
      lookups: (0..19)
        .map(|index| {
          Lookup::pull(
            Expr::preprocessed(0),
            vec![
              Expr::constant(Scalar::from_u8(93)),
              Expr::constant(Scalar::ONE),
              Expr::constant(Scalar::from_usize(index)),
              if index == 0 {
                Expr::constant(Scalar::ZERO)
              } else {
                Expr::main(u32::try_from(index - 1).unwrap())
              },
            ],
          )
        })
        .collect(),
      ..Default::default()
    };
    let (first_system, first_key) =
      System::new(config.clone(), [definition.clone()]);
    let (second_system, second_key) = System::new(config, [definition]);
    let first = input(first_system, &first_key, [0; 18]);
    let mut second =
      input(second_system, &second_key, std::array::from_fn(|i| i as u64));
    assert_ne!(first.proof_bytes, second.proof_bytes);
    let identity = first.plan().unwrap().identity();
    assert_eq!(identity, second.plan().unwrap().identity());
    let other = LayoutPolicy { max_table_height: 1 << 20, ..layout() };
    assert_ne!(
      identity,
      Plan::new(
        &first.system,
        &first.logs,
        claim_schema(&first.claims).unwrap(),
        other
      )
      .unwrap()
      .identity()
    );
    for claim in &mut second.claims {
      claim[0] += Scalar::ONE;
    }
    assert_ne!(identity, second.plan().unwrap().identity());
    for claim in &mut second.claims {
      claim[0] -= Scalar::ONE;
    }
    second.claims[0][3] = Scalar::ONE;
    assert!(second.plan().is_err());
    second.claims[0][3] = Scalar::ZERO;
    second.claims[18][3] = Scalar::from_limbs_le([0, 1, 0, 0]);
    assert!(second.plan().is_err());
  }

  #[test]
  fn saved_loader_requires_binding_before_setup_metadata() -> Result<()> {
    let root = std::env::temp_dir()
      .join(format!("ix-saved-binding-{}", std::process::id()));
    fs::create_dir(&root)?;
    let ns = Scalar::from_u8(93);
    let mut claims: Vec<_> = std::iter::once(0)
      .chain(init_claim::INIT_PUBLIC_WORDS)
      .enumerate()
      .map(|(index, word)| {
        vec![ns, Scalar::ONE, Scalar::from_usize(index), Scalar::from_u64(word)]
      })
      .collect();
    claims.extend(
      (0..11).map(|i| vec![ns, Scalar::from_u8(3), Scalar::from_usize(i)]),
    );
    claims.extend((0..6).map(|i| {
      vec![ns, Scalar::from_u8(4), Scalar::from_u8(3), Scalar::from_usize(i)]
    }));
    let manifest = (vec![1usize; 21], vec![1usize << 24; 21], claims);
    fs::write(
      root.join("manifest.bin"),
      bincode::serde::encode_to_vec(&manifest, bincode::config::standard())?,
    )?;
    fs::write(root.join("setup-0.bin"), [0xff])?;
    let missing =
      Input::load(&root, &crate::pipeline::WorkerConfig::development())
        .err()
        .unwrap();
    assert_eq!(
      missing.downcast_ref::<std::io::Error>().unwrap().kind(),
      std::io::ErrorKind::NotFound
    );
    fs::write(root.join(BINDING_FILE), [0; 32])?;
    let wrong =
      Input::load(&root, &crate::pipeline::WorkerConfig::development())
        .err()
        .unwrap();
    assert!(wrong.to_string().contains("mismatch"));
    fs::remove_file(root.join(BINDING_FILE))?;
    fs::write(
      root.join(BINDING_FILE),
      SetupSource::development(FIRST_SEED, (1 << 24) - 1)?
        .identity(1 << 24, 2)?,
    )?;
    let malformed =
      Input::load(&root, &crate::pipeline::WorkerConfig::development())
        .err()
        .unwrap();
    assert!(malformed.downcast_ref::<bincode::error::DecodeError>().is_some());
    fs::remove_dir_all(root)?;
    Ok(())
  }
}
