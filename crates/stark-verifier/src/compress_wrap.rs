//! Generic Goldilocks recursion as a stable input to fixed-shape compression.
//!
//! The recursive program verifies a key and claims supplied as data. Its public
//! arguments bind both byte strings, so the compression key can remain fixed
//! while a caller independently authorizes another root key and statement.
use aiur::{
  artifact::Package,
  bytecode::CheckedProgram,
  field::{FieldBackend, NativeField},
  trace::{
    TracePlan,
    stark::{Backend, BatchProof, Parameters, VerifyingKey},
  },
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

pub const ENTRY: &str = "CompressWrap::verify_root";
pub const STATEMENT_DOMAIN: &[u8; 20] = b"ix/compress-wrap/v1\0";
pub const STATEMENT_BYTES: usize = STATEMENT_DOMAIN.len() + 64;

type Field = NativeField<Val>;
type Program = CheckedProgram<Field>;

/// An independently authorized root statement, before recursive claim encoding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Statement {
  pub key_digest: [u8; 32],
  pub claims_digest: [u8; 32],
}

impl Statement {
  pub fn new(key_digest: [u8; 32], claims: &[Vec<Val>]) -> Self {
    Self {
      key_digest,
      claims_digest: *blake3::hash(&crate::claims_bytes(claims)).as_bytes(),
    }
  }

  /// The final statement's domain-separated digest preimage. Its two digests
  /// authenticate the original root key and every serialized root claim row.
  pub fn preimage(&self) -> [u8; STATEMENT_BYTES] {
    let mut bytes = [0; STATEMENT_BYTES];
    bytes[..STATEMENT_DOMAIN.len()].copy_from_slice(STATEMENT_DOMAIN);
    bytes[STATEMENT_DOMAIN.len()..STATEMENT_DOMAIN.len() + 32]
      .copy_from_slice(&self.key_digest);
    bytes[STATEMENT_DOMAIN.len() + 32..].copy_from_slice(&self.claims_digest);
    bytes
  }

  /// A fixed zero prefix and the packed statement digest. The fixed prefix
  /// keeps the outer compression verifier independent of the root's key.
  pub fn arguments(&self) -> [u64; 16] {
    let mut args = [0; 16];
    args[8..].copy_from_slice(&crate::digest_words(&self.preimage()));
    args
  }
}

/// A natively verified proof whose key is checked against a caller-supplied pin.
/// The original claims remain available as the digest preimage of the wrapper
/// statement; they must not be confused with the original Ix claim bytes.
pub struct Input {
  statement: Statement,
  key: Vec<u8>,
  claims: Vec<Vec<Val>>,
  claims_bytes: Vec<u8>,
  proof: Vec<u8>,
}

impl Input {
  pub fn new(
    key: &[u8],
    expected_key_digest: [u8; 32],
    expected_claims: &[Vec<Val>],
    proof: &[u8],
  ) -> Result<Self, String> {
    if blake3::hash(key).as_bytes() != &expected_key_digest {
      return Err(
        "compression wrapper root key differs from the trusted pin".into(),
      );
    }
    if expected_claims.is_empty() {
      return Err("compression wrapper needs an expected root claim".into());
    }
    let verifying_key = VerifyingKey::from_bytes(key)?;
    let decoded =
      BatchProof::from_bytes(proof).map_err(|error| error.to_string())?;
    if decoded.to_bytes().map_err(|error| error.to_string())? != proof {
      return Err("noncanonical or trailing root proof bytes".into());
    }
    verifying_key
      .verify(expected_claims, &decoded)
      .map_err(|error| format!("compression wrapper root proof: {error}"))?;
    Ok(Self {
      statement: Statement::new(expected_key_digest, expected_claims),
      key: key.to_vec(),
      claims: expected_claims.to_vec(),
      claims_bytes: crate::claims_bytes(expected_claims),
      proof: proof.to_vec(),
    })
  }

  pub fn from_bytes(
    key: &[u8],
    expected_key_digest: [u8; 32],
    expected_claims: &[u8],
    proof: &[u8],
  ) -> Result<Self, String> {
    Self::new(key, expected_key_digest, &decode_claims(expected_claims)?, proof)
  }

  pub const fn statement(&self) -> &Statement {
    &self.statement
  }

  pub fn key_bytes(&self) -> &[u8] {
    &self.key
  }

  pub fn claims(&self) -> &[Vec<Val>] {
    &self.claims
  }

  pub fn claims_bytes(&self) -> &[u8] {
    &self.claims_bytes
  }

  pub fn proof_bytes(&self) -> &[u8] {
    &self.proof
  }

  pub fn invocation(&self) -> crate::Invocation {
    let mut invocation =
      crate::invocation(&self.key, &self.claims_bytes, &self.proof);
    invocation.entry = ENTRY.into();
    invocation.args = self.statement.arguments().to_vec();
    invocation
  }
}

/// Decode the canonical little-endian list-of-claims format. Counts are bounded
/// by the remaining bytes before allocation, and every field word is canonical.
pub fn decode_claims(bytes: &[u8]) -> Result<Vec<Vec<Val>>, String> {
  let (words, rest) = bytes.as_chunks::<8>();
  if !rest.is_empty() || words.is_empty() {
    return Err("invalid root claims encoding".into());
  }
  let count = |word: [u8; 8]| {
    usize::try_from(u64::from_le_bytes(word))
      .map_err(|_error| "root claims length overflow".to_owned())
  };
  let rows = count(words[0])?;
  let mut words = &words[1..];
  if rows > words.len() {
    return Err("root claims count exceeds the input".into());
  }
  let mut claims = Vec::with_capacity(rows);
  for _ in 0..rows {
    let (length, rest) = words.split_first().ok_or("truncated root claims")?;
    let length = count(*length)?;
    if length > rest.len() {
      return Err("root claim length exceeds the input".into());
    }
    let (row, rest) = rest.split_at(length);
    let values = row
      .iter()
      .map(|bytes| {
        let word = u64::from_le_bytes(*bytes);
        if word >= Val::ORDER_U64 {
          Err("noncanonical root claim field word".to_owned())
        } else {
          Ok(Val::from_u64(word))
        }
      })
      .collect::<Result<_, _>>()?;
    claims.push(values);
    words = rest;
  }
  if !words.is_empty() {
    return Err("trailing root claims bytes".into());
  }
  Ok(claims)
}

/// A candidate normalized layout, bound to the generic verifier's compiled key.
/// Choosing a layout is a release/measurement operation, not part of proving
/// each input: all accepted inputs must fit the same independently chosen one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Layout {
  pub key_blake3: String,
  pub log_heights: Vec<u8>,
  pub memory_circuits: Vec<(usize, usize)>,
  pub claim_len: usize,
}

/// The trusted generic recursion artifact and its proving backend.
pub struct Wrapper {
  program: Arc<Program>,
  backend: Backend<'static, 'static, Field>,
  artifact_digest: [u8; 32],
  key: Vec<u8>,
  key_digest: [u8; 32],
  parameters: Parameters,
}

/// An execution whose public arguments and originating wrapper are retained.
pub struct Executed<'a> {
  input: &'a Input,
  record: aiur::Execution<Field>,
  args: Vec<Val>,
  wrapper_key_digest: [u8; 32],
  wrapper_artifact_digest: [u8; 32],
}

impl Executed<'_> {
  pub const fn input(&self) -> &Input {
    self.input
  }

  pub const fn record(&self) -> &aiur::Execution<Field> {
    &self.record
  }
}

/// Raw wrapper material plus the original root statement's digest preimages.
/// The key is transport data; a consumer must independently authorize it.
pub struct Proven {
  pub key: Vec<u8>,
  pub claims: Vec<u8>,
  pub proof: Vec<u8>,
  pub root_key: Vec<u8>,
  pub root_claims: Vec<u8>,
  pub statement: [u8; STATEMENT_BYTES],
  pub layout: Layout,
}

impl Wrapper {
  /// `package` must be trusted compiler output for the generic recursive
  /// verifier. This constructor checks structure, not the program's meaning.
  pub fn new(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    let artifact_digest = *blake3::hash(&package.encode()).as_bytes();
    let (program, trace) = package.traced()?;
    let mut program = program.check_field::<Val>()?;
    program.track_depth(&trace)?;
    program.entry(ENTRY)?;
    let program = Arc::new(program);
    let plan = Arc::new(TracePlan::new(Arc::clone(&program), trace)?);
    let backend = Backend::for_batch_on_device(plan, parameters, device)?;
    let claim = backend.claim(ENTRY, &[Val::ZERO; 16], &[])?;
    if claim.len() != 18 {
      return Err("compression wrapper must expose an 18-word claim".into());
    }
    let key = backend.verifying_key_bytes()?;
    let key_digest = *blake3::hash(&key).as_bytes();
    Ok(Self { program, backend, artifact_digest, key, key_digest, parameters })
  }

  pub fn key_bytes(&self) -> &[u8] {
    &self.key
  }

  pub const fn key_digest(&self) -> &[u8; 32] {
    &self.key_digest
  }

  pub const fn artifact_digest(&self) -> &[u8; 32] {
    &self.artifact_digest
  }

  pub const fn parameters(&self) -> Parameters {
    self.parameters
  }

  pub fn claim_for(&self, statement: &Statement) -> Result<Vec<Val>, String> {
    let args = self.program.field().decode(&statement.arguments())?;
    self.backend.claim(ENTRY, &args, &[])
  }

  pub fn execute<'a>(&self, input: &'a Input) -> Result<Executed<'a>, String> {
    let args = self.program.field().decode(&input.statement.arguments())?;
    let advice = crate::advice(
      self.program.field(),
      &input.key,
      &input.claims_bytes,
      &input.proof,
    )?;
    let record = crate::prepare_advice(&self.program, &advice)?
      .execute(ENTRY, args.clone())
      .map_err(|error| format!("compression wrapper execution: {error}"))?;
    if !record.output.is_empty() {
      return Err("compression wrapper returned a non-unit value".into());
    }
    Ok(Executed {
      input,
      record,
      args,
      wrapper_key_digest: self.key_digest,
      wrapper_artifact_digest: self.artifact_digest,
    })
  }

  pub fn statistics(
    &self,
    execution: &Executed<'_>,
  ) -> Result<aiur::trace::stark::ExecutionStatistics, String> {
    self.check_execution(execution)?;
    Ok(self.backend.execution_statistics(&execution.record))
  }

  pub fn plan_layout(
    &self,
    execution: &Executed<'_>,
    headroom: u8,
  ) -> Result<Layout, String> {
    self.check_execution(execution)?;
    let rows = self.backend.execution_rows(&execution.record);
    Ok(Layout {
      key_blake3: blake3::Hash::from(self.key_digest).to_hex().to_string(),
      log_heights: self.backend.normalized_log_heights(&rows, headroom)?,
      memory_circuits: self.backend.memory_circuits(),
      claim_len: 18,
    })
  }

  /// Prove one all-active shard at an explicitly supplied layout. No layout
  /// resizing occurs here; executions exceeding its bounds are rejected.
  pub fn prove_normalized(
    &self,
    execution: Executed<'_>,
    layout: &Layout,
  ) -> Result<Proven, String> {
    self.check_execution(&execution)?;
    self.validate_layout(layout)?;
    let (claim, proof) = self.backend.prove_normalized(
      ENTRY,
      &execution.args,
      &[],
      execution.record,
      &layout.log_heights,
    )?;
    check_normalized_shape(&proof, layout)?;
    Ok(Proven {
      key: self.key.clone(),
      claims: crate::claims_bytes(&[claim]),
      proof: proof.to_bytes().map_err(|error| error.to_string())?,
      root_key: execution.input.key.clone(),
      root_claims: execution.input.claims_bytes.clone(),
      statement: execution.input.statement.preimage(),
      layout: layout.clone(),
    })
  }

  pub fn validate_layout(&self, layout: &Layout) -> Result<(), String> {
    if layout.key_blake3
      != blake3::Hash::from(self.key_digest).to_hex().as_str()
      || layout.memory_circuits != self.backend.memory_circuits()
      || layout.claim_len != 18
    {
      return Err("compression wrapper layout differs from its backend".into());
    }
    let statistics = self.backend.statistics();
    if statistics.len() != layout.log_heights.len()
      || statistics.iter().zip(&layout.log_heights).any(|(circuit, &height)| {
        !(1..=26).contains(&height)
          || (circuit.preprocessed_height != 0
            && circuit.preprocessed_height != 1usize << height)
      })
    {
      return Err(
        "compression wrapper layout has invalid circuit heights".into(),
      );
    }
    Ok(())
  }

  /// Verify against root digests obtained independently of the wrapper proof.
  pub fn verify(
    &self,
    expected: &Statement,
    proof_bytes: &[u8],
  ) -> Result<(), String> {
    let proof = decode_proof(proof_bytes)?;
    let args = self.program.field().decode(&expected.arguments())?;
    self.backend.verify_batch(ENTRY, &args, &[], &proof)
  }

  /// Verify the independently expected statement and the exact geometry used
  /// by a fixed outer verifier, before constructing that verifier's circuit.
  pub fn verify_normalized(
    &self,
    expected: &Statement,
    proof_bytes: &[u8],
    layout: &Layout,
  ) -> Result<(), String> {
    self.validate_layout(layout)?;
    let proof = decode_proof(proof_bytes)?;
    check_normalized_shape(&proof, layout)?;
    let args = self.program.field().decode(&expected.arguments())?;
    self.backend.verify_batch(ENTRY, &args, &[], &proof)
  }

  fn check_execution(&self, execution: &Executed<'_>) -> Result<(), String> {
    if execution.wrapper_artifact_digest != self.artifact_digest {
      return Err("compression execution belongs to another artifact".into());
    }
    if execution.wrapper_key_digest != self.key_digest {
      return Err("compression execution belongs to another wrapper".into());
    }
    Ok(())
  }
}

fn decode_proof(bytes: &[u8]) -> Result<BatchProof, String> {
  let proof =
    BatchProof::from_bytes(bytes).map_err(|error| error.to_string())?;
  if proof.to_bytes().map_err(|error| error.to_string())? != bytes {
    return Err("noncanonical or trailing wrapper proof bytes".into());
  }
  Ok(proof)
}

fn check_normalized_shape(
  proof: &BatchProof,
  layout: &Layout,
) -> Result<(), String> {
  let [header] = proof.preamble.headers.as_slice() else {
    return Err(
      "normalized compression wrapper must have exactly one header".into(),
    );
  };
  if proof.proofs.len() != 1
    || header.active.len() != layout.log_heights.len()
    || header.active.iter().any(|&active| !active)
    || header.log_degrees != layout.log_heights
  {
    return Err(
      "compression wrapper proof geometry differs from its layout".into(),
    );
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    batch::ShardInput,
    expr::Expr,
    lookup::Lookup,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::GoldilocksBlake3Config,
  };
  use std::sync::OnceLock;

  struct Fixture {
    key: Vec<u8>,
    claims: Vec<Vec<Val>>,
    proof: Vec<u8>,
  }

  fn fixture() -> &'static Fixture {
    static FIXTURE: OnceLock<Fixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
      let parameters = Parameters::default();
      let cp = parameters.commitment();
      let fp = parameters.fri();
      let one = Expr::constant(Val::ONE);
      let mut message = vec![one.clone(), Expr::constant(Val::ZERO)];
      message.extend((0..16).map(Expr::main));
      let inputs = vec![CircuitInputs {
        main_width: 16,
        constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
        lookups: vec![Lookup::pull(one, message)],
        ..Default::default()
      }];
      let (system, pk) =
        System::new(GoldilocksBlake3Config::new(cp, fp), inputs);
      let mut words = (0..16).map(Val::from_u64).collect::<Vec<_>>();
      words[0] = Val::from_u64(3);
      words[1] = Val::from_u64(9);
      let mut claim = vec![Val::ONE, Val::ZERO];
      claim.extend_from_slice(&words);
      let claims = vec![claim];
      let witness = SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new(words, 16)],
        &system,
      );
      let proof = system.prove_batch(
        &pk,
        vec![ShardInput { claims: claims.clone(), witness }],
        vec![],
      );
      Fixture {
        key: stark_key::to_bytes(&system, cp, fp),
        claims,
        proof: proof.to_bytes().unwrap(),
      }
    })
  }

  #[test]
  fn verified_input_preserves_the_original_statement_and_fixed_prefix() {
    let f = fixture();
    let pin = *blake3::hash(&f.key).as_bytes();
    let input = Input::new(&f.key, pin, &f.claims, &f.proof).unwrap();
    assert_eq!(input.key_bytes(), f.key);
    assert_eq!(input.claims(), f.claims);
    assert_eq!(input.proof_bytes(), f.proof);
    let bytes = input.statement().preimage();
    assert_eq!(&bytes[..20], STATEMENT_DOMAIN);
    assert_eq!(&bytes[20..52], &pin);
    assert_eq!(&bytes[52..], blake3::hash(input.claims_bytes()).as_bytes());
    let invocation = input.invocation();
    assert_eq!(invocation.entry, ENTRY);
    assert_eq!(&invocation.args[..8], &[0; 8]);
    assert_eq!(&invocation.args[8..], crate::digest_words(&bytes));
    assert_eq!(
      invocation.streams,
      crate::invocation(&f.key, input.claims_bytes(), &f.proof).streams
    );
  }

  #[test]
  fn input_rejects_another_trusted_key_or_expected_root_claim() {
    let f = fixture();
    let pin = *blake3::hash(&f.key).as_bytes();
    let mut wrong_pin = pin;
    wrong_pin[0] ^= 1;
    assert!(Input::new(&f.key, wrong_pin, &f.claims, &f.proof).is_err());
    for index in [0, 1, 2, 10, 17] {
      let mut wrong = f.claims.clone();
      wrong[0][index] += Val::ONE;
      assert!(Input::new(&f.key, pin, &wrong, &f.proof).is_err());
    }
    let mut extra = f.claims.clone();
    extra.push(extra[0].clone());
    assert!(Input::new(&f.key, pin, &extra, &f.proof).is_err());
    assert!(Input::new(&f.key, pin, &[], &f.proof).is_err());
  }

  #[test]
  fn input_rejects_changed_openings_and_trailing_proof_bytes() {
    let f = fixture();
    let pin = *blake3::hash(&f.key).as_bytes();
    let mut proof = BatchProof::from_bytes(&f.proof).unwrap();
    proof.proofs[0].stage_1_opened_values[0][0][0] +=
      multi_stark::types::ExtVal::ONE;
    assert!(
      Input::new(&f.key, pin, &f.claims, &proof.to_bytes().unwrap()).is_err()
    );
    let mut trailing = f.proof.clone();
    trailing.push(0);
    assert!(Input::new(&f.key, pin, &f.claims, &trailing).is_err());
  }

  #[test]
  fn statement_binds_every_original_claim_word_and_the_key() {
    let claims = vec![(0..18).map(Val::from_u64).collect::<Vec<_>>()];
    let statement = Statement::new([7; 32], &claims);
    let changed_key = Statement::new([8; 32], &claims);
    assert_eq!(&statement.arguments()[..8], &changed_key.arguments()[..8]);
    assert_ne!(statement.arguments(), changed_key.arguments());
    for index in 0..claims[0].len() {
      let mut changed = claims.clone();
      changed[0][index] += Val::ONE;
      assert_ne!(
        statement.arguments(),
        Statement::new([7; 32], &changed).arguments()
      );
    }
  }

  #[test]
  fn claims_decoding_rejects_noncanonical_counts_words_and_suffixes() {
    let claims = vec![vec![Val::ZERO, Val::ONE], vec![]];
    let encoded = crate::claims_bytes(&claims);
    assert_eq!(decode_claims(&encoded).unwrap(), claims);
    for end in 0..encoded.len() {
      assert!(decode_claims(&encoded[..end]).is_err());
    }
    let mut too_many = encoded.clone();
    too_many[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_claims(&too_many).is_err());
    let mut too_long = encoded.clone();
    too_long[8..16].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(decode_claims(&too_long).is_err());
    let mut noncanonical = encoded.clone();
    noncanonical[16..24].copy_from_slice(&Val::ORDER_U64.to_le_bytes());
    assert!(decode_claims(&noncanonical).is_err());
    let mut trailing = encoded;
    trailing.extend_from_slice(&0u64.to_le_bytes());
    assert!(decode_claims(&trailing).is_err());
  }

  #[test]
  fn normalized_geometry_rejects_other_heights_inactive_circuits_and_batches() {
    let f = fixture();
    let proof = BatchProof::from_bytes(&f.proof).unwrap();
    let layout = Layout {
      key_blake3: blake3::hash(&f.key).to_hex().to_string(),
      log_heights: proof.preamble.headers[0].log_degrees.clone(),
      memory_circuits: vec![],
      claim_len: 18,
    };
    check_normalized_shape(&proof, &layout).unwrap();
    let mut wrong = layout.clone();
    wrong.log_heights[0] += 1;
    assert!(check_normalized_shape(&proof, &wrong).is_err());
    let mut inactive = proof.clone();
    inactive.preamble.headers[0].active[0] = false;
    assert!(check_normalized_shape(&inactive, &layout).is_err());
    let mut extra_header = proof.clone();
    extra_header
      .preamble
      .headers
      .push(extra_header.preamble.headers[0].clone());
    assert!(check_normalized_shape(&extra_header, &layout).is_err());
    let mut extra_proof = proof.clone();
    extra_proof.proofs.push(extra_proof.proofs[0].clone());
    assert!(check_normalized_shape(&extra_proof, &layout).is_err());
  }

  #[test]
  #[ignore = "requires IX_COMPRESS_WRAP_TEST_ARTIFACT to name an exported CompressWrap package"]
  fn execution_replay_rejects_another_artifact_with_the_same_key() {
    let path = std::env::var("IX_COMPRESS_WRAP_TEST_ARTIFACT").unwrap();
    let (package, _) = Package::load(path.as_ref()).unwrap();
    let mut variant = package.clone();
    variant.program.tables[0].name.push_str("_metadata_variant");
    let wrapper = Wrapper::new(package, Parameters::default(), None).unwrap();
    let other = Wrapper::new(variant, Parameters::default(), None).unwrap();
    assert_eq!(wrapper.key_bytes(), other.key_bytes());
    assert_ne!(wrapper.artifact_digest(), other.artifact_digest());
    let f = fixture();
    let input =
      Input::new(&f.key, *blake3::hash(&f.key).as_bytes(), &f.claims, &f.proof)
        .unwrap();
    let execution = wrapper.execute(&input).unwrap();
    let layout = wrapper.plan_layout(&execution, 0).unwrap();
    assert!(other.statistics(&execution).is_err());
    assert!(other.plan_layout(&execution, 0).is_err());
    assert!(other.prove_normalized(execution, &layout).is_err());
  }
}
