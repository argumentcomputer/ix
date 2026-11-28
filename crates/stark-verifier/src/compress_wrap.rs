//! Generic Goldilocks recursion as a stable input to fixed-shape compression.
//!
//! The recursive program verifies a key and claims supplied as data. Its public
//! arguments bind both byte strings, so the compression key can remain fixed
//! while a caller independently authorizes another root key and statement.
use aiur::{
  artifact::{EXECUTION_MAGIC, ExecutionPackage, PACKAGE_MAGIC, Package},
  bytecode::{CheckedProgram, Program as RawProgram, Type},
  field::{FieldBackend, NativeField},
  hints::{HintChannels, PreparedHints},
  library::{advice::Advice, io::StreamAdvice},
  maps::MapOverrides,
  trace::{
    TracePlan,
    stark::{
      Backend, BatchProof, Parameters, RomLayout, VerifyingKey, rom_lanes,
      wide::{CrossCheck, Export, WideBackend},
    },
  },
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use serde::{Deserialize, Serialize};
use std::{
  path::{Path, PathBuf},
  sync::Arc,
};

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
    self.invocation_for(ENTRY)
  }

  pub fn invocation_for(&self, entry: &str) -> crate::Invocation {
    let mut invocation =
      crate::invocation(&self.key, &self.claims_bytes, &self.proof);
    invocation.entry = entry.into();
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
  /// Where the wrapper's circuits come from: absent for the Rust lowering
  /// (with `MEMSEG`-closed ROM circuits), [`LEAN_LOWERING`] for the Lean
  /// exporter's tables (fixed-address ROM tables, no boundary messages).
  /// Absent, it is not serialized, so earlier layouts keep their digests.
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub lowering: Option<String>,
}

/// [`Layout::lowering`] of a wrapper whose circuits are `wide_export`'s
/// (singles, groups, every map in the compiler's shared layout, power-of-two
/// rows, one `romCircuit` per memory width at the layout's capacity).
pub const LEAN_LOWERING: &str = "lean-wide-v1";

impl Layout {
  /// Digest of the compact JSON encoding, used to pin a layout alongside the
  /// wrapper key in downstream stage policies.
  pub fn blake3(&self) -> Result<[u8; 32], String> {
    let bytes = serde_json::to_vec(self).map_err(|error| error.to_string())?;
    Ok(*blake3::hash(&bytes).as_bytes())
  }
}

pub const LAYOUT_CONFIG_FORMAT: &str = "ix-compress-wrap-layout-v1";

/// A versioned normalized layout for one wrapper artifact. Every root accepted
/// under this configuration is proven at exactly these capacities, so the
/// wrapper proof's geometry is independent of which root it wraps. `sizing`
/// records how the capacities were chosen and is not consulted when proving.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LayoutConfig {
  pub format: String,
  pub version: u32,
  pub grouping: String,
  pub artifact_blake3: String,
  pub layout: Layout,
  pub layout_blake3: String,
  pub sizing: serde_json::Value,
}

impl LayoutConfig {
  /// Check the configuration's internal consistency and that it names this
  /// wrapper artifact and key.
  pub fn check(&self, wrapper: &Wrapper) -> Result<(), String> {
    if self.format != LAYOUT_CONFIG_FORMAT {
      return Err("unknown compression wrapper layout format".into());
    }
    if self.artifact_blake3
      != blake3::Hash::from(wrapper.artifact_digest).to_hex().as_str()
    {
      return Err(
        "compression wrapper layout names another wrapper artifact".into(),
      );
    }
    if self.layout_blake3
      != blake3::Hash::from(self.layout.blake3()?).to_hex().as_str()
    {
      return Err("compression wrapper layout digest mismatch".into());
    }
    wrapper.validate_layout(&self.layout)
  }
}

/// Unpadded per-circuit rows of one execution against a layout's capacities.
#[derive(Clone, Debug, Serialize)]
pub struct Admission {
  pub circuits: Vec<AdmittedCircuit>,
}

#[derive(Clone, Debug, Serialize)]
pub struct AdmittedCircuit {
  pub name: String,
  pub rows: usize,
  pub log_height: u8,
  pub fixed: bool,
}

/// The wrapper's circuits: the Rust lowering, or the Lean exporter's over a
/// Rust row generator.
enum Circuits {
  Rust(Box<Backend<'static, 'static, Field>>),
  Lean(Box<WideBackend<'static, 'static, Field>>),
}

/// The same call on either lowering.
macro_rules! circuits {
  ($circuits:expr, $backend:ident => $call:expr) => {
    match $circuits {
      Circuits::Rust($backend) => $call,
      Circuits::Lean($backend) => $call,
    }
  };
}

/// The trusted generic recursion artifact and its proving backend.
pub struct Wrapper {
  program: Arc<Program>,
  entry: String,
  advice_program: Option<RawProgram>,
  backend: Circuits,
  artifact_digest: [u8; 32],
  key: Vec<u8>,
  key_digest: [u8; 32],
  parameters: Parameters,
  cross_check: Option<CrossCheck>,
}

/// The Lean exporter `wide_export` and the directory caching its exports, by
/// exporter binary and input contents (`IX_WIDE_EXPORT`,
/// `IX_WIDE_EXPORT_CACHE`). Exports are layout-only, so a cached one is the
/// exporter's output for that input; a different export changes the key,
/// which the layout pins.
pub struct Exporter {
  pub binary: PathBuf,
  pub cache: PathBuf,
}

/// A source of `wide_export` exports: the artifact file the exporter input
/// names, and the export (layout JSON, fixed file) of an input.
pub trait WideExporter: Sync {
  /// The artifact's bytes at a path named by their digest.
  fn artifact(&self, bytes: &[u8], digest: &str) -> Result<PathBuf, String>;
  /// The layout and fixed file of `input`.
  fn export(
    &self,
    input: &serde_json::Value,
  ) -> Result<(Vec<u8>, Vec<u8>), String>;
}

impl WideExporter for Exporter {
  fn artifact(&self, bytes: &[u8], digest: &str) -> Result<PathBuf, String> {
    Self::artifact(self, bytes, digest)
  }

  fn export(
    &self,
    input: &serde_json::Value,
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    Self::export(self, input)
  }
}

const WIDE_COMPLETE_FORMAT: &str = "ix-wide-export-complete-v1";

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct WideCompleteMarker {
  format: String,
  key: String,
  binary_blake3: String,
  input_blake3: String,
  layout_blake3: String,
  fixed_blake3: String,
}

impl Exporter {
  pub fn from_env() -> Result<Self, String> {
    let var = |name: &str| {
      std::env::var_os(name)
        .map(PathBuf::from)
        .ok_or_else(|| format!("set {name} for the Lean wrapper circuits"))
    };
    Ok(Self {
      binary: var("IX_WIDE_EXPORT")?,
      cache: var("IX_WIDE_EXPORT_CACHE")?,
    })
  }

  /// The artifact's bytes at a path named by their digest, for the exporter.
  fn artifact(&self, bytes: &[u8], digest: &str) -> Result<PathBuf, String> {
    let directory = self.cache.join("artifacts");
    let path = directory.join(format!("{digest}.ixa"));
    if std::fs::read(&path).is_ok_and(|stored| stored == bytes) {
      return Ok(path);
    }
    std::fs::create_dir_all(&directory)
      .map_err(|e| format!("{}: {e}", directory.display()))?;
    let staging = directory.join(format!(".{digest}.{}", std::process::id()));
    std::fs::write(&staging, bytes)
      .and_then(|()| std::fs::rename(&staging, &path))
      .map_err(|e| format!("{}: {e}", path.display()))?;
    std::path::absolute(&path).map_err(|e| e.to_string())
  }

  /// Verify an existing cache entry's authenticated `complete` sentinel and
  /// return the verified `(layout.json, fixed.bin)` bytes. Refuses empty,
  /// malformed, mismatched, or tampered cache entries fail-closed.
  fn read_verified_entry(
    entry: &Path,
    key: &str,
    binary_blake3: &str,
    input_blake3: &str,
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    let read =
      |p: &Path| std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()));
    let complete_path = entry.join("complete");
    let raw = read(&complete_path)?;
    if raw.is_empty() {
      return Err(format!(
        "{}: unauthenticated empty complete marker; refusing stale cache entry",
        complete_path.display()
      ));
    }
    let marker: WideCompleteMarker = serde_json::from_slice(&raw).map_err(|e| {
      format!(
        "{}: malformed complete marker ({e}); refusing cache entry",
        complete_path.display()
      )
    })?;
    if marker.format != WIDE_COMPLETE_FORMAT {
      return Err(format!(
        "{}: unsupported complete marker format {:?}",
        complete_path.display(),
        marker.format
      ));
    }
    if marker.key != key
      || marker.binary_blake3 != binary_blake3
      || marker.input_blake3 != input_blake3
    {
      return Err(format!(
        "{}: complete marker metadata differs from requested export",
        complete_path.display()
      ));
    }
    let stored_input = read(&entry.join("input.json"))?;
    let actual_input = blake3::hash(&stored_input).to_hex().to_string();
    if actual_input != marker.input_blake3 {
      return Err(format!(
        "{}: input.json BLAKE3 {actual_input} differs from complete marker {}",
        entry.display(),
        marker.input_blake3
      ));
    }
    let layout = read(&entry.join("layout.json"))?;
    let actual_layout = blake3::hash(&layout).to_hex().to_string();
    if actual_layout != marker.layout_blake3 {
      return Err(format!(
        "{}: layout.json BLAKE3 {actual_layout} differs from complete marker {}",
        entry.display(),
        marker.layout_blake3
      ));
    }
    let fixed = read(&entry.join("fixed.bin"))?;
    let actual_fixed = blake3::hash(&fixed).to_hex().to_string();
    if actual_fixed != marker.fixed_blake3 {
      return Err(format!(
        "{}: fixed.bin BLAKE3 {actual_fixed} differs from complete marker {}",
        entry.display(),
        marker.fixed_blake3
      ));
    }
    Ok((layout, fixed))
  }

  /// The layout and fixed file of `input`, exported once per exporter
  /// binary and input. Cache hits verify BLAKE3 digests of `input.json`,
  /// `layout.json`, and `fixed.bin` recorded in the `complete` sentinel.
  pub fn export(
    &self,
    input: &serde_json::Value,
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    let read =
      |p: &Path| std::fs::read(p).map_err(|e| format!("{}: {e}", p.display()));
    let input = serde_json::to_vec_pretty(input).map_err(|e| e.to_string())?;
    let binary_hash = blake3::hash(&read(&self.binary)?);
    let input_hash = blake3::hash(&input);
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix/wide-export-cache/v1\0");
    hasher.update(binary_hash.as_bytes());
    hasher.update(input_hash.as_bytes());
    let key = hasher.finalize().to_hex().to_string();
    let binary_blake3 = binary_hash.to_hex().to_string();
    let input_blake3 = input_hash.to_hex().to_string();
    let entry = self.cache.join(&key);
    if entry.join("complete").is_file() {
      return Self::read_verified_entry(
        &entry,
        &key,
        &binary_blake3,
        &input_blake3,
      );
    }
    std::fs::create_dir_all(&self.cache)
      .map_err(|e| format!("{}: {e}", self.cache.display()))?;
    let staging = self.cache.join(format!(
      ".tmp-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos())
    ));
    let io = |e: std::io::Error| format!("{}: {e}", staging.display());
    std::fs::create_dir_all(&staging).map_err(io)?;
    std::fs::write(staging.join("input.json"), &input).map_err(io)?;
    let log = std::fs::File::create(staging.join("export.log")).map_err(io)?;
    let status = std::process::Command::new(&self.binary)
      .arg(staging.join("input.json"))
      .arg(staging.join("layout.json"))
      .arg(staging.join("fixed.bin"))
      .stderr(log)
      .status()
      .map_err(|e| format!("{}: {e}", self.binary.display()))?;
    if !status.success() {
      return Err(format!(
        "{} failed ({status}); see {}",
        self.binary.display(),
        staging.join("export.log").display()
      ));
    }
    let layout = read(&staging.join("layout.json"))?;
    let fixed = read(&staging.join("fixed.bin"))?;
    let marker = WideCompleteMarker {
      format: WIDE_COMPLETE_FORMAT.to_owned(),
      key: key.clone(),
      binary_blake3: binary_blake3.clone(),
      input_blake3: input_blake3.clone(),
      layout_blake3: blake3::hash(&layout).to_hex().to_string(),
      fixed_blake3: blake3::hash(&fixed).to_hex().to_string(),
    };
    let marker_bytes =
      serde_json::to_vec_pretty(&marker).map_err(|e| e.to_string())?;
    std::fs::write(staging.join("complete"), &marker_bytes).map_err(io)?;
    if std::fs::rename(&staging, &entry).is_err() {
      // Another process published this entry first; verify its sentinel too.
      let _ = std::fs::remove_dir_all(&staging);
      return Self::read_verified_entry(
        &entry,
        &key,
        &binary_blake3,
        &input_blake3,
      );
    }
    Ok((layout, fixed))
  }
}

/// The exporter of a Rust-lowering layout, which exports nothing.
struct NoExporter;

impl WideExporter for NoExporter {
  fn artifact(&self, _: &[u8], _: &str) -> Result<PathBuf, String> {
    Err("this wrapper layout has no Lean circuits".into())
  }

  fn export(
    &self,
    _: &serde_json::Value,
  ) -> Result<(Vec<u8>, Vec<u8>), String> {
    Err("this wrapper layout has no Lean circuits".into())
  }
}

/// Whether to compare the Lean circuits with the Rust lowering on
/// construction (`IX_WRAP_RUST_CROSS_CHECK=1`).
fn cross_check_requested() -> Result<bool, String> {
  match std::env::var("IX_WRAP_RUST_CROSS_CHECK").as_deref() {
    Err(_) | Ok("" | "0") => Ok(false),
    Ok("1") => Ok(true),
    Ok(other) => {
      Err(format!("IX_WRAP_RUST_CROSS_CHECK must be 0 or 1, not {other:?}"))
    },
  }
}

/// Capacities of the Lean wrapper's tables (its ROM tables' fixed heights).
#[derive(Clone, Copy)]
pub enum Capacities<'a> {
  /// A Lean layout's heights, in its circuit order.
  Lean(&'a [u8]),
  /// A Rust-lowering layout's heights, translated by circuit.
  Rust(&'a [u8]),
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
  /// Authenticate the compiler package and derived backend key against
  /// independently selected pins before accepting a wrapper proof.
  pub fn from_bytes(
    bytes: &[u8],
    artifact_pin: &[u8; 32],
    key_pin: &[u8; 32],
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::from_bytes_with_entry(
      bytes,
      artifact_pin,
      key_pin,
      parameters,
      device,
      ENTRY,
    )
  }

  /// [`Self::from_bytes`] selecting a custom entry point (e.g., `"Prog::main0"`
  /// for an `ixcc-aiur` compiled wrapper circuit).
  pub fn from_bytes_with_entry(
    bytes: &[u8],
    artifact_pin: &[u8; 32],
    key_pin: &[u8; 32],
    parameters: Parameters,
    device: Option<i32>,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    if blake3::hash(bytes).as_bytes() != artifact_pin {
      return Err(
        "compression wrapper artifact differs from the trusted pin".into(),
      );
    }
    let wrapper =
      Self::new_with_entry(Package::decode(bytes)?, parameters, device, entry)?;
    if wrapper.key_digest() != key_pin {
      return Err(
        "compression wrapper key differs from the trusted pin".into(),
      );
    }
    Ok(wrapper)
  }

  /// The wrapper for `layout`'s lowering ([`Self::new`] or [`Self::lean`]),
  /// checked against the layout.
  pub fn for_layout(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
  ) -> Result<Self, String> {
    Self::for_layout_entry(package, parameters, device, layout, ENTRY)
  }

  /// [`Self::for_layout`] selecting a custom entry point.
  pub fn for_layout_entry(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    match layout.lowering.as_deref() {
      Some(LEAN_LOWERING) => Self::for_layout_with_entry(
        package,
        parameters,
        device,
        layout,
        &Exporter::from_env()?,
        entry,
      ),
      _ => Self::for_layout_with_entry(
        package,
        parameters,
        device,
        layout,
        &NoExporter,
        entry,
      ),
    }
  }

  /// [`Self::for_layout`] with the Lean circuits from `exporter`.
  pub fn for_layout_with(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
    exporter: &dyn WideExporter,
  ) -> Result<Self, String> {
    Self::for_layout_with_entry(
      package, parameters, device, layout, exporter, ENTRY,
    )
  }

  /// [`Self::for_layout_with`] selecting a custom entry point (e.g.,
  /// `"Prog::main0"` or [`ENTRY`]).
  pub fn for_layout_with_entry(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
    exporter: &dyn WideExporter,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    let entry = entry.into();
    let wrapper = match layout.lowering.as_deref() {
      None => Self::new_with_entry(package, parameters, device, entry)?,
      Some(LEAN_LOWERING) => Self::lean_with_entry(
        package,
        parameters,
        device,
        Capacities::Lean(&layout.log_heights),
        exporter,
        entry,
      )?,
      Some(other) => return Err(format!("unknown wrapper lowering {other:?}")),
    };
    wrapper.validate_layout(layout)?;
    Ok(wrapper)
  }

  /// [`Self::from_bytes`] for `layout`'s lowering ([`Self::for_layout`]).
  pub fn from_bytes_for_layout(
    bytes: &[u8],
    artifact_pin: &[u8; 32],
    key_pin: &[u8; 32],
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
  ) -> Result<Self, String> {
    Self::from_bytes_for_layout_with_entry(
      bytes,
      artifact_pin,
      key_pin,
      parameters,
      device,
      layout,
      ENTRY,
    )
  }

  /// [`Self::from_bytes_for_layout`] selecting a custom entry point.
  pub fn from_bytes_for_layout_with_entry(
    bytes: &[u8],
    artifact_pin: &[u8; 32],
    key_pin: &[u8; 32],
    parameters: Parameters,
    device: Option<i32>,
    layout: &Layout,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    if blake3::hash(bytes).as_bytes() != artifact_pin {
      return Err(
        "compression wrapper artifact differs from the trusted pin".into(),
      );
    }
    let wrapper = Self::for_layout_entry(
      Package::decode(bytes)?,
      parameters,
      device,
      layout,
      entry,
    )?;
    if wrapper.key_digest() != key_pin {
      return Err(
        "compression wrapper key differs from the trusted pin".into(),
      );
    }
    Ok(wrapper)
  }

  fn program(
    package: Package,
    entry: &str,
  ) -> Result<([u8; 32], Arc<Program>, Arc<TracePlan<'static, Field>>), String>
  {
    let artifact_digest = *blake3::hash(&package.encode()).as_bytes();
    let (program, trace) = package.traced()?;
    let mut program = program.check_field::<Val>()?;
    program.track_depth(&trace)?;
    program.entry(entry)?;
    let program = Arc::new(program);
    let plan = Arc::new(TracePlan::new(Arc::clone(&program), trace)?);
    Ok((artifact_digest, program, plan))
  }

  fn finish(
    program: Arc<Program>,
    entry: String,
    backend: Circuits,
    artifact_digest: [u8; 32],
    parameters: Parameters,
    cross_check: Option<CrossCheck>,
  ) -> Result<Self, String> {
    let (claim, key) = circuits!(&backend, b => (
      b.claim(&entry, &[Val::ZERO; 16], &[])?,
      b.verifying_key_bytes()?,
    ));
    if claim.len() != 18 {
      return Err("compression wrapper must expose an 18-word claim".into());
    }
    let key_digest = *blake3::hash(&key).as_bytes();
    Ok(Self {
      program,
      entry,
      advice_program: None,
      backend,
      artifact_digest,
      key,
      key_digest,
      parameters,
      cross_check,
    })
  }

  /// Attach an unmodified pre-guess `ixcc` advice package (written by
  /// `ixcc-aiur --advice-out`) so `"ixcc.guess.*"` channels in a compiled
  /// wrapper circuit are answered automatically during [`Self::execute`].
  /// Validates the advice program and its guess-channel bindings immediately.
  pub fn with_advice(mut self, advice: Package) -> Result<Self, String> {
    let raw = advice.program;
    let checked = raw.clone().check_field::<Val>()?;
    let mut probe = HintChannels::new();
    aiur::library::ixcc::register_advice_program(
      &mut probe,
      &self.program,
      checked,
    )?;
    self.advice_program = Some(raw);
    Ok(self)
  }

  /// Decode an `ixcc` advice artifact (`IXAIURP\0` or `IXAIURX\0`) and attach
  /// it via [`Self::with_advice`].
  pub fn with_advice_bytes(self, bytes: &[u8]) -> Result<Self, String> {
    let package = if bytes.starts_with(PACKAGE_MAGIC) {
      Package::decode(bytes)?
    } else if bytes.starts_with(EXECUTION_MAGIC) {
      ExecutionPackage::decode(bytes)?.package
    } else {
      return Err(
        "unrecognized advice artifact magic (expected IXAIURP\\0 or IXAIURX\\0)"
          .into(),
      );
    };
    self.with_advice(package)
  }

  /// The Rust lowering of the circuits (layouts without
  /// [`Layout::lowering`]). `package` must be trusted compiler output for
  /// the generic recursive verifier. This constructor checks structure, not
  /// the program's meaning.
  pub fn new(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::new_with_entry(package, parameters, device, ENTRY)
  }

  /// [`Self::new`] selecting a custom entry point (e.g., `"Prog::main0"`).
  pub fn new_with_entry(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    let entry = entry.into();
    let (artifact_digest, program, plan) = Self::program(package, &entry)?;
    let backend = Backend::for_batch_on_device(plan, parameters, device)?;
    Self::finish(
      program,
      entry,
      Circuits::Rust(Box::new(backend)),
      artifact_digest,
      parameters,
      None,
    )
  }

  /// The circuits of the Lean exporter ([`LEAN_LOWERING`], through
  /// [`Exporter::from_env`]), with ROM tables at `capacities`. The Rust
  /// lowering only generates rows; with `IX_WRAP_RUST_CROSS_CHECK=1` the
  /// exported circuits are also compared with it.
  pub fn lean(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    capacities: Capacities<'_>,
  ) -> Result<Self, String> {
    Self::lean_entry(package, parameters, device, capacities, ENTRY)
  }

  /// [`Self::lean`] selecting a custom entry point.
  pub fn lean_entry(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    capacities: Capacities<'_>,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    Self::lean_with_entry(
      package,
      parameters,
      device,
      capacities,
      &Exporter::from_env()?,
      entry,
    )
  }

  /// [`Self::lean`] with the circuits from `exporter`.
  pub fn lean_with(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    capacities: Capacities<'_>,
    exporter: &dyn WideExporter,
  ) -> Result<Self, String> {
    Self::lean_with_entry(
      package, parameters, device, capacities, exporter, ENTRY,
    )
  }

  /// [`Self::lean_with`] selecting a custom entry point.
  pub fn lean_with_entry(
    package: Package,
    parameters: Parameters,
    device: Option<i32>,
    capacities: Capacities<'_>,
    exporter: &dyn WideExporter,
    entry: impl Into<String>,
  ) -> Result<Self, String> {
    let entry = entry.into();
    let bytes = package.encode();
    let (artifact_digest, program, plan) = Self::program(package, &entry)?;
    let rows = Backend::for_batch_on_device_with_rom_layout(
      plan,
      parameters,
      RomLayout::Scalar,
      device,
    )?;
    let order = rows.wide_order()?;
    let heights: Vec<u8> = match capacities {
      Capacities::Lean(heights) => heights.to_vec(),
      Capacities::Rust(heights) => {
        if heights.len() != order.len() {
          return Err("the Rust layout has another circuit count".into());
        }
        // Rust-lowering layouts pack ROM entries across `rom_lanes(width)`
        // lanes per row, whereas Lean's `romCircuit` stores one entry per row.
        let rom_extra: std::collections::HashMap<usize, u8> = rows
          .memory_circuits()
          .into_iter()
          .map(|(width, ci)| {
            let extra = u8::try_from(rom_lanes(width).ilog2())
              .expect("ROM lane log2 fits in u8");
            (ci, extra)
          })
          .collect();
        order
          .iter()
          .map(|&ci| {
            let extra = rom_extra.get(&ci).copied().unwrap_or(0);
            heights[ci]
              .checked_add(extra)
              .ok_or_else(|| "ROM capacity overflow".to_string())
          })
          .collect::<Result<Vec<_>, _>>()?
      },
    };
    let capacities = heights
      .iter()
      .map(|&log| 1usize.checked_shl(u32::from(log)).filter(|_| log <= 26))
      .collect::<Option<Vec<_>>>()
      .ok_or("wrapper capacity above 2^26")?;
    let digest = blake3::Hash::from(artifact_digest).to_hex();
    let artifact = exporter.artifact(&bytes, digest.as_str())?;
    let input =
      rows.wide_input(&artifact, digest.as_str(), &entry, &capacities)?;
    let (layout, fixed) = exporter.export(&input)?;
    let wide = WideBackend::new(rows, Export::parse(&layout, &fixed)?)?;
    wide.check_request(&wide.claim(&entry, &[Val::ZERO; 16], &[])?)?;
    let cross_check =
      if cross_check_requested()? { Some(wide.cross_check(4)?) } else { None };
    Self::finish(
      program,
      entry,
      Circuits::Lean(Box::new(wide)),
      artifact_digest,
      parameters,
      cross_check,
    )
  }

  /// Entrypoint name invoked by this wrapper (default [`ENTRY`]).
  pub fn entry(&self) -> &str {
    &self.entry
  }

  /// Whether an `ixcc` advice package is attached for Tier-2 `"ixcc.guess.*"`
  /// host advice channels.
  pub const fn has_advice(&self) -> bool {
    self.advice_program.is_some()
  }

  /// The comparison with the Rust lowering, when [`Self::lean`] ran one.
  pub const fn cross_check(&self) -> Option<&CrossCheck> {
    self.cross_check.as_ref()
  }

  /// [`Layout::lowering`] of this wrapper's layouts.
  pub const fn lowering(&self) -> Option<&'static str> {
    match self.backend {
      Circuits::Rust(_) => None,
      Circuits::Lean(_) => Some(LEAN_LOWERING),
    }
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
    circuits!(&self.backend, b => b.claim(&self.entry, &args, &[]))
  }

  fn prepare_hints<'a>(
    &'a self,
    advice: &Advice<Field>,
  ) -> Result<PreparedHints<'a, Field>, String> {
    let field = self.program.field();
    let mut channels = HintChannels::new();
    aiur::library::u32::register(&mut channels, field)?;
    aiur::library::u64::register(&mut channels, field)?;
    aiur::library::ixcc::register(&mut channels, field)?;
    channels.insert_fixed::<1, 1>(
      "goldilocks.inverse",
      Type::Field,
      Type::Field,
      move |[x]| Ok([field.inverse(x).unwrap_or_else(|| field.zero())]),
    )?;
    advice.register_read::<1>("stark.io.read1", false, &mut channels)?;
    advice.register_read::<8>("stark.io.read8", false, &mut channels)?;
    advice.register_read::<64>("stark.io.read64", false, &mut channels)?;
    if let Some(adv_raw) = &self.advice_program {
      let checked_adv = adv_raw.clone().check_field::<Val>()?;
      aiur::library::ixcc::register_advice_program(
        &mut channels,
        &self.program,
        checked_adv,
      )?;
    }
    let mut data = advice.metadata(
      "stark.io.info",
      &Type::Tuple { items: vec![Type::Field; 2] },
      None,
      |_, key| key.len() == 1,
      false,
    )?;
    data.extend(advice.metadata(
      "stark.io.address",
      &Type::Tuple {
        items: vec![Type::Field, Type::Tuple { items: vec![Type::Field; 32] }],
      },
      None,
      |_, key| key.len() == 32,
      false,
    )?);
    data.extend(advice.metadata(
      "stark.io.digest",
      &Type::Tuple { items: vec![Type::Field; 8] },
      Some(4),
      |channel, key| channel == 4 && key.len() == 8,
      false,
    )?);
    let prepared = self.program.prepare_hint_channels(&data, &channels)?;
    let mut maps = MapOverrides::new();
    aiur::library::u8::register_maps(&self.program, &mut maps)?;
    prepared.with_map_overrides(&maps)
  }

  pub fn execute<'a>(&self, input: &'a Input) -> Result<Executed<'a>, String> {
    let args = self.program.field().decode(&input.statement.arguments())?;
    let advice = crate::advice(
      self.program.field(),
      &input.key,
      &input.claims_bytes,
      &input.proof,
    )?;
    let record = self
      .prepare_hints(&advice)?
      .execute(&self.entry, args.clone())
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
    Ok(circuits!(&self.backend, b => b.execution_statistics(&execution.record)))
  }

  pub fn plan_layout(
    &self,
    execution: &Executed<'_>,
    headroom: u8,
  ) -> Result<Layout, String> {
    self.check_execution(execution)?;
    let rows =
      circuits!(&self.backend, b => b.execution_rows(&execution.record));
    Ok(Layout {
      key_blake3: blake3::Hash::from(self.key_digest).to_hex().to_string(),
      log_heights: circuits!(&self.backend, b => b.normalized_log_heights(&rows, headroom))?,
      memory_circuits: self.memory_circuits(),
      claim_len: 18,
      lowering: self.lowering().map(str::to_owned),
    })
  }

  /// Capacities covering both this execution and a per-circuit row bound
  /// (in canonical circuit order) that the caller derives from what can vary
  /// between admissible roots. Fixed tables keep their preprocessed height.
  pub fn plan_capacities(
    &self,
    execution: &Executed<'_>,
    row_bounds: &[usize],
  ) -> Result<Layout, String> {
    let mut layout = self.plan_layout(execution, 0)?;
    if row_bounds.len() != layout.log_heights.len() {
      return Err(format!(
        "expected {} circuit row bounds, got {}",
        layout.log_heights.len(),
        row_bounds.len()
      ));
    }
    for ((height, &bound), circuit) in layout
      .log_heights
      .iter_mut()
      .zip(row_bounds)
      .zip(self.circuit_statistics())
    {
      if circuit.preprocessed_height != 0 {
        continue;
      }
      while bound > 1usize << *height {
        *height += 1;
      }
    }
    self.validate_layout(&layout)?;
    Ok(layout)
  }

  /// Run before proving: reject an execution that does not fit the layout,
  /// and report each circuit's rows against its capacity.
  pub fn admit(
    &self,
    execution: &Executed<'_>,
    layout: &Layout,
  ) -> Result<Admission, String> {
    self.check_execution(execution)?;
    self.validate_layout(layout)?;
    let rows =
      circuits!(&self.backend, b => b.execution_rows(&execution.record));
    let statistics = self.circuit_statistics();
    let mut circuits = Vec::with_capacity(rows.len());
    for ((rows, &log_height), circuit) in
      rows.into_iter().zip(&layout.log_heights).zip(statistics)
    {
      if rows > 1usize << log_height {
        return Err(format!(
          "root exceeds the compression wrapper layout: {} needs {rows} rows, capacity 2^{log_height}",
          circuit.name
        ));
      }
      circuits.push(AdmittedCircuit {
        name: circuit.name,
        rows,
        log_height,
        fixed: circuit.preprocessed_height != 0,
      });
    }
    Ok(Admission { circuits })
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
    let (claim, proof) = circuits!(&self.backend, b => b.prove_normalized(
      &self.entry,
      &execution.args,
      &[],
      execution.record,
      &layout.log_heights,
    ))?;
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

  /// `(payload_width, circuit_index)` of every ROM circuit, by width.
  pub fn memory_circuits(&self) -> Vec<(usize, usize)> {
    circuits!(&self.backend, b => b.memory_circuits())
  }

  /// Every circuit's shape, in layout order.
  pub fn circuit_statistics(
    &self,
  ) -> Vec<aiur::trace::stark::CircuitStatistics> {
    circuits!(&self.backend, b => b.statistics())
  }

  pub fn validate_layout(&self, layout: &Layout) -> Result<(), String> {
    if layout.key_blake3
      != blake3::Hash::from(self.key_digest).to_hex().as_str()
      || layout.lowering.as_deref() != self.lowering()
      || layout.memory_circuits != self.memory_circuits()
      || layout.claim_len != 18
    {
      return Err("compression wrapper layout differs from its backend".into());
    }
    let statistics = self.circuit_statistics();
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
    circuits!(&self.backend, b => b.verify_batch(&self.entry, &args, &[], &proof))
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
    circuits!(&self.backend, b => b.verify_batch(&self.entry, &args, &[], &proof))
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
  // The Rust lowering closes each ROM circuit's `[0, rows)` with one pull
  // and one push; the Lean ROM tables need no boundary messages.
  let messages = if layout.lowering.is_some() {
    0
  } else {
    2 * layout.memory_circuits.len()
  };
  if proof.preamble.messages.len() != messages {
    return Err(
      "compression wrapper proof has another number of boundary messages"
        .into(),
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
    types::GoldilocksBlake3V6Config,
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
        System::new(GoldilocksBlake3V6Config::new(cp, fp), inputs);
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
      multi_stark::types::ExtVal3::ONE;
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
      lowering: None,
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
  fn layout_config_round_trips_and_its_digest_binds_every_height() {
    let layout = Layout {
      key_blake3: "00".repeat(32),
      log_heights: vec![1, 19, 21, 8],
      memory_circuits: vec![(3, 3)],
      claim_len: 18,
      lowering: None,
    };
    let digest = layout.blake3().unwrap();
    for index in 0..layout.log_heights.len() {
      let mut other = layout.clone();
      other.log_heights[index] += 1;
      assert_ne!(other.blake3().unwrap(), digest);
    }
    let config = LayoutConfig {
      format: LAYOUT_CONFIG_FORMAT.into(),
      version: 1,
      grouping: "t65536".into(),
      artifact_blake3: "11".repeat(32),
      layout_blake3: blake3::Hash::from(digest).to_hex().to_string(),
      layout,
      sizing: serde_json::json!({"rule": "test"}),
    };
    let bytes = serde_json::to_vec(&config).unwrap();
    assert_eq!(serde_json::from_slice::<LayoutConfig>(&bytes).unwrap(), config);
    let mut extra: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
    extra["unknown"] = 1.into();
    assert!(serde_json::from_value::<LayoutConfig>(extra).is_err());
  }

  #[test]
  fn released_layouts_keep_their_digests_and_lowerings() {
    for (bytes, lowering) in [
      (&include_bytes!("../compress-wrap/m16384w64-v2.layout.json")[..], None),
      (
        &include_bytes!("../compress-wrap/m16384w64-v3.layout.json")[..],
        Some(LEAN_LOWERING),
      ),
    ] {
      let config: LayoutConfig = serde_json::from_slice(bytes).unwrap();
      assert_eq!(config.layout.lowering.as_deref(), lowering);
      assert_eq!(
        blake3::Hash::from(config.layout.blake3().unwrap()).to_hex().as_str(),
        config.layout_blake3
      );
    }
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
    let bytes = std::fs::read(&path).unwrap();
    assert!(
      Wrapper::from_bytes(
        &bytes,
        blake3::hash(&bytes).as_bytes(),
        wrapper.key_digest(),
        Parameters::default(),
        None
      )
      .is_ok()
    );
    assert!(
      Wrapper::from_bytes(
        &bytes,
        &[0; 32],
        wrapper.key_digest(),
        Parameters::default(),
        None
      )
      .is_err()
    );
    assert!(
      Wrapper::from_bytes(
        &bytes,
        blake3::hash(&bytes).as_bytes(),
        &[0; 32],
        Parameters::default(),
        None
      )
      .is_err()
    );
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

  fn compiled_wrapper_fixture(guess_offset: u64) -> (Package, Package) {
    use aiur::{
      bytecode::{Binary, Entry, Function, Instruction, VERSION},
      trace::TraceArtifact,
      value::IoType,
    };
    let pair = Type::Tuple { items: vec![Type::Field; 2] };
    let args_ty = Type::Tuple { items: vec![Type::Field; 16] };
    let unit_ty = Type::Tuple { items: vec![] };
    let main_prog = RawProgram {
      version: VERSION,
      modulus: Val::ORDER_U64,
      functions: vec![Function {
        name: "Prog::main0".into(),
        params: vec![args_ty],
        result: unit_ty,
        registers: 28,
        code: vec![
          Instruction::Literal { dest: 16, value: 1 },
          Instruction::Literal { dest: 17, value: 0 },
          Instruction::Hint {
            channel: "stark.io.info".into(),
            key_type: pair.clone(),
            r#type: pair.clone(),
            key: vec![16, 17],
            dest: vec![18, 19],
          },
          Instruction::Literal { dest: 20, value: 7 },
          Instruction::Hint {
            channel: "ixcc.divmod".into(),
            key_type: pair.clone(),
            r#type: pair,
            key: vec![8, 20],
            dest: vec![21, 22],
          },
          Instruction::Binary {
            dest: 23,
            operator: Binary::Mul,
            left: 21,
            right: 20,
          },
          Instruction::Binary {
            dest: 24,
            operator: Binary::Add,
            left: 23,
            right: 22,
          },
          Instruction::AssertEq {
            left: vec![24],
            right: vec![8],
            message: Some("divmod check".into()),
            runtime_check: true,
          },
          Instruction::Hint {
            channel: "ixcc.guess.stmt_check".into(),
            key_type: Type::Field,
            r#type: Type::Field,
            key: vec![8],
            dest: vec![25],
          },
          Instruction::Literal { dest: 26, value: 5 },
          Instruction::Binary {
            dest: 27,
            operator: Binary::Add,
            left: 8,
            right: 26,
          },
          Instruction::AssertEq {
            left: vec![25],
            right: vec![27],
            message: Some("guess check".into()),
            runtime_check: true,
          },
          Instruction::Ret { value: vec![] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::main0".into(),
        function: 0,
        inputs: vec![IoType::Tuple { items: vec![IoType::Field; 16] }],
        output: Some(IoType::Tuple { items: vec![] }),
      }],
    };
    let writes: Vec<serde_json::Value> = (0..16)
      .map(|i| {
        serde_json::json!({
          "column": i,
          "source": i,
          "guard": { "const": 1 }
        })
      })
      .collect();
    let trace: TraceArtifact = serde_json::from_value(serde_json::json!({
      "version": 3,
      "modulus": Val::ORDER_U64,
      "functions": [{
        "name": "Prog::main0",
        "chip": "Prog::main0",
        "witnesses": 16,
        "inputs": (0..16).collect::<Vec<_>>(),
        "output": [],
        "steps": [],
        "writes": writes
      }],
      "chips": [{
        "name": "Prog::main0",
        "width": 17,
        "activation": 16,
        "inputs": (0..16).collect::<Vec<_>>(),
        "output": [],
        "constraints": [{
          "mul": [
            { "var": 16 },
            { "sub": [{ "const": 1 }, { "var": 16 }] }
          ]
        }],
        "sends": [],
        "memory": []
      }]
    }))
    .unwrap();
    let advice_prog = RawProgram {
      version: VERSION,
      modulus: Val::ORDER_U64,
      functions: vec![Function {
        name: "Prog::stmt_check".into(),
        params: vec![Type::Field],
        result: Type::Field,
        registers: 3,
        code: vec![
          Instruction::Literal { dest: 1, value: guess_offset },
          Instruction::Binary {
            dest: 2,
            operator: Binary::Add,
            left: 0,
            right: 1,
          },
          Instruction::Ret { value: vec![2] },
        ],
      }],
      enums: vec![],
      tables: vec![],
      maps: vec![],
      entries: vec![Entry {
        name: "Prog::stmt_check".into(),
        function: 0,
        inputs: vec![IoType::Field],
        output: Some(IoType::Field),
      }],
    };
    (
      Package { program: main_prog, trace: Some(trace) },
      Package { program: advice_prog, trace: None },
    )
  }

  #[test]
  fn custom_entry_with_ixcc_and_guess_advice_proves_and_verifies() {
    let f = fixture();
    let pin = *blake3::hash(&f.key).as_bytes();
    let input = Input::new(&f.key, pin, &f.claims, &f.proof).unwrap();
    let (pkg, good_advice) = compiled_wrapper_fixture(5);
    let (_, bad_advice) = compiled_wrapper_fixture(6);
    let params = Parameters {
      log_blowup: 1,
      num_queries: 282,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };

    // Without advice attached, execution fails on the unbound guess channel.
    let no_advice =
      Wrapper::new_with_entry(pkg.clone(), params, None, "Prog::main0")
        .unwrap();
    assert_eq!(no_advice.entry(), "Prog::main0");
    assert!(!no_advice.has_advice());
    assert!(no_advice.execute(&input).is_err());

    // Invalid advice magic fails closed.
    assert!(
      Wrapper::new_with_entry(pkg.clone(), params, None, "Prog::main0")
        .unwrap()
        .with_advice_bytes(b"NOT_AIUR")
        .is_err()
    );

    // Wrong advice fails the circuit's verified checker during execution.
    let bad_wrapper =
      Wrapper::new_with_entry(pkg.clone(), params, None, "Prog::main0")
        .unwrap()
        .with_advice(bad_advice)
        .unwrap();
    assert!(bad_wrapper.execute(&input).is_err());

    // Honest advice executes, proves normalized, and verifies via for_layout_with_entry.
    let advice_bytes = good_advice.encode();
    let wrapper =
      Wrapper::new_with_entry(pkg.clone(), params, None, "Prog::main0")
        .unwrap()
        .with_advice_bytes(&advice_bytes)
        .unwrap();
    assert!(wrapper.has_advice());
    let execution = wrapper.execute(&input).unwrap();
    let layout = wrapper.plan_layout(&execution, 0).unwrap();
    let _admission = wrapper.admit(&execution, &layout).unwrap();
    let proven = wrapper.prove_normalized(execution, &layout).unwrap();
    wrapper
      .verify_normalized(input.statement(), &proven.proof, &layout)
      .unwrap();

    // Reconstruct through `for_layout_with_entry` and verify + reject forged statement.
    let reloaded = Wrapper::for_layout_with_entry(
      pkg,
      params,
      None,
      &layout,
      &NoExporter,
      "Prog::main0",
    )
    .unwrap()
    .with_advice_bytes(&advice_bytes)
    .unwrap();
    reloaded
      .verify_normalized(input.statement(), &proven.proof, &layout)
      .unwrap();
    let mut wrong_stmt = input.statement().clone();
    wrong_stmt.claims_digest[0] ^= 1;
    assert!(
      reloaded.verify_normalized(&wrong_stmt, &proven.proof, &layout).is_err()
    );
  }

  #[test]
  fn exporter_cache_complete_sentinel_authenticates_layout_and_fixed() {
    use std::os::unix::fs::PermissionsExt;

    let base = std::env::temp_dir().join(format!(
      "ix-compress-wrap-exporter-m9-{}",
      std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&base);
    let cache = base.join("cache");
    std::fs::create_dir_all(&cache).unwrap();

    let count_file = base.join("runs.txt");
    let script = base.join("fake_wide_export.sh");
    std::fs::write(
      &script,
      format!(
        "#!/bin/sh\nset -e\necho x >> '{}'\nprintf '{{\"ok\":true}}' > \"$2\"\nprintf 'FIXED_BYTES' > \"$3\"\n",
        count_file.display()
      ),
    )
    .unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o755);
    std::fs::set_permissions(&script, perms).unwrap();

    let exporter = Exporter { binary: script.clone(), cache: cache.clone() };
    let req = serde_json::json!({"test": "m9"});

    // First export runs the binary and writes an authenticated JSON `complete` marker.
    let (layout1, fixed1) = exporter.export(&req).unwrap();
    assert_eq!(layout1, br#"{"ok":true}"#);
    assert_eq!(fixed1, b"FIXED_BYTES");
    assert_eq!(std::fs::read_to_string(&count_file).unwrap().lines().count(), 1);

    // Second export hits the verified cache without re-running the binary.
    let (layout2, fixed2) = exporter.export(&req).unwrap();
    assert_eq!((layout2, fixed2), (layout1.clone(), fixed1.clone()));
    assert_eq!(std::fs::read_to_string(&count_file).unwrap().lines().count(), 1);

    // Locate the single cache entry directory.
    let entry = std::fs::read_dir(&cache)
      .unwrap()
      .filter_map(Result::ok)
      .map(|e| e.path())
      .find(|p| p.join("complete").is_file())
      .expect("cache entry directory");
    let orig_complete = std::fs::read(entry.join("complete")).unwrap();

    // Negative control 1: tampered layout.json fails closed.
    std::fs::write(entry.join("layout.json"), br#"{"ok":false}"#).unwrap();
    assert!(exporter.export(&req).unwrap_err().contains("layout.json"));
    std::fs::write(entry.join("layout.json"), &layout1).unwrap();

    // Negative control 2: tampered fixed.bin fails closed.
    std::fs::write(entry.join("fixed.bin"), b"TAMPERED").unwrap();
    assert!(exporter.export(&req).unwrap_err().contains("fixed.bin"));
    std::fs::write(entry.join("fixed.bin"), &fixed1).unwrap();

    // Negative control 3: tampered input.json fails closed.
    let orig_input = std::fs::read(entry.join("input.json")).unwrap();
    std::fs::write(entry.join("input.json"), b"{}").unwrap();
    assert!(exporter.export(&req).unwrap_err().contains("input.json"));
    std::fs::write(entry.join("input.json"), &orig_input).unwrap();

    // Negative control 4: legacy 0-byte `complete` sentinel fails closed.
    std::fs::write(entry.join("complete"), b"").unwrap();
    assert!(exporter.export(&req).unwrap_err().contains("empty complete"));

    // Negative control 5: malformed JSON in `complete` fails closed.
    std::fs::write(entry.join("complete"), b"not-json").unwrap();
    assert!(exporter.export(&req).unwrap_err().contains("malformed complete"));

    // Restoring the valid sentinel restores cache hit cleanly.
    std::fs::write(entry.join("complete"), &orig_complete).unwrap();
    assert_eq!(exporter.export(&req).unwrap(), (layout1, fixed1));

    let _ = std::fs::remove_dir_all(&base);
  }
}
