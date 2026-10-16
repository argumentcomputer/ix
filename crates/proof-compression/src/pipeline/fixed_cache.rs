//! Trusted local preprocessing, independent of each proof's witness and
//! openings. Entries bind the circuit relation, lowering layout, stage
//! semantics and setup, independently of the executable and execution backend.
//! The root is `IX_KZG_FIXED_CACHE`, or `<stage>/kzg/fixed-cache`.
use super::storage::{self, Manifest, Result};
use crate::kzg::Scalar;
use multi_stark::{plonkish::MultiStarkCircuit, traits::Algebra};
use serde::{Deserialize, Serialize};
use std::{
  fs::{self, File},
  io::{self, BufWriter, Write},
  path::{Path, PathBuf},
};

/// Bump when the merged-table lowering, KZG lookup grouping, polynomial
/// representation or checkpoint encoding changes without changing the IR.
const PREPROCESSING_VERSION: &[u8] = b"ix/plonkish-kzg-preprocessing/v1";

#[derive(Serialize, Deserialize)]
pub(crate) struct Shape {
  pub(crate) widths: Vec<usize>,
  pub(crate) heights: Vec<usize>,
}

#[derive(Serialize, Deserialize)]
struct CachedFile {
  name: String,
  size: u64,
  /// BLAKE3 of the file at publication, checked on every restore. Checkpoint
  /// readers only detect changes made after they index a file, so a
  /// checkpoint damaged in the cache would otherwise be proved against.
  digest: [u8; 32],
}

#[derive(Serialize, Deserialize)]
struct Entry {
  identity: [u8; 32],
  shape: Shape,
  files: Vec<CachedFile>,
}

pub(crate) struct FixedCache {
  identity: [u8; 32],
  directory: PathBuf,
}

fn file_digest(path: &Path) -> io::Result<[u8; 32]> {
  let mut hasher = blake3::Hasher::new();
  hasher.update_mmap_rayon(path)?;
  Ok(*hasher.finalize().as_bytes())
}

impl FixedCache {
  /// `compiled` uses the pipeline's merged-table lowering. `semantics` binds
  /// the source verifier and setup identity, including transcript and degree
  /// limits. Only logical wire indices enter the key; process-local circuit
  /// IDs, names, witness recipes and public input values do not.
  pub(crate) fn from_semantics(
    root: &Path,
    semantics: &[u8],
    compiled: &MultiStarkCircuit<Scalar>,
  ) -> Result<Self> {
    let mut hasher = blake3::Hasher::new();
    {
      // Stream the compact IR instead of materializing padded fixed matrices.
      let mut out = BufWriter::with_capacity(1 << 20, &mut hasher);
      encode(
        ("ix/kzg-fixed-cache/v6", PREPROCESSING_VERSION, semantics),
        &mut out,
      )?;
      let circuit = compiled.circuit();
      encode(circuit.gates().len(), &mut out)?;
      for gate in circuit.gates() {
        encode(
          (gate.wires.map(|wire| wire.index()), &gate.coefficients),
          &mut out,
        )?;
      }
      encode(circuit.tables().len(), &mut out)?;
      for table in circuit.tables() {
        encode(table.rows(), &mut out)?;
      }
      encode(circuit.lookups().len(), &mut out)?;
      for lookup in circuit.lookups() {
        encode((lookup.table.index(), lookup.values.len()), &mut out)?;
        for value in &lookup.values {
          encode(value.index(), &mut out)?;
        }
      }
      encode(circuit.stats().hash_calls, &mut out)?;
      for (input, output) in circuit.blake3_calls() {
        encode(input.len(), &mut out)?;
        for value in input.iter().chain(output) {
          encode(value.index(), &mut out)?;
        }
      }
      encode(circuit.public_values().len(), &mut out)?;
      for value in circuit.public_values() {
        encode(value.index(), &mut out)?;
      }
      encode(compiled.main_heights(), &mut out)?;
      encode(compiled.num_circuits(), &mut out)?;
      for index in 0..compiled.num_circuits() {
        encode(
          compiled.trace_dimensions(index).ok_or("missing compiled trace")?,
          &mut out,
        )?;
      }
      // Zero placeholders retain the namespace, public locations and partition
      // activation claims without binding a particular proof's statement.
      encode(
        compiled.claims(&vec![Scalar::ZERO; circuit.public_values().len()])?,
        &mut out,
      )?;
      out.flush()?;
    }
    let identity = *hasher.finalize().as_bytes();
    Ok(Self::new(root, identity))
  }

  fn new(root: &Path, identity: [u8; 32]) -> Self {
    Self {
      identity,
      directory: root
        .join(blake3::Hash::from_bytes(identity).to_hex().as_str()),
    }
  }

  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/cache_restore"
  )]
  pub(crate) fn restore(&self, staged: &Path) -> Result<Option<Shape>> {
    let ready = self.directory.join("ready.bin");
    if !ready.try_exists()? {
      eprintln!("Fixed preprocessing cache miss: {}", self.directory.display());
      return Ok(None);
    }
    let entry: Entry = storage::load(&ready)?;
    if entry.identity != self.identity
      || entry.shape.widths.is_empty()
      || entry.shape.widths.len() != entry.shape.heights.len()
      || entry.files.len() != entry.shape.widths.len() * 2
    {
      return Err("fixed cache identity or shape mismatch".into());
    }
    let expected = file_names(entry.shape.widths.len());
    for (file, expected) in entry.files.iter().zip(expected) {
      let path = self.directory.join(&file.name);
      if file.name != expected
        || fs::metadata(&path)?.len() != file.size
        || file_digest(&path)? != file.digest
      {
        return Err("fixed cache entry is incomplete or damaged".into());
      }
    }
    fs::create_dir_all(staged.join("kzg"))?;
    for CachedFile { name, .. } in &entry.files {
      link_or_copy(&self.directory.join(name), &staged.join(name))?;
    }
    eprintln!("Reused fixed preprocessing: {}", self.directory.display());
    Ok(Some(entry.shape))
  }

  /// Publish only after the proof using these parameters has verified.
  /// The cache directory must be trusted like the development SRS cache;
  /// metadata and field decoding detect truncation, not a malicious producer.
  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "compression/cache_publish"
  )]
  pub(crate) fn publish(&self, staged: &Path) -> Result<()> {
    if self.directory.join("ready.bin").try_exists()? {
      return Ok(());
    }
    let manifest: Manifest = storage::load(&staged.join("manifest.bin"))?;
    let temporary = storage::temporary_path(&self.directory);
    fs::create_dir_all(temporary.join("kzg"))?;
    let mut files = Vec::new();
    for name in file_names(manifest.widths.len()) {
      let source = staged.join(&name);
      let size = fs::metadata(&source)?.len();
      let digest = file_digest(&source)?;
      let published = temporary.join(&name);
      link_or_copy(&source, &published)?;
      File::open(published)?.sync_all()?;
      files.push(CachedFile { name, size, digest });
    }
    storage::save(
      &temporary.join("ready.bin"),
      &Entry {
        identity: self.identity,
        shape: Shape { widths: manifest.widths, heights: manifest.heights },
        files,
      },
    )?;
    storage::sync_directory(&temporary.join("kzg"))?;
    match storage::persist(&temporary, &self.directory) {
      Ok(()) => (),
      Err(_) if self.directory.join("ready.bin").try_exists()? => {
        fs::remove_dir_all(temporary)?;
      },
      Err(error) => return Err(error.into()),
    }
    eprintln!("Published fixed preprocessing: {}", self.directory.display());
    Ok(())
  }
}

fn encode(value: impl Serialize, out: &mut impl Write) -> Result<()> {
  bincode::serde::encode_into_std_write(
    value,
    out,
    bincode::config::standard(),
  )?;
  Ok(())
}

fn file_names(count: usize) -> impl Iterator<Item = String> {
  (0..count)
    .flat_map(|i| [format!("kzg/setup-{i}.bin"), format!("kzg/fixed-{i}.bin")])
}

fn link_or_copy(source: &Path, destination: &Path) -> Result<()> {
  if destination.try_exists()? {
    return Err(
      format!("refusing to replace {}", destination.display()).into(),
    );
  }
  match fs::hard_link(source, destination) {
    Ok(()) => Ok(()),
    Err(error) if error.kind() == io::ErrorKind::CrossesDevices => {
      fs::copy(source, destination)?;
      Ok(())
    },
    Err(error) => Err(error.into()),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{plonkish::CircuitBuilder, traits::Field};

  #[derive(Clone, Copy)]
  enum Change {
    None,
    Coefficient,
    Wiring,
    Table,
    LookupTable,
    LookupValue,
    PublicBinding,
    Namespace,
    Partition,
  }

  fn circuit(name: &str, change: Change) -> Result<MultiStarkCircuit<Scalar>> {
    let mut builder = CircuitBuilder::new();
    let a = builder.input(format!("{name}-a"));
    let b = builder.input(format!("{name}-b"));
    let zero = builder.constant(Scalar::ZERO);
    let coefficient = if matches!(change, Change::Coefficient) {
      Scalar::TWO
    } else {
      Scalar::ONE
    };
    let wires = if matches!(change, Change::Wiring) {
      [a, a, zero]
    } else {
      [a, b, zero]
    };
    builder.constrain_gate(
      wires,
      [Scalar::ZERO, coefficient, Scalar::NEG_ONE, Scalar::ZERO, Scalar::ZERO],
    );
    let table_value = if matches!(change, Change::Table) { 3 } else { 2 };
    let first = builder.fixed_table(
      format!("{name}-first"),
      vec![vec![Scalar::ONE], vec![Scalar::from_u8(table_value)]],
    );
    let second = builder.fixed_table(
      format!("{name}-second"),
      vec![vec![Scalar::from_u8(3)], vec![Scalar::from_u8(4)]],
    );
    let table =
      if matches!(change, Change::LookupTable) { second } else { first };
    let value = if matches!(change, Change::LookupValue) { b } else { a };
    builder.lookup(table, &[value]);
    let publics =
      if matches!(change, Change::PublicBinding) { [b, a] } else { [a, b] };
    for public in publics {
      builder.expose_public(public);
    }
    let namespace = if matches!(change, Change::Namespace) { 94 } else { 93 };
    let height = if matches!(change, Change::Partition) { 4 } else { 64 };
    Ok(
      builder
        .finish()
        .lower_to_multi_stark_sharded(Scalar::from_u8(namespace), height)?
        .merge_table_traces(8)?,
    )
  }

  fn cache(compiled: &MultiStarkCircuit<Scalar>) -> Result<FixedCache> {
    FixedCache::from_semantics(Path::new("cache"), &[0; 64], compiled)
  }

  #[test]
  fn identity_survives_reconstruction_and_diagnostic_renaming() -> Result<()> {
    let first = circuit("first-build", Change::None)?;
    let rebuilt = circuit("another-build", Change::None)?;
    assert_ne!(first.circuit().id(), rebuilt.circuit().id());
    assert_eq!(cache(&first)?.identity, cache(&rebuilt)?.identity);
    let relocated =
      FixedCache::from_semantics(Path::new("elsewhere"), &[0; 64], &rebuilt)?;
    assert_eq!(cache(&first)?.identity, relocated.identity);
    assert_ne!(cache(&first)?.directory, relocated.directory);
    Ok(())
  }

  #[test]
  fn equal_trace_dimensions_do_not_alias_different_relations() -> Result<()> {
    let original = circuit("original", Change::None)?;
    let expected = cache(&original)?.identity;
    for change in [
      Change::Coefficient,
      Change::Wiring,
      Change::Table,
      Change::LookupTable,
      Change::LookupValue,
      Change::PublicBinding,
      Change::Namespace,
    ] {
      let changed = circuit("changed", change)?;
      assert_eq!(original.num_circuits(), changed.num_circuits());
      for index in 0..original.num_circuits() {
        assert_eq!(
          original.trace_dimensions(index),
          changed.trace_dimensions(index)
        );
      }
      assert_ne!(expected, cache(&changed)?.identity);
    }
    Ok(())
  }

  #[test]
  fn identity_binds_partitioning_source_verifier_and_setup() -> Result<()> {
    let original = circuit("original", Change::None)?;
    let partitioned = circuit("partitioned", Change::Partition)?;
    assert_ne!(original.main_heights(), partitioned.main_heights());
    let expected = cache(&original)?.identity;
    assert_ne!(expected, cache(&partitioned)?.identity);
    for offset in [0, 32] {
      let mut semantics = [0; 64];
      semantics[offset] = 1;
      let changed =
        FixedCache::from_semantics(Path::new("cache"), &semantics, &original)?;
      assert_ne!(expected, changed.identity);
    }
    Ok(())
  }
}
