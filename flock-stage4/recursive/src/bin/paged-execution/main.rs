//! Original IXBF/IXFI/IXFO component proving and complete recursive execution.
//! Verifier configuration is an explicit caller input, separate from proofs.
mod aggregate;
mod leaves;
mod store;

use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use ix_flock_recursion::PagedTreeCompiler;
use ixby_flock::{
  hash::pack_bytes,
  ixby::{
    ixbf::{self, DecodeLimits},
    ixbf_decode::paged::endpoints::FunctionalProfile,
    paged_exec::BatchClass,
  },
};
use serde_json::json;
use std::{collections::BTreeMap, path::PathBuf, time::Instant};
use store::{Store, read, words, words_bytes, write_new};

const MAX_ARTIFACT_BYTES: u64 = 1 << 24;
struct Options {
  command: String,
  values: BTreeMap<String, String>,
}
impl Options {
  fn parse() -> Result<Self> {
    let mut args = std::env::args().skip(1);
    let command = args.next().context(
      "usage: paged-execution profile|statement|leaves|aggregate|prove|verify|census [options]",
    )?;
    let mut values = BTreeMap::new();
    while let Some(key) = args.next() {
      ensure!(key.starts_with("--"), "expected option, got {key}");
      let value = if key == "--resume" {
        "true".to_owned()
      } else {
        args.next().with_context(|| format!("missing value for {key}"))?
      };
      ensure!(values.insert(key.clone(), value).is_none(), "duplicate {key}");
    }
    Ok(Self { command, values })
  }
  fn take(&mut self, key: &str) -> Result<String> {
    self.values.remove(key).with_context(|| format!("missing {key}"))
  }
  fn flag(&mut self, key: &str) -> bool {
    self.values.remove(key).is_some()
  }
  fn finish(self) -> Result<()> {
    ensure!(
      self.values.is_empty(),
      "unknown options: {:?}",
      self.values.keys()
    );
    Ok(())
  }
}
fn class(name: &str) -> Result<BatchClass> {
  Ok(match name {
    "small" => BatchClass::Small,
    "objects" => BatchClass::Objects,
    "compact" => BatchClass::Compact,
    "bytes" => BatchClass::Bytes,
    "shared-compact" => BatchClass::SharedCompact,
    "shared" => BatchClass::Shared,
    "shared-compact-boolean" => BatchClass::SharedCompactBoolean,
    "shared-boolean" => BatchClass::SharedBoolean,
    "shared-1024" => BatchClass::Shared1024,
    "shared-compact-packed" => BatchClass::SharedCompactPacked,
    "shared-packed-1024" => BatchClass::SharedPacked1024,
    _ => anyhow::bail!("unknown execution class {name}"),
  })
}
fn counts(value: &str) -> Result<[usize; 11]> {
  value
    .split(',')
    .map(|s| Ok(s.parse()?))
    .collect::<Result<Vec<_>>>()?
    .try_into()
    .map_err(|_| {
      anyhow::anyhow!("expected exactly eleven comma-separated counts")
    })
}
fn source_profile(program: &[u8]) -> Result<FunctionalProfile> {
  let artifact = ixbf::decode_program(program, DecodeLimits::default())?;
  let l = artifact.limits();
  let limits = [
    &l.functions,
    &l.constructors,
    &l.blocks,
    &l.locals,
    &l.operands,
    &l.continuations,
    &l.input_nodes,
    &l.nat_bits,
    &l.string_bytes,
    &l.byte_array_bytes,
  ]
  .into_iter()
  .map(|n| {
    u128::try_from(n)
      .map_err(|_| anyhow::anyhow!("IXFP profile limit exceeds u128"))
  })
  .collect::<Result<Vec<_>>>()?;
  FunctionalProfile::new(
    limits.try_into().unwrap(),
    u64::try_from(artifact.max_steps())
      .map_err(|_| anyhow::anyhow!("IXFP fuel exceeds u64"))?,
  )
}
struct Artifacts {
  program: Vec<u8>,
  input: Vec<u8>,
  output: Vec<u8>,
}
impl Artifacts {
  fn read(options: &mut Options) -> Result<Self> {
    Ok(Self {
      program: read(
        &PathBuf::from(options.take("--program")?),
        MAX_ARTIFACT_BYTES,
      )?,
      input: read(
        &PathBuf::from(options.take("--input")?),
        MAX_ARTIFACT_BYTES,
      )?,
      output: read(
        &PathBuf::from(options.take("--output")?),
        MAX_ARTIFACT_BYTES,
      )?,
    })
  }
  fn statement(&self, profile: &FunctionalProfile) -> [F128; 2] {
    fn hash(tag: u8, prefix: &[u8], data: &[u8]) -> [u8; 32] {
      let mut h = blake3::Hasher::new();
      h.update(b"IxBy/commit/v0\0");
      h.update(&[tag]);
      h.update(prefix);
      h.update(data);
      *h.finalize().as_bytes()
    }
    let p = hash(0, &[], &profile.encode());
    let b = hash(1, &p, &self.program);
    let i = hash(2, &b, &self.input);
    let o = hash(3, &b, &self.output);
    let s = hash(4, &[], &[p, b, i, o].concat());
    [pack_bytes(&s[..16]), pack_bytes(&s[16..])]
  }
  fn config(
    &self,
    profile: &FunctionalProfile,
    class: &str,
  ) -> serde_json::Value {
    let sources = [&self.program, &self.input, &self.output].map(|bytes|
      json!({"length":bytes.len(),"blake3":blake3::hash(bytes).to_hex().as_str()}));
    json!({"format":"IxBy/paged-execution-run/v0", "profile":profile.encode().to_vec(),
      "class":class, "sources":sources})
  }
}
fn main() -> Result<()> {
  let mut options = Options::parse()?;
  let command = options.command.clone();
  ensure!(
    [
      "profile",
      "statement",
      "leaves",
      "aggregate",
      "prove",
      "verify",
      "census"
    ]
    .contains(&command.as_str()),
    "unknown command {command}"
  );
  if command == "profile" {
    let program =
      read(&PathBuf::from(options.take("--program")?), MAX_ARTIFACT_BYTES)?;
    let output = PathBuf::from(options.take("--out")?);
    options.finish()?;
    let profile = source_profile(&program)?;
    write_new(&output, &profile.encode())?;
    println!("{}", json!({"profile":output,"bytes":profile.encode().len()}));
    return Ok(());
  }
  let profile = FunctionalProfile::decode(&read(
    &PathBuf::from(options.take("--profile")?),
    184,
  )?)?;
  if command == "statement" {
    let artifacts = Artifacts::read(&mut options)?;
    let output = PathBuf::from(options.take("--out")?);
    options.finish()?;
    let bytes = words_bytes(&artifacts.statement(&profile));
    write_new(&output, &bytes)?;
    println!(
      "{}",
      json!({"statement":output,"digest":blake3::Hash::from(
      <[u8;32]>::try_from(bytes.as_slice())?).to_hex().as_str()})
    );
    return Ok(());
  }
  let class_name = options.take("--class")?;
  let class = class(&class_name)?;
  let threads =
    options.values.remove("--threads").map_or(Ok(4usize), |s| s.parse())?;
  ensure!((1..=64).contains(&threads), "thread count outside policy");
  rayon::ThreadPoolBuilder::new().num_threads(threads).build_global()?;
  let started = Instant::now();
  if ["verify", "census", "aggregate"].contains(&command.as_str()) {
    let counts = counts(&options.take("--counts")?)?;
    // The caller selects the complete physical setup before proof reads.
    let mut compiler = PagedTreeCompiler::new(profile, class, counts)?;
    if command == "census" {
      options.finish()?;
      let node = compiler.compile_complete()?;
      println!(
        "{}",
        json!({"counts":counts,"geometry":node.geometry(),
        "identity":blake3::Hash::from(node.identity()).to_hex().as_str(),
        "setup_seconds":started.elapsed().as_secs_f64()})
      );
      return Ok(());
    }
    let expected_path = PathBuf::from(options.take("--statement")?);
    if command == "verify" {
      let proof_path = PathBuf::from(options.take("--proof")?);
      options.finish()?;
      let verifier = compiler.verifier()?;
      drop(compiler);
      let setup_seconds = started.elapsed().as_secs_f64();
      let expected: [F128; 2] =
        words(&read(&expected_path, 32)?, 2)?.try_into().unwrap();
      let proof = read(&proof_path, ix_flock_recursion::MAX_PAGED_TREE_BYTES)?;
      let checking = Instant::now();
      verifier.verify(expected, &proof)?;
      println!(
        "{}",
        json!({"accepted":true,"claim":"complete original-format paged execution",
        "counts":counts,"proof_bytes":proof.len(),"setup_seconds":setup_seconds,
        "verification_seconds":checking.elapsed().as_secs_f64(),
        "identity":blake3::Hash::from(verifier.identity()).to_hex().as_str()})
      );
      return Ok(());
    }
    let directory = PathBuf::from(options.take("--dir")?);
    options.finish()?;
    let store = Store::existing(directory)?;
    let expected: [F128; 2] =
      words(&read(&expected_path, 32)?, 2)?.try_into().unwrap();
    let result = aggregate::complete(&mut compiler, &store, expected)?;
    println!("{result}");
    return Ok(());
  }
  let artifacts = Artifacts::read(&mut options)?;
  let directory = PathBuf::from(options.take("--out")?);
  let resume = options.flag("--resume");
  options.finish()?;
  ensure!(
    source_profile(&artifacts.program)? == profile,
    "program functional profile differs from --profile"
  );
  let store =
    Store::open(directory, resume, artifacts.config(&profile, &class_name))?;
  let expected = artifacts.statement(&profile);
  let counts = leaves::generate(&artifacts, &profile, class, &store)?;
  store.save_bytes("expected.statement", &words_bytes(&expected))?;
  let leaf_result = json!({"counts":counts,"class":class_name,
    "statement":store.directory().join("expected.statement"),
    "elapsed_seconds":started.elapsed().as_secs_f64()});
  store.save_bytes(
    "leaves.json",
    &serde_json::to_vec_pretty(&json!({
    "counts":counts,"class":class_name}))?,
  )?;
  if command == "leaves" {
    println!("{leaf_result}");
    return Ok(());
  }
  let mut compiler = PagedTreeCompiler::new(profile, class, counts)?;
  let result = aggregate::complete(&mut compiler, &store, expected)?;
  println!(
    "{}",
    json!({"leaves":leaf_result,"execution":result,
    "elapsed_seconds":started.elapsed().as_secs_f64()})
  );
  Ok(())
}
