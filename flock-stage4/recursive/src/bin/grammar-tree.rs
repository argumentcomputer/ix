//! Aggregate an exact, externally selected Program grammar batch count.
//! The receiver needs only the final proof, statement, source pins and count.
use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use ix_flock_recursion::{
  CompiledGrammarNode, GrammarRootVerifier, GrammarTreeCompiler,
  MAX_GRAMMAR_TREE_BYTES, MAX_GRAMMAR_TREE_LEAVES,
};
use ixby_flock::hash::pack_bytes;
use ixby_flock::ixby::ixbf_decode::{
  GrammarKind,
  stream::batch::{BATCH_MAX_PROOF_BYTES, GrammarBatchStatement},
};
use serde_json::json;
use std::{
  collections::BTreeMap,
  io::{Read, Write},
  path::{Path, PathBuf},
  sync::atomic::{AtomicBool, AtomicUsize, Ordering},
  time::Instant,
};

const STATEMENT_BYTES: u64 = 63 * 16;
const FRAME_HEADER: usize = 4 + 30 * 16;

struct Options {
  command: String,
  values: BTreeMap<String, String>,
}
impl Options {
  fn parse() -> Result<Self> {
    let mut args = std::env::args().skip(1);
    let command = args.next().context(
      "usage: grammar-tree aggregate|verify|census --batches N [options]",
    )?;
    let mut values = BTreeMap::new();
    while let Some(key) = args.next() {
      ensure!(key.starts_with("--"), "expected option, got {key}");
      let value = if ["--resume", "--check-rejections"].contains(&key.as_str())
      {
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
  fn number(&mut self, key: &str, default: usize) -> Result<usize> {
    self.values.remove(key).map_or(Ok(default), |v| Ok(v.parse()?))
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
#[derive(Clone, Copy)]
struct Source {
  length: u64,
  digest: [u8; 32],
}
impl Source {
  fn check(&self, statement: &GrammarBatchStatement) -> Result<()> {
    let expected = GrammarBatchStatement::new(
      self.length,
      self.digest,
      *statement.initial(),
      *statement.final_state(),
    )?;
    ensure!(statement == &expected, "unexpected source length or digest");
    Ok(())
  }
  fn json(self) -> serde_json::Value {
    json!({"length": self.length, "blake3": blake3::Hash::from(self.digest).to_hex().as_str()})
  }
}
#[derive(Clone, Copy, Debug)]
struct Chunk {
  start: usize,
  leaves: usize,
}
#[derive(Clone, Copy)]
struct Job {
  left: Chunk,
  right: Chunk,
}
impl Job {
  fn parent(self) -> Chunk {
    Chunk {
      start: self.left.start,
      leaves: self.left.leaves + self.right.leaves,
    }
  }
}
fn paths(directory: &Path, chunk: Chunk) -> (PathBuf, PathBuf) {
  let name = format!("node-{:06}-{:06}", chunk.start, chunk.leaves);
  (
    directory.join(format!("{name}.flock")),
    directory.join(format!("{name}.statement")),
  )
}
fn read(path: &Path, limit: u64) -> Result<Vec<u8>> {
  let mut bytes = Vec::new();
  std::fs::File::open(path)
    .with_context(|| format!("open {}", path.display()))?
    .take(limit + 1)
    .read_to_end(&mut bytes)?;
  ensure!(
    bytes.len() as u64 <= limit,
    "file exceeds bound: {}",
    path.display()
  );
  Ok(bytes)
}
fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
  let mut file =
    std::fs::OpenOptions::new().write(true).create_new(true).open(path)?;
  file.write_all(bytes)?;
  file.sync_all()?;
  Ok(())
}
fn statement_bytes(statement: &GrammarBatchStatement) -> Vec<u8> {
  statement
    .words()
    .iter()
    .flat_map(|v| {
      let mut bytes = [0; 16];
      bytes[..8].copy_from_slice(&v.lo.to_le_bytes());
      bytes[8..].copy_from_slice(&v.hi.to_le_bytes());
      bytes
    })
    .collect()
}
fn read_statement(path: &Path) -> Result<GrammarBatchStatement> {
  let bytes = read(path, STATEMENT_BYTES)?;
  ensure!(bytes.len() as u64 == STATEMENT_BYTES, "statement width");
  let words = bytes
    .as_chunks::<16>()
    .0
    .iter()
    .map(|word| pack_bytes(word))
    .collect::<Vec<_>>();
  GrammarBatchStatement::from_words(&words)
}
fn frame_end(bytes: &[u8]) -> Result<[F128; 30]> {
  ensure!(bytes.len() >= FRAME_HEADER, "truncated frame header");
  Ok(std::array::from_fn(|i| pack_bytes(&bytes[4 + i * 16..20 + i * 16])))
}
fn read_chunk(
  frames: &Path,
  directory: &Path,
  source: Source,
  chunk: Chunk,
) -> Result<(GrammarBatchStatement, Vec<u8>)> {
  if chunk.leaves != 1 {
    let (proof, statement) = paths(directory, chunk);
    let statement = read_statement(&statement)?;
    source.check(&statement)?;
    return Ok((statement, read(&proof, MAX_GRAMMAR_TREE_BYTES)?));
  }
  let path = frames.join(format!("program-{:06}.frame", chunk.start));
  let bytes = read(&path, BATCH_MAX_PROOF_BYTES + FRAME_HEADER as u64)?;
  let final_state = frame_end(&bytes)?;
  let proof_len = u32::from_le_bytes(bytes[..4].try_into()?) as usize;
  ensure!(bytes.len() == FRAME_HEADER + proof_len, "frame length mismatch");
  let initial = if chunk.start == 0 {
    let mut initial = [F128::ZERO; 30];
    initial[0] = F128::new(0, source.length);
    initial
  } else {
    // This header is untrusted advice. Both actual child proofs and all
    // thirty continuity words are constrained in every parent relation.
    let mut previous = [0; FRAME_HEADER];
    std::fs::File::open(
      frames.join(format!("program-{:06}.frame", chunk.start - 1)),
    )?
    .read_exact(&mut previous)?;
    frame_end(&previous)?
  };
  let statement = GrammarBatchStatement::new(
    source.length,
    source.digest,
    initial,
    final_state,
  )?;
  Ok((statement, bytes[FRAME_HEADER..].to_vec()))
}
fn join(
  left: &GrammarBatchStatement,
  right: &GrammarBatchStatement,
) -> Result<GrammarBatchStatement> {
  ensure!(
    left.source_identity() == right.source_identity(),
    "child source mismatch"
  );
  ensure!(left.final_state() == right.initial(), "child boundary mismatch");
  let mut words = *left.words();
  words[33..].copy_from_slice(&right.words()[33..]);
  GrammarBatchStatement::from_words(&words)
}
struct Run<'a> {
  frames: &'a Path,
  directory: &'a Path,
  source: Source,
  resume: bool,
  pools: Vec<rayon::ThreadPool>,
}
impl Run<'_> {
  fn level(
    &self,
    compiler: &mut GrammarTreeCompiler,
    jobs: &[Job],
  ) -> Result<serde_json::Value> {
    let started = Instant::now();
    let leaves = jobs[0].parent().leaves;
    let node = compiler.compile(leaves)?;
    let setup_seconds = started.elapsed().as_secs_f64();
    let geometry = node.geometry();
    let identity = blake3::Hash::from(node.identity()).to_hex().to_string();
    eprintln!(
      "{}",
      json!({"event":"level_setup", "seconds":setup_seconds, "jobs":jobs.len(), "identity":identity, "geometry":geometry})
    );
    let next = AtomicUsize::new(0);
    let completed = AtomicUsize::new(0);
    let cancelled = AtomicBool::new(false);
    let proving = Instant::now();
    let result = std::thread::scope(|scope| {
      let handles = self.pools.iter().take(jobs.len()).map(|pool| {
        let node = &node;
        let next = &next;
        let completed = &completed;
        let cancelled = &cancelled;
        scope.spawn(move || -> Result<usize> {
          let mut reused = 0;
          while !cancelled.load(Ordering::Relaxed) {
            let index = next.fetch_add(1, Ordering::Relaxed);
            let Some(&job) = jobs.get(index) else { break };
            let start = Instant::now();
            match pool.install(|| self.prove_job(node, job)) {
              Ok(cached) => { reused += usize::from(cached); },
              Err(error) => {
                cancelled.store(true, Ordering::Relaxed);
                return Err(error.context(format!("node {}+{}", job.left.start, leaves)));
              },
            }
            let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
            eprintln!("{}", json!({"event":"node_done", "leaves":leaves, "start":job.left.start, "completed":done, "jobs":jobs.len(), "seconds":start.elapsed().as_secs_f64()}));
          }
          Ok(reused)
        })
      }).collect::<Vec<_>>();
      let mut reused = 0;
      let mut failure = None;
      for handle in handles {
        match handle.join() {
          Ok(Ok(count)) => reused += count,
          Ok(Err(error)) => {
            failure.get_or_insert(error);
          },
          Err(_) => {
            failure
              .get_or_insert_with(|| anyhow::anyhow!("prover worker panicked"));
          },
        }
      }
      if let Some(error) = failure {
        return Err(error);
      }
      Ok(reused)
    })?;
    ensure!(
      completed.load(Ordering::Relaxed) == jobs.len(),
      "incomplete level"
    );
    let result = json!({"leaves":leaves, "jobs":jobs.len(), "reused":result, "setup_seconds":setup_seconds, "proving_seconds":proving.elapsed().as_secs_f64(), "identity":identity, "geometry":geometry});
    eprintln!("{}", json!({"event":"level_done", "result":result}));
    Ok(result)
  }
  fn prove_job(&self, node: &CompiledGrammarNode, job: Job) -> Result<bool> {
    ensure!(
      job.left.start + job.left.leaves == job.right.start,
      "nonadjacent children"
    );
    let left = read_chunk(self.frames, self.directory, self.source, job.left)?;
    let right =
      read_chunk(self.frames, self.directory, self.source, job.right)?;
    let statement = join(&left.0, &right.0)?;
    let (proof_path, statement_path) = paths(self.directory, job.parent());
    if self.resume && proof_path.exists() && statement_path.exists() {
      ensure!(
        read_statement(&statement_path)? == statement,
        "cached statement differs"
      );
      node.verify(&statement, &read(&proof_path, MAX_GRAMMAR_TREE_BYTES)?)?;
      return Ok(true);
    }
    let proof = node.prove([&left.0, &right.0], [&left.1, &right.1])?;
    // Parents replay the actual child proof; the final root discharges every
    // inherited table claim. Resume files are checked fully before reuse.
    write_new(&proof_path, &proof)?;
    write_new(&statement_path, &statement_bytes(&statement))?;
    Ok(false)
  }
}
fn forest(count: usize) -> Vec<Chunk> {
  let mut forest = Vec::new();
  let mut start = 0;
  while start < count {
    let leaves = 1usize << (count - start).ilog2();
    forest.push(Chunk { start, leaves });
    start += leaves;
  }
  forest
}
fn reject_mutations(
  verifier: &GrammarRootVerifier,
  statement: &GrammarBatchStatement,
  proof: &[u8],
) -> Result<()> {
  for position in [1, 3 + 29, 33 + 29] {
    let mut words = *statement.words();
    words[position] += F128::ONE;
    ensure!(
      verifier
        .verify(&GrammarBatchStatement::from_words(&words)?, proof)
        .is_err(),
      "altered statement accepted at {position}"
    );
  }
  // Fixed-width bundle: magic(8), identity(32), count(8), advice length(8).
  for position in [8, 40, 56, proof.len() - 1] {
    let mut mutated = proof.to_vec();
    mutated[position] ^= 1;
    ensure!(
      verifier.verify(statement, &mutated).is_err(),
      "altered bundle accepted at {position}"
    );
  }
  let mut trailing = proof.to_vec();
  trailing.push(0);
  ensure!(
    verifier.verify(statement, &trailing).is_err(),
    "trailing byte accepted"
  );
  ensure!(
    verifier.verify(statement, &proof[..proof.len() - 1]).is_err(),
    "truncated proof accepted"
  );
  Ok(())
}
fn main() -> Result<()> {
  let mut options = Options::parse()?;
  let command = options.command.clone();
  ensure!(
    ["aggregate", "verify", "census"].contains(&command.as_str()),
    "unknown command {command}"
  );
  let batches: usize = options.take("--batches")?.parse()?;
  ensure!(
    (2..=MAX_GRAMMAR_TREE_LEAVES).contains(&batches),
    "batch count outside policy"
  );
  let started = Instant::now();
  if command == "census" {
    options.finish()?;
    let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program)?;
    let node = compiler.compile(batches)?;
    println!(
      "{}",
      json!({"geometry":node.geometry(), "identity":blake3::Hash::from(node.identity()).to_hex().as_str(), "setup_seconds":started.elapsed().as_secs_f64()})
    );
    return Ok(());
  }
  let source = Source {
    length: options.take("--length")?.parse()?,
    digest: *blake3::Hash::from_hex(options.take("--digest")?)?.as_bytes(),
  };
  if command == "verify" {
    let proof_path = PathBuf::from(options.take("--proof")?);
    let statement_path = PathBuf::from(options.take("--statement")?);
    let check_rejections = options.flag("--check-rejections");
    options.finish()?;
    // Compile solely from caller-approved count and grammar before reading
    // the statement or bundle. Neither is permitted to choose verifier code.
    let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program)?;
    let verifier = compiler.verifier(batches)?;
    drop(compiler);
    let setup_seconds = started.elapsed().as_secs_f64();
    let statement = read_statement(&statement_path)?;
    source.check(&statement)?;
    let proof = read(&proof_path, MAX_GRAMMAR_TREE_BYTES)?;
    let verifying = Instant::now();
    verifier.verify_complete(&statement, &[F128::ZERO; 15], &proof)?;
    let verification_seconds = verifying.elapsed().as_secs_f64();
    if check_rejections {
      reject_mutations(&verifier, &statement, &proof)?;
    }
    println!(
      "{}",
      json!({"accepted":true, "claim":"complete Program grammar parse", "batches":batches, "source":source.json(), "proof_bytes":proof.len(), "identity":blake3::Hash::from(verifier.identity()).to_hex().as_str(), "setup_seconds":setup_seconds, "verification_seconds":verification_seconds, "rejection_checks":if check_rejections {9} else {0}})
    );
    return Ok(());
  }
  let frames = PathBuf::from(options.take("--frames")?);
  let directory = PathBuf::from(options.take("--out")?);
  let workers = options.number("--workers", 8)?;
  let threads = options.number("--threads", 4)?;
  let resume = options.flag("--resume");
  ensure!(
    (1..=32).contains(&workers) && (1..=64).contains(&threads),
    "worker/thread bounds"
  );
  options.finish()?;
  let config = json!({"format":"IxBy/grammar-tree-run/v0", "batches":batches, "source":source.json(), "grammar":"Program"});
  if resume {
    let previous: serde_json::Value =
      serde_json::from_slice(&read(&directory.join("run.json"), 4096)?)?;
    ensure!(previous == config, "resume configuration differs");
  } else {
    std::fs::create_dir(&directory)?;
    write_new(
      &directory.join("run.json"),
      &serde_json::to_vec_pretty(&config)?,
    )?;
  }
  let pools = (0..workers)
    .map(|_| rayon::ThreadPoolBuilder::new().num_threads(threads).build())
    .collect::<std::result::Result<Vec<_>, _>>()?;
  let run =
    Run { frames: &frames, directory: &directory, source, resume, pools };
  let mut compiler = GrammarTreeCompiler::new(GrammarKind::Program)?;
  let mut levels = Vec::new();
  let mut width = 2;
  while width <= batches {
    let jobs = (0..batches / width)
      .map(|i| Job {
        left: Chunk { start: i * width, leaves: width / 2 },
        right: Chunk { start: i * width + width / 2, leaves: width / 2 },
      })
      .collect::<Vec<_>>();
    levels.push(run.level(&mut compiler, &jobs)?);
    width *= 2;
  }
  let mut chunks = forest(batches);
  let mut root = chunks.pop().context("empty tree")?;
  while let Some(left) = chunks.pop() {
    let job = Job { left, right: root };
    levels.push(run.level(&mut compiler, &[job])?);
    root = job.parent();
  }
  ensure!(root.start == 0 && root.leaves == batches, "incomplete aggregation");
  let verifier = compiler.verifier(batches)?;
  drop(compiler);
  let (statement, proof) = read_chunk(&frames, &directory, source, root)?;
  let verifying = Instant::now();
  verifier.verify_complete(&statement, &[F128::ZERO; 15], &proof)?;
  let verification_seconds = verifying.elapsed().as_secs_f64();
  for (name, bytes) in [
    ("root.flock", proof.clone()),
    ("root.statement", statement_bytes(&statement)),
  ] {
    let path = directory.join(name);
    if resume && path.exists() {
      ensure!(
        read(&path, MAX_GRAMMAR_TREE_BYTES)? == bytes,
        "existing root differs"
      );
    } else {
      write_new(&path, &bytes)?;
    }
  }
  let result = json!({"accepted":true, "claim":"complete Program grammar parse", "batches":batches, "merges":batches - 1, "source":source.json(), "proof_bytes":proof.len(), "identity":blake3::Hash::from(verifier.identity()).to_hex().as_str(), "workers":workers, "threads_per_worker":threads, "elapsed_seconds":started.elapsed().as_secs_f64(), "verification_seconds":verification_seconds, "levels":levels});
  write_new(
    &directory.join("result.json"),
    &serde_json::to_vec_pretty(&result)?,
  )?;
  println!("{result}");
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn canonical_forest_covers_every_batch_without_padding() {
    for count in 2..=MAX_GRAMMAR_TREE_LEAVES {
      let chunks = forest(count);
      assert_eq!(chunks.iter().map(|c| c.leaves).sum::<usize>(), count);
      let mut previous = 0;
      for chunk in &chunks {
        assert_eq!(chunk.start, previous);
        assert!(chunk.leaves.is_power_of_two());
        previous += chunk.leaves;
      }
      let mut total = chunks.last().unwrap().leaves;
      for chunk in chunks[..chunks.len() - 1].iter().rev() {
        total += chunk.leaves;
        assert_eq!(chunk.leaves, 1usize << (total - 1).ilog2());
      }
      let power_merges =
        (1..=count.ilog2()).map(|level| count >> level).sum::<usize>();
      assert_eq!(power_merges + chunks.len() - 1, count - 1);
    }
  }
}
