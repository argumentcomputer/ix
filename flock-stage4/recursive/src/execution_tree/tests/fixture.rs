//! Actual original-format bytes, production leaf proofs, and one recursive
//! execution proof. Native execution supplies advice only; the receiver has
//! neither the artifacts nor any child proof.
use super::*;
use ixby_flock::{
  hash::pack_bytes,
  ixby::{
    auth_memory::{MemoryDepth, SparseMemory},
    ixbf::DecodeLimits,
    ixbf_decode::{
      dispatch::DISPATCH_CONTEXT_INDICES,
      paged::{
        code_capture::batch::{CodeCaptureWitness, CompiledCodeCapture},
        commitment_bridge::{
          ArtifactDomain, CommitmentBridgeWitness, CompiledCommitmentBridge,
        },
        constructor_ids::{CompiledConstructorIds, ConstructorIdsAdvice},
        endpoints::{CompiledEndpoints, EndpointAdvice, EndpointFacts},
        input_capture::batch::{CompiledInputCapture, InputCaptureWitness},
        output_bytes::{CompiledOutputBytes, OutputBytesWitness},
        references::{CompiledReferences, ReferenceWitness},
        source_bytes::{CompiledSourceBytes, SourceBank, SourceBytesWitness},
      },
    },
    paged_exec::{CompiledPagedExecution, ExecutionStatement, NativeImage},
  },
};
use std::{
  io::{Read, Write},
  path::{Path, PathBuf},
  process::{Command, Stdio},
  time::Instant,
};

const IDENTITY: &[u8] = &[
  b'I', b'X', b'B', b'F', 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 8, 0x80,
  0x20, 64, 64, 24, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
];
const COUNTS: [usize; 11] = [1; 11];
const RECEIVER: &str = "execution_tree::tests::fixture::complete_root_receiver";

struct Cache(PathBuf);
impl Cache {
  fn new() -> Self {
    let directory = std::env::var_os("IXBY_PAGED_EXECUTION_OUT")
      .map(PathBuf::from)
      .unwrap_or_else(|| {
        std::env::temp_dir().join(format!(
          "ixby-complete-execution-{}-{}",
          std::process::id(),
          std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
        ))
      });
    std::fs::create_dir_all(&directory).unwrap();
    let marker = directory.join("fixture-format");
    let expected = b"IxBy/original-identity-recursive-proof-fixture/v0\n";
    if marker.exists() {
      assert_eq!(std::fs::read(&marker).unwrap(), expected);
    } else {
      std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&marker)
        .unwrap()
        .write_all(expected)
        .unwrap();
    }
    eprintln!("complete execution proof cache: {}", directory.display());
    Self(directory)
  }
  fn record(
    &self,
    name: &str,
    expected: &[F128],
    prove: impl FnOnce() -> Result<Vec<u8>>,
    verify: impl Fn(&[u8]) -> Result<()>,
  ) -> PagedNodeProof {
    let statement_path = self.0.join(format!("{name}.statement"));
    let proof_path = self.0.join(format!("{name}.flock"));
    let statement =
      expected.iter().flat_map(|&v| crate::f128::bytes(v)).collect::<Vec<_>>();
    if statement_path.exists() && proof_path.exists() {
      let saved = read_bounded(&statement_path, statement.len() as u64);
      let proof = read_bounded(&proof_path, MAX_PAGED_TREE_BYTES);
      if saved == statement && verify(&proof).is_ok() {
        eprintln!("reused verified {name}: {} bytes", proof.len());
        return PagedNodeProof { statement: expected.to_vec(), proof };
      }
      eprintln!("rebuilding stale fixture proof {name}");
    }
    let started = Instant::now();
    let proof = prove().unwrap_or_else(|e| panic!("proving {name}: {e:#}"));
    let prove_time = started.elapsed();
    verify(&proof).unwrap_or_else(|e| panic!("verifying {name}: {e:#}"));
    eprintln!(
      "proved {name}: {} bytes; witness+prove {prove_time:?}; with verification {:?}",
      proof.len(),
      started.elapsed()
    );
    atomic_write(&statement_path, &statement);
    atomic_write(&proof_path, &proof);
    PagedNodeProof { statement: expected.to_vec(), proof }
  }
}
fn read_bounded(path: &Path, limit: u64) -> Vec<u8> {
  let mut bytes = Vec::new();
  std::fs::File::open(path)
    .unwrap()
    .take(limit + 1)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(bytes.len() as u64 <= limit);
  bytes
}
fn atomic_write(path: &Path, bytes: &[u8]) {
  let temporary = path.with_extension(format!("tmp-{}", std::process::id()));
  let mut file = std::fs::OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(&temporary)
    .unwrap();
  file.write_all(bytes).unwrap();
  file.sync_all().unwrap();
  drop(file);
  std::fs::rename(temporary, path).unwrap();
}
fn native_statement(
  profile: &[u8],
  program: &[u8],
  input: &[u8],
  output: &[u8],
) -> [F128; 2] {
  fn hash(tag: u8, prefix: &[u8], data: &[u8]) -> [u8; 32] {
    let mut bytes = b"IxBy/commit/v0".to_vec();
    bytes.extend([0, tag]);
    bytes.extend(prefix);
    bytes.extend(data);
    *blake3::hash(&bytes).as_bytes()
  }
  let p = hash(0, &[], profile);
  let b = hash(1, &p, program);
  let i = hash(2, &b, input);
  let o = hash(3, &b, output);
  let s = hash(4, &[], &[p, b, i, o].concat());
  [pack_bytes(&s[..16]), pack_bytes(&s[16..])]
}

fn leaves(cache: &Cache) -> (Vec<PagedNodeProof>, EndpointAdvice) {
  let payload = b"complete original-format execution";
  let mut input = b"IXFI\x01\0\0\0\0\0\0\0\x01\0\x06".to_vec();
  input.push(u8::try_from(payload.len()).unwrap());
  input.extend(payload);
  let mut output = b"IXFO\x01\0\0\0\0\0\0\0\0\x06".to_vec();
  output.push(u8::try_from(payload.len()).unwrap());
  output.extend(payload);
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let mut components = Vec::new();
  macro_rules! record {
    ($name:expr, $setup:expr, $advice:expr) => {
      cache.record(
        $name,
        $advice.statement.words(),
        || $setup.prove(&$advice),
        |bytes| $setup.verify(&$advice.statement, bytes),
      )
    };
  }
  let setup = CompiledSourceBytes::compile(SourceBank::Program).unwrap();
  let mut walk =
    SourceBytesWitness::new(SourceBank::Program, IDENTITY).unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-00", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  drop(setup);
  let setup = CompiledCodeCapture::compile().unwrap();
  let mut walk = CodeCaptureWitness::new(IDENTITY).unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-01", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  let context = DISPATCH_CONTEXT_INDICES.map(|i| walk.parser()[i]);
  drop(setup);
  let setup = CompiledReferences::compile().unwrap();
  let mut walk =
    ReferenceWitness::new([context[1], context[0], context[12]]).unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-02", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  drop(setup);
  let setup = CompiledConstructorIds::compile().unwrap();
  let a = ConstructorIdsAdvice::new(&mut memory, 0).unwrap();
  components.push(record!("component-03", setup, a));
  drop(setup);
  let setup = CompiledSourceBytes::compile(SourceBank::Input).unwrap();
  let mut walk = SourceBytesWitness::new(SourceBank::Input, &input).unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-04", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  drop(setup);
  let setup = CompiledInputCapture::compile().unwrap();
  let mut walk = InputCaptureWitness::new(&input, context).unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-05", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  drop(setup);
  let image =
    NativeImage::load(IDENTITY, &input, DecodeLimits::default()).unwrap();
  assert_eq!(memory.root(), image.memory.root());
  let setup = CompiledPagedExecution::compile(BatchClass::Small).unwrap();
  let mut machine = image.machine().unwrap();
  let a = machine.batch(BatchClass::Small, &mut memory).unwrap().unwrap();
  let statement = ExecutionStatement::from_words(&a.expected).unwrap();
  components.push(cache.record(
    "component-06",
    statement.words(),
    || setup.prove(&a),
    |bytes| setup.verify(&statement, bytes),
  ));
  assert!(machine.batch(BatchClass::Small, &mut memory).unwrap().is_none());
  assert_eq!(machine.state[0], F128::new(2, 0));
  drop(setup);
  let setup = CompiledOutputBytes::compile().unwrap();
  let mut walk =
    OutputBytesWitness::new(&output, [machine.state[2], machine.state[3]])
      .unwrap();
  let a = walk.next_batch(&mut memory).unwrap().unwrap();
  components.push(record!("component-07", setup, a));
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  drop(setup);
  let p = profile();
  let mut parent = p.digest();
  for (index, (domain, raw)) in [
    (ArtifactDomain::Program, IDENTITY),
    (ArtifactDomain::Input, input.as_slice()),
    (ArtifactDomain::Output, output.as_slice()),
  ]
  .into_iter()
  .enumerate()
  {
    let setup = CompiledCommitmentBridge::compile(domain).unwrap();
    let mut walk = CommitmentBridgeWitness::new(domain, raw, parent).unwrap();
    let a = walk.next_batch().unwrap().unwrap();
    components.push(record!(&format!("component-{:02}", 8 + index), setup, a));
    assert!(walk.next_batch().unwrap().is_none());
    if domain == ArtifactDomain::Program {
      parent = walk.digest();
    }
  }
  assert_eq!(components.len(), COUNTS.len());
  let facts = EndpointFacts::assemble(
    components
      .iter()
      .map(|p| p.statement.as_slice())
      .collect::<Vec<_>>()
      .try_into()
      .unwrap(),
  )
  .unwrap();
  let endpoints = EndpointAdvice::new(&p, facts).unwrap();
  assert_eq!(
    endpoints.statement.digest(),
    native_statement(&p.encode(), IDENTITY, &input, &output)
  );
  (components, endpoints)
}

fn join_components(
  compiler: &mut PagedTreeCompiler,
  cache: &Cache,
  components: &[PagedNodeProof],
  first: usize,
  end: usize,
) -> PagedNodeProof {
  if first + 1 == end {
    let p = &components[first];
    return PagedNodeProof {
      statement: p.statement.clone(),
      proof: p.proof.clone(),
    };
  }
  let middle = first + (1usize << (end - first - 1).ilog2());
  let left = join_components(compiler, cache, components, first, middle);
  let right = join_components(compiler, cache, components, middle, end);
  let expected =
    [left.statement.as_slice(), right.statement.as_slice()].concat();
  let started = Instant::now();
  let node = compiler.compile_components(first, end).unwrap();
  eprintln!(
    "compiled facts-{first:02}-{end:02} in {:?}: {:?}",
    started.elapsed(),
    node.geometry()
  );
  cache.record(
    &format!("facts-{first:02}-{end:02}"),
    &expected,
    || {
      let p = node.prove(
        [&left.statement, &right.statement],
        [&left.proof, &right.proof],
      )?;
      ensure!(p.statement == expected, "joined component publication");
      Ok(p.proof)
    },
    |bytes| node.verify(&expected, bytes),
  )
}

#[test]
#[ignore = "all genuine Stage 3 leaves and one complete recursive execution proof"]
fn original_bytes_identity_proves_one_execution_digest() {
  let cache = Cache::new();
  // Profile, class and exact tree are chosen before any cached proof is read.
  let mut compiler =
    PagedTreeCompiler::new(profile(), BatchClass::Small, COUNTS).unwrap();
  let (components, endpoints) = leaves(&cache);
  let setup = CompiledEndpoints::compile(profile()).unwrap();
  let endpoint_proof = cache.record(
    "endpoints",
    endpoints.statement.words(),
    || setup.prove(&endpoints),
    |p| setup.verify(&endpoints.statement, p),
  );

  // This is a genuinely valid conditional endpoint proof with unchanged S.
  // The endpoint relation leaves parser metadata to the actual parser proof.
  // The closing relation must identify ALL facts, including that metadata.
  let mut changed = *endpoints.facts.words();
  changed[Component::CodeCapture.range().start + 43].hi ^= 1 << 63;
  let changed = EndpointAdvice::new(
    &profile(),
    EndpointFacts::from_words(&changed).unwrap(),
  )
  .unwrap();
  assert_eq!(changed.statement.digest(), endpoints.statement.digest());
  let different_endpoint = cache.record(
    "endpoints-different-parser-metadata",
    changed.statement.words(),
    || setup.prove(&changed),
    |p| setup.verify(&changed.statement, p),
  );
  drop(setup);
  let facts = join_components(&mut compiler, &cache, &components, 0, 11);
  assert_eq!(facts.statement, endpoints.facts.words());
  let started = Instant::now();
  let node = compiler.compile_complete().unwrap();
  eprintln!(
    "compiled complete root in {:?}: {:?}; identity {}",
    started.elapsed(),
    node.geometry(),
    blake3::Hash::from(node.identity())
  );
  let expected = endpoints.statement.digest();
  let root = cache.record(
    "complete-root",
    &expected,
    || {
      let p = node.prove(
        [&facts.statement, &endpoint_proof.statement],
        [&facts.proof, &endpoint_proof.proof],
      )?;
      ensure!(p.statement == expected, "complete root statement digest");
      Ok(p.proof)
    },
    |p| node.verify(&expected, p),
  );
  let error = node
    .prove(
      [&facts.statement, &different_endpoint.statement],
      [&facts.proof, &different_endpoint.proof],
    )
    .err()
    .expect("closing relation accepted mismatched valid child proofs");
  assert!(error.to_string().contains("advice constraints"), "{error:#}");
  eprintln!(
    "valid child proofs with different parser metadata rejected: {error:#}"
  );
  drop(node);
  drop(compiler);
  drop(components);
  drop(facts);
  drop(endpoint_proof);
  drop(different_endpoint);
  fresh_verify(expected, &root.proof);
}

fn fresh_verify(expected: [F128; 2], proof: &[u8]) {
  let mut child = Command::new(std::env::current_exe().unwrap())
    .args(["--ignored", "--exact", RECEIVER, "--test-threads=1", "--nocapture"])
    .current_dir(std::env::temp_dir())
    .env_clear()
    .env("IXBY_COMPLETE_ROOT_RECEIVER", "1")
    .env("RAYON_NUM_THREADS", "4")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();
  let mut stdin = child.stdin.take().unwrap();
  for word in expected {
    stdin.write_all(&crate::f128::bytes(word)).unwrap();
  }
  stdin.write_all(proof).unwrap();
  drop(stdin);
  let output = child.wait_with_output().unwrap();
  eprintln!(
    "{}{}",
    String::from_utf8_lossy(&output.stdout),
    String::from_utf8_lossy(&output.stderr)
  );
  assert!(
    output.status.success(),
    "fresh complete execution verifier rejected"
  );
}

#[test]
#[ignore = "fresh receiver supplied only an approved setup, S and a root proof"]
fn complete_root_receiver() {
  assert!(std::env::var_os("IXBY_COMPLETE_ROOT_RECEIVER").is_some());
  check_root_receiver(profile(), BatchClass::Small);
}

#[test]
#[ignore = "fresh receiver for the semantics-1 conversion CLI fixture; stdin contains only S and the root proof"]
fn conversion_root_receiver() {
  assert!(std::env::var_os("IXBY_CONVERSION_ROOT_RECEIVER").is_some());
  let profile =
    FunctionalProfile::new([1, 0, 6, 6, 2, 0, 8, 128, 0, 64], 7).unwrap();
  check_root_receiver(profile, BatchClass::Bytes);
}

fn check_root_receiver(profile: FunctionalProfile, class: BatchClass) {
  let started = Instant::now();
  // This entire setup is fixed before the receiver reads any proof bytes.
  let mut compiler = PagedTreeCompiler::new(profile, class, COUNTS).unwrap();
  let verifier = compiler.verifier().unwrap();
  drop(compiler);
  eprintln!(
    "fresh complete setup {:?}; identity {}",
    started.elapsed(),
    blake3::Hash::from(verifier.identity())
  );
  let mut bytes = Vec::new();
  std::io::stdin()
    .take(MAX_PAGED_TREE_BYTES + 33)
    .read_to_end(&mut bytes)
    .unwrap();
  assert!(bytes.len() > 32 && bytes.len() as u64 <= MAX_PAGED_TREE_BYTES + 32);
  let expected = [pack_bytes(&bytes[..16]), pack_bytes(&bytes[16..32])];
  let proof = &bytes[32..];
  let started = Instant::now();
  verifier.verify(expected, proof).unwrap();
  eprintln!(
    "fresh complete execution verification {:?}; {} root bytes",
    started.elapsed(),
    proof.len()
  );
  for index in 0..2 {
    for high in [false, true] {
      let mut wrong = expected;
      if high {
        wrong[index].hi ^= 1 << 63;
      } else {
        wrong[index].lo ^= 1;
      }
      assert!(verifier.verify(wrong, proof).is_err());
    }
  }
  let mut bundle: Bundle = codec().deserialize(proof).unwrap();
  bundle.root_advice[0] += F128::ONE;
  assert!(
    verifier.verify(expected, &codec().serialize(&bundle).unwrap()).is_err()
  );
  for at in [0, 8, 40, proof.len() - 1] {
    let mut bad = proof.to_vec();
    bad[at] ^= 1;
    assert!(verifier.verify(expected, &bad).is_err());
  }
  assert!(verifier.verify(expected, &proof[..proof.len() - 1]).is_err());
  let mut bad = proof.to_vec();
  bad.push(0);
  assert!(verifier.verify(expected, &bad).is_err());
}

#[test]
#[ignore = "three actual source batches, two recursive levels, and valid nonadjacent children"]
fn source_chain_links_all_boundaries_through_two_recursive_levels() {
  let cache = Cache::new();
  let mut counts = COUNTS;
  counts[Component::ProgramBytes as usize] = 3;
  let mut compiler =
    PagedTreeCompiler::new(profile(), BatchClass::Small, counts).unwrap();
  let source = (0usize..5121)
    .map(|i| u8::try_from((i * 43 + 17) % 256).unwrap())
    .collect::<Vec<_>>();
  let setup = CompiledSourceBytes::compile(SourceBank::Program).unwrap();
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let mut walk = SourceBytesWitness::new(SourceBank::Program, &source).unwrap();
  let mut leaves = Vec::new();
  for i in 0..3 {
    let a = walk.next_batch(&mut memory).unwrap().unwrap();
    leaves.push(cache.record(
      &format!("chain-leaf-{i}"),
      a.statement.words(),
      || setup.prove(&a),
      |p| setup.verify(&a.statement, p),
    ));
  }
  assert!(walk.next_batch(&mut memory).unwrap().is_none());
  // Same artifact and chunk interval as leaf 1, but an unrelated initial root.
  // Both leaf proofs verify. The parent must reject their memory boundary.
  let mut walk = SourceBytesWitness::new(SourceBank::Program, &source).unwrap();
  let mut empty = SparseMemory::new(MemoryDepth::new(40).unwrap());
  walk.next_batch(&mut empty).unwrap().unwrap();
  let mut reset = SparseMemory::new(MemoryDepth::new(40).unwrap());
  let a = walk.next_batch(&mut reset).unwrap().unwrap();
  let disconnected = cache.record(
    "chain-disconnected-leaf",
    a.statement.words(),
    || setup.prove(&a),
    |p| setup.verify(&a.statement, p),
  );
  assert_eq!(&disconnected.statement[..4], &leaves[1].statement[..4]);
  assert_ne!(&disconnected.statement[4..6], &leaves[1].statement[4..6]);
  drop(setup);
  fn join_expected(a: &[F128], b: &[F128]) -> Vec<F128> {
    assert_eq!(&a[..3], &b[..3]);
    assert_eq!(&a[6..9], &b[3..6]);
    [a[..6].to_vec(), b[6..9].to_vec()].concat()
  }
  let node = compiler.compile_component(Component::ProgramBytes, 2).unwrap();
  let expected = join_expected(&leaves[0].statement, &leaves[1].statement);
  let first = cache.record(
    "chain-node-2",
    &expected,
    || {
      let p = node.prove(
        [&leaves[0].statement, &leaves[1].statement],
        [&leaves[0].proof, &leaves[1].proof],
      )?;
      ensure!(p.statement == expected, "two-leaf chain publication");
      Ok(p.proof)
    },
    |p| node.verify(&expected, p),
  );
  let error = node
    .prove(
      [&leaves[0].statement, &disconnected.statement],
      [&leaves[0].proof, &disconnected.proof],
    )
    .err()
    .expect("chain accepted valid disconnected memory roots");
  assert!(error.to_string().contains("advice constraints"), "{error:#}");
  eprintln!("valid disconnected source proofs rejected: {error:#}");
  drop(node);
  let node = compiler.compile_component(Component::ProgramBytes, 3).unwrap();
  let expected = join_expected(&first.statement, &leaves[2].statement);
  let root = cache.record(
    "chain-node-3",
    &expected,
    || {
      let p = node.prove(
        [&first.statement, &leaves[2].statement],
        [&first.proof, &leaves[2].proof],
      )?;
      ensure!(p.statement == expected, "three-leaf chain publication");
      Ok(p.proof)
    },
    |p| node.verify(&expected, p),
  );
  assert_eq!(root.statement[3], F128::ZERO);
  assert_eq!(root.statement[6], F128::new(6, 0));
  for at in 0..9 {
    for high in [false, true] {
      let mut wrong = expected.clone();
      if high {
        wrong[at].hi ^= 1 << 63;
      } else {
        wrong[at].lo ^= 1;
      }
      assert!(node.verify(&wrong, &root.proof).is_err());
    }
  }
  let mut bundle: Bundle = codec().deserialize(&root.proof).unwrap();
  bundle.root_advice[0] += F128::ONE;
  assert!(
    node.verify(&expected, &codec().serialize(&bundle).unwrap()).is_err()
  );
}
