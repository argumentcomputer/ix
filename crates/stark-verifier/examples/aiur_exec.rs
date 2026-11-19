//! Prove `AiurExec::aiur_exec` nodes: a leaf over one batch proof of a program
//! entry, a join of two aggregate nodes, and a wrap of one. A node directory
//! holds `proof.bin` (raw batch proof), `claims.bin` (its serialized outer
//! claim), `out.bin` (the 104-byte output claim) and `report.json`. A program
//! proof directory holds `root-vk.bin`, `root-claims.bin` and `root-proof.bin`
//! (`batch_root`).
//!
//! ```text
//! aiur_exec identity AX.ixa PROGRAM_VK PROGRAM_CLAIMS OUT_DIR
//! aiur_exec leaf  AX.ixa IDENTITY_DIR PROGRAM_DIR NODE_DIR
//! aiur_exec join  AX.ixa IDENTITY_DIR LEFT_DIR RIGHT_DIR NODE_DIR
//! aiur_exec wrap  AX.ixa IDENTITY_DIR CHILD_DIR NODE_DIR
//! aiur_exec root  NODE_DIR IDENTITY_DIR ROOT_DIR
//! ```
//!
//! `identity` writes the aggregator's key (`vk.bin`), its entry index, the
//! program's key digest and entry index, and the 80-byte identity blob
//! (`allowed.bin`); `root` lays a node out as the ladder's root directory.
use aiur::{
  artifact::Package,
  field::FieldBackend,
  library::io::{Stream, Streams},
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use serde_json::json;
use std::{error::Error, fs, path::Path, time::Instant};

const ENTRY: &str = "AiurExec::aiur_exec";
const OUT_BYTES: usize = 104;
/// Words of each model in a program claim `[1, index, m, data, m']`.
const MODEL_WORDS: usize = 331;

type R<T> = Result<T, Box<dyn Error>>;

fn digest_words(bytes: &[u8]) -> Vec<u64> {
  stark_verifier::digest_words(bytes)
}

fn stream(channel: u64, key: Vec<u64>, bytes: &[u8]) -> Stream {
  Stream { channel, key, values: bytes.iter().map(|&b| u64::from(b)).collect() }
}

/// `serializeClaims` of one claim.
fn claims_bytes(claim: &[u64]) -> Vec<u8> {
  let mut out = 1u64.to_le_bytes().to_vec();
  out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
  for w in claim {
    out.extend_from_slice(&w.to_le_bytes());
  }
  out
}

fn decode_one_claim(bytes: &[u8]) -> R<Vec<u64>> {
  let claims = stark_verifier::compress_wrap::decode_claims(bytes)?;
  if claims.len() != 1 {
    return Err("expected exactly one claim".into());
  }
  Ok(claims[0].iter().map(|v| v.as_canonical_u64()).collect())
}

fn out_claim(count: u64, first: &[u8; 32], last: &[u8; 32], data: &[u8; 32]) -> Vec<u8> {
  let mut out = count.to_le_bytes().to_vec();
  out.extend_from_slice(first);
  out.extend_from_slice(last);
  out.extend_from_slice(data);
  out
}

fn parse_out(bytes: &[u8]) -> R<(u64, [u8; 32], [u8; 32], [u8; 32])> {
  if bytes.len() != OUT_BYTES {
    return Err("output claim is not 104 bytes".into());
  }
  let a = |i: usize| -> [u8; 32] { bytes[8 + 32 * i..8 + 32 * (i + 1)].try_into().unwrap() };
  Ok((u64::from_le_bytes(bytes[..8].try_into()?), a(0), a(1), a(2)))
}

fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  let mut pre = vec![1u8];
  pre.extend_from_slice(left);
  pre.extend_from_slice(right);
  *blake3::hash(&pre).as_bytes()
}

struct Prover {
  package_digest: String,
  program: aiur::bytecode::CheckedProgram<aiur::field::NativeField<Val>>,
  trace: aiur::trace::TraceArtifact,
}

impl Prover {
  fn load(path: &str) -> R<Self> {
    let (package, digest) = Package::load(path.as_ref())?;
    let (program, trace) = package.traced()?;
    let mut program = program.check_field::<Val>()?;
    program.track_depth(&trace)?;
    Ok(Self { package_digest: digest.to_string(), program, trace })
  }

  fn plan(&self) -> R<TracePlan<'_, aiur::field::NativeField<Val>>> {
    Ok(TracePlan::new(&self.program, self.trace.clone())?)
  }

  /// Executes and proves the entry over `streams` as one normalized shard;
  /// writes the node directory.
  fn prove(&self, streams: Vec<Stream>, out: &[u8], dir: &Path, label: &str) -> R<()> {
    fs::create_dir_all(dir)?;
    let allowed = streams
      .iter()
      .find(|s| s.channel == 3)
      .map(|s| s.values.iter().map(|&v| v as u8).collect::<Vec<u8>>())
      .ok_or("no identity stream")?;
    let mut args = digest_words(&allowed);
    args.extend(digest_words(out));
    let start = Instant::now();
    let hints = stark_verifier::prepare(&self.program, &Streams(streams))?;
    let address = self.program.field().decode(&args)?;
    let record = hints.execute(ENTRY, address.clone())?;
    let execution_seconds = start.elapsed().as_secs_f64();
    let plan = self.plan()?;
    let backend = Backend::for_batch(&plan, Parameters::default())?;
    let rows = backend.execution_rows(&record);
    let logs = backend.normalized_log_heights(&rows, 0)?;
    let start = Instant::now();
    let (claim, proof) = backend.prove_normalized(ENTRY, &address, &[], record, &logs)?;
    let prove_seconds = start.elapsed().as_secs_f64();
    let start = Instant::now();
    backend.verify_batch(ENTRY, &address, &[], &proof)?;
    let verify_seconds = start.elapsed().as_secs_f64();
    let raw = proof.to_bytes().map_err(|e| e.to_string())?;
    let claim: Vec<u64> = claim.iter().map(|v| v.as_canonical_u64()).collect();
    fs::write(dir.join("proof.bin"), &raw)?;
    fs::write(dir.join("claims.bin"), claims_bytes(&claim))?;
    fs::write(dir.join("out.bin"), out)?;
    let report = json!({
      "node": label,
      "package_blake3": self.package_digest,
      "execution_seconds": execution_seconds,
      "prove_seconds": prove_seconds,
      "verify_seconds": verify_seconds,
      "proof_bytes": raw.len(),
      "max_log_height": logs.iter().max(),
      "rows": rows.iter().sum::<usize>(),
      "peak_rss_bytes": aiur::trace::stark::planning::peak_resident_memory(),
    });
    fs::write(dir.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
    println!("{report}");
    Ok(())
  }
}

struct Identity {
  allowed: Vec<u8>,
  vk: Vec<u8>,
  program_vk: Vec<u8>,
}

impl Identity {
  fn load(dir: &Path) -> R<Self> {
    Ok(Self {
      allowed: fs::read(dir.join("allowed.bin"))?,
      vk: fs::read(dir.join("vk.bin"))?,
      program_vk: fs::read(dir.join("program-vk.bin"))?,
    })
  }
}

fn child_out(dir: &Path) -> R<Vec<u8>> {
  Ok(fs::read(dir.join("out.bin"))?)
}

fn main() -> R<()> {
  let args: Vec<String> = std::env::args().collect();
  let mode = args.get(1).map(String::as_str).unwrap_or("");
  match (mode, &args[2.min(args.len())..]) {
    ("identity", [ax, program_vk, program_claims, out]) => {
      let prover = Prover::load(ax)?;
      let plan = prover.plan()?;
      let backend = Backend::for_batch(&plan, Parameters::default())?;
      let vk = backend.verifying_key_bytes()?;
      let zero = prover.program.field().decode(&[0; 16])?;
      let own = backend.claim(ENTRY, &zero, &[])?;
      let own_index = own[1].as_canonical_u64();
      let program_vk = fs::read(program_vk)?;
      let claim = decode_one_claim(&fs::read(program_claims)?)?;
      let program_index = claim[1];
      let mut allowed = blake3::hash(&program_vk).as_bytes().to_vec();
      allowed.extend_from_slice(&program_index.to_le_bytes());
      allowed.extend_from_slice(blake3::hash(&vk).as_bytes());
      allowed.extend_from_slice(&own_index.to_le_bytes());
      let out = Path::new(out);
      fs::create_dir_all(out)?;
      fs::write(out.join("vk.bin"), &vk)?;
      fs::write(out.join("program-vk.bin"), &program_vk)?;
      fs::write(out.join("allowed.bin"), &allowed)?;
      let report = json!({
        "aggregator_package_blake3": prover.package_digest,
        "aggregator_key_blake3": blake3::hash(&vk).to_hex().to_string(),
        "aggregator_key_bytes": vk.len(),
        "aggregator_entry_index": own_index,
        "program_key_blake3": blake3::hash(&program_vk).to_hex().to_string(),
        "program_entry_index": program_index,
        "allowed_blake3": blake3::hash(&allowed).to_hex().to_string(),
      });
      fs::write(out.join("identity.json"), serde_json::to_vec_pretty(&report)?)?;
      println!("{report}");
      Ok(())
    },
    ("leaf", [ax, id, program, node]) => {
      let (id, program) = (Identity::load(Path::new(id))?, Path::new(program));
      if fs::read(program.join("root-vk.bin"))? != id.program_vk {
        return Err("the program proof is under another key".into());
      }
      let claims = fs::read(program.join("root-claims.bin"))?;
      let claim = decode_one_claim(&claims)?;
      if claim.len() < 2 + 2 * MODEL_WORDS {
        return Err("program claim is shorter than its two models".into());
      }
      let bytes = |w: &[u64]| w.iter().flat_map(|v| v.to_le_bytes()).collect::<Vec<u8>>();
      let m0 = &claim[2..2 + MODEL_WORDS];
      let data = &claim[2 + MODEL_WORDS..claim.len() - MODEL_WORDS];
      let m1 = &claim[claim.len() - MODEL_WORDS..];
      let out = out_claim(
        1,
        blake3::hash(&bytes(m0)).as_bytes(),
        blake3::hash(&bytes(m1)).as_bytes(),
        blake3::hash(&bytes(data)).as_bytes(),
      );
      let streams = vec![
        stream(3, vec![0], &id.allowed),
        stream(6, vec![0], &[0]),
        stream(1, vec![0], &id.program_vk),
        stream(0, vec![0], &fs::read(program.join("root-proof.bin"))?),
        stream(2, vec![0], &claims),
        stream(2, vec![2], &out),
      ];
      Prover::load(ax)?.prove(streams, &out, Path::new(node), "leaf")
    },
    ("join", [ax, id, left, right, node]) => {
      let id = Identity::load(Path::new(id))?;
      let (left, right) = (Path::new(left), Path::new(right));
      let (lo, ro) = (child_out(left)?, child_out(right)?);
      let (lc, lf, ll, ld) = parse_out(&lo)?;
      let (rc, rf, rl, rd) = parse_out(&ro)?;
      if ll != rf {
        return Err("the chains do not meet".into());
      }
      let out = out_claim(lc + rc, &lf, &rl, &node_hash(&ld, &rd));
      let streams = vec![
        stream(3, vec![0], &id.allowed),
        stream(6, vec![0], &[1]),
        stream(1, vec![1], &id.vk),
        stream(0, vec![0], &fs::read(left.join("proof.bin"))?),
        stream(2, vec![0], &fs::read(left.join("claims.bin"))?),
        stream(0, vec![1], &fs::read(right.join("proof.bin"))?),
        stream(2, vec![1], &fs::read(right.join("claims.bin"))?),
        stream(2, vec![2], &out),
        stream(4, digest_words(&lo), &lo),
        stream(4, digest_words(&ro), &ro),
      ];
      Prover::load(ax)?.prove(streams, &out, Path::new(node), "join")
    },
    ("wrap", [ax, id, child, node]) => {
      let id = Identity::load(Path::new(id))?;
      let child = Path::new(child);
      let out = child_out(child)?;
      let streams = vec![
        stream(3, vec![0], &id.allowed),
        stream(6, vec![0], &[2]),
        stream(1, vec![1], &id.vk),
        stream(0, vec![0], &fs::read(child.join("proof.bin"))?),
        stream(2, vec![0], &fs::read(child.join("claims.bin"))?),
      ];
      Prover::load(ax)?.prove(streams, &out, Path::new(node), "wrap")
    },
    ("root", [node, id, root]) => {
      let (node, root) = (Path::new(node), Path::new(root));
      let id = Identity::load(Path::new(id))?;
      fs::create_dir_all(root)?;
      fs::write(root.join("root-vk.bin"), &id.vk)?;
      fs::copy(node.join("claims.bin"), root.join("root-claims.bin"))?;
      fs::copy(node.join("proof.bin"), root.join("root-proof.bin"))?;
      fs::copy(node.join("out.bin"), root.join("out.bin"))?;
      fs::write(root.join("allowed.bin"), &id.allowed)?;
      println!("root key {}", blake3::hash(&id.vk).to_hex());
      Ok(())
    },
    _ => Err("usage: aiur_exec identity|leaf|join|wrap|root ... (see the module docs)".into()),
  }
}
