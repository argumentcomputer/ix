//! Prove an Aiur join (`ix_aggr` shape 17 or 18): an environment's aggregate
//! root and an Aiur program's proof, joined into one `AiurRun` claim, and
//! `ix_aggr` wraps (shape 1) of the result.
//!
//! ```text
//! aiur_join join IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 ENV.ixe MANIFEST.ixes ENV_ROOT AIUR_ROOT THEOREM BINDING NODE
//! aiur_join wrap IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 CHILD NODE
//! aiur_join root IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 NODE ROOT
//! ```
//!
//! - `ENV_ROOT`: an exported aggregate root (`export_root extract`):
//!   `root-proof.bin`, `root-claims.bin`, `ix-claim.bin`.
//! - `AIUR_ROOT`: an Aiur program proof: `root-vk.bin`, `root-claims.bin`,
//!   `root-proof.bin`.
//! - `THEOREM`, `BINDING`: names of two constants of `ENV.ixe`.
//!
//! A node directory holds `proof.bin` (raw batch proof), `claims.bin` (its
//! outer claim list), `out.bin` (the `AiurRun` claim) and `report.json`;
//! `root` lays it out as an exported root (`root-vk.bin`, `root-claims.bin`,
//! `root-proof.bin`, `ix-claim.bin`, `backend-allowed.bin`).
use aggregate_controller::{
  aiur::AiurRun,
  plan, prepare,
  protocol::ChildKind,
  streams::{self, Keys, Transport},
};
use aiur::{
  field::FieldBackend,
  library::io::{Stream, Streams},
};
use ix_prover::{
  aggregate::AGGR_ENTRY,
  request::{Environment, IXVM_ENTRY},
  system::{Program, ProtocolParameters, System},
};
use ixon::shard::ShardManifest;
use multi_stark::p3_field::PrimeField64;
use serde_json::json;
use std::{error::Error, fs, path::Path, time::Instant};

type R<T> = Result<T, Box<dyn Error>>;


fn pinned_system(path: &str, expected: &str) -> R<System> {
  let pin = blake3::Hash::from_hex(expected)?;
  let (bytes, digest) = aiur::artifact::read(path.as_ref())?;
  if &digest.0 != pin.as_bytes() {
    return Err(format!("artifact differs from its pin: {path}").into());
  }
  let package = aiur::artifact::Package::decode(&bytes)?;
  let (program, trace) = package.traced()?;
  let program = Program::new(program, trace, digest)?;
  Ok(System::prepare(&program, ProtocolParameters::default())?)
}

fn digest_words(bytes: &[u8]) -> Vec<u64> {
  stark_verifier::digest_words(bytes)
}

fn claims_bytes(claim: &[u64]) -> Vec<u8> {
  let mut out = 1u64.to_le_bytes().to_vec();
  out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
  for w in claim {
    out.extend_from_slice(&w.to_le_bytes());
  }
  out
}

struct Ctx {
  aggr: System,
  allowed: Vec<u8>,
  ixvm_key: Vec<u8>,
  aggr_index: u64,
}

fn ctx(args: &[String]) -> R<Ctx> {
  let ixvm = pinned_system(&args[0], &args[1])?;
  let aggr = pinned_system(&args[2], &args[3])?;
  let ixvm_id = ixvm.identity(IXVM_ENTRY, 8)?;
  let aggr_id = aggr.identity(AGGR_ENTRY, 16)?;
  let allowed = aggregate_controller::protocol::allowed_blob(
    &ixvm_id.key, ixvm_id.function_index, &aggr_id.key, aggr_id.function_index);
  Ok(Ctx { allowed, ixvm_key: ixvm_id.key, aggr_index: aggr_id.function_index, aggr })
}

/// Executes and proves `ix_aggr` over `streams` as one normalized shard on
/// device 0 (the CPU without CUDA) and writes the node directory.
fn prove(c: &Ctx, entries: &[streams::Entry<'_>], out: &[u8], dir: &Path, label: &str) -> R<()> {
  fs::create_dir_all(dir)?;
  let streams = Streams(
    entries
      .iter()
      .map(|(channel, key, payload)| Stream {
        channel: *channel,
        key: key.clone(),
        values: payload.iter().map(|&b| u64::from(b)).collect(),
      })
      .collect(),
  );
  let mut args = digest_words(&c.allowed);
  args.extend(digest_words(out));
  let program = c.aggr.program().checked();
  let start = Instant::now();
  let hints = stark_verifier::prepare(program, &streams)?;
  let address = program.field().decode(&args)?;
  let record = hints.execute(AGGR_ENTRY, address.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();
  let device = if cfg!(feature = "cuda") { Some(0) } else { None };
  let backend = c.aggr.prover(device)?;
  let rows = backend.execution_rows(&record);
  let logs = backend.normalized_log_heights(&rows, 0)?;
  let start = Instant::now();
  let (claim, proof) = backend.prove_normalized(AGGR_ENTRY, &address, &[], record, &logs)?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let raw = proof.to_bytes().map_err(|e| e.to_string())?;
  let start = Instant::now();
  let shards = c.aggr.verify(AGGR_ENTRY, &args, &raw)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  let claim: Vec<u64> = claim.iter().map(|v| v.as_canonical_u64()).collect();
  fs::write(dir.join("proof.bin"), &raw)?;
  fs::write(dir.join("claims.bin"), claims_bytes(&claim))?;
  fs::write(dir.join("out.bin"), out)?;
  let report = json!({
    "node": label,
    "aggregator_key_blake3": blake3::hash(c.aggr.key()).to_hex().to_string(),
    "execution_seconds": execution_seconds,
    "prove_seconds": prove_seconds,
    "verify_seconds": verify_seconds,
    "shards": shards,
    "proof_bytes": raw.len(),
    "max_log_height": logs.iter().max(),
    "rows": rows.iter().sum::<usize>(),
    "peak_rss_bytes": aiur::trace::stark::planning::peak_resident_memory(),
  });
  fs::write(dir.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{report}");
  Ok(())
}

fn main() -> R<()> {
  let args: Vec<String> = std::env::args().collect();
  let mode = args.get(1).map(String::as_str).unwrap_or("");
  let rest = &args[2.min(args.len())..];
  match (mode, rest.len()) {
    ("join", 11) => {
      let c = ctx(rest)?;
      let [env_path, manifest, env_root, aiur_root, theorem, binding, node] = &rest[4..] else {
        unreachable!()
      };
      // Names are metadata: only the full decode keeps them.
      let environment = Environment::from_bytes(&fs::read(env_path)?)?;
      let env = environment.env();
      let manifest = ShardManifest::from_bytes(&fs::read(manifest)?)?;
      let context = aggregate_controller::claim_context(env, false)?;
      let prepared = prepare::prepare_run(&context, env, &manifest)?;
      let specs = plan::build_statement_specs(&prepared, 0)?;
      let statement = &specs.last().ok_or("no root statement")?.statement;
      prepare::validate_root_statement(&prepared, statement)?;
      let (env_root, aiur_root) = (Path::new(env_root), Path::new(aiur_root));
      let env_claim = fs::read(env_root.join("ix-claim.bin"))?;
      if env_claim != statement.claim_bytes {
        return Err("the environment root is not this environment's claim".into());
      }
      let addr_of = |name: &str| -> R<ix_common::address::Address> {
        env.named.iter().find(|e| e.key().pretty() == name).map(|e| e.value().addr.clone())
          .ok_or_else(|| format!("no constant named {name}").into())
      };
      let aiur_key = fs::read(aiur_root.join("root-vk.bin"))?;
      let aiur_claims = fs::read(aiur_root.join("root-claims.bin"))?;
      let run = AiurRun::new(statement, &prepared.owner_by_address, &addr_of(theorem)?,
        &addr_of(binding)?, &aiur_key, &aiur_claims)?;
      let env_proof = fs::read(env_root.join("root-proof.bin"))?;
      let env_claims = fs::read(env_root.join("root-claims.bin"))?;
      let aiur_proof = fs::read(aiur_root.join("root-proof.bin"))?;
      let keys = Keys { allowed: &c.allowed, ixvm: &c.ixvm_key, aggr: c.aggr.key() };
      let s = streams::aiur_join(
        keys,
        Transport { kind: ChildKind::Aggr, proof: &env_proof, claims: &env_claims },
        &env_claim,
        &aiur_key,
        &aiur_proof,
        &aiur_claims,
        &run.claim_bytes,
        run.theorem_path.clone(),
        run.binding_path.clone(),
      );
      prove(&c, s.entries(), &run.claim_bytes, Path::new(node), "aiur-join")
    },
    ("wrap", 6) => {
      let c = ctx(rest)?;
      let (child, node) = (Path::new(&rest[4]), Path::new(&rest[5]));
      let out = fs::read(child.join("out.bin"))?;
      let proof = fs::read(child.join("proof.bin"))?;
      let claims = fs::read(child.join("claims.bin"))?;
      let keys = Keys { allowed: &c.allowed, ixvm: &c.ixvm_key, aggr: c.aggr.key() };
      let s = streams::wrap(keys, 1, Transport { kind: ChildKind::Aggr, proof: &proof, claims: &claims });
      prove(&c, s.entries(), &out, node, "wrap")
    },
    ("root", 6) => {
      let c = ctx(rest)?;
      let (node, root) = (Path::new(&rest[4]), Path::new(&rest[5]));
      fs::create_dir_all(root)?;
      fs::write(root.join("root-vk.bin"), c.aggr.key())?;
      fs::copy(node.join("claims.bin"), root.join("root-claims.bin"))?;
      fs::copy(node.join("proof.bin"), root.join("root-proof.bin"))?;
      fs::copy(node.join("out.bin"), root.join("ix-claim.bin"))?;
      fs::write(root.join("backend-allowed.bin"), &c.allowed)?;
      println!("root key {} (aggregate entry {})", blake3::hash(c.aggr.key()).to_hex(), c.aggr_index);
      Ok(())
    },
    _ => Err("usage: aiur_join join|wrap|root ... (see the module docs)".into()),
  }
}
