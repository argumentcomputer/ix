//! Check what an Aiur-join aggregate root claims (`ix_aggr` shapes 17 and
//! 18, an `AiurRun` claim), against everything a verifier recomputes on its
//! own: the IxVM and `ix_aggr` keys from their pinned artifacts, the
//! environment's `CheckEnv` claim from the environment and its partition, the
//! theorem's and binding's addresses from the environment, the run
//! aggregator's and the program's keys from their packages, and the run's
//! endpoints and data root from the specification's arguments and expected
//! output.
//!
//! ```text
//! aiur_join_check IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 ENV.ixe MANIFEST.ixes ROOT_DIR
//!   RUN_AGGR.ixa PROGRAM.ixa RUN_ROOT SPEC_ARGS EXPECTED_OUTPUT COUNT STEPS THEOREM BINDING
//! ```
//!
//! - `ROOT_DIR`: `root-vk.bin` and `root-claims.bin`, the key and claims a
//!   compression certificate binds by BLAKE3, and the claim's preimage
//!   `ix-claim.bin` (the `AiurRun` claim).
//! - `RUN_ROOT`: the Aiur child's claim preimages, `root-claims.bin`,
//!   `allowed.bin` (80-byte identity) and `out.bin` (104-byte run claim).
//! - `SPEC_ARGS`, `EXPECTED_OUTPUT`, `COUNT`, `STEPS`: as `aiur_exec_check`.
//!
//! Prints `PROVED` with the statement and its remaining hypotheses, or
//! `REJECT` with the first failed check.
use aggregate_controller::{plan, prepare, protocol::allowed_blob};
use aiur::{
  artifact::{ExecutionPackage, Package},
  field::FieldBackend,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use ix_common::address::Address;
use ix_prover::{
  aggregate::AGGR_ENTRY,
  request::{Environment, IXVM_ENTRY},
  system::{ProtocolParameters, System},
};
use ixon::{Claim, shard::ShardManifest};
use multi_stark::{p3_field::PrimeField64, types::Val};
use std::{error::Error, fs, path::Path};

const P: i128 = 18446744069414584321;
const MODEL: usize = 331;
const XS: usize = 160;
const TS: usize = 220;

type R<T> = Result<T, Box<dyn Error>>;

fn words(path: &str) -> R<Vec<i128>> {
  Ok(fs::read_to_string(path)?.split_whitespace().map(str::parse).collect::<Result<_, _>>()?)
}

fn enc(values: &[i128]) -> Vec<u8> {
  values.iter().flat_map(|v| (v.rem_euclid(P) as u64).to_le_bytes()).collect()
}

fn h(bytes: &[u8]) -> [u8; 32] {
  *blake3::hash(bytes).as_bytes()
}

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  let mut pre = vec![1u8];
  pre.extend_from_slice(left);
  pre.extend_from_slice(right);
  h(&pre)
}

/// The run aggregation's data root: adjacent nodes joined level by level, an
/// odd last node carried up.
fn data_root(mut level: Vec<[u8; 32]>) -> [u8; 32] {
  while level.len() > 1 {
    let mut next: Vec<_> = level.chunks_exact(2).map(|p| node(&p[0], &p[1])).collect();
    if level.len() % 2 == 1 {
      next.push(*level.last().unwrap());
    }
    level = next;
  }
  level[0]
}

/// The batch verifying key of a program's first entry, and that entry's
/// claim index and length for `arity` argument and `outputs` output words.
fn batch_key(program: aiur::Program, trace: aiur::trace::TraceArtifact, arity: usize,
  outputs: usize) -> R<(Vec<u8>, u64, usize)> {
  let mut program = program.check_field::<Val>()?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(&program, trace)?;
  let backend = Backend::for_batch(&plan, Parameters::default())?;
  let entry = program.program().entries.first().ok_or("no entry")?.name.clone();
  let claim = backend.claim(&entry, &program.field().decode(&vec![0; arity])?,
    &program.field().decode(&vec![0; outputs])?)?;
  Ok((backend.verifying_key_bytes()?, claim[1].as_canonical_u64(), claim.len()))
}

fn pinned_system(path: &str, expected: &str) -> R<System> {
  let pin = blake3::Hash::from_hex(expected)?;
  let (bytes, digest) = aiur::artifact::read(path.as_ref())?;
  if &digest.0 != pin.as_bytes() {
    return Err(format!("artifact differs from its pin: {path}").into());
  }
  let package = Package::decode(&bytes)?;
  let (program, trace) = package.traced()?;
  let program = ix_prover::system::Program::new(program, trace, digest)?;
  Ok(System::prepare(&program, ProtocolParameters::default())?)
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
  haystack.windows(needle.len()).any(|w| w == needle)
}

fn main() {
  match run() {
    Ok(()) => {},
    Err(e) => {
      println!("{e}");
      std::process::exit(1);
    },
  }
}

fn run() -> R<()> {
  let a: Vec<String> = std::env::args().collect();
  let [_, ixvm, ixvm_b3, aggr, aggr_b3, env_path, manifest, root, run_aggr, program, run_root,
    spec, expected, count, steps, theorem, binding] = a.as_slice()
  else {
    return Err("usage: aiur_join_check IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 ENV.ixe MANIFEST.ixes ROOT_DIR RUN_AGGR.ixa PROGRAM.ixa RUN_ROOT SPEC_ARGS EXPECTED_OUTPUT COUNT STEPS THEOREM BINDING".into());
  };
  let (count, steps): (usize, usize) = (count.parse()?, steps.parse()?);
  let (xs_words, ts_words) = (steps * XS, steps * TS);
  let (root, run_root) = (Path::new(root), Path::new(run_root));
  let check = |ok: bool, what: &str| -> R<()> {
    if ok { println!("ok: {what}"); Ok(()) } else { Err(format!("REJECT: {what}").into()) }
  };

  let ixvm_sys = pinned_system(ixvm, ixvm_b3)?;
  let aggr_sys = pinned_system(aggr, aggr_b3)?;
  let ixvm_id = ixvm_sys.identity(IXVM_ENTRY, 8)?;
  let aggr_id = aggr_sys.identity(AGGR_ENTRY, 16)?;
  check(fs::read(root.join("root-vk.bin"))? == aggr_id.key,
    "the certificate's root key is ix_aggr's, recompiled from the pinned artifact")?;
  let allowed = allowed_blob(&ixvm_id.key, ixvm_id.function_index, &aggr_id.key,
    aggr_id.function_index);
  let claims = stark_verifier::compress_wrap::decode_claims(&fs::read(root.join("root-claims.bin"))?)?;
  check(claims.len() == 1 && claims[0].len() == 18, "one 18-word root claim")?;
  let c: Vec<u64> = claims[0].iter().map(|v| v.as_canonical_u64()).collect();
  let out = fs::read(root.join("ix-claim.bin"))?;
  check(c[0] == aggr_id.call_channel && c[1] == aggr_id.function_index,
    "the root claim is a call of MultiStark::ix_aggr")?;
  check(c[2..10] == stark_verifier::digest_words(&allowed)[..],
    "the root claim names IxVM's and ix_aggr's keys and entries")?;
  check(c[10..18] == stark_verifier::digest_words(&out)[..], "ix-claim.bin is the claim's preimage")?;
  let Claim::AiurRun { env: env_digest, root: subject_root, theorem: theorem_addr,
    binding: binding_addr, key, claims: run_claims_digest } = Claim::from_bytes(&out)?
  else {
    return Err("REJECT: the root claim is not an AiurRun claim".into());
  };
  println!("ok: the root claim is an AiurRun claim");

  // Names are metadata: only the full decode keeps them.
  let environment = Environment::from_bytes(&fs::read(env_path)?)?;
  let env = environment.env();
  let manifest = ShardManifest::from_bytes(&fs::read(manifest)?)?;
  let ctx = aggregate_controller::claim_context(env, false)?;
  let prepared = prepare::prepare_run(&ctx, env, &manifest)?;
  let specs = plan::build_statement_specs(&prepared, 0)?;
  let statement = &specs.last().ok_or("no root statement")?.statement;
  prepare::validate_root_statement(&prepared, statement)?;
  let Claim::CheckEnv { root: env_root, assumptions: None, .. } = &statement.claim else {
    return Err("REJECT: the environment's root claim is not an unconditional CheckEnv".into());
  };
  check(env_digest.as_bytes() == &h(&statement.claim_bytes),
    &format!("the environment claim is the CheckEnv of the environment ({} constants, {} shards)",
      prepared.env_count, manifest.shards.len()))?;
  check(subject_root == *env_root, "the subject root is the environment's")?;
  let addr_of = |name: &str| -> R<Address> {
    env.named.iter().find(|e| e.key().pretty() == name).map(|e| e.value().addr.clone())
      .ok_or_else(|| format!("REJECT: no constant named {name}").into())
  };
  check(theorem_addr == addr_of(theorem)? && prepared.owner_by_address.contains_key(&theorem_addr),
    &format!("the theorem is {theorem} ({}), a subject of the environment", theorem_addr.hex()))?;
  check(binding_addr == addr_of(binding)? && prepared.owner_by_address.contains_key(&binding_addr),
    &format!("the binding is {binding} ({}), a subject of the environment", binding_addr.hex()))?;
  // The environment's claim lists its user axioms. The only one a run may rest on is the
  // refinement statement itself, which then is assumed rather than checked.
  let user_axioms = ixon::ClaimContext::user_axioms(env);
  let assumed = user_axioms.contains(&theorem_addr);
  check(user_axioms.iter().all(|a| *a == theorem_addr),
    &format!("the environment has no user axiom other than the theorem ({} user axiom(s))", user_axioms.len()))?;

  let (ax_pkg, _) = Package::load(run_aggr.as_ref())?;
  let (ax_prog, ax_trace) = ax_pkg.traced()?;
  let (ax_key, ax_index, _) = batch_key(ax_prog, ax_trace, 16, 0)?;
  check(key.as_bytes() == &h(&ax_key), "the Aiur child's key is the run aggregator's, recompiled")?;
  let run_claims = fs::read(run_root.join("root-claims.bin"))?;
  check(run_claims_digest.as_bytes() == &h(&run_claims), "root-claims.bin is the Aiur child's claim list")?;
  let rc = stark_verifier::compress_wrap::decode_claims(&run_claims)?;
  check(rc.len() == 1 && rc[0].len() == 18, "the Aiur child exposes one 18-word claim")?;
  let rc: Vec<u64> = rc[0].iter().map(|v| v.as_canonical_u64()).collect();
  let run_id = fs::read(run_root.join("allowed.bin"))?;
  let run_out = fs::read(run_root.join("out.bin"))?;
  check(rc[0] == 1 && rc[1] == ax_index, "the Aiur child's claim is a call of AiurExec::aiur_exec")?;
  check(rc[2..10] == stark_verifier::digest_words(&run_id)[..], "allowed.bin is its identity")?;
  check(rc[10..18] == stark_verifier::digest_words(&run_out)[..], "out.bin is its output claim")?;
  let (step_pkg, _) = ExecutionPackage::load(program.as_ref())?;
  let (step_prog, step_trace) = step_pkg.package.traced()?;
  let (step_key, step_index, step_claim_len) =
    batch_key(step_prog, step_trace, MODEL + xs_words + ts_words + 1, MODEL)?;
  check(step_claim_len == 2 + 2 * MODEL + xs_words + ts_words + 1,
    &format!("the program's claim is model, {steps} batches and the rate, model"))?;
  let mut expected_id = h(&step_key).to_vec();
  expected_id.extend_from_slice(&step_index.to_le_bytes());
  expected_id.extend_from_slice(&h(&ax_key));
  expected_id.extend_from_slice(&ax_index.to_le_bytes());
  check(run_id == expected_id,
    "the run's identity names the program's and the run aggregator's keys and entries, recompiled")?;

  let binding_bytes = env.get_const_bytes(&binding_addr).ok_or("no binding constant")?;
  let key_hex = hex(&h(&step_key));
  let key_blob = env
    .blobs
    .iter()
    .find(|e| e.value().as_slice() == key_hex.as_bytes())
    .map(|e| e.key().clone())
    .ok_or("REJECT: the environment has no blob holding the program key")?;
  check(contains(&binding_bytes, key_blob.as_bytes()),
    "the binding's constant names the program key, as a string literal")?;
  check(contains(&binding_bytes, theorem_addr.as_bytes()), "the binding's constant references the theorem")?;
  let theorem_bytes = env.get_const_bytes(&theorem_addr).ok_or("no theorem constant")?;
  // The addresses let a caller compare these constants with the ones its own job names.
  for name in ["IxAICore.train", "IxAICore.Triage.spec", "IxAIAiur.fullConfig"] {
    let addr = addr_of(name)?;
    check(contains(&theorem_bytes, addr.as_bytes()),
      &format!("the theorem's statement references {name} ({})", addr.hex()))?;
  }

  let spec = words(spec)?;
  check(spec.len() == MODEL + 1 + count * (xs_words + ts_words), "specification arguments have the full config's length")?;
  let (m0, lr) = (&spec[..MODEL], spec[MODEL]);
  let xs = &spec[MODEL + 1..MODEL + 1 + count * xs_words];
  let ts = &spec[MODEL + 1 + count * xs_words..];
  let last = words(expected)?;
  let param = |v: &i128| (-8191..=8191).contains(v);
  let input = |v: &i128| (-4096..=4096).contains(v);
  check(m0.iter().all(param) && last.len() == MODEL && last.iter().all(param), "modelOkB of m0 and of the final model")?;
  check(xs.iter().all(input) && ts.iter().all(input) && lr.abs() <= 256, "BatchOk of every batch, |lr| <= 2^8")?;
  check(run_out.len() == 104 && u64::from_le_bytes(run_out[..8].try_into()?) == count as u64,
    &format!("the chain has {count} executions"))?;
  check(run_out[8..40] == h(&enc(m0)), "the chain starts at m0")?;
  check(run_out[40..72] == h(&enc(&last)), "the chain ends at the expected model")?;
  let leaves: Vec<[u8; 32]> = (0..count)
    .map(|i| {
      let (x, t) = (&xs[i * xs_words..(i + 1) * xs_words], &ts[i * ts_words..(i + 1) * ts_words]);
      let d = if steps == 1 { [x, t, &[lr]].concat() } else { [&[lr], x, t].concat() };
      h(&enc(&d))
    })
    .collect();
  check(run_out[72..104] == data_root(leaves), "execution i used its batches and lr, for every i")?;
  println!(
    "PROVED (under the hypotheses below): environment claim {} (subject root {}) holds and \
     contains {theorem} and {binding}; the program with key {key_hex} ran {count} chained \
     executions from m0 to the model with BLAKE3 {}, which {theorem} and eq_of_encModel_eq make \
     IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig.",
    env_digest.hex(), subject_root.hex(), hex(&h(&enc(&last))));
  if assumed {
    println!("assumed: {theorem} ({}) is an axiom of this environment, listed in its claim; \
       the certificate does not check a proof of it.", theorem_addr.hex());
  }
  println!("hypotheses: STARK acceptance implies memo-checker acceptance (Ix's Audit boundary); \
     the program key compiles the deployed preparation (BlockOnlyParity, checked by #eval); \
     soundness of ix_aggr (including shapes 17/18) and of AiurExec; the claim encoding enc, \
     checked here rather than in Lean.");
  Ok(())
}
