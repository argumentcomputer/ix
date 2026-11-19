//! Check what an `aiur_exec` root claims, against a specification supplied by
//! the verifier: that it covers `count` chained executions of the program's
//! entry from the model `m₀` to `mₙ` over the given data, in order, each
//! execution `steps` SGD steps (1 for `Fixed::step`, 20 for
//! `Fixed::train_block`).
//!
//! ```text
//! aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED_OUTPUT COUNT [STEPS]
//! aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED_OUTPUT 1 STEPS --tree MODELS
//! ```
//!
//! - `ROOT_DIR`: `root-vk.bin` and `root-claims.bin`, the key and claims a
//!   compression certificate binds by BLAKE3, and the preimages it needs:
//!   `allowed.bin` (identity blob) and `out.bin` (output claim).
//! - `SPEC_ARGS`: signed integers `m₀ (331) ‖ lr ‖ xs (count·steps·160) ‖
//!   ts (count·steps·220)`, as `Fixed::train` takes them; `EXPECTED_OUTPUT`:
//!   `mₙ` (331).
//! - An execution's data is `xs ‖ ts ‖ lr` for one step (`Fixed::step`'s
//!   arguments) and `lr ‖ xs ‖ ts` for several (`Fixed::train_block`'s).
//!
//! - With `--tree`, the program is `FixedTree::train_tree`: one execution of
//!   all `STEPS` steps, whose claim is `m₀ ‖ lr → root ‖ mₙ` and whose data is
//!   `lr ‖ root`. `root` is the BLAKE3 Merkle tree over the steps that
//!   `IxAITree.lean` describes (leaf `i`: the model after step `i`, then batch
//!   `i`, each word as the two little-endian bytes of `v + 32768`; a node over
//!   `n` steps splits them `⌊n/2⌋ | ⌈n/2⌉`). `MODELS` lists the model after
//!   each step, one line per step, as the specification computes them; the
//!   root binds them along with every batch.
//!
//! Every key is recomputed from its program: the aggregator's must be the
//! certificate's root key, and the identity blob must name the program's.
use aiur::{
  artifact::{ExecutionPackage, Package},
  field::FieldBackend,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
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

/// Words as `FixedTree` hashes them: the two little-endian bytes of `v + 32768`.
fn enc16(values: &[i128]) -> R<Vec<u8>> {
  let mut out = Vec::with_capacity(2 * values.len());
  for v in values {
    let u = u16::try_from(v + 32768).map_err(|_| format!("word {v} outside 16 bits"))?;
    out.extend_from_slice(&u.to_le_bytes());
  }
  Ok(out)
}

/// `FixedTree::range`'s root over `leaves`: the first `⌊n/2⌋` and the rest, joined by
/// BLAKE3 of the two 32-byte children.
fn tree_root(leaves: &[[u8; 32]]) -> [u8; 32] {
  if leaves.len() == 1 {
    return leaves[0];
  }
  let (l, r) = leaves.split_at(leaves.len() / 2);
  h(&[tree_root(l), tree_root(r)].concat())
}

fn h(bytes: &[u8]) -> [u8; 32] {
  *blake3::hash(bytes).as_bytes()
}

fn node(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  let mut pre = vec![1u8];
  pre.extend_from_slice(left);
  pre.extend_from_slice(right);
  h(&pre)
}

/// The aggregation's data root: adjacent nodes joined level by level, an odd
/// last node carried up.
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

/// The batch verifying key of a program's first entry, and that entry's claim
/// index and claim length for `arity` argument and `outputs` output words.
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

fn main() -> R<()> {
  let a: Vec<String> = std::env::args().collect();
  let (a, tree_models) = match a.iter().position(|x| x == "--tree") {
    Some(i) if i + 2 == a.len() => (a[..i].to_vec(), Some(a[i + 1].clone())),
    Some(_) => return Err("--tree MODELS must come last".into()),
    None => (a, None),
  };
  let tree = tree_models.is_some();
  let (ax, program, root, spec, expected, count, steps) = match a.as_slice() {
    [_, ax, program, root, spec, expected, count] => (ax, program, root, spec, expected, count, 1),
    [_, ax, program, root, spec, expected, count, steps] => {
      (ax, program, root, spec, expected, count, steps.parse::<usize>()?)
    },
    _ => {
      return Err("usage: aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED_OUTPUT COUNT [STEPS]".into());
    },
  };
  let count: usize = count.parse()?;
  if steps == 0 {
    return Err("STEPS must be positive".into());
  }
  let (xs_words, ts_words) = (steps * XS, steps * TS);
  let root = Path::new(root);
  let check = |ok: bool, what: &str| -> R<()> {
    if ok { println!("ok: {what}"); Ok(()) } else { Err(format!("REJECT: {what}").into()) }
  };

  let (ax_pkg, _) = Package::load(ax.as_ref())?;
  let (ax_prog, ax_trace) = ax_pkg.traced()?;
  let (ax_key, ax_index, _) = batch_key(ax_prog, ax_trace, 16, 0)?;
  let root_key = fs::read(root.join("root-vk.bin"))?;
  check(ax_key == root_key, "the certificate's root key is the aggregator's, recompiled")?;

  let (step_pkg, _) = ExecutionPackage::load(program.as_ref())?;
  let (step_prog, step_trace) = step_pkg.package.traced()?;
  let (step_key, step_index, step_claim_len) = if tree {
    batch_key(step_prog, step_trace, MODEL + 1, 32 + MODEL)?
  } else {
    batch_key(step_prog, step_trace, MODEL + xs_words + ts_words + 1, MODEL)?
  };
  if tree {
    check(count == 1 && step_claim_len == 2 + MODEL + 1 + 32 + MODEL,
      &format!("one execution; the program's claim is model and the rate, root and model"))?;
  } else {
    check(step_claim_len == 2 + 2 * MODEL + xs_words + ts_words + 1,
      &format!("the program's claim is model, {steps} batches and the rate, model"))?;
  }

  let claims = stark_verifier::compress_wrap::decode_claims(&fs::read(root.join("root-claims.bin"))?)?;
  check(claims.len() == 1 && claims[0].len() == 18, "one 18-word root claim")?;
  let c: Vec<u64> = claims[0].iter().map(|v| v.as_canonical_u64()).collect();
  let allowed = fs::read(root.join("allowed.bin"))?;
  let out = fs::read(root.join("out.bin"))?;
  check(c[0] == 1 && c[1] == ax_index, "the root claim is a call of AiurExec::aiur_exec")?;
  check(c[2..10] == stark_verifier::digest_words(&allowed)[..], "identity blob matches the claim")?;
  check(c[10..18] == stark_verifier::digest_words(&out)[..], "output claim matches the claim")?;

  check(allowed.len() == 80, "identity blob is 80 bytes")?;
  check(allowed[..32] == h(&step_key), "the identity names the program's key, recompiled")?;
  check(u64::from_le_bytes(allowed[32..40].try_into()?) == step_index, "the identity names the program's entry")?;
  check(allowed[40..72] == h(&ax_key), "the identity names the aggregator's own key")?;
  check(u64::from_le_bytes(allowed[72..80].try_into()?) == ax_index, "the identity names the aggregator's entry")?;

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

  check(out.len() == 104, "output claim is 104 bytes")?;
  check(u64::from_le_bytes(out[..8].try_into()?) == count as u64, &format!("the chain has {count} executions"))?;
  check(out[8..40] == h(&enc(m0)), "the chain starts at m0")?;
  check(out[40..72] == h(&enc(&last)), "the chain ends at the expected model")?;
  if let Some(models) = tree_models {
    let models: Vec<Vec<i128>> = fs::read_to_string(models)?
      .lines()
      .map(|l| l.split_whitespace().map(str::parse).collect::<Result<_, _>>())
      .collect::<Result<_, _>>()?;
    check(models.len() == steps && models.iter().all(|m| m.len() == MODEL && m.iter().all(param)),
      &format!("{steps} intermediate models"))?;
    check(models[steps - 1] == last, "the last intermediate model is the expected model")?;
    let (xs1, ts1) = (XS, TS);
    let mut leaves = Vec::with_capacity(steps);
    for (i, m) in models.iter().enumerate() {
      let (x, t) = (&xs[i * xs1..(i + 1) * xs1], &ts[i * ts1..(i + 1) * ts1]);
      leaves.push(h(&[enc16(m)?, enc16(x)?, enc16(t)?].concat()));
    }
    let merkle = tree_root(&leaves);
    let data: Vec<i128> = std::iter::once(lr).chain(merkle.iter().map(|&b| b as i128)).collect();
    check(out[72..104] == h(&enc(&data)),
      "the execution used lr, every batch in order and every intermediate model (Merkle root)")?;
    println!("Merkle root {}", blake3::Hash::from(merkle).to_hex());
    println!("ACCEPT: one execution of the program (key {}), {steps} steps from m0 to the expected model",
      blake3::Hash::from(h(&step_key)).to_hex());
    return Ok(());
  }
  let leaves: Vec<[u8; 32]> = (0..count)
    .map(|i| {
      let (x, t) = (&xs[i * xs_words..(i + 1) * xs_words], &ts[i * ts_words..(i + 1) * ts_words]);
      let d = if steps == 1 { [x, t, &[lr]].concat() } else { [&[lr], x, t].concat() };
      h(&enc(&d))
    })
    .collect();
  check(out[72..104] == data_root(leaves), "execution i used its batches and lr, for every i")?;
  println!("ACCEPT: {count} chained executions of the program (key {}) from m0 to the expected model",
    blake3::Hash::from(h(&step_key)).to_hex());
  Ok(())
}
