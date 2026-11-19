//! Check what an `aiur_exec` root claims, against a specification supplied by
//! the verifier: that it covers `count` chained executions of the program's
//! entry from the model `m₀` to `mₙ` over the given data, in order.
//!
//! ```text
//! aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED_OUTPUT COUNT
//! ```
//!
//! - `ROOT_DIR`: `root-vk.bin` and `root-claims.bin`, the key and claims a
//!   compression certificate binds by BLAKE3, and the preimages it needs:
//!   `allowed.bin` (identity blob) and `out.bin` (output claim).
//! - `SPEC_ARGS`: signed integers `m₀ (331) ‖ lr ‖ xs (count·160) ‖ ts (count·220)`,
//!   as `Fixed::train` takes them; `EXPECTED_OUTPUT`: `mₙ` (331).
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
  let [_, ax, program, root, spec, expected, count] = a.as_slice() else {
    return Err("usage: aiur_exec_check AX.ixa PROGRAM.ixa ROOT_DIR SPEC_ARGS EXPECTED_OUTPUT COUNT".into());
  };
  let count: usize = count.parse()?;
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
  let (step_key, step_index, step_claim_len) = batch_key(step_prog, step_trace, MODEL + XS + TS + 1, MODEL)?;
  check(step_claim_len == 2 + 2 * MODEL + XS + TS + 1, "the program's claim is model, batch, rate, model")?;

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
  check(spec.len() == MODEL + 1 + count * (XS + TS), "specification arguments have the full config's length")?;
  let (m0, lr) = (&spec[..MODEL], spec[MODEL]);
  let xs = &spec[MODEL + 1..MODEL + 1 + count * XS];
  let ts = &spec[MODEL + 1 + count * XS..];
  let last = words(expected)?;
  let param = |v: &i128| (-8191..=8191).contains(v);
  let input = |v: &i128| (-4096..=4096).contains(v);
  check(m0.iter().all(param) && last.len() == MODEL && last.iter().all(param), "modelOkB of m0 and of the final model")?;
  check(xs.iter().all(input) && ts.iter().all(input) && lr.abs() <= 256, "BatchOk of every batch, |lr| <= 2^8")?;

  check(out.len() == 104, "output claim is 104 bytes")?;
  check(u64::from_le_bytes(out[..8].try_into()?) == count as u64, &format!("the chain has {count} executions"))?;
  check(out[8..40] == h(&enc(m0)), "the chain starts at m0")?;
  check(out[40..72] == h(&enc(&last)), "the chain ends at the expected model")?;
  let leaves: Vec<[u8; 32]> = (0..count)
    .map(|i| {
      let mut d = xs[i * XS..(i + 1) * XS].to_vec();
      d.extend_from_slice(&ts[i * TS..(i + 1) * TS]);
      d.push(lr);
      h(&enc(&d))
    })
    .collect();
  check(out[72..104] == data_root(leaves), "execution i used batch i and lr, for every i")?;
  println!("ACCEPT: {count} chained executions of the program (key {}) from m0 to the expected model",
    blake3::Hash::from(h(&step_key)).to_hex());
  Ok(())
}
