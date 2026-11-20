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
//!
//! Options after the positional arguments, each adding `ok:` lines (or a
//! `REJECT`) after the run's checks and before `PROVED`:
//!
//! - `--model-constant NAME`: `NAME` is a subject of the environment and its
//!   value is a model literal whose decoding (see [`decode_model`]) encodes,
//!   word for word, as `EXPECTED_OUTPUT` does; so the run ends at that
//!   constant's model.
//! - `--contains NAME` (repeatable): `NAME` is a subject of the environment;
//!   its address is printed.
//!
//! Without options the output is that of the positional form alone.
//!
//! The model-literal check also runs alone, against an environment with no
//! partition or certificate:
//!
//! ```text
//! aiur_join_check model-constant ENV.ixe NAME EXPECTED_OUTPUT
//! ```
//!
//! It prints `ok: NAME (ADDRESS) is the expected model: N words`, or
//! `REJECT` with the reason or the first differing position, and exits
//! non-zero.
use aggregate_controller::{plan, prepare, protocol::allowed_blob};
use aiur::{
  artifact::{ExecutionPackage, Package},
  field::FieldBackend,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use ix_common::{address::Address, env::DefinitionSafety, prim_addrs::PrimAddrs};
use ix_prover::{
  aggregate::AGGR_ENTRY,
  request::{Environment, IXVM_ENTRY},
  system::{ProtocolParameters, System},
};
use ixon::{Claim, Constant, ConstantInfo, DefKind, Env, Expr, MutConst, Univ, shard::ShardManifest};
use multi_stark::{p3_field::PrimeField64, types::Val};
use std::{error::Error, fs, path::Path, sync::Arc};

const P: i128 = 18446744069414584321;
const MODEL: usize = 331;
const XS: usize = 160;
const TS: usize = 220;
/// The deployed model's shape: `w1` is `HIDDEN` rows of `INPUTS`, `b1` has
/// `HIDDEN` entries, `w2` is `OUTPUTS` rows of `HIDDEN`, `b2` has `OUTPUTS`.
const INPUTS: usize = 8;
const HIDDEN: usize = 16;
const OUTPUTS: usize = 11;
const _: () = assert!(HIDDEN * INPUTS + HIDDEN + OUTPUTS * HIDDEN + OUTPUTS == MODEL);
/// The largest magnitude of a decoded integer: on `[-BOUND, BOUND]` the field
/// encoding `v mod p` is injective, so equal words mean equal integers.
const BOUND: i128 = (P - 1) / 2;
/// The most application nodes and list cells a literal may have; a bound on
/// work, far above a model's size.
const FUEL: usize = 1 << 20;

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

fn reject<T>(why: String) -> R<T> {
  Err(format!("REJECT: {why}").into())
}

/// The address of the one constant whose name prints as `name`.
fn unique_address(env: &Env, name: &str) -> R<Address> {
  let mut found =
    env.named.iter().filter(|e| e.key().pretty() == name).map(|e| e.value().addr.clone());
  match (found.next(), found.next()) {
    (Some(addr), None) => Ok(addr),
    (None, _) => reject(format!("no constant named {name}")),
    _ => reject(format!("more than one constant is named {name}")),
  }
}

/// The constant stored at `addr`, whose bytes must hash to `addr`.
fn stored(env: &Env, addr: &Address) -> R<Arc<Constant>> {
  let bytes = env.get_const_bytes(addr).ok_or_else(|| format!("REJECT: no constant at {}", addr.hex()))?;
  if Address::hash(&bytes) != *addr {
    return reject(format!("the constant at {} does not hash to its address", addr.hex()));
  }
  Ok(env.try_get_const(addr).ok_or("constant vanished")??)
}

/// The constructors and types a model literal is built from, each resolved
/// from its name and checked against the environment's own inductive blocks.
#[derive(Clone, Debug)]
struct ModelCtors {
  int_of_nat: Address,
  int_neg_succ: Address,
  list: Address,
  list_nil: Address,
  list_cons: Address,
  fx: Address,
  fx_mk: Address,
  model: Address,
  model_mk: Address,
}

/// The address of the constructor named `name`, after checking that it is
/// constructor number `cidx` of the inductive at `ty`, with `params`
/// parameters, `fields` fields and `lvls` universe parameters.
fn constructor(env: &Env, ty: &Address, name: &str, cidx: u64, params: u64, fields: u64, lvls: u64)
  -> R<Address> {
  let addr = unique_address(env, name)?;
  let (ty_const, ctor_const) = (stored(env, ty)?, stored(env, &addr)?);
  let (ConstantInfo::IPrj(ind), ConstantInfo::CPrj(ctor)) = (&ty_const.info, &ctor_const.info) else {
    return reject(format!("{name} is not a constructor of an inductive type"));
  };
  let block = stored(env, &ind.block)?;
  let ConstantInfo::Muts(members) = &block.info else {
    return reject(format!("the block of {name}'s type is not a mutual block"));
  };
  let Some(MutConst::Indc(inductive)) = usize::try_from(ind.idx).ok().and_then(|i| members.get(i))
  else {
    return reject(format!("the type of {name} is not an inductive of its block"));
  };
  let shape = usize::try_from(cidx).ok().and_then(|i| inductive.ctors.get(i));
  let ok = ctor.block == ind.block && ctor.idx == ind.idx && ctor.cidx == cidx
    && shape.is_some_and(|c| c.cidx == cidx && c.params == params && c.fields == fields && c.lvls == lvls)
    && inductive.lvls == lvls && inductive.indices == 0;
  if !ok {
    return reject(format!("{name} is not constructor {cidx} ({params} parameters, {fields} fields) of its type"));
  }
  Ok(addr)
}

impl ModelCtors {
  /// Resolves the constructors by name and checks each one's place in its
  /// inductive block.
  fn resolve(env: &Env) -> R<Self> {
    let int = unique_address(env, "Int")?;
    let list = unique_address(env, "List")?;
    let fx = unique_address(env, "IxAICore.Fx")?;
    let model = unique_address(env, "IxAICore.Model")?;
    Ok(ModelCtors {
      int_of_nat: constructor(env, &int, "Int.ofNat", 0, 0, 1, 0)?,
      int_neg_succ: constructor(env, &int, "Int.negSucc", 1, 0, 1, 0)?,
      list_nil: constructor(env, &list, "List.nil", 0, 1, 0, 1)?,
      list_cons: constructor(env, &list, "List.cons", 1, 1, 2, 1)?,
      fx_mk: constructor(env, &fx, "IxAICore.Fx.mk", 0, 0, 1, 0)?,
      model_mk: constructor(env, &model, "IxAICore.Model.mk", 0, 0, 4, 0)?,
      list,
      fx,
      model,
    })
  }

  /// `Int` and `List` are Lean's own: their addresses must be the pinned
  /// primitive addresses, so the names cannot point at look-alike types.
  fn check_pinned(&self) -> R<()> {
    let p = PrimAddrs::new();
    if self.int_of_nat != p.int_of_nat || self.int_neg_succ != p.int_neg_succ || self.list != p.list
      || self.list_nil != p.list_nil || self.list_cons != p.list_cons {
      return reject("Int.ofNat, Int.negSucc, List, List.nil or List.cons is not at its pinned primitive address".into());
    }
    Ok(())
  }
}

/// Reads one definition's value as a model literal, using that constant's
/// tables (or, for a member of a mutual block, the block's).
struct Literal<'a> {
  env: &'a Env,
  tables: &'a Constant,
  ctors: &'a ModelCtors,
  name: &'a str,
}

impl<'a> Literal<'a> {
  fn bad<T>(&self, what: &str) -> R<T> {
    reject(format!("{} is not a model literal: {what}", self.name))
  }

  fn unshare(&self, mut e: &'a Expr) -> R<&'a Expr> {
    for _ in 0..=self.tables.sharing.len() {
      let Expr::Share(i) = e else { return Ok(e) };
      match usize::try_from(*i).ok().and_then(|i| self.tables.sharing.get(i)) {
        Some(next) => e = next,
        None => return self.bad("a shared subterm is out of range"),
      }
    }
    self.bad("a cycle of shared subterms")
  }

  fn reference(&self, i: u64) -> R<&'a Address> {
    match usize::try_from(i).ok().and_then(|i| self.tables.refs.get(i)) {
      Some(addr) => Ok(addr),
      None => self.bad("a reference is out of range"),
    }
  }

  /// The arguments of `e` when it is `head` applied to exactly `args`
  /// arguments, with `univs` universe arguments, each universe zero.
  fn apply(&self, e: &'a Expr, head: &Address, univs: usize, args: usize) -> R<Vec<&'a Expr>> {
    let mut e = self.unshare(e)?;
    let mut out = Vec::new();
    while let Expr::App(f, a) = e {
      if out.len() == FUEL {
        return self.bad("an application is too long");
      }
      out.push(a.as_ref());
      e = self.unshare(f)?;
    }
    out.reverse();
    let Expr::Ref(i, us) = e else { return self.bad("a subterm's head is not a constant") };
    if self.reference(*i)? != head || us.len() != univs || out.len() != args {
      return self.bad("a subterm is not the expected constructor or type, fully applied");
    }
    for u in us {
      match usize::try_from(*u).ok().and_then(|u| self.tables.univs.get(u)) {
        Some(u) if matches!(u.as_ref(), Univ::Zero) => {},
        _ => return self.bad("a universe argument is not zero"),
      }
    }
    Ok(out)
  }

  /// `IxAICore.Fx` when `nested` is false, `List IxAICore.Fx` when true.
  fn element_type(&self, e: &'a Expr, nested: bool) -> R<()> {
    if nested {
      let args = self.apply(e, &self.ctors.list, 1, 1)?;
      self.element_type(args[0], false)
    } else {
      self.apply(e, &self.ctors.fx, 0, 0).map(drop)
    }
  }

  /// A list literal `@List.cons T x (... (@List.nil T))` of the given
  /// element type, its elements decoded by `item`.
  fn list<T>(&self, mut e: &'a Expr, nested: bool, item: impl Fn(&'a Expr) -> R<T>) -> R<Vec<T>> {
    let mut out = Vec::new();
    loop {
      if out.len() == FUEL {
        return self.bad("a list is too long");
      }
      if let Ok(args) = self.apply(e, &self.ctors.list_cons, 1, 3) {
        self.element_type(args[0], nested)?;
        out.push(item(args[1])?);
        e = args[2];
      } else {
        let args = self.apply(e, &self.ctors.list_nil, 1, 1)?;
        self.element_type(args[0], nested)?;
        return Ok(out);
      }
    }
  }

  /// `Int.ofNat (nat_lit n)` or `Int.negSucc (nat_lit n)`, within
  /// `[-BOUND, BOUND]`.
  fn int(&self, e: &'a Expr) -> R<i128> {
    let (negative, args) = match self.apply(e, &self.ctors.int_of_nat, 0, 1) {
      Ok(args) => (false, args),
      Err(_) => (true, self.apply(e, &self.ctors.int_neg_succ, 0, 1)?),
    };
    let Expr::Nat(i) = self.unshare(args[0])? else {
      return self.bad("an integer's argument is not a natural number literal");
    };
    let blob_addr = self.reference(*i)?;
    let Some(blob) = self.env.get_blob(blob_addr) else {
      return self.bad("a natural number literal's blob is missing");
    };
    if Address::hash(&blob) != *blob_addr {
      return self.bad("a natural number literal's blob does not hash to its address");
    }
    let digits = blob.iter().rposition(|b| *b != 0).map_or(0, |last| last + 1);
    if digits > 8 {
      return self.bad("an integer literal is out of range");
    }
    let n = blob[..digits].iter().rev().fold(0i128, |n, b| (n << 8) | i128::from(*b));
    let v = if negative { -n - 1 } else { n };
    if v.abs() > BOUND {
      return self.bad("an integer literal is out of range");
    }
    Ok(v)
  }

  fn fx(&self, e: &'a Expr) -> R<i128> {
    let args = self.apply(e, &self.ctors.fx_mk, 0, 1)?;
    self.int(args[0])
  }

  fn vector(&self, e: &'a Expr) -> R<Vec<i128>> {
    self.list(e, false, |x| self.fx(x))
  }

  fn matrix(&self, e: &'a Expr) -> R<Vec<Vec<i128>>> {
    self.list(e, true, |row| self.vector(row))
  }
}

/// Decodes the definition named `name` as a model literal,
/// `IxAICore.Model.mk w1 b1 w2 b2` of list literals of
/// `IxAICore.Fx.mk (Int.ofNat (nat_lit n))` or `... (Int.negSucc (nat_lit n))`,
/// into its integers in the order of the model's field encoding: `w1` row by
/// row, `b1`, `w2` row by row, `b2`. Rejects anything else: a constant that
/// is not a safe, universe-monomorphic definition of type `IxAICore.Model`, a
/// head other than those constructors (so no variable, no other constant, no
/// unevaluated function), a literal outside `[-BOUND, BOUND]`, and a shape
/// other than the deployed model's.
fn decode_model(env: &Env, ctors: &ModelCtors, name: &str) -> R<(Address, Vec<i128>)> {
  let addr = unique_address(env, name)?;
  let constant = stored(env, &addr)?;
  let (tables, definition) = match &constant.info {
    ConstantInfo::Defn(d) => (constant.clone(), d.clone()),
    ConstantInfo::DPrj(p) => {
      let block = stored(env, &p.block)?;
      let Some(MutConst::Defn(d)) = usize::try_from(p.idx).ok().and_then(|i| match &block.info {
        ConstantInfo::Muts(members) => members.get(i),
        _ => None,
      }) else {
        return reject(format!("{name} is not a definition of its block"));
      };
      let d = d.clone();
      (block, d)
    },
    _ => return reject(format!("{name} ({}) is not a definition", addr.hex())),
  };
  let literal = Literal { env, tables: &tables, ctors, name };
  if definition.kind != DefKind::Definition || definition.safety != DefinitionSafety::Safe
    || definition.lvls != 0 {
    return literal.bad("not a safe definition without universe parameters");
  }
  literal.apply(&definition.typ, &ctors.model, 0, 0)?;
  let fields = literal.apply(&definition.value, &ctors.model_mk, 0, 4)?;
  let (w1, b1) = (literal.matrix(fields[0])?, literal.vector(fields[1])?);
  let (w2, b2) = (literal.matrix(fields[2])?, literal.vector(fields[3])?);
  let shaped = w1.len() == HIDDEN && w1.iter().all(|r| r.len() == INPUTS) && b1.len() == HIDDEN
    && w2.len() == OUTPUTS && w2.iter().all(|r| r.len() == HIDDEN) && b2.len() == OUTPUTS;
  if !shaped {
    return literal.bad(&format!("its shape is not {HIDDEN}x{INPUTS}, {HIDDEN}, {OUTPUTS}x{HIDDEN}, {OUTPUTS}"));
  }
  Ok((addr, [w1.concat(), b1, w2.concat(), b2].concat()))
}

/// Checks that `name` decodes to a model whose field encoding is that of
/// `expected`, word for word; the success line's text.
fn check_model(env: &Env, ctors: &ModelCtors, name: &str, expected: &[i128]) -> R<(Address, String)> {
  let (addr, model) = decode_model(env, ctors, name)?;
  let (words, want) = (enc(&model), enc(expected));
  if let Some(i) = (0..model.len().min(expected.len())).find(|&i| words[8 * i..8 * i + 8] != want[8 * i..8 * i + 8]) {
    return reject(format!("{name} differs from the expected model at word {i}: {} against {}", model[i], expected[i]));
  }
  if model.len() != expected.len() {
    return reject(format!("{name} has {} words, the expected model {}", model.len(), expected.len()));
  }
  Ok((addr.clone(), format!("{name} ({}) is the expected model: {} words", addr.hex(), model.len())))
}

fn model_constant(args: &[String]) -> R<()> {
  let [env_path, name, expected] = args else {
    return Err("usage: aiur_join_check model-constant ENV.ixe NAME EXPECTED_OUTPUT".into());
  };
  let expected = words(expected)?;
  let environment = Environment::from_bytes(&fs::read(env_path)?)?;
  let env = environment.env();
  let ctors = ModelCtors::resolve(env)?;
  ctors.check_pinned()?;
  let (_, line) = check_model(env, &ctors, name, &expected)?;
  println!("ok: {line}");
  Ok(())
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

/// The options after the join check's positional arguments.
#[derive(Debug, Default, PartialEq)]
struct Options {
  model_constant: Option<String>,
  contains: Vec<String>,
}

fn options(args: &[String]) -> R<Options> {
  let mut out = Options::default();
  let mut args = args.iter();
  while let Some(flag) = args.next() {
    let value = args.next().ok_or_else(|| format!("{flag} needs a constant name"))?.clone();
    match flag.as_str() {
      "--model-constant" if out.model_constant.is_none() => out.model_constant = Some(value),
      "--model-constant" => return Err("--model-constant is given more than once".into()),
      "--contains" => out.contains.push(value),
      _ => return Err(format!("unknown option {flag}").into()),
    }
  }
  Ok(out)
}

fn run() -> R<()> {
  let a: Vec<String> = std::env::args().collect();
  if a.get(1).map(String::as_str) == Some("model-constant") {
    return model_constant(&a[2..]);
  }
  const USAGE: &str = "usage: aiur_join_check IXVM.ixa IXVM_B3 AGGR.ixa AGGR_B3 ENV.ixe MANIFEST.ixes ROOT_DIR RUN_AGGR.ixa PROGRAM.ixa RUN_ROOT SPEC_ARGS EXPECTED_OUTPUT COUNT STEPS THEOREM BINDING [--model-constant NAME] [--contains NAME]...\n       aiur_join_check model-constant ENV.ixe NAME EXPECTED_OUTPUT";
  let (Some(positional), Some(rest)) = (a.get(..17), a.get(17..)) else { return Err(USAGE.into()) };
  let [_, ixvm, ixvm_b3, aggr, aggr_b3, env_path, manifest, root, run_aggr, program, run_root,
    spec, expected, count, steps, theorem, binding] = positional
  else {
    return Err(USAGE.into());
  };
  let opts = options(rest)?;
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
  let mut also = String::new();
  if let Some(name) = &opts.model_constant {
    let ctors = ModelCtors::resolve(env)?;
    ctors.check_pinned()?;
    let (addr, line) = check_model(env, &ctors, name, &last)?;
    check(prepared.owner_by_address.contains_key(&addr),
      &format!("{line}, a subject of the environment"))?;
    also = format!("; the environment's {name} is that model");
  }
  for name in &opts.contains {
    let addr = unique_address(env, name)?;
    check(prepared.owner_by_address.contains_key(&addr),
      &format!("{name} ({}) is a subject of the environment", addr.hex()))?;
  }
  println!(
    "PROVED (under the hypotheses below): environment claim {} (subject root {}) holds and \
     contains {theorem} and {binding}; the program with key {key_hex} ran {count} chained \
     executions from m0 to the model with BLAKE3 {}, which {theorem} and eq_of_encModel_eq make \
     IxAICore.train IxAICore.Triage.spec IxAIAiur.fullConfig{also}.",
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

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::Name;
  use ixon::{Constructor, ConstructorProj, Definition, DefinitionProj, Inductive, InductiveProj};

  fn name(s: &str) -> Name {
    s.split('.').fold(Name::anon(), |n, part| Name::str(n, part.into()))
  }

  fn store(env: &Env, c: Constant) -> Address {
    let mut bytes = Vec::new();
    c.put(&mut bytes);
    let addr = Address::hash(&bytes);
    env.store_const_lazy(addr.clone(), bytes.into());
    addr
  }

  fn plain(info: ConstantInfo) -> Constant {
    Constant { info, sharing: vec![], refs: vec![], univs: vec![Arc::new(Univ::Zero)] }
  }

  fn register(env: &Env, n: &str, addr: &Address) {
    env.register_name(name(n), ixon::Named::with_addr(addr.clone()));
  }

  /// An inductive `ty` with constructors `(name, fields)`, its parameters
  /// and universe parameters both `lvls`.
  fn inductive(env: &Env, ty: &str, lvls: u64, ctors: &[(&str, u64)]) {
    let ctor = |cidx: usize, fields: u64| Constructor {
      is_unsafe: false, lvls, cidx: cidx as u64, params: lvls, fields, typ: Expr::sort(0),
    };
    let block = store(env, plain(ConstantInfo::Muts(vec![MutConst::Indc(Inductive {
      is_unsafe: false, lvls, params: lvls, indices: 0, typ: Expr::sort(0),
      ctors: ctors.iter().enumerate().map(|(i, (_, f))| ctor(i, *f)).collect(),
    })])));
    let ty_addr = store(env, plain(ConstantInfo::IPrj(InductiveProj { idx: 0, block: block.clone() })));
    register(env, ty, &ty_addr);
    for (cidx, (n, _)) in ctors.iter().enumerate() {
      let addr = store(env, plain(ConstantInfo::CPrj(ConstructorProj {
        idx: 0, cidx: cidx as u64, block: block.clone(),
      })));
      register(env, n, &addr);
    }
  }

  fn fixture() -> Env {
    let env = Env::new();
    inductive(&env, "Int", 0, &[("Int.ofNat", 1), ("Int.negSucc", 1)]);
    inductive(&env, "List", 1, &[("List.nil", 0), ("List.cons", 2)]);
    inductive(&env, "IxAICore.Fx", 0, &[("IxAICore.Fx.mk", 1)]);
    inductive(&env, "IxAICore.Model", 0, &[("IxAICore.Model.mk", 4)]);
    env
  }

  const MODEL_T: u64 = 0;
  const MODEL_MK: u64 = 1;
  const CONS: u64 = 2;
  const NIL: u64 = 3;
  const LIST: u64 = 4;
  const FX: u64 = 5;
  const FX_MK: u64 = 6;
  const OF_NAT: u64 = 7;
  const NEG_SUCC: u64 = 8;

  /// Builds a model literal's tables and value; `leaf` may replace the
  /// integer term of a given position.
  struct Builder<'e> {
    env: &'e Env,
    refs: Vec<Address>,
    shared: bool,
    leaf: Option<(usize, Arc<Expr>)>,
    position: usize,
  }

  impl<'e> Builder<'e> {
    fn new(env: &'e Env) -> Self {
      let refs = ["IxAICore.Model", "IxAICore.Model.mk", "List.cons", "List.nil", "List", "IxAICore.Fx",
        "IxAICore.Fx.mk", "Int.ofNat", "Int.negSucc"]
        .iter()
        .map(|n| unique_address(env, n).unwrap())
        .collect();
      Builder { env, refs, shared: false, leaf: None, position: 0 }
    }

    fn nat_bytes(&mut self, bytes: Vec<u8>) -> Arc<Expr> {
      self.refs.push(self.env.store_blob(bytes));
      Expr::nat(self.refs.len() as u64 - 1)
    }

    fn int(&mut self, v: i128) -> Arc<Expr> {
      let (ctor, n) = if v >= 0 { (OF_NAT, v) } else { (NEG_SUCC, -v - 1) };
      let bytes = n.to_le_bytes();
      let digits = bytes.iter().rposition(|b| *b != 0).map_or(0, |i| i + 1);
      let lit = self.nat_bytes(bytes[..digits].to_vec());
      Expr::app(Expr::reference(ctor, vec![]), lit)
    }

    fn fx_type(&self) -> Arc<Expr> {
      if self.shared { Expr::share(0) } else { Expr::reference(FX, vec![]) }
    }

    fn list(&self, ty: Arc<Expr>, items: Vec<Arc<Expr>>) -> Arc<Expr> {
      let nil = Expr::app(Expr::reference(NIL, vec![0]), ty.clone());
      items.into_iter().rev().fold(nil, |tail, x| {
        Expr::app(Expr::app(Expr::app(Expr::reference(CONS, vec![0]), ty.clone()), x), tail)
      })
    }

    fn vector(&mut self, xs: &[i128]) -> Arc<Expr> {
      let items = xs
        .iter()
        .map(|v| {
          let term = match &self.leaf {
            Some((k, term)) if *k == self.position => term.clone(),
            _ => self.int(*v),
          };
          self.position += 1;
          Expr::app(Expr::reference(FX_MK, vec![]), term)
        })
        .collect();
      self.list(self.fx_type(), items)
    }

    fn matrix(&mut self, rows: &[Vec<i128>]) -> Arc<Expr> {
      let items = rows.iter().map(|r| self.vector(r)).collect();
      let ty = Expr::app(Expr::reference(LIST, vec![0]), self.fx_type());
      self.list(ty, items)
    }

    fn model(&mut self, w1: &[Vec<i128>], b1: &[i128], w2: &[Vec<i128>], b2: &[i128]) -> Arc<Expr> {
      let fields = [self.matrix(w1), self.vector(b1), self.matrix(w2), self.vector(b2)];
      fields.into_iter().fold(Expr::reference(MODEL_MK, vec![]), Expr::app)
    }

    fn tables(self, info: ConstantInfo) -> Constant {
      let sharing = if self.shared { vec![Expr::reference(FX, vec![])] } else { vec![] };
      Constant { info, sharing, refs: self.refs, univs: vec![Arc::new(Univ::Zero)] }
    }
  }

  fn definition(value: Arc<Expr>) -> Definition {
    Definition {
      kind: DefKind::Definition, safety: DefinitionSafety::Safe, lvls: 0,
      typ: Expr::reference(MODEL_T, vec![]), value,
    }
  }

  fn sample() -> Vec<i128> {
    (0..MODEL as i128).map(|i| (i * 37) % 211 - 105).collect()
  }

  fn split(m: &[i128]) -> (Vec<Vec<i128>>, Vec<i128>, Vec<Vec<i128>>, Vec<i128>) {
    let (w1, rest) = m.split_at(HIDDEN * INPUTS);
    let (b1, rest) = rest.split_at(HIDDEN);
    let (w2, b2) = rest.split_at(OUTPUTS * HIDDEN);
    (w1.chunks(INPUTS).map(<[_]>::to_vec).collect(), b1.to_vec(),
      w2.chunks(HIDDEN).map(<[_]>::to_vec).collect(), b2.to_vec())
  }

  /// Defines `n` as the literal of `m` in the deployed shape, built by `b`.
  fn define_with(env: &Env, n: &str, m: &[i128], mut b: Builder<'_>) -> Address {
    let (w1, b1, w2, b2) = split(m);
    let value = b.model(&w1, &b1, &w2, &b2);
    let addr = store(env, b.tables(ConstantInfo::Defn(definition(value))));
    register(env, n, &addr);
    addr
  }

  fn decode(env: &Env, n: &str) -> R<Vec<i128>> {
    let ctors = ModelCtors::resolve(env)?;
    decode_model(env, &ctors, n).map(|(_, m)| m)
  }

  fn rejection(r: R<impl std::fmt::Debug>) -> String {
    let e = r.expect_err("accepted").to_string();
    assert!(e.starts_with("REJECT: "), "{e}");
    e
  }

  #[test]
  fn a_model_literal_decodes_in_encoding_order() {
    let env = fixture();
    let m = sample();
    let addr = define_with(&env, "M.model", &m, Builder::new(&env));
    assert_eq!(decode(&env, "M.model").unwrap(), m);
    let ctors = ModelCtors::resolve(&env).unwrap();
    let (got, line) = check_model(&env, &ctors, "M.model", &m).unwrap();
    assert_eq!(got, addr);
    assert_eq!(line, format!("M.model ({}) is the expected model: 331 words", addr.hex()));
  }

  #[test]
  fn shared_subterms_and_block_members_decode_alike() {
    let env = fixture();
    let m = sample();
    let mut b = Builder::new(&env);
    b.shared = true;
    define_with(&env, "M.shared", &m, b);
    assert_eq!(decode(&env, "M.shared").unwrap(), m);

    let (w1, b1, w2, b2) = split(&m);
    let mut b = Builder::new(&env);
    let value = b.model(&w1, &b1, &w2, &b2);
    let block = store(&env, b.tables(ConstantInfo::Muts(vec![MutConst::Defn(definition(value))])));
    let member = store(&env, plain(ConstantInfo::DPrj(DefinitionProj { idx: 0, block })));
    register(&env, "M.member", &member);
    assert_eq!(decode(&env, "M.member").unwrap(), m);
  }

  #[test]
  fn extreme_integers_decode_and_out_of_range_ones_are_rejected() {
    let env = fixture();
    let mut m = sample();
    (m[0], m[1], m[2]) = (BOUND, -BOUND, 0);
    define_with(&env, "M.edge", &m, Builder::new(&env));
    assert_eq!(decode(&env, "M.edge").unwrap(), m);
    assert_eq!(enc(&m[..2]), [enc(&[BOUND]), enc(&[P - BOUND])].concat());

    for (k, v) in [(3, BOUND + 1), (4, -BOUND - 1)] {
      let mut m = sample();
      m[k] = v;
      define_with(&env, "M.far", &m, Builder::new(&env));
      assert!(rejection(decode(&env, "M.far")).contains("out of range"));
      env.named.remove(&name("M.far"));
    }
    let mut b = Builder::new(&env);
    let lit = b.nat_bytes(vec![1; 9]);
    b.leaf = Some((5, Expr::app(Expr::reference(OF_NAT, vec![]), lit)));
    define_with(&env, "M.wide", &sample(), b);
    assert!(rejection(decode(&env, "M.wide")).contains("out of range"));
  }

  #[test]
  fn a_different_or_shorter_expected_output_is_rejected_at_its_first_difference() {
    let env = fixture();
    let m = sample();
    define_with(&env, "M.model", &m, Builder::new(&env));
    let ctors = ModelCtors::resolve(&env).unwrap();
    let mut other = m.clone();
    other[200] += 1;
    other[300] -= 1;
    let e = rejection(check_model(&env, &ctors, "M.model", &other));
    assert!(e.contains("at word 200"), "{e}");
    let e = rejection(check_model(&env, &ctors, "M.model", &m[..330]));
    assert!(e.contains("331 words, the expected model 330"), "{e}");
    // A word equal modulo p is the same field word: the run's claim cannot tell them apart.
    let mut wrapped = m.clone();
    wrapped[0] += P;
    assert!(check_model(&env, &ctors, "M.model", &wrapped).is_ok());
  }

  #[test]
  fn foreign_heads_and_non_literals_are_rejected() {
    let env = fixture();
    let axiom = store(&env, plain(ConstantInfo::Axio(ixon::Axiom {
      is_unsafe: false, lvls: 0, typ: Expr::sort(0),
    })));
    register(&env, "M.ax", &axiom);
    let leaves = |b: &mut Builder<'_>| {
      b.refs.push(axiom.clone());
      let other = b.refs.len() as u64 - 1;
      vec![
        Expr::var(0),
        Expr::reference(other, vec![]),
        Expr::app(Expr::reference(other, vec![]), Expr::var(0)),
        Expr::app(Expr::reference(OF_NAT, vec![]), Expr::var(0)),
        Expr::app(Expr::reference(OF_NAT, vec![]), Expr::reference(other, vec![])),
        Expr::app(Expr::app(Expr::reference(OF_NAT, vec![]), Expr::var(0)), Expr::var(0)),
        Expr::app(Expr::reference(FX_MK, vec![]), Expr::var(0)),
        Expr::share(7),
      ]
    };
    let count = leaves(&mut Builder::new(&env)).len();
    for i in 0..count {
      let mut b = Builder::new(&env);
      let term = leaves(&mut b).swap_remove(i);
      b.leaf = Some((17, term));
      define_with(&env, "M.bad", &sample(), b);
      rejection(decode(&env, "M.bad"));
      env.named.remove(&name("M.bad"));
    }
    let e = rejection(decode(&env, "M.ax"));
    assert!(e.contains("is not a definition"), "{e}");
    assert!(rejection(decode(&env, "M.absent")).contains("no constant named M.absent"));
  }

  #[test]
  fn theorems_other_types_and_other_shapes_are_rejected() {
    let env = fixture();
    let m = sample();
    let (w1, b1, w2, b2) = split(&m);

    let mut b = Builder::new(&env);
    let mut d = definition(b.model(&w1, &b1, &w2, &b2));
    d.kind = DefKind::Theorem;
    register(&env, "M.thm", &store(&env, b.tables(ConstantInfo::Defn(d))));
    rejection(decode(&env, "M.thm"));

    let mut b = Builder::new(&env);
    let mut d = definition(b.model(&w1, &b1, &w2, &b2));
    d.typ = Expr::reference(FX, vec![]);
    register(&env, "M.typed", &store(&env, b.tables(ConstantInfo::Defn(d))));
    rejection(decode(&env, "M.typed"));

    // The same 331 integers with the first two rows of w1 regrouped as 7 and 9.
    let mut regrouped = w1.clone();
    let moved = regrouped[0].pop().unwrap();
    regrouped[1].insert(0, moved);
    let mut b = Builder::new(&env);
    let value = b.model(&regrouped, &b1, &w2, &b2);
    register(&env, "M.shape", &store(&env, b.tables(ConstantInfo::Defn(definition(value)))));
    assert!(rejection(decode(&env, "M.shape")).contains("shape"));

    // A list whose element type is not the expected one.
    let mut b = Builder::new(&env);
    let fields = [b.matrix(&w1), b.list(Expr::reference(MODEL_T, vec![]), vec![]), b.matrix(&w2), b.vector(&b2)];
    let value = fields.into_iter().fold(Expr::reference(MODEL_MK, vec![]), Expr::app);
    register(&env, "M.elem", &store(&env, b.tables(ConstantInfo::Defn(definition(value)))));
    rejection(decode(&env, "M.elem"));
  }

  #[test]
  fn constructors_are_checked_against_their_blocks_and_pins() {
    let env = fixture();
    let ctors = ModelCtors::resolve(&env).unwrap();
    // The fixture's types are look-alikes, not Lean's Int and List.
    assert!(rejection(ctors.check_pinned()).contains("pinned primitive address"));

    // A name pointing at another constructor of its type.
    let env = fixture();
    let neg_succ = unique_address(&env, "Int.negSucc").unwrap();
    register(&env, "Int.ofNat", &neg_succ);
    assert!(rejection(ModelCtors::resolve(&env)).contains("Int.ofNat is not constructor 0"));

    // A constructor of a different type under the expected name.
    let env = fixture();
    let fx_mk = unique_address(&env, "IxAICore.Fx.mk").unwrap();
    register(&env, "IxAICore.Model.mk", &fx_mk);
    rejection(ModelCtors::resolve(&env));

    // Two names that print alike.
    let env = fixture();
    let model = unique_address(&env, "IxAICore.Model").unwrap();
    env.register_name(Name::str(Name::anon(), "IxAICore.Model".into()), ixon::Named::with_addr(model));
    assert!(rejection(ModelCtors::resolve(&env)).contains("more than one constant"));

    // Bytes that do not hash to their address.
    let env = fixture();
    let of_nat = unique_address(&env, "Int.ofNat").unwrap();
    let mut forged = Vec::new();
    plain(ConstantInfo::CPrj(ConstructorProj { idx: 0, cidx: 0, block: Address::hash(b"elsewhere") })).put(&mut forged);
    env.store_const_lazy(of_nat, forged.into());
    assert!(rejection(ModelCtors::resolve(&env)).contains("does not hash"));
  }

  #[test]
  fn options_parse_and_reject_unknown_or_incomplete_flags() {
    let args = |s: &[&str]| s.iter().map(|x| x.to_string()).collect::<Vec<_>>();
    assert_eq!(options(&[]).unwrap(), Options::default());
    assert_eq!(
      options(&args(&["--contains", "A", "--model-constant", "M", "--contains", "B"])).unwrap(),
      Options { model_constant: Some("M".into()), contains: vec!["A".into(), "B".into()] }
    );
    assert!(options(&args(&["--contains"])).is_err());
    assert!(options(&args(&["--model-constant", "M", "--model-constant", "N"])).is_err());
    assert!(options(&args(&["--other", "X"])).is_err());
  }
}
