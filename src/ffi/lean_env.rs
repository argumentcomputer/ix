//! Decode Lean kernel objects from their in-memory C representation.
//!
//! Provides functions to walk Lean object pointers and decode them into
//! the Rust `Name`, `Level`, `Expr`, and `ConstantInfo` types defined in
//! `crate::ix::env`. Used by the compilation pipeline to read the Lean
//! environment before transforming it to Ixon format.
//!
//! Uses a two-level cache (`GlobalCache` + `LocalCache`) to avoid redundant
//! decoding of shared subterms when processing environments in parallel.

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]
#![allow(clippy::cast_possible_wrap)]

use dashmap::DashMap;
use rayon::prelude::*;

use rustc_hash::FxHashMap;

#[cfg(feature = "test-ffi")]
use crate::ix::compile::compile_env;
#[cfg(feature = "test-ffi")]
use crate::ix::decompile::{check_decompile, decompile_env};
#[cfg(feature = "test-ffi")]
use std::sync::Arc;

use lean_ffi::nat::Nat;
use lean_ffi::object::{LeanBorrowed, LeanList, LeanRef, LeanShared};

use crate::ix::env::{
  AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
  DefinitionSafety, DefinitionVal, Env, Expr, InductiveVal, Int, Level,
  Literal, Name, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
  ReducibilityHints, SourceInfo, Substring, Syntax, SyntaxPreresolved,
  TheoremVal,
};

const PARALLEL_THRESHOLD: usize = 100;

/// Global cache for Names, shared across all threads.
#[derive(Default)]
pub struct GlobalCache {
  names: DashMap<*mut lean_ffi::include::lean_object, Name>,
}

impl GlobalCache {
  fn new() -> Self {
    Self { names: DashMap::new() }
  }

  fn with_capacity(capacity: usize) -> Self {
    Self { names: DashMap::with_capacity(capacity) }
  }
}

// SAFETY: The raw pointers are only used as keys for identity comparison.
// The underlying Lean memory remains valid for the duration of decoding.
unsafe impl Send for GlobalCache {}
unsafe impl Sync for GlobalCache {}

/// Thread-local cache for Levels and Exprs.
#[derive(Default)]
struct LocalCache {
  univs: FxHashMap<*mut lean_ffi::include::lean_object, Level>,
  exprs: FxHashMap<*mut lean_ffi::include::lean_object, Expr>,
}

// SAFETY: LocalCache is only accessed by a single thread.
unsafe impl Send for LocalCache {}

/// Combined cache reference passed to decoding functions.
pub struct Cache<'g> {
  global: &'g GlobalCache,
  local: LocalCache,
}

impl<'g> Cache<'g> {
  pub fn new(global: &'g GlobalCache) -> Self {
    Self { global, local: LocalCache::default() }
  }
}

/// Collect list elements as borrowed pointers (no refcount changes).
/// Uses `LeanList::to_vec` which preserves the `'a` lifetime from the
/// underlying Lean objects rather than tying it to a local borrow.
fn collect_list_borrowed<'a>(
  list: LeanList<LeanBorrowed<'a>>,
) -> Vec<LeanBorrowed<'a>> {
  list.to_vec()
}

/// Collect list elements as LeanShared handles for cross-thread use.
/// The caller should have already MT-marked the parent list via `LeanShared::new`,
/// so `lean_mark_mt` on each element is a single `lean_is_st` check (fast no-op).
fn collect_list_shared(list: LeanList<LeanBorrowed<'_>>) -> Vec<LeanShared> {
  list.iter().map(|b| LeanShared::new(b.to_owned_ref())).collect()
}

// Name decoding with global cache
pub fn decode_name(obj: LeanBorrowed<'_>, global: &GlobalCache) -> Name {
  let ptr = obj.as_raw();
  // Fast path: check if already cached
  if let Some(name) = global.names.get(&ptr) {
    return name.clone();
  }

  // Compute the name
  let name = if obj.is_scalar() {
    Name::anon()
  } else {
    let ctor = obj.as_ctor();
    let [pre, pos] = ctor.objs();
    // Recursive call - will also use global cache
    let pre = decode_name(pre, global);
    match ctor.tag() {
      1 => Name::str(pre, pos.as_string().to_string()),
      2 => Name::num(pre, Nat::from_obj(&pos)),
      _ => unreachable!(),
    }
  };

  // Insert and return (entry API handles races gracefully)
  global.names.entry(ptr).or_insert(name).clone()
}

fn decode_level(obj: LeanBorrowed<'_>, cache: &mut Cache<'_>) -> Level {
  let ptr = obj.as_raw();
  if let Some(cached) = cache.local.univs.get(&ptr) {
    return cached.clone();
  }
  let level = if obj.is_scalar() {
    Level::zero()
  } else {
    let ctor = obj.as_ctor();
    match ctor.tag() {
      1 => {
        let [u] = ctor.objs::<1>().map(|o| decode_level(o, cache));
        Level::succ(u)
      },
      2 => {
        let [u, v] = ctor.objs::<2>().map(|o| decode_level(o, cache));
        Level::max(u, v)
      },
      3 => {
        let [u, v] = ctor.objs::<2>().map(|o| decode_level(o, cache));
        Level::imax(u, v)
      },
      4 => {
        let [name] = ctor.objs::<1>().map(|o| decode_name(o, cache.global));
        Level::param(name)
      },
      5 => {
        let [name] = ctor.objs::<1>().map(|o| decode_name(o, cache.global));
        Level::mvar(name)
      },
      _ => unreachable!(),
    }
  };
  cache.local.univs.insert(ptr, level.clone());
  level
}

fn decode_substring(obj: LeanBorrowed<'_>) -> Substring {
  let ctor = obj.as_ctor();
  let [str_obj, start_pos, stop_pos] = ctor.objs();
  let str = str_obj.as_string().to_string();
  let start_pos = Nat::from_obj(&start_pos);
  let stop_pos = Nat::from_obj(&stop_pos);
  Substring { str, start_pos, stop_pos }
}

fn decode_source_info(obj: LeanBorrowed<'_>) -> SourceInfo {
  if obj.is_scalar() {
    return SourceInfo::None;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let [leading, pos, trailing, end_pos] = ctor.objs();
      let leading = decode_substring(leading);
      let pos = Nat::from_obj(&pos);
      let trailing = decode_substring(trailing);
      let end_pos = Nat::from_obj(&end_pos);
      SourceInfo::Original(leading, pos, trailing, end_pos)
    },
    1 => {
      let [pos, end_pos, canonical] = ctor.objs();
      let pos = Nat::from_obj(&pos);
      let end_pos = Nat::from_obj(&end_pos);
      let canonical = canonical.as_raw() as usize == 1;
      SourceInfo::Synthetic(pos, end_pos, canonical)
    },
    _ => unreachable!(),
  }
}

fn decode_syntax_preresolved(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> SyntaxPreresolved {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      let [name_obj] = ctor.objs::<1>();
      let name = decode_name(name_obj, cache.global);
      SyntaxPreresolved::Namespace(name)
    },
    1 => {
      let [name_obj, fields_obj] = ctor.objs();
      let name = decode_name(name_obj, cache.global);
      let fields: Vec<String> = fields_obj
        .as_list()
        .iter()
        .map(|o| o.as_string().to_string())
        .collect();
      SyntaxPreresolved::Decl(name, fields)
    },
    _ => unreachable!(),
  }
}

fn decode_syntax(obj: LeanBorrowed<'_>, cache: &mut Cache<'_>) -> Syntax {
  if obj.is_scalar() {
    return Syntax::Missing;
  }
  let ctor = obj.as_ctor();
  match ctor.tag() {
    1 => {
      let [info, kind, args] = ctor.objs();
      let info = decode_source_info(info);
      let kind = decode_name(kind, cache.global);
      let args: Vec<_> =
        args.as_array().iter().map(|o| decode_syntax(o, cache)).collect();
      Syntax::Node(info, kind, args)
    },
    2 => {
      let [info, val] = ctor.objs();
      let info = decode_source_info(info);
      Syntax::Atom(info, val.as_string().to_string())
    },
    3 => {
      let [info, raw_val, val, preresolved] = ctor.objs();
      let info = decode_source_info(info);
      let raw_val = decode_substring(raw_val);
      let val = decode_name(val, cache.global);
      let preresolved = collect_list_borrowed(preresolved.as_list())
        .into_iter()
        .map(|o| decode_syntax_preresolved(o, cache))
        .collect();
      Syntax::Ident(info, raw_val, val, preresolved)
    },
    _ => unreachable!(),
  }
}

fn decode_name_data_value(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> (Name, DataValue) {
  let ctor = obj.as_ctor();
  let [name_obj, data_value_obj] = ctor.objs();
  let name = decode_name(name_obj, cache.global);
  let dv_ctor = data_value_obj.as_ctor();
  let [inner] = dv_ctor.objs::<1>();
  let data_value = match dv_ctor.tag() {
    0 => DataValue::OfString(inner.as_string().to_string()),
    1 => DataValue::OfBool(inner.as_raw() as usize == 1),
    2 => DataValue::OfName(decode_name(inner, cache.global)),
    3 => DataValue::OfNat(Nat::from_obj(&inner)),
    4 => {
      let inner_ctor = inner.as_ctor();
      let [nat_obj] = inner_ctor.objs::<1>();
      let nat = Nat::from_obj(&nat_obj);
      let int = match inner_ctor.tag() {
        0 => Int::OfNat(nat),
        1 => Int::NegSucc(nat),
        _ => unreachable!(),
      };
      DataValue::OfInt(int)
    },
    5 => DataValue::OfSyntax(decode_syntax(inner, cache).into()),
    _ => unreachable!(),
  };
  (name, data_value)
}

pub fn decode_expr(obj: LeanBorrowed<'_>, cache: &mut Cache<'_>) -> Expr {
  let ptr = obj.as_raw();
  if let Some(cached) = cache.local.exprs.get(&ptr) {
    return cached.clone();
  }
  let ctor = obj.as_ctor();
  let expr = match ctor.tag() {
    0 => {
      let [nat, _hash] = ctor.objs();
      Expr::bvar(Nat::from_obj(&nat))
    },
    1 => {
      let [name_obj, _hash] = ctor.objs();
      let name = decode_name(name_obj, cache.global);
      Expr::fvar(name)
    },
    2 => {
      let [name_obj, _hash] = ctor.objs();
      let name = decode_name(name_obj, cache.global);
      Expr::mvar(name)
    },
    3 => {
      let [u, _hash] = ctor.objs();
      let u = decode_level(u, cache);
      Expr::sort(u)
    },
    4 => {
      let [name_obj, levels, _hash] = ctor.objs();
      let name = decode_name(name_obj, cache.global);
      let levels = collect_list_borrowed(levels.as_list())
        .into_iter()
        .map(|o| decode_level(o, cache))
        .collect();
      Expr::cnst(name, levels)
    },
    5 => {
      let [f, a, _hash] = ctor.objs();
      let f = decode_expr(f, cache);
      let a = decode_expr(a, cache);
      Expr::app(f, a)
    },
    6 => {
      let [binder_name, binder_typ, body, _hash, binder_info] = ctor.objs();
      let binder_name = decode_name(binder_name, cache.global);
      let binder_typ = decode_expr(binder_typ, cache);
      let body = decode_expr(body, cache);
      let binder_info = match binder_info.as_raw() as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::lam(binder_name, binder_typ, body, binder_info)
    },
    7 => {
      let [binder_name, binder_typ, body, _hash, binder_info] = ctor.objs();
      let binder_name = decode_name(binder_name, cache.global);
      let binder_typ = decode_expr(binder_typ, cache);
      let body = decode_expr(body, cache);
      let binder_info = match binder_info.as_raw() as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::all(binder_name, binder_typ, body, binder_info)
    },
    8 => {
      let [decl_name, typ, value, body, _hash, nondep] = ctor.objs();
      let decl_name = decode_name(decl_name, cache.global);
      let typ = decode_expr(typ, cache);
      let value = decode_expr(value, cache);
      let body = decode_expr(body, cache);
      let nondep = nondep.as_raw() as usize == 1;
      Expr::letE(decl_name, typ, value, body, nondep)
    },
    9 => {
      let [literal, _hash] = ctor.objs();
      let lit_ctor = literal.as_ctor();
      let [inner] = lit_ctor.objs::<1>();
      match lit_ctor.tag() {
        0 => Expr::lit(Literal::NatVal(Nat::from_obj(&inner))),
        1 => Expr::lit(Literal::StrVal(inner.as_string().to_string())),
        _ => unreachable!(),
      }
    },
    10 => {
      let [data, expr_obj] = ctor.objs();
      let kv_map: Vec<_> = collect_list_borrowed(data.as_list())
        .into_iter()
        .map(|o| decode_name_data_value(o, cache))
        .collect();
      let expr = decode_expr(expr_obj, cache);
      Expr::mdata(kv_map, expr)
    },
    11 => {
      let [typ_name, idx, struct_expr] = ctor.objs();
      let typ_name = decode_name(typ_name, cache.global);
      let idx = Nat::from_obj(&idx);
      let struct_expr = decode_expr(struct_expr, cache);
      Expr::proj(typ_name, idx, struct_expr)
    },
    _ => unreachable!(),
  };
  cache.local.exprs.insert(ptr, expr.clone());
  expr
}

fn decode_recursor_rule(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> RecursorRule {
  let ctor = obj.as_ctor();
  let [ctor_name, n_fields, rhs] = ctor.objs();
  let ctor_name = decode_name(ctor_name, cache.global);
  let n_fields = Nat::from_obj(&n_fields);
  let rhs = decode_expr(rhs, cache);
  RecursorRule { ctor: ctor_name, n_fields, rhs }
}

fn decode_constant_val(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> ConstantVal {
  let ctor = obj.as_ctor();
  let [name_obj, level_params, typ] = ctor.objs();
  let name = decode_name(name_obj, cache.global);
  let level_params: Vec<_> = collect_list_borrowed(level_params.as_list())
    .into_iter()
    .map(|o| decode_name(o, cache.global))
    .collect();
  let typ = decode_expr(typ, cache);
  ConstantVal { name, level_params, typ }
}

pub fn decode_constant_info(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> ConstantInfo {
  let ctor = obj.as_ctor();
  let [inner_val] = ctor.objs::<1>();
  let inner = inner_val.as_ctor();

  match ctor.tag() {
    0 => {
      let [constant_val, is_unsafe] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let is_unsafe = is_unsafe.as_raw() as usize == 1;
      ConstantInfo::AxiomInfo(AxiomVal { cnst: constant_val, is_unsafe })
    },
    1 => {
      let [constant_val, value, hints, all, safety] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let value = decode_expr(value, cache);
      let hints = if hints.is_scalar() {
        match hints.unbox_usize() {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          _ => unreachable!(),
        }
      } else {
        let hints_ctor = hints.as_ctor();
        let [height] = hints_ctor.objs::<1>();
        ReducibilityHints::Regular(height.as_raw() as u32)
      };
      let all: Vec<_> = collect_list_borrowed(all.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let safety = match safety.as_raw() as usize {
        0 => DefinitionSafety::Unsafe,
        1 => DefinitionSafety::Safe,
        2 => DefinitionSafety::Partial,
        _ => unreachable!(),
      };
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: constant_val,
        value,
        hints,
        safety,
        all,
      })
    },
    2 => {
      let [constant_val, value, all] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let value = decode_expr(value, cache);
      let all: Vec<_> = collect_list_borrowed(all.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      ConstantInfo::ThmInfo(TheoremVal { cnst: constant_val, value, all })
    },
    3 => {
      let [constant_val, value, all, is_unsafe] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let value = decode_expr(value, cache);
      let all: Vec<_> = collect_list_borrowed(all.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let is_unsafe = is_unsafe.as_raw() as usize == 1;
      ConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: constant_val,
        value,
        is_unsafe,
        all,
      })
    },
    4 => {
      let [constant_val, kind] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let kind = match kind.as_raw() as usize {
        0 => QuotKind::Type,
        1 => QuotKind::Ctor,
        2 => QuotKind::Lift,
        3 => QuotKind::Ind,
        _ => unreachable!(),
      };
      ConstantInfo::QuotInfo(QuotVal { cnst: constant_val, kind })
    },
    5 => {
      let [
        constant_val,
        num_params,
        num_indices,
        all,
        ctors,
        num_nested,
        bools,
      ] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let num_params = Nat::from_obj(&num_params);
      let num_indices = Nat::from_obj(&num_indices);
      let all: Vec<_> = collect_list_borrowed(all.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let ctors: Vec<_> = collect_list_borrowed(ctors.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let num_nested = Nat::from_obj(&num_nested);
      let [is_rec, is_unsafe, is_reflexive, ..] =
        (bools.as_raw() as usize).to_le_bytes().map(|b| b == 1);
      ConstantInfo::InductInfo(InductiveVal {
        cnst: constant_val,
        num_params,
        num_indices,
        all,
        ctors,
        num_nested,
        is_rec,
        is_unsafe,
        is_reflexive,
      })
    },
    6 => {
      let [constant_val, induct, cidx, num_params, num_fields, is_unsafe] =
        inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let induct = decode_name(induct, cache.global);
      let cidx = Nat::from_obj(&cidx);
      let num_params = Nat::from_obj(&num_params);
      let num_fields = Nat::from_obj(&num_fields);
      let is_unsafe = is_unsafe.as_raw() as usize == 1;
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: constant_val,
        induct,
        cidx,
        num_params,
        num_fields,
        is_unsafe,
      })
    },
    7 => {
      let [
        constant_val,
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        bools,
      ] = inner.objs();
      let constant_val = decode_constant_val(constant_val, cache);
      let all: Vec<_> = collect_list_borrowed(all.as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let num_params = Nat::from_obj(&num_params);
      let num_indices = Nat::from_obj(&num_indices);
      let num_motives = Nat::from_obj(&num_motives);
      let num_minors = Nat::from_obj(&num_minors);
      let rules: Vec<_> = collect_list_borrowed(rules.as_list())
        .into_iter()
        .map(|o| decode_recursor_rule(o, cache))
        .collect();
      let [k, is_unsafe, ..] =
        (bools.as_raw() as usize).to_le_bytes().map(|b| b == 1);
      ConstantInfo::RecInfo(RecursorVal {
        cnst: constant_val,
        all,
        num_params,
        num_indices,
        num_motives,
        num_minors,
        rules,
        k,
        is_unsafe,
      })
    },
    _ => unreachable!(),
  }
}

/// Decode a single (Name, ConstantInfo) pair.
fn decode_name_constant_info(
  obj: LeanBorrowed<'_>,
  global: &GlobalCache,
) -> (Name, ConstantInfo) {
  let mut cache = Cache::new(global);
  let ctor = obj.as_ctor();
  let [name_obj, constant_info] = ctor.objs();
  let name = decode_name(name_obj, global);
  let constant_info = decode_constant_info(constant_info, &mut cache);
  (name, constant_info)
}

// Decode a Lean environment in parallel with hybrid caching.
pub fn decode_env(list: LeanList<LeanBorrowed<'_>>) -> Env {
  // Phase 1: Mark entire list graph as MT, then collect elements as LeanShared.
  // lean_mark_mt recursively marks all reachable objects. Subsequent
  // LeanShared::new calls on elements are a fast no-op (single is_st check).
  let shared_list = LeanShared::new(list.inner().to_owned_ref());
  let objs = collect_list_shared(shared_list.borrow().as_list());

  if objs.len() < PARALLEL_THRESHOLD {
    // Sequential fallback for small environments — no MT overhead needed,
    // but objects are already marked. Just borrow directly.
    let global = GlobalCache::new();
    let mut env = Env::default();
    env.reserve(objs.len());
    for o in &objs {
      let (name, constant_info) =
        decode_name_constant_info(o.borrow(), &global);
      env.insert(name, constant_info);
    }
    return env;
  }

  // Estimate: ~3 unique names per constant on average
  let global = GlobalCache::with_capacity(objs.len() * 3);

  // Phase 2: Decode in parallel with shared global name cache
  let pairs: Vec<(Name, ConstantInfo)> = objs
    .into_par_iter()
    .map(|shared| decode_name_constant_info(shared.borrow(), &global))
    .collect();

  // Phase 3: Build final map
  let mut env = Env::default();
  env.reserve(pairs.len());
  for (name, constant_info) in pairs {
    env.insert(name, constant_info);
  }
  env
}

// Debug/analysis entry point invoked via the `rust-compile` test flag in
// `Tests/Main.lean`. Exercises the full compile→decompile→check→serialize
// roundtrip and size analysis with phased logging.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_tmp_decode_const_map(
  obj: LeanList<LeanBorrowed<'_>>,
) -> usize {
  // Enable hash-consed size tracking for debugging
  crate::ix::compile::TRACK_HASH_CONSED_SIZE
    .store(true, std::sync::atomic::Ordering::Relaxed);

  // Enable verbose sharing analysis for debugging pathological blocks
  crate::ix::compile::ANALYZE_SHARING
    .store(false, std::sync::atomic::Ordering::Relaxed);

  let env = decode_env(obj);
  let n = env.len();
  let env = Arc::new(env);
  let t0 = std::time::Instant::now();

  // Phase 1: Compile
  eprintln!("[rust-compile] Phase 1: Compiling {n} constants...");
  let stt = match compile_env(&env) {
    Ok(s) => s,
    Err(e) => {
      eprintln!("[rust-compile] Phase 1 FAILED: {e:?}");
      return n;
    },
  };
  eprintln!(
    "[rust-compile] Phase 1 done in {:.2}s ({} consts, {} named, {} names, {} blobs)",
    t0.elapsed().as_secs_f32(),
    stt.env.const_count(),
    stt.env.named.len(),
    stt.env.names.len(),
    stt.env.blob_count(),
  );

  // Phase 2: Decompile
  eprintln!("[rust-compile] Phase 2: Decompiling...");
  let t1 = std::time::Instant::now();
  let dstt = match decompile_env(&stt) {
    Ok(d) => d,
    Err(e) => {
      eprintln!(
        "[rust-compile] Phase 2 FAILED after {:.2}s: {e:?}",
        t1.elapsed().as_secs_f32()
      );
      return n;
    },
  };
  eprintln!(
    "[rust-compile] Phase 2 done in {:.2}s ({} constants)",
    t1.elapsed().as_secs_f32(),
    dstt.env.len()
  );

  // Phase 3: Check roundtrip
  eprintln!("[rust-compile] Phase 3: Checking decompile roundtrip...");
  let t2 = std::time::Instant::now();
  let _ = check_decompile(env.as_ref(), &stt, &dstt);
  eprintln!(
    "[rust-compile] Phase 3 done in {:.2}s",
    t2.elapsed().as_secs_f32()
  );

  // Phase 4: Size analysis
  eprintln!("[rust-compile] Phase 4: Size analysis...");
  let _ = stt.env.serialized_size_breakdown();
  analyze_const_size(&stt, "Nat.add_comm");
  analyze_block_size_stats(&stt);

  // Phase 5: Serialize
  eprintln!("[rust-compile] Phase 5: Serializing env...");
  let t3 = std::time::Instant::now();
  let mut serialized = Vec::new();
  if let Err(e) = stt.env.put(&mut serialized) {
    eprintln!("[rust-compile] Phase 5 FAILED: {e}");
    return n;
  }
  eprintln!(
    "[rust-compile] Phase 5 done: {} bytes in {:.2}s",
    serialized.len(),
    t3.elapsed().as_secs_f32()
  );

  // Phase 6: Deserialize + re-decompile
  eprintln!("[rust-compile] Phase 6: Deserializing and re-decompiling...");
  let t4 = std::time::Instant::now();
  let mut buf: &[u8] = &serialized;
  match crate::ix::ixon::env::Env::get(&mut buf) {
    Ok(fresh_env) => {
      let fresh_stt = crate::ix::compile::CompileState {
        env: fresh_env,
        ..Default::default()
      };
      for entry in fresh_stt.env.named.iter() {
        fresh_stt
          .name_to_addr
          .insert(entry.key().clone(), entry.value().addr.clone());
      }
      match decompile_env(&fresh_stt) {
        Ok(dstt2) => {
          let _ = check_decompile(env.as_ref(), &fresh_stt, &dstt2);
        },
        Err(e) => {
          eprintln!("[rust-compile] Phase 6 re-decompile FAILED: {e:?}");
          return n;
        },
      }
    },
    Err(e) => {
      eprintln!("[rust-compile] Phase 6 deserialize FAILED: {e}");
      return n;
    },
  }
  eprintln!(
    "[rust-compile] Phase 6 done in {:.2}s",
    t4.elapsed().as_secs_f32()
  );

  eprintln!(
    "[rust-compile] All phases complete. Total: {:.2}s",
    t0.elapsed().as_secs_f32()
  );
  n
}

// ============================================================================
// Comprehensive validation: rust-compile-validate-aux
// ============================================================================

#[cfg(feature = "test-ffi")]
const VALIDATE_PREFIX: &str = "[validate-aux]";

/// Per-phase result accumulator.
#[cfg(feature = "test-ffi")]
struct PhaseResult {
  name: &'static str,
  pass: usize,
  fail: usize,
  failures: Vec<String>,
}

#[cfg(feature = "test-ffi")]
impl PhaseResult {
  fn new(name: &'static str) -> Self {
    PhaseResult { name, pass: 0, fail: 0, failures: Vec::new() }
  }

  fn record_pass(&mut self) {
    self.pass += 1;
  }

  fn record_fail(&mut self, msg: String) {
    self.fail += 1;
    if self.failures.len() < 20 {
      self.failures.push(msg);
    }
  }

  fn report(&self) {
    println!("{VALIDATE_PREFIX} Phase: {}", self.name);
    println!("{VALIDATE_PREFIX}   {} pass, {} fail", self.pass, self.fail);
    for f in &self.failures {
      println!("{VALIDATE_PREFIX}     ✗ {f}");
    }
  }
}

/// Comprehensive 6-phase validation of the aux_gen compile pipeline.
///
/// Returns total failure count across all phases.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
extern "C" fn rs_compile_validate_aux(
  obj: LeanList<LeanBorrowed<'_>>,
) -> usize {
  use crate::ix::congruence::const_alpha_eq;
  use rustc_hash::FxHashSet;

  let t_total = std::time::Instant::now();

  // ── Decode ──────────────────────────────────────────────────────────
  println!("{VALIDATE_PREFIX} decoding...");
  let env = decode_env(obj);
  let n = env.len();
  println!("{VALIDATE_PREFIX} decoded {n} constants");
  let env = Arc::new(env);

  // ══════════════════════════════════════════════════════════════════════
  // Phase 1: Compilation succeeds
  // ══════════════════════════════════════════════════════════════════════
  let mut p1 = PhaseResult::new("Compilation");
  println!("{VALIDATE_PREFIX} compiling...");
  let t0 = std::time::Instant::now();
  let stt = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    compile_env(&env)
  })) {
    Ok(Ok(s)) => s,
    Ok(Err(e)) => {
      p1.record_fail(format!("compile_env FAILED: {e}"));
      p1.report();
      println!(
        "{VALIDATE_PREFIX} RESULT: {} total failures (aborted after Phase 1)",
        p1.fail
      );
      return p1.fail;
    },
    Err(panic) => {
      let msg = panic
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("(non-string panic)");
      p1.record_fail(format!("compile_env PANICKED: {msg}"));
      p1.report();
      println!(
        "{VALIDATE_PREFIX} RESULT: {} total failures (aborted after Phase 1)",
        p1.fail
      );
      return p1.fail;
    },
  };
  println!("{VALIDATE_PREFIX} compiled in {:.2}s", t0.elapsed().as_secs_f32());

  for (name, _) in env.iter() {
    if stt.ungrounded.contains_key(name) {
      continue;
    }
    if stt.resolve_addr(name).is_some() {
      p1.record_pass();
    } else {
      p1.record_fail(format!("{}: not compiled", name.pretty()));
    }
  }
  p1.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 2: No ephemeral constant leaks
  // ══════════════════════════════════════════════════════════════════════
  let mut p2 = PhaseResult::new("No ephemeral leaks");

  for entry in stt.env.named.iter() {
    let named = entry.value();
    if let Some((orig_addr, _)) = &named.original {
      if *orig_addr != named.addr && stt.env.consts.contains_key(orig_addr) {
        p2.record_fail(format!(
          "{}: ephemeral original addr {:?} leaked into consts",
          entry.key().pretty(),
          orig_addr,
        ));
      } else {
        p2.record_pass();
      }
    }
  }
  p2.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 3: Alpha-equivalence group canonicity
  // ══════════════════════════════════════════════════════════════════════
  let mut p3 = PhaseResult::new("Alpha-equivalence canonicity");
  {
    // Deduplicate blocks: every name in a mutual block stores the same
    // Vec<Vec<Name>>, so we only need to check each block once.
    let mut seen_blocks: FxHashSet<Name> = FxHashSet::default();

    for entry in stt.blocks.iter() {
      let classes = entry.value();
      // Use the first name of the first class as a dedup key.
      if let Some(first_class) = classes.first()
        && let Some(first_name) = first_class.first()
        && !seen_blocks.insert(first_name.clone())
      {
        continue;
      }

      for class in classes.iter() {
        if class.len() <= 1 {
          // Singleton class: trivially canonical.
          p3.record_pass();
          continue;
        }

        // All names in the class must resolve to the same address.
        let addrs: Vec<_> =
          class.iter().map(|name| (name, stt.resolve_addr(name))).collect();

        let first_addr = &addrs[0].1;
        if addrs.iter().all(|(_, a)| a == first_addr) {
          p3.record_pass();
        } else {
          let detail: Vec<_> = addrs
            .iter()
            .map(|(n, a)| {
              format!(
                "{}={}",
                n.pretty(),
                a.as_ref().map_or("MISSING".to_string(), |a| format!("{a:?}"))
              )
            })
            .collect();
          p3.record_fail(format!("class addrs differ: {}", detail.join(", ")));
        }
      }
    }
  }
  p3.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 4: Decompile with debug info
  // ══════════════════════════════════════════════════════════════════════
  let mut p4 = PhaseResult::new("Decompile (with debug)");
  println!("{VALIDATE_PREFIX} decompiling (with debug)...");
  let t1 = std::time::Instant::now();

  let dstt = match decompile_env(&stt) {
    Ok(d) => {
      println!(
        "{VALIDATE_PREFIX} decompiled in {:.2}s ({} constants)",
        t1.elapsed().as_secs_f32(),
        d.env.len()
      );
      Some(d)
    },
    Err(e) => {
      p4.record_fail(format!("decompile_env FAILED: {e:?}"));
      println!(
        "{VALIDATE_PREFIX} decompile FAILED in {:.2}s: {e:?}",
        t1.elapsed().as_secs_f32()
      );
      None
    },
  };

  if let Some(ref dstt) = dstt {
    let check = check_decompile(env.as_ref(), &stt, dstt);
    match check {
      Ok(r) => {
        p4.pass = r.matches;
        if r.mismatches > 0 {
          p4.record_fail(format!("{} hash mismatches", r.mismatches));
        }
        if r.missing > 0 {
          p4.record_fail(format!("{} missing from original", r.missing));
        }
      },
      Err(e) => {
        p4.record_fail(format!("check_decompile FAILED: {e:?}"));
      },
    }
  }
  p4.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 5: Aux congruence
  // ══════════════════════════════════════════════════════════════════════
  let mut p5 = PhaseResult::new("Aux congruence");

  if let (Some(dstt), Some(lean_env)) = (&dstt, &stt.lean_env) {
    for name in stt.aux_gen_extra_names.iter() {
      let name = name.key();
      let orig_ci = match lean_env.get(name) {
        Some(ci) => ci,
        None => {
          p5.record_fail(format!(
            "{}: not in original Lean env",
            name.pretty()
          ));
          continue;
        },
      };
      let dec_ci = match dstt.env.get(name) {
        Some(ci) => ci,
        None => {
          p5.record_fail(format!("{}: not in decompiled env", name.pretty()));
          continue;
        },
      };
      match const_alpha_eq(dec_ci.value(), orig_ci) {
        Ok(()) => p5.record_pass(),
        Err(e) => p5.record_fail(format!("{}: {e}", name.pretty())),
      }
    }
  } else {
    if dstt.is_none() {
      p5.record_fail("skipped: decompilation failed in Phase 4".into());
    }
    if stt.lean_env.is_none() {
      p5.record_fail("skipped: lean_env not available".into());
    }
  }
  p5.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 6: Decompile without debug info (serialize → deserialize)
  // ══════════════════════════════════════════════════════════════════════
  let mut p6 = PhaseResult::new("Decompile (without debug)");
  println!("{VALIDATE_PREFIX} serializing...");
  let t2 = std::time::Instant::now();

  let mut serialized = Vec::new();
  match stt.env.put(&mut serialized) {
    Ok(()) => {
      println!(
        "{VALIDATE_PREFIX} serialized {} bytes in {:.2}s",
        serialized.len(),
        t2.elapsed().as_secs_f32()
      );
    },
    Err(e) => {
      p6.record_fail(format!("serialize FAILED: {e}"));
      p6.report();
      let total = p1.fail + p2.fail + p3.fail + p4.fail + p5.fail + p6.fail;
      println!("{VALIDATE_PREFIX} RESULT: {total} total failures");
      return total;
    },
  }

  println!("{VALIDATE_PREFIX} deserializing and re-decompiling...");
  let t3 = std::time::Instant::now();
  let mut buf: &[u8] = &serialized;
  match crate::ix::ixon::env::Env::get(&mut buf) {
    Ok(fresh_env) => {
      let fresh_stt = crate::ix::compile::CompileState {
        env: fresh_env,
        ..Default::default()
      };
      let mut n_original = 0usize;
      for entry in fresh_stt.env.named.iter() {
        fresh_stt
          .name_to_addr
          .insert(entry.key().clone(), entry.value().addr.clone());
        if entry.value().original.is_some() {
          n_original += 1;
        }
      }
      println!(
        "{VALIDATE_PREFIX} deserialized: {} named, {} with original",
        fresh_stt.env.named.len(),
        n_original
      );
      match decompile_env(&fresh_stt) {
        Ok(dstt2) => {
          println!(
            "{VALIDATE_PREFIX} re-decompiled in {:.2}s ({} constants)",
            t3.elapsed().as_secs_f32(),
            dstt2.env.len()
          );
          match check_decompile(env.as_ref(), &fresh_stt, &dstt2) {
            Ok(r) => {
              p6.pass = r.matches;
              if r.mismatches > 0 {
                p6.record_fail(format!("{} hash mismatches", r.mismatches));
              }
              if r.missing > 0 {
                p6.record_fail(format!("{} missing from original", r.missing));
              }
            },
            Err(e) => {
              p6.record_fail(format!("check_decompile FAILED: {e:?}"));
            },
          }
        },
        Err(e) => {
          p6.record_fail(format!("re-decompile FAILED: {e:?}"));
        },
      }
    },
    Err(e) => {
      p6.record_fail(format!("deserialize FAILED: {e}"));
    },
  }
  p6.report();

  // ══════════════════════════════════════════════════════════════════════
  // Summary
  // ══════════════════════════════════════════════════════════════════════
  let total = p1.fail + p2.fail + p3.fail + p4.fail + p5.fail + p6.fail;
  println!(
    "{VALIDATE_PREFIX} done ({:.2}s total)",
    t_total.elapsed().as_secs_f32()
  );
  println!("{VALIDATE_PREFIX} RESULT: {total} total failures");
  total
}

#[cfg(feature = "test-ffi")]
/// Size breakdown for a constant: alpha-invariant vs metadata
#[derive(Default, Clone)]
struct ConstSizeBreakdown {
  alpha_size: usize, // Alpha-invariant constant data
  meta_size: usize,  // Metadata (names, binder info, etc.)
}

#[cfg(feature = "test-ffi")]
impl ConstSizeBreakdown {
  fn total(&self) -> usize {
    self.alpha_size + self.meta_size
  }
}

#[cfg(feature = "test-ffi")]
/// Analyze the serialized size of a constant and its transitive dependencies.
fn analyze_const_size(stt: &crate::ix::compile::CompileState, name_str: &str) {
  use crate::ix::address::Address;
  use std::collections::{HashSet, VecDeque};

  // Build a global name index for metadata serialization
  let name_index = build_name_index(stt);

  // Parse the name (e.g., "Nat.add_comm" -> Name::str(Name::str(Name::anon(), "Nat"), "add_comm"))
  let name = parse_name(name_str);

  // Look up the constant's address
  let addr = match stt.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => {
      println!("\n=== Size analysis for {} ===", name_str);
      println!("  Constant not found");
      return;
    },
  };

  // Get the constant
  let constant = match stt.env.consts.get(&addr) {
    Some(c) => c.clone(),
    None => {
      println!("\n=== Size analysis for {} ===", name_str);
      println!("  Constant data not found at address");
      return;
    },
  };

  // Compute direct sizes (alpha-invariant and metadata)
  let direct_breakdown =
    compute_const_size_breakdown(&constant, &name, stt, &name_index);

  // BFS to collect all transitive dependencies
  let mut visited: HashSet<Address> = HashSet::new();
  let mut queue: VecDeque<Address> = VecDeque::new();
  let mut dep_breakdowns: Vec<(String, ConstSizeBreakdown)> = Vec::new();

  // Start with the constant's refs
  visited.insert(addr.clone());
  for dep_addr in &constant.refs {
    if !visited.contains(dep_addr) {
      queue.push_back(dep_addr.clone());
      visited.insert(dep_addr.clone());
    }
  }

  // BFS through all transitive dependencies
  while let Some(dep_addr) = queue.pop_front() {
    if let Some(dep_const) = stt.env.consts.get(&dep_addr) {
      // Get the name for this dependency (scan named entries)
      let dep_name_opt: Option<Name> = stt
        .env
        .named
        .iter()
        .find(|e| e.value().addr == dep_addr)
        .map(|e| e.key().clone());
      let dep_name_str = dep_name_opt
        .as_ref()
        .map_or_else(|| format!("{:.12}", dep_addr.hex()), |n| n.pretty());

      let breakdown = if let Some(ref dep_name) = dep_name_opt {
        compute_const_size_breakdown(&dep_const, dep_name, stt, &name_index)
      } else {
        ConstSizeBreakdown {
          alpha_size: serialized_const_size(&dep_const),
          meta_size: 0,
        }
      };

      dep_breakdowns.push((dep_name_str, breakdown));

      // Add this constant's refs to the queue
      for ref_addr in &dep_const.refs {
        if !visited.contains(ref_addr) {
          queue.push_back(ref_addr.clone());
          visited.insert(ref_addr.clone());
        }
      }
    }
  }

  // Sort by total size descending
  dep_breakdowns.sort_by(|a, b| b.1.total().cmp(&a.1.total()));

  let total_deps_alpha: usize =
    dep_breakdowns.iter().map(|(_, b)| b.alpha_size).sum();
  let total_deps_meta: usize =
    dep_breakdowns.iter().map(|(_, b)| b.meta_size).sum();
  let total_deps_size = total_deps_alpha + total_deps_meta;

  let total_alpha = direct_breakdown.alpha_size + total_deps_alpha;
  let total_meta = direct_breakdown.meta_size + total_deps_meta;
  let total_size = total_alpha + total_meta;

  println!("\n=== Size analysis for {} ===", name_str);
  println!(
    "  Direct alpha-invariant size: {} bytes",
    direct_breakdown.alpha_size
  );
  println!("  Direct metadata size: {} bytes", direct_breakdown.meta_size);
  println!("  Direct total size: {} bytes", direct_breakdown.total());
  println!();
  println!("  Transitive dependencies: {} constants", dep_breakdowns.len());
  println!(
    "  Dependencies alpha-invariant: {} bytes ({:.2} KB)",
    total_deps_alpha,
    total_deps_alpha as f64 / 1024.0
  );
  println!(
    "  Dependencies metadata: {} bytes ({:.2} KB)",
    total_deps_meta,
    total_deps_meta as f64 / 1024.0
  );
  println!(
    "  Dependencies total: {} bytes ({:.2} KB)",
    total_deps_size,
    total_deps_size as f64 / 1024.0
  );
  println!();
  println!(
    "  TOTAL alpha-invariant: {} bytes ({:.2} KB)",
    total_alpha,
    total_alpha as f64 / 1024.0
  );
  println!(
    "  TOTAL metadata: {} bytes ({:.2} KB)",
    total_meta,
    total_meta as f64 / 1024.0
  );
  println!(
    "  TOTAL size: {} bytes ({:.2} KB)",
    total_size,
    total_size as f64 / 1024.0
  );

  // Show top 10 largest dependencies
  if !dep_breakdowns.is_empty() {
    println!("\n  Top 10 largest dependencies (by total size):");
    for (name, breakdown) in dep_breakdowns.iter().take(10) {
      println!(
        "    {} bytes (alpha: {}, meta: {}): {}",
        breakdown.total(),
        breakdown.alpha_size,
        breakdown.meta_size,
        name
      );
    }
  }
}

/// Build a name index for metadata serialization.
#[cfg(feature = "test-ffi")]
fn build_name_index(
  stt: &crate::ix::compile::CompileState,
) -> crate::ix::ixon::metadata::NameIndex {
  use crate::ix::address::Address;
  use crate::ix::ixon::metadata::NameIndex;

  let mut idx = NameIndex::new();
  let mut counter: u64 = 0;

  // Add all names from the names map
  for entry in stt.env.names.iter() {
    idx.insert(entry.key().clone(), counter);
    counter += 1;
  }

  // Add anonymous name
  let anon_addr = Address::from_blake3_hash(*Name::anon().get_hash());
  idx.entry(anon_addr).or_insert(counter);

  idx
}

/// Compute size breakdown for a constant (alpha-invariant vs metadata).
#[cfg(feature = "test-ffi")]
fn compute_const_size_breakdown(
  constant: &crate::ix::ixon::constant::Constant,
  name: &Name,
  stt: &crate::ix::compile::CompileState,
  name_index: &crate::ix::ixon::metadata::NameIndex,
) -> ConstSizeBreakdown {
  // Alpha-invariant size
  let alpha_size = serialized_const_size(constant);

  // Metadata size
  let meta_size = if let Some(named) = stt.env.named.get(name) {
    serialized_meta_size(&named.meta, name_index)
  } else {
    0
  };

  ConstSizeBreakdown { alpha_size, meta_size }
}

/// Compute the serialized size of constant metadata.
#[cfg(feature = "test-ffi")]
fn serialized_meta_size(
  meta: &crate::ix::ixon::metadata::ConstantMeta,
  name_index: &crate::ix::ixon::metadata::NameIndex,
) -> usize {
  let mut buf = Vec::new();
  meta
    .put_indexed(name_index, &mut buf)
    .expect("metadata serialization failed");
  buf.len()
}

/// Parse a dotted name string into a Name.
#[cfg(feature = "test-ffi")]
fn parse_name(s: &str) -> Name {
  let parts: Vec<&str> = s.split('.').collect();
  let mut name = Name::anon();
  for part in parts {
    name = Name::str(name, part.to_string());
  }
  name
}

/// Compute the serialized size of a constant.
#[cfg(feature = "test-ffi")]
fn serialized_const_size(
  constant: &crate::ix::ixon::constant::Constant,
) -> usize {
  let mut buf = Vec::new();
  constant.put(&mut buf);
  buf.len()
}

/// Analyze block size statistics: hash-consing vs serialization.
#[cfg(feature = "test-ffi")]
fn analyze_block_size_stats(stt: &crate::ix::compile::CompileState) {
  use crate::ix::compile::BlockSizeStats;

  // Check if hash-consed size tracking was enabled
  let tracking_enabled = crate::ix::compile::TRACK_HASH_CONSED_SIZE
    .load(std::sync::atomic::Ordering::Relaxed);
  if !tracking_enabled {
    println!("\n=== Block Size Analysis ===");
    println!(
      "  Hash-consed size tracking disabled (set IX_TRACK_HASH_CONSED=1 to enable)"
    );
    return;
  }

  // Collect all stats into a vector for analysis
  let stats: Vec<(String, BlockSizeStats)> = stt
    .block_stats
    .iter()
    .map(|entry| (entry.key().pretty(), entry.value().clone()))
    .collect();

  if stats.is_empty() {
    println!("\n=== Block Size Analysis ===");
    println!("  No block statistics collected");
    return;
  }

  // Compute totals
  let total_hash_consed: usize =
    stats.iter().map(|(_, s)| s.hash_consed_size).sum();
  let total_serialized: usize =
    stats.iter().map(|(_, s)| s.serialized_size).sum();
  let total_blocks = stats.len();
  let total_consts: usize = stats.iter().map(|(_, s)| s.const_count).sum();

  // Compute per-block overhead (serialized - hash_consed)
  let mut overheads: Vec<(String, isize, f64, usize)> = stats
    .iter()
    .map(|(name, s)| {
      let overhead = s.serialized_size as isize - s.hash_consed_size as isize;
      let ratio = if s.hash_consed_size > 0 {
        s.serialized_size as f64 / s.hash_consed_size as f64
      } else {
        1.0
      };
      (name.clone(), overhead, ratio, s.const_count)
    })
    .collect();

  // Sort by overhead descending (most bloated first)
  overheads.sort_by(|a, b| b.1.cmp(&a.1));

  // Compute statistics
  let avg_ratio = if total_hash_consed > 0 {
    total_serialized as f64 / total_hash_consed as f64
  } else {
    1.0
  };

  // Find blocks with worst ratio (only for blocks with >100 bytes hash-consed)
  let mut ratios: Vec<_> = stats
    .iter()
    .filter(|(_, s)| s.hash_consed_size > 100)
    .map(|(name, s)| {
      let ratio = s.serialized_size as f64 / s.hash_consed_size as f64;
      (name.clone(), ratio, s.hash_consed_size, s.serialized_size)
    })
    .collect();
  ratios
    .sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));

  println!("\n=== Block Size Analysis (Hash-Consing vs Serialization) ===");
  println!("  Total blocks: {}", total_blocks);
  println!("  Total constants: {}", total_consts);
  println!();
  println!(
    "  Total hash-consed size: {} bytes ({:.2} KB)",
    total_hash_consed,
    total_hash_consed as f64 / 1024.0
  );
  println!(
    "  Total serialized size:  {} bytes ({:.2} KB)",
    total_serialized,
    total_serialized as f64 / 1024.0
  );
  println!("  Overall ratio: {:.3}x", avg_ratio);
  println!(
    "  Total overhead: {} bytes ({:.2} KB)",
    total_serialized as isize - total_hash_consed as isize,
    (total_serialized as f64 - total_hash_consed as f64) / 1024.0
  );

  // Distribution of ratios (more granular buckets for analysis)
  let count_in_range = |lo: f64, hi: f64| -> usize {
    stats
      .iter()
      .filter(|(_, s)| {
        if s.hash_consed_size == 0 {
          return false;
        }
        let r = s.serialized_size as f64 / s.hash_consed_size as f64;
        r >= lo && r < hi
      })
      .count()
  };

  let ratio_under_0_05 = count_in_range(0.0, 0.05);
  let ratio_0_05_to_0_1 = count_in_range(0.05, 0.1);
  let ratio_0_1_to_0_2 = count_in_range(0.1, 0.2);
  let ratio_0_2_to_0_5 = count_in_range(0.2, 0.5);
  let ratio_0_5_to_1 = count_in_range(0.5, 1.0);
  let ratio_1_to_1_5 = count_in_range(1.0, 1.5);
  let ratio_1_5_to_2 = count_in_range(1.5, 2.0);
  let ratio_over_2 = count_in_range(2.0, f64::INFINITY);

  println!();
  println!("  Ratio distribution (serialized / hash-consed):");
  println!("    < 0.05x (20x+ compression): {} blocks", ratio_under_0_05);
  println!("    0.05-0.1x (10-20x):         {} blocks", ratio_0_05_to_0_1);
  println!("    0.1-0.2x (5-10x):           {} blocks", ratio_0_1_to_0_2);
  println!("    0.2-0.5x (2-5x):            {} blocks", ratio_0_2_to_0_5);
  println!("    0.5-1.0x (1-2x):            {} blocks", ratio_0_5_to_1);
  println!("    1.0-1.5x (slight bloat):    {} blocks", ratio_1_to_1_5);
  println!("    1.5-2.0x:                   {} blocks", ratio_1_5_to_2);
  println!("    >= 2.0x (high bloat):       {} blocks", ratio_over_2);

  // Top 10 blocks by absolute overhead
  if !overheads.is_empty() {
    println!();
    println!("  Top 10 blocks by overhead (serialized - hash_consed):");
    for (name, overhead, ratio, const_count) in overheads.iter().take(10) {
      println!(
        "    {:+} bytes ({:.2}x, {} consts): {}",
        overhead,
        ratio,
        const_count,
        truncate_name(name, 50)
      );
    }
  }

  // Top 10 blocks by worst ratio (with >100 bytes)
  if !ratios.is_empty() {
    println!();
    println!("  Top 10 blocks by ratio (hash-consed > 100 bytes):");
    for (name, ratio, hc, ser) in ratios.iter().take(10) {
      println!(
        "    {:.2}x ({} -> {} bytes): {}",
        ratio,
        hc,
        ser,
        truncate_name(name, 50)
      );
    }
  }

  // Bottom 10 blocks by ratio (best compression)
  let mut best_ratios: Vec<_> = stats
    .iter()
    .filter(|(_, s)| s.hash_consed_size > 100)
    .map(|(name, s)| {
      let ratio = s.serialized_size as f64 / s.hash_consed_size as f64;
      (name.clone(), ratio, s.hash_consed_size, s.serialized_size)
    })
    .collect();
  best_ratios
    .sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal));

  if !best_ratios.is_empty() {
    println!();
    println!("  Top 10 blocks by best ratio (most efficient):");
    for (name, ratio, hc, ser) in best_ratios.iter().take(10) {
      println!(
        "    {:.2}x ({} -> {} bytes): {}",
        ratio,
        hc,
        ser,
        truncate_name(name, 50)
      );
    }
  }
}

/// Truncate a name for display.
#[cfg(feature = "test-ffi")]
fn truncate_name(name: &str, max_len: usize) -> String {
  if name.len() <= max_len {
    name.to_string()
  } else {
    format!("...{}", &name[name.len() - max_len + 3..])
  }
}
