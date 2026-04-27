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

use crate::ix::compile::{CompileOptions, compile_env_with_options};
use crate::ix::decompile::{check_decompile, decompile_env};
use std::sync::Arc;

use lean_ffi::nat::Nat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanList, LeanRef, LeanShared,
};

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

/// Decode an `@& Array Lean.Name` FFI argument into a `Vec<Name>`.
///
/// Uses a fresh `GlobalCache` to deduplicate shared sub-names within the
/// array (the cache keys by pointer identity, so repeat prefixes like
/// `Lean.Meta.Grind.Arith.Cutsat` are decoded once). Callers don't need
/// to manage the cache; it's dropped when this function returns.
///
/// Preferred over going through `String` + `parse_name` at the FFI
/// boundary: Lean's `Name.toString` adds `«»` escaping for components
/// that aren't valid identifiers, and the resulting string doesn't
/// round-trip through a naive split-on-`.` parser. By decoding the
/// structured `Lean.Name` directly we match the kernel's stored `Name`s
/// exactly (same component strings, same content hash).
pub fn decode_name_array(arr: &LeanArray<LeanBorrowed<'_>>) -> Vec<Name> {
  let global = GlobalCache::new();
  arr.map(|obj| decode_name(obj, &global))
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
  let stt = match compile_env_with_options(
    &env,
    CompileOptions { check_originals: false, ..Default::default() },
  ) {
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

  // Phase 1b: Aux_gen congruence (full env)
  eprintln!("[rust-compile] Phase 1b: Checking aux_gen congruence...");
  {
    use crate::ix::compile::aux_gen::{self, PatchedConstant};
    use crate::ix::congruence::const_alpha_eq;
    use crate::ix::env::{
      ConstantInfo as LeanCI, ConstantVal as LeanCV, DefinitionSafety,
      DefinitionVal, InductiveVal, ReducibilityHints,
    };
    use rustc_hash::{FxHashMap, FxHashSet};

    // Build per-block PermCtx for the permutation-aware comparator.
    // Mirrors `build_perm_ctx` in `rs_compile_validate_aux` below; kept
    // as a local fn here so the `#[cfg(feature = "test-ffi")]` path
    // doesn't escape its scope.
    fn build_perm_ctx_1b(
      all: &[Name],
      env: &Env,
      stt: &crate::ix::compile::CompileState,
      perm: &[usize],
    ) -> Option<crate::ix::congruence::perm::PermCtx> {
      use crate::ix::congruence::perm::{PermCtx, RecHeadInfo, RecHeadKind};
      use crate::ix::env::{ConstantInfo as LeanCI, ExprData};

      let first = all.first()?;
      let n_params = match env.get(first) {
        Some(LeanCI::InductInfo(v)) => {
          v.num_params.to_u64().unwrap_or(0) as usize
        },
        _ => return None,
      };
      let n_primary = all.len();
      let primary_ctor_counts: Vec<usize> = all
        .iter()
        .map(|n| match env.get(n) {
          Some(LeanCI::InductInfo(v)) => v.ctors.len(),
          _ => 0,
        })
        .collect();
      let source_aux_order = match aux_gen::nested::source_aux_order(all, env) {
        Ok(order) => order,
        Err(_) => return None,
      };
      let source_aux_ctor_counts: Vec<usize> = source_aux_order
        .iter()
        .map(|(head, _)| match env.get(head) {
          Some(LeanCI::InductInfo(v)) => v.ctors.len(),
          _ => 0,
        })
        .collect();
      let n_motives = n_primary + source_aux_ctor_counts.len();
      let n_minors: usize = primary_ctor_counts.iter().sum::<usize>()
        + source_aux_ctor_counts.iter().sum::<usize>();

      let mut rec_heads: FxHashMap<Name, RecHeadInfo> = FxHashMap::default();
      let mk_info = |kind: RecHeadKind, n_indices: usize| RecHeadInfo {
        kind,
        n_params,
        n_motives,
        n_minors: match kind {
          RecHeadKind::Rec => n_minors,
          _ => 0,
        },
        n_indices,
        primary_ctor_counts: primary_ctor_counts.clone(),
        source_aux_ctor_counts: source_aux_ctor_counts.clone(),
        aux_perm: perm.to_vec(),
      };
      let n_indices_for = |rec_name: &Name| match env.get(rec_name) {
        Some(LeanCI::RecInfo(r)) => {
          r.num_indices.to_u64().unwrap_or(0) as usize
        },
        _ => 0,
      };
      for member in all {
        let rec_name = Name::str(member.clone(), "rec".to_string());
        let ni = n_indices_for(&rec_name);
        rec_heads.insert(rec_name, mk_info(RecHeadKind::Rec, ni));
        let below_name = Name::str(member.clone(), "below".to_string());
        rec_heads.insert(below_name, mk_info(RecHeadKind::Below, ni));
        let brecon_name = Name::str(member.clone(), "brecOn".to_string());
        rec_heads.insert(brecon_name.clone(), mk_info(RecHeadKind::BRecOn, ni));
        rec_heads.insert(
          Name::str(brecon_name.clone(), "go".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
        rec_heads.insert(
          Name::str(brecon_name, "eq".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
      }
      for source_j in 0..source_aux_ctor_counts.len() {
        let idx = source_j + 1;
        let rec_name = Name::str(first.clone(), format!("rec_{idx}"));
        let ni = n_indices_for(&rec_name);
        rec_heads.insert(rec_name, mk_info(RecHeadKind::Rec, ni));
        let below_name = Name::str(first.clone(), format!("below_{idx}"));
        rec_heads.insert(below_name, mk_info(RecHeadKind::Below, ni));
        let brecon_name = Name::str(first.clone(), format!("brecOn_{idx}"));
        rec_heads.insert(brecon_name.clone(), mk_info(RecHeadKind::BRecOn, ni));
        rec_heads.insert(
          Name::str(brecon_name.clone(), "go".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
        rec_heads.insert(
          Name::str(brecon_name, "eq".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
      }

      let mut const_addr: FxHashMap<Name, crate::ix::address::Address> =
        FxHashMap::default();
      let mut add_addr = |name: &Name| {
        if let Some(addr) = stt.resolve_addr(name) {
          const_addr.insert(name.clone(), addr);
        }
      };
      for member in all {
        add_addr(member);
        for suffix in ["rec", "casesOn", "recOn", "below", "brecOn"] {
          add_addr(&Name::str(member.clone(), suffix.to_string()));
        }
        if let Some(LeanCI::InductInfo(v)) = env.get(member) {
          for ctor in &v.ctors {
            add_addr(ctor);
          }
        }
      }
      for source_j in 0..source_aux_order.len() {
        let idx = source_j + 1;
        for suffix in [
          format!("rec_{idx}"),
          format!("below_{idx}"),
          format!("brecOn_{idx}"),
        ] {
          let name = Name::str(first.clone(), suffix);
          add_addr(&name);
          add_addr(&Name::str(name.clone(), "go".to_string()));
          add_addr(&Name::str(name, "eq".to_string()));
        }
      }
      fn collect_const_addrs(
        e: &Expr,
        stt: &crate::ix::compile::CompileState,
        out: &mut FxHashMap<Name, crate::ix::address::Address>,
      ) {
        match e.as_data() {
          ExprData::Const(n, _, _) => {
            if let Some(addr) = stt.resolve_addr(n) {
              out.insert(n.clone(), addr);
            }
          },
          ExprData::App(f, a, _) => {
            collect_const_addrs(f, stt, out);
            collect_const_addrs(a, stt, out);
          },
          ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
            collect_const_addrs(t, stt, out);
            collect_const_addrs(b, stt, out);
          },
          ExprData::LetE(_, t, v, b, _, _) => {
            collect_const_addrs(t, stt, out);
            collect_const_addrs(v, stt, out);
            collect_const_addrs(b, stt, out);
          },
          ExprData::Proj(n, _, v, _) => {
            if let Some(addr) = stt.resolve_addr(n) {
              out.insert(n.clone(), addr);
            }
            collect_const_addrs(v, stt, out);
          },
          ExprData::Mdata(_, v, _) => collect_const_addrs(v, stt, out),
          _ => {},
        }
      }
      for (_head, specs) in &source_aux_order {
        for spec in specs {
          collect_const_addrs(spec, stt, &mut const_addr);
        }
      }

      Some(PermCtx {
        aux_perm: perm.to_vec(),
        n_params,
        n_primary,
        primary_ctor_counts,
        source_aux_ctor_counts,
        const_map: FxHashMap::default(),
        const_addr,
        rec_heads,
      })
    }

    let t_cong = std::time::Instant::now();
    let mut n_pass = 0usize;
    let mut n_fail = 0usize;
    let mut seen_blocks: FxHashSet<Vec<Name>> = FxHashSet::default();

    for (name, ci) in env.iter() {
      let all = match ci {
        LeanCI::InductInfo(v) => &v.all,
        _ => continue,
      };
      if all.first() != Some(name) {
        continue;
      }
      let mut key: Vec<Name> = all.clone();
      key.sort();
      if !seen_blocks.insert(key) {
        continue;
      }

      let original_classes: Vec<Vec<Name>> =
        all.iter().map(|n| vec![n.clone()]).collect();
      // We only need the `all` list for aux_gen now; MutConsts are no
      // longer required at this call site. Still verify the block has at
      // least one ingress-able inductive so we don't waste work on
      // broken envs.
      let has_indc =
        all.iter().any(|n| matches!(env.get(n), Some(LeanCI::InductInfo(_))));
      if !has_indc {
        continue;
      }

      let orig_aux_out = match aux_gen::generate_aux_patches(
        &original_classes,
        all.as_slice(),
        &env,
        &stt,
        &stt.kctx,
      ) {
        Ok(p) => p,
        Err(e) => {
          eprintln!(
            "[rust-compile] aux_gen congruence: {}: generate failed: {e}",
            name.pretty()
          );
          n_fail += 1;
          continue;
        },
      };
      let orig_patches = &orig_aux_out.patches;

      // Build per-block PermCtx so Lean's source-order originals can
      // be compared against aux_gen's canonical hash-sorted layout via
      // the permutation-aware comparator. No-op (None) when the perm
      // is absent or empty. See `build_phase2_perm_ctx` below (in
      // `rs_compile_validate_aux`) for the full builder; the
      // `#[cfg(feature = "test-ffi")]` Phase 1b path here uses a
      // local copy with the same logic.
      let perm_ctx_1b: Option<crate::ix::congruence::perm::PermCtx> =
        match &orig_aux_out.perm {
          Some(perm) if !perm.is_empty() => {
            build_perm_ctx_1b(all, &env, &stt, perm)
          },
          _ => None,
        };

      for (patch_name, patch) in orig_patches.iter() {
        let gen_ci = match patch {
          PatchedConstant::Rec(r) => LeanCI::RecInfo(r.clone()),
          PatchedConstant::CasesOn(d) | PatchedConstant::RecOn(d) => {
            LeanCI::DefnInfo(DefinitionVal {
              cnst: LeanCV {
                name: d.name.clone(),
                level_params: d.level_params.clone(),
                typ: d.typ.clone(),
              },
              value: d.value.clone(),
              hints: ReducibilityHints::Abbrev,
              safety: DefinitionSafety::Safe,
              all: vec![],
            })
          },
          PatchedConstant::BelowDef(d) => LeanCI::DefnInfo(DefinitionVal {
            cnst: LeanCV {
              name: d.name.clone(),
              level_params: d.level_params.clone(),
              typ: d.typ.clone(),
            },
            value: d.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          }),
          PatchedConstant::BRecOn(d) => LeanCI::DefnInfo(DefinitionVal {
            cnst: LeanCV {
              name: d.name.clone(),
              level_params: d.level_params.clone(),
              typ: d.typ.clone(),
            },
            value: d.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          }),
          PatchedConstant::BelowIndc(bi) => LeanCI::InductInfo(InductiveVal {
            cnst: LeanCV {
              name: bi.name.clone(),
              level_params: bi.level_params.clone(),
              typ: bi.typ.clone(),
            },
            num_params: Nat::from(bi.n_params as u64),
            num_indices: Nat::from(bi.n_indices as u64),
            all: vec![bi.name.clone()],
            ctors: bi.ctors.iter().map(|c| c.name.clone()).collect(),
            num_nested: Nat::from(0u64),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: bi.is_reflexive,
          }),
        };
        let Some(orig_ci_ref) = env.get(patch_name) else {
          continue;
        };
        let orig_ci: &LeanCI = orig_ci_ref;
        let eq_result = match &perm_ctx_1b {
          Some(ctx) => crate::ix::congruence::perm::const_alpha_eq_with_perm(
            &gen_ci, orig_ci, ctx,
          ),
          None => const_alpha_eq(&gen_ci, orig_ci),
        };
        match eq_result {
          Ok(()) => n_pass += 1,
          Err(e) => {
            eprintln!(
              "[rust-compile] aux_gen congruence: {}: {e}",
              patch_name.pretty()
            );
            // On first failure for a given inductive block, dump the
            // full generated + original value for manual inspection.
            if std::env::var("IX_CONGRUENCE_DUMP").is_ok() {
              let name_match =
                std::env::var("IX_CONGRUENCE_DUMP").ok().filter(|s| s != "1");
              let should_dump = match &name_match {
                Some(target) => patch_name.pretty().contains(target.as_str()),
                None => true,
              };
              if should_dump {
                eprintln!(
                  "  === generated type ===\n  {}\n  === original type ===\n  {}",
                  gen_ci.get_type().pretty(),
                  orig_ci.get_type().pretty(),
                );
                let gen_val_str = match &gen_ci {
                  LeanCI::DefnInfo(d) => d.value.pretty(),
                  LeanCI::ThmInfo(t) => t.value.pretty(),
                  LeanCI::RecInfo(r) => format!(
                    "<rec with {} rules>\n  rule[0].rhs: {}",
                    r.rules.len(),
                    r.rules.first().map(|x| x.rhs.pretty()).unwrap_or_default()
                  ),
                  _ => "<no value>".into(),
                };
                let orig_val_str = match orig_ci {
                  LeanCI::DefnInfo(d) => d.value.pretty(),
                  LeanCI::ThmInfo(t) => t.value.pretty(),
                  LeanCI::RecInfo(r) => format!(
                    "<rec with {} rules>\n  rule[0].rhs: {}",
                    r.rules.len(),
                    r.rules.first().map(|x| x.rhs.pretty()).unwrap_or_default()
                  ),
                  _ => "<no value>".into(),
                };
                eprintln!(
                  "  === generated value ===\n  {gen_val_str}\n  === original value ===\n  {orig_val_str}"
                );
              }
            }
            n_fail += 1;
          },
        }
      }
    }
    eprintln!(
      "[rust-compile] Phase 1b done in {:.2}s: {} pass, {} fail",
      t_cong.elapsed().as_secs_f32(),
      n_pass,
      n_fail,
    );
    if n_fail > 0 {
      eprintln!(
        "[rust-compile] Phase 1b FAILED: {n_fail} aux_gen congruence failures"
      );
      return n;
    }
  }

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

const VALIDATE_PREFIX: &str = "[validate-aux]";

/// Per-phase result accumulator.
struct PhaseResult {
  name: &'static str,
  pass: usize,
  fail: usize,
  failures: Vec<String>,
}

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

/// Comprehensive 8-phase validation of the aux_gen compile pipeline.
///
/// Available in the main `ix` binary (unlike the other `#[cfg(feature =
/// "test-ffi")]` helpers in this file) because `ix validate --path <file>`
/// uses it to run the full compile → decompile → roundtrip → nested-detect
/// pipeline on arbitrary Lean files. The `validate-aux` test suite in
/// `Tests/Ix/Compile/ValidateAux.lean` also calls this FFI via
/// `ix_rs_test`, but it's not gated on test-ffi any more — same function,
/// same binary entry point, just two callers.
///
/// Returns total failure count across all phases.
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
  let mut p1 = PhaseResult::new("1. Compilation");
  println!("{VALIDATE_PREFIX} phase 1: compiling...");
  let t0 = std::time::Instant::now();
  // `stt` is `mut` so Phase 7 can `std::mem::take(&mut stt.env)` to extract
  // the Ixon env for serialization while freeing the rest of the state
  // (kctx, name_to_addr, etc.) before serialize allocates a 3 GB buffer.
  let mut stt =
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      compile_env_with_options(
        &env,
        CompileOptions { check_originals: false, ..Default::default() },
      )
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

  // Parallel scan of all 707k+ constants against `stt`. Each check is an
  // independent pair of DashMap lookups (`ungrounded.contains_key` +
  // `resolve_addr`), so `env.par_iter()` over the FxHashMap is safe and
  // dramatically faster than a serial walk on Mathlib-scale inputs.
  {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let passes = AtomicUsize::new(0);
    let fails = AtomicUsize::new(0);
    let fail_msgs: Mutex<Vec<String>> = Mutex::new(Vec::new());

    env.par_iter().for_each(|(name, _)| {
      if stt.ungrounded.contains_key(name) {
        return;
      }
      if stt.resolve_addr(name).is_some() {
        passes.fetch_add(1, Ordering::Relaxed);
      } else {
        fails.fetch_add(1, Ordering::Relaxed);
        let mut msgs = fail_msgs.lock().unwrap();
        if msgs.len() < 20 {
          msgs.push(format!("{}: not compiled", name.pretty()));
        }
      }
    });

    p1.pass = passes.load(Ordering::Relaxed);
    p1.fail = fails.load(Ordering::Relaxed);
    p1.failures = fail_msgs.into_inner().unwrap();
  }
  p1.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 2: Aux_gen congruence (post-compilation, uses real CompileState)
  // ══════════════════════════════════════════════════════════════════════
  //
  // Structure: three passes.
  //   1. Serial — collect unique blocks (dedup by sorted `.all` names) and
  //      build `MutConst` values eagerly. Can't parallelize: the env iter
  //      is serial and the dedup set needs cross-iteration visibility.
  //   2. Serial — pre-ingress each block's transitive ctor-field deps into
  //      the shared `p2_kctx`. Serial because the visited set
  //      (`p2_ingressed`) is shared across blocks, and we want each name
  //      processed at most once (idempotent but wasteful in parallel).
  //   3. Parallel — for each block, run `generate_aux_patches` + per-patch
  //      `const_alpha_eq` against Lean's original. Independent across
  //      blocks, and the shared `p2_kctx` is internally DashMap-based so
  //      concurrent reads+writes are safe. Per-block results are collected
  //      into a `Vec<BlockResult>` and aggregated into `p2` serially
  //      afterward.
  let mut p2 = PhaseResult::new("2. Aux_gen congruence");
  println!("{VALIDATE_PREFIX} phase 2: checking aux_gen congruence...");
  {
    use crate::ix::compile::aux_gen::{self, PatchedConstant, expr_utils};
    use crate::ix::compile::{KernelCtx, mk_indc};
    use crate::ix::env::ConstantInfo as LeanCI;
    use crate::ix::mutual::MutConst;

    // Ephemeral kernel context for original-structure congruence testing.
    // Shared across all blocks (accumulates inductives incrementally).
    let p2_kctx = KernelCtx::new();
    expr_utils::ensure_prelude_in_kenv_of(&stt, &p2_kctx);

    // ── Pass 1: collect unique work items ─────────────────────────────
    // Dedup by sorted `.all` names so mutually-recursive blocks aren't
    // processed once per member.
    let mut seen_blocks: FxHashSet<Vec<Name>> = FxHashSet::default();
    let work: Vec<(Name, Vec<Name>, Vec<MutConst>)> = env
      .iter()
      .filter_map(|(name, ci)| {
        let all = match ci {
          LeanCI::InductInfo(v) => v.all.clone(),
          _ => return None,
        };
        if all.first() != Some(name) {
          return None;
        }
        let mut key = all.clone();
        key.sort();
        if !seen_blocks.insert(key) {
          return None;
        }
        let original_cs: Vec<MutConst> = all
          .iter()
          .filter_map(|n| match env.get(n) {
            Some(LeanCI::InductInfo(v)) => {
              Some(MutConst::Indc(mk_indc(v, &env).ok()?))
            },
            _ => None,
          })
          .collect();
        if original_cs.is_empty() {
          return None;
        }
        Some((name.clone(), all, original_cs))
      })
      .collect();
    drop(seen_blocks);
    println!(
      "{VALIDATE_PREFIX} phase 2: {} unique blocks to validate",
      work.len()
    );

    // ── Pass 2: serial pre-ingress ────────────────────────────────────
    // Transitive-ingress bookkeeping shared across all blocks.
    //
    // `.below` / `.brecOn` generation calls `TcScope::get_level` on RESTORED
    // field domains — i.e., field types that contain the original external
    // inductive heads (`StrictOrLazy`, `WithRpcRef`, `Do.Alt`, ...) rather
    // than the `_nested.X_N` auxiliaries used inside the recursor overlay.
    // Sort inference therefore needs those externals in kenv, but nothing
    // in `generate_aux_patches` adds them (the in-recursor
    // `ingress_field_deps` walks the overlay — it only sees the synthetic
    // aux names). Without this ingress, blocks whose ctors mention
    // externals that don't appear in any simpler block's dep graph (e.g.,
    // `Lean.Widget.MsgEmbed`, `Lean.Elab.Term.Do.Code`) fail Phase 2 with
    // "unknown constant".
    //
    // This pass MUST precede Pass 3 (parallel aux_gen) because aux_gen's
    // sort-inference reads `p2_kctx` without any synchronization point;
    // we can't interleave ingress with aux_gen under parallelism without
    // introducing races (even though individual DashMap inserts are safe,
    // a reader may observe a partially-ingressed kctx and fail).
    {
      use crate::ix::graph::get_constant_info_references;
      // Step A (serial): enumerate the transitive-closure of names to
      // ingress. BFS walking the env hashmap is cheap — the per-node cost
      // is a lookup and a ref-walk, dwarfed by Step B's actual ingress.
      // Keeping enumeration serial means dedup via a plain FxHashSet, and
      // the resulting Vec is used as a parallel work queue in Step B.
      let mut p2_ingressed: FxHashSet<Name> = FxHashSet::default();
      let mut p2_names: Vec<Name> = Vec::new();
      for (_, all, _) in &work {
        let mut stack: Vec<Name> = all.clone();
        while let Some(name) = stack.pop() {
          if !p2_ingressed.insert(name.clone()) {
            continue;
          }
          if let Some(ci) = env.get(&name) {
            for ref_name in get_constant_info_references(ci) {
              if !p2_ingressed.contains(&ref_name) {
                stack.push(ref_name);
              }
            }
          }
          p2_names.push(name);
        }
      }
      drop(p2_ingressed);

      // Step B (parallel): each `ensure_in_kenv_of` is idempotent and the
      // shared `p2_kctx.kenv` is DashMap-backed, so concurrent ingress of
      // distinct names is safe. Names already visited in Step A are
      // deduplicated, so there's no redundant work here beyond the
      // internal `kctx.kenv.get(&zid).is_some()` early-exit guard.
      p2_names.par_iter().for_each(|name| {
        expr_utils::ensure_in_kenv_of(name, &env, &stt, &p2_kctx);
      });
    }

    // ── Pass 3: parallel aux_gen + alpha-equivalence check ────────────
    // Per-block result accumulator. Each block reports passes, an optional
    // `generate_aux_patches` error, and a list of per-patch alpha-eq
    // failure messages. Aggregation into `p2` happens serially after the
    // parallel map completes, so `PhaseResult` itself never crosses
    // thread boundaries.
    #[derive(Default)]
    struct BlockResult {
      passes: usize,
      generate_error: Option<String>,
      failures: Vec<String>,
    }

    // Build a `PermCtx` for the block: the congruence comparator uses
    // it to walk gen vs orig in lockstep with permutation awareness.
    // See `crate::ix::congruence::perm` for details.
    //
    // `n_primary = all.len()` because Phase 2 uses singleton classes
    // (one class per original, no alpha-collapse at the primary level).
    fn build_perm_ctx(
      all: &[Name],
      env: &Env,
      stt: &crate::ix::compile::CompileState,
      perm: &[usize],
    ) -> Option<crate::ix::congruence::perm::PermCtx> {
      use crate::ix::congruence::perm::{PermCtx, RecHeadInfo};
      use crate::ix::env::ConstantInfo as LeanCI;
      use rustc_hash::FxHashMap;

      let first = all.first()?;
      let n_params = match env.get(first) {
        Some(LeanCI::InductInfo(v)) => {
          v.num_params.to_u64().unwrap_or(0) as usize
        },
        _ => return None,
      };
      let n_primary = all.len();
      let primary_ctor_counts: Vec<usize> = all
        .iter()
        .map(|n| match env.get(n) {
          Some(LeanCI::InductInfo(v)) => v.ctors.len(),
          _ => 0,
        })
        .collect();
      // Source-walk aux discovery: same walker `compute_aux_perm` uses.
      let source_aux_order = match aux_gen::nested::source_aux_order(all, env) {
        Ok(order) => order,
        Err(_) => return None,
      };
      let source_aux_ctor_counts: Vec<usize> = source_aux_order
        .iter()
        .map(|(head, _)| match env.get(head) {
          Some(LeanCI::InductInfo(v)) => v.ctors.len(),
          _ => 0,
        })
        .collect();

      // Build rec_heads for every permutation-sensitive head in the
      // block. The comparator uses these to recognize App-spine
      // permutation opportunities at internal references (e.g., an
      // inner `@A.rec` inside a `.casesOn` body, or an `A.below`
      // applied inside `A.brecOn_N`'s type).
      //
      // Covered heads:
      // - Primary `.rec`   (kind = Rec)     — `{name}.rec`
      // - Aux     `.rec_N` (kind = Rec)     — `{first}.rec_{N}`
      // - Primary `.below` (kind = Below)   — `{name}.below`
      // - Aux     `.below_N` (kind = Below) — `{first}.below_{N}`
      // - Primary `.brecOn`/.go/.eq (kind = BRecOn)
      // - Aux     `.brecOn_N`/.go/.eq (kind = BRecOn)
      use crate::ix::congruence::perm::RecHeadKind;
      let n_motives = n_primary + source_aux_ctor_counts.len();
      let n_minors: usize = primary_ctor_counts.iter().sum::<usize>()
        + source_aux_ctor_counts.iter().sum::<usize>();
      let mut rec_heads: FxHashMap<Name, RecHeadInfo> = FxHashMap::default();
      let mk_info = |kind: RecHeadKind, n_indices: usize| RecHeadInfo {
        kind,
        n_params,
        n_motives,
        n_minors: match kind {
          RecHeadKind::Rec => n_minors,
          _ => 0,
        },
        n_indices,
        primary_ctor_counts: primary_ctor_counts.clone(),
        source_aux_ctor_counts: source_aux_ctor_counts.clone(),
        aux_perm: perm.to_vec(),
      };

      // Helper: look up `n_indices` for a specific recursor, falling
      // back to 0 when the rec isn't in env (e.g., if Lean didn't
      // generate it for this aux — the entry is benign in that case).
      let n_indices_for = |rec_name: &Name| match env.get(rec_name) {
        Some(LeanCI::RecInfo(r)) => {
          r.num_indices.to_u64().unwrap_or(0) as usize
        },
        _ => 0,
      };

      // Primary heads: .rec / .below / .brecOn / .brecOn.go / .brecOn.eq.
      for member in all {
        let rec_name = Name::str(member.clone(), "rec".to_string());
        let ni = n_indices_for(&rec_name);
        rec_heads.insert(rec_name, mk_info(RecHeadKind::Rec, ni));

        let below_name = Name::str(member.clone(), "below".to_string());
        rec_heads.insert(below_name, mk_info(RecHeadKind::Below, ni));

        let brecon_name = Name::str(member.clone(), "brecOn".to_string());
        rec_heads.insert(brecon_name.clone(), mk_info(RecHeadKind::BRecOn, ni));
        rec_heads.insert(
          Name::str(brecon_name.clone(), "go".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
        rec_heads.insert(
          Name::str(brecon_name, "eq".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
      }

      // Aux heads: hang off `first` (Lean's source-all[0]) with _N suffix.
      for source_j in 0..source_aux_ctor_counts.len() {
        let idx = source_j + 1;
        let rec_name = Name::str(first.clone(), format!("rec_{idx}"));
        let ni = n_indices_for(&rec_name);
        rec_heads.insert(rec_name, mk_info(RecHeadKind::Rec, ni));

        let below_name = Name::str(first.clone(), format!("below_{idx}"));
        rec_heads.insert(below_name, mk_info(RecHeadKind::Below, ni));

        let brecon_name = Name::str(first.clone(), format!("brecOn_{idx}"));
        rec_heads.insert(brecon_name.clone(), mk_info(RecHeadKind::BRecOn, ni));
        rec_heads.insert(
          Name::str(brecon_name.clone(), "go".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
        rec_heads.insert(
          Name::str(brecon_name, "eq".to_string()),
          mk_info(RecHeadKind::BRecOn, ni),
        );
      }

      // `const_map` is empty for Phase 2 (singleton classes).
      // Under singleton classes there's no primary alpha-collapse, so
      // no aliases to rewrite. Source vs canonical aux inductive names
      // also don't need remapping because `aux_gen::RestoreCtx::restore`
      // replaces `_nested.X_N` references in gen bodies with external
      // applications — the orig side's `_nested.*` names (if any) don't
      // appear in gen at all, and vice versa.
      //
      // This may need to grow when we extend to blocks that DO undergo
      // alpha-collapse (Phase 1b and beyond).
      let const_map: FxHashMap<Name, Name> = FxHashMap::default();
      let mut const_addr: FxHashMap<Name, crate::ix::address::Address> =
        FxHashMap::default();
      let mut add_addr = |name: &Name| {
        if let Some(addr) = stt.resolve_addr(name) {
          const_addr.insert(name.clone(), addr);
        }
      };
      for member in all {
        add_addr(member);
        for suffix in ["rec", "casesOn", "recOn", "below", "brecOn"] {
          add_addr(&Name::str(member.clone(), suffix.to_string()));
        }
        if let Some(LeanCI::InductInfo(v)) = env.get(member) {
          for ctor in &v.ctors {
            add_addr(ctor);
          }
        }
      }
      if let Some(first) = all.first() {
        for source_j in 0..source_aux_order.len() {
          let idx = source_j + 1;
          for suffix in [
            format!("rec_{idx}"),
            format!("below_{idx}"),
            format!("brecOn_{idx}"),
          ] {
            let name = Name::str(first.clone(), suffix);
            add_addr(&name);
            add_addr(&Name::str(name.clone(), "go".to_string()));
            add_addr(&Name::str(name, "eq".to_string()));
          }
        }
      }
      fn collect_const_addrs(
        e: &Expr,
        stt: &crate::ix::compile::CompileState,
        out: &mut FxHashMap<Name, crate::ix::address::Address>,
      ) {
        use crate::ix::env::ExprData;
        match e.as_data() {
          ExprData::Const(n, _, _) => {
            if let Some(addr) = stt.resolve_addr(n) {
              out.insert(n.clone(), addr);
            }
          },
          ExprData::App(f, a, _) => {
            collect_const_addrs(f, stt, out);
            collect_const_addrs(a, stt, out);
          },
          ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
            collect_const_addrs(t, stt, out);
            collect_const_addrs(b, stt, out);
          },
          ExprData::LetE(_, t, v, b, _, _) => {
            collect_const_addrs(t, stt, out);
            collect_const_addrs(v, stt, out);
            collect_const_addrs(b, stt, out);
          },
          ExprData::Proj(n, _, v, _) => {
            if let Some(addr) = stt.resolve_addr(n) {
              out.insert(n.clone(), addr);
            }
            collect_const_addrs(v, stt, out);
          },
          ExprData::Mdata(_, v, _) => collect_const_addrs(v, stt, out),
          _ => {},
        }
      }
      for (_head, specs) in &source_aux_order {
        for spec in specs {
          collect_const_addrs(spec, stt, &mut const_addr);
        }
      }

      Some(PermCtx {
        aux_perm: perm.to_vec(),
        n_params,
        n_primary,
        primary_ctor_counts,
        source_aux_ctor_counts,
        const_map,
        const_addr,
        rec_heads,
      })
    }

    // Helper to wrap a patch as a Lean `ConstantInfo` for alpha-eq.
    fn patch_to_lean_ci(patch: &PatchedConstant) -> Option<ConstantInfo> {
      use crate::ix::env::{
        ConstantInfo as LeanCI, ConstantVal as LeanCV, DefinitionSafety,
        DefinitionVal, InductiveVal, ReducibilityHints,
      };
      Some(match patch {
        PatchedConstant::Rec(r) => LeanCI::RecInfo(r.clone()),
        PatchedConstant::CasesOn(d) | PatchedConstant::RecOn(d) => {
          LeanCI::DefnInfo(DefinitionVal {
            cnst: ConstantVal {
              name: d.name.clone(),
              level_params: d.level_params.clone(),
              typ: d.typ.clone(),
            },
            value: d.value.clone(),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![],
          })
        },
        PatchedConstant::BelowDef(d) => LeanCI::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: d.name.clone(),
            level_params: d.level_params.clone(),
            typ: d.typ.clone(),
          },
          value: d.value.clone(),
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![],
        }),
        PatchedConstant::BRecOn(d) => LeanCI::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: d.name.clone(),
            level_params: d.level_params.clone(),
            typ: d.typ.clone(),
          },
          value: d.value.clone(),
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![],
        }),
        PatchedConstant::BelowIndc(bi) => LeanCI::InductInfo(InductiveVal {
          cnst: LeanCV {
            name: bi.name.clone(),
            level_params: bi.level_params.clone(),
            typ: bi.typ.clone(),
          },
          num_params: Nat::from(bi.n_params as u64),
          num_indices: Nat::from(bi.n_indices as u64),
          all: vec![bi.name.clone()],
          ctors: bi.ctors.iter().map(|c| c.name.clone()).collect(),
          num_nested: Nat::from(0u64),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: bi.is_reflexive,
        }),
      })
    }

    // Diagnostic dump printed per-thread on alpha-eq failure. Writes go
    // to stderr, so lines may interleave across threads — acceptable for
    // debug output where the important signal (which names failed) is
    // already preserved in `failures`.
    fn dump_diagnostics(
      patch_name: &Name,
      gen_ci: &ConstantInfo,
      orig_ci: &ConstantInfo,
      err: &str,
    ) {
      use crate::ix::env::{Expr, ExprData as ED};

      fn extract_sort(e: &Expr, depth: usize) -> String {
        match e.as_data() {
          ED::ForallE(_, _, body, _, _) => extract_sort(body, depth + 1),
          ED::Sort(lvl, _) => format!("depth={depth} sort={}", lvl.pretty()),
          _ => format!("depth={depth} NOT_SORT"),
        }
      }

      let pn = patch_name.pretty();
      eprintln!("[aux_gen congruence DETAIL] {}:\n  error: {err}", pn);
      eprintln!("  gen_type: {}", extract_sort(gen_ci.get_type(), 0));
      eprintln!("  org_type: {}", extract_sort(orig_ci.get_type(), 0));
    }

    // Cap on per-block diagnostic dumps. Replaces the pre-parallel
    // `if p2.fail < 3` heuristic, which is racy and meaningless when
    // multiple threads emit dumps concurrently. Per-block cap keeps
    // output bounded while still surfacing the most relevant context.
    const DUMP_PER_BLOCK: usize = 3;

    let results: Vec<BlockResult> = work
      .par_iter()
      .map(|(name, all, _original_cs)| {
        let original_classes: Vec<Vec<Name>> =
          all.iter().map(|n| vec![n.clone()]).collect();

        let orig_aux_out = match aux_gen::generate_aux_patches(
          &original_classes,
          all.as_slice(),
          &env,
          &stt,
          &p2_kctx,
        ) {
          Ok(p) => p,
          Err(e) => {
            return BlockResult {
              generate_error: Some(format!(
                "{}: generate_aux_patches failed: {e}",
                name.pretty(),
              )),
              ..Default::default()
            };
          },
        };
        let orig_patches = &orig_aux_out.patches;

        // Build a PermCtx for this block once. When the block has no
        // nested auxes (`perm == None` or empty), we pass `None` and
        // fall through to plain `const_alpha_eq`.
        let perm_ctx: Option<crate::ix::congruence::perm::PermCtx> =
          match &orig_aux_out.perm {
            Some(p) if !p.is_empty() => {
              build_perm_ctx(all.as_slice(), &env, &stt, p)
            },
            _ => None,
          };

        let mut result = BlockResult::default();
        let mut dumped = 0usize;
        for (patch_name, patch) in orig_patches.iter() {
          let Some(gen_ci) = patch_to_lean_ci(patch) else { continue };
          let Some(orig_ci_ref) = env.get(patch_name) else {
            continue; // Synthetic name — no Lean original.
          };
          let orig_ci: &LeanCI = orig_ci_ref;

          let eq_result = match &perm_ctx {
            Some(ctx) => crate::ix::congruence::perm::const_alpha_eq_with_perm(
              &gen_ci, orig_ci, ctx,
            ),
            None => const_alpha_eq(&gen_ci, orig_ci),
          };

          match eq_result {
            Ok(()) => result.passes += 1,
            Err(e) => {
              if dumped < DUMP_PER_BLOCK {
                dump_diagnostics(patch_name, &gen_ci, orig_ci, &e);
                dumped += 1;
              }
              result.failures.push(format!("{}: {e}", patch_name.pretty()));
            },
          }
        }
        result
      })
      .collect();

    // ── Serial aggregation into PhaseResult ──────────────────────────
    for r in results {
      for _ in 0..r.passes {
        p2.record_pass();
      }
      if let Some(err) = r.generate_error {
        p2.record_fail(err);
      }
      for f in r.failures {
        p2.record_fail(f);
      }
    }
  }
  p2.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 3: No ephemeral constant leaks
  // ══════════════════════════════════════════════════════════════════════
  let mut p3 = PhaseResult::new("3. No ephemeral leaks");

  // Precompute canonical addresses: any orig_addr that matches another Named
  // entry's canonical addr is in consts legitimately (not an ephemeral leak).
  // The gather itself parallelizes cleanly over the DashMap.
  let canonical_addrs: FxHashSet<crate::ix::address::Address> =
    stt.env.named.par_iter().map(|e| e.value().addr.clone()).collect();

  // Parallel scan over named DashMap. Each check is read-only against
  // `stt.env.consts` (DashMap), `canonical_addrs` (read-only set), and
  // the entry's own `named.original` tuple.
  {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let passes = AtomicUsize::new(0);
    let fails = AtomicUsize::new(0);
    let fail_msgs: Mutex<Vec<String>> = Mutex::new(Vec::new());

    stt.env.named.par_iter().for_each(|entry| {
      let named = entry.value();
      if let Some((orig_addr, _)) = &named.original {
        if *orig_addr != named.addr
          && stt.env.consts.contains_key(orig_addr)
          && !canonical_addrs.contains(orig_addr)
        {
          fails.fetch_add(1, Ordering::Relaxed);
          let mut msgs = fail_msgs.lock().unwrap();
          if msgs.len() < 20 {
            msgs.push(format!(
              "{}: ephemeral original addr {:?} leaked into consts",
              entry.key().pretty(),
              orig_addr,
            ));
          }
        } else {
          passes.fetch_add(1, Ordering::Relaxed);
        }
      }
    });

    p3.pass = passes.load(Ordering::Relaxed);
    p3.fail = fails.load(Ordering::Relaxed);
    p3.failures = fail_msgs.into_inner().unwrap();
  }
  p3.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 4: Alpha-equivalence group canonicity
  // ══════════════════════════════════════════════════════════════════════
  let mut p4 = PhaseResult::new("4. Alpha-equivalence canonicity");
  {
    use dashmap::DashSet;
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    // Dedup block entries that share a canonical `first_name`. Under
    // parallel iteration, only one thread wins the race to insert each
    // `first_name` — the others see `insert() == false` and skip. Matches
    // the serial `FxHashSet::insert` semantics exactly.
    let seen_blocks: DashSet<Name> = DashSet::new();
    let passes = AtomicUsize::new(0);
    let fails = AtomicUsize::new(0);
    let fail_msgs: Mutex<Vec<String>> = Mutex::new(Vec::new());

    stt.blocks.par_iter().for_each(|entry| {
      let classes = entry.value();
      if let Some(first_class) = classes.first()
        && let Some(first_name) = first_class.first()
        && !seen_blocks.insert(first_name.clone())
      {
        return;
      }

      for class in classes.iter() {
        if class.len() <= 1 {
          passes.fetch_add(1, Ordering::Relaxed);
          continue;
        }

        let addrs: Vec<_> =
          class.iter().map(|name| (name, stt.resolve_addr(name))).collect();

        let first_addr = &addrs[0].1;
        if addrs.iter().all(|(_, a)| a == first_addr) {
          passes.fetch_add(1, Ordering::Relaxed);
        } else {
          fails.fetch_add(1, Ordering::Relaxed);
          let mut msgs = fail_msgs.lock().unwrap();
          if msgs.len() < 20 {
            let detail: Vec<_> = addrs
              .iter()
              .map(|(n, a)| {
                format!(
                  "{}={}",
                  n.pretty(),
                  a.as_ref()
                    .map_or("MISSING".to_string(), |a| format!("{a:?}"))
                )
              })
              .collect();
            msgs.push(format!("class addrs differ: {}", detail.join(", ")));
          }
        }
      }
    });

    p4.pass = passes.load(Ordering::Relaxed);
    p4.fail = fails.load(Ordering::Relaxed);
    p4.failures = fail_msgs.into_inner().unwrap();
  }
  p4.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 4b: Explicit cross-namespace canonicity fixtures
  // ══════════════════════════════════════════════════════════════════════
  let mut p4b = PhaseResult::new("4b. Cross-namespace canonicity");
  {
    /// Build a dotted Lean name from a dot-separated string.
    /// Numeric components (e.g. the `0` in `_private.Foo.0.Bar`) are
    /// created as `Name::num` so that private-prefix names resolve
    /// correctly.
    fn mk_name(s: &str) -> Name {
      let mut name = Name::anon();
      for part in s.split('.') {
        if let Ok(n) = part.parse::<u64>() {
          name = Name::num(name, Nat::from(n));
        } else {
          name = Name::str(name, part.to_string());
        }
      }
      name
    }

    fn describe_addr(
      stt: &crate::ix::compile::CompileState,
      addr: &crate::ix::address::Address,
    ) -> String {
      match stt.env.get_const(addr).map(|c| c.info) {
        Some(crate::ix::ixon::constant::ConstantInfo::RPrj(p)) => {
          format!("RPrj(idx={}, block={:.12})", p.idx, p.block.hex())
        },
        Some(crate::ix::ixon::constant::ConstantInfo::IPrj(p)) => {
          format!("IPrj(idx={}, block={:.12})", p.idx, p.block.hex())
        },
        Some(crate::ix::ixon::constant::ConstantInfo::CPrj(p)) => {
          format!(
            "CPrj(idx={}, cidx={}, block={:.12})",
            p.idx,
            p.cidx,
            p.block.hex()
          )
        },
        Some(other) => format!("{other:?}"),
        None => "MISSING_CONST".to_string(),
      }
    }

    fn describe_rprj_block(
      stt: &crate::ix::compile::CompileState,
      addr: &crate::ix::address::Address,
    ) -> Option<String> {
      fn expand_shares_expr(
        expr: &Arc<crate::ix::ixon::expr::Expr>,
        sharing: &[Arc<crate::ix::ixon::expr::Expr>],
      ) -> Arc<crate::ix::ixon::expr::Expr> {
        use crate::ix::ixon::expr::Expr;
        match expr.as_ref() {
          Expr::Share(idx) => sharing.get(*idx as usize).map_or_else(
            || expr.clone(),
            |shared| expand_shares_expr(shared, sharing),
          ),
          Expr::Prj(type_ref_idx, field_idx, val) => Expr::prj(
            *type_ref_idx,
            *field_idx,
            expand_shares_expr(val, sharing),
          ),
          Expr::App(fun, arg) => Expr::app(
            expand_shares_expr(fun, sharing),
            expand_shares_expr(arg, sharing),
          ),
          Expr::Lam(ty, body) => Expr::lam(
            expand_shares_expr(ty, sharing),
            expand_shares_expr(body, sharing),
          ),
          Expr::All(ty, body) => Expr::all(
            expand_shares_expr(ty, sharing),
            expand_shares_expr(body, sharing),
          ),
          Expr::Let(non_dep, ty, val, body) => Expr::let_(
            *non_dep,
            expand_shares_expr(ty, sharing),
            expand_shares_expr(val, sharing),
            expand_shares_expr(body, sharing),
          ),
          _ => expr.clone(),
        }
      }

      fn expand_shares_member(
        member: &crate::ix::ixon::constant::MutConst,
        sharing: &[Arc<crate::ix::ixon::expr::Expr>],
      ) -> crate::ix::ixon::constant::MutConst {
        use crate::ix::ixon::constant::{MutConst, RecursorRule};
        match member {
          MutConst::Defn(def) => {
            let mut def = def.clone();
            def.typ = expand_shares_expr(&def.typ, sharing);
            def.value = expand_shares_expr(&def.value, sharing);
            MutConst::Defn(def)
          },
          MutConst::Indc(ind) => {
            let mut ind = ind.clone();
            ind.typ = expand_shares_expr(&ind.typ, sharing);
            for ctor in &mut ind.ctors {
              ctor.typ = expand_shares_expr(&ctor.typ, sharing);
            }
            MutConst::Indc(ind)
          },
          MutConst::Recr(rec) => {
            let mut rec = rec.clone();
            rec.typ = expand_shares_expr(&rec.typ, sharing);
            rec.rules = rec
              .rules
              .into_iter()
              .map(|rule| RecursorRule {
                fields: rule.fields,
                rhs: expand_shares_expr(&rule.rhs, sharing),
              })
              .collect();
            MutConst::Recr(rec)
          },
        }
      }

      fn expr_hash_prefix(expr: &Arc<crate::ix::ixon::expr::Expr>) -> String {
        let mut buf = Vec::new();
        crate::ix::ixon::serialize::put_expr(expr, &mut buf);
        let h = crate::ix::address::Address::hash(&buf);
        format!("{}:{}", buf.len(), &h.hex()[..12])
      }

      fn member_parts_summary(
        member: &crate::ix::ixon::constant::MutConst,
        sharing: &[Arc<crate::ix::ixon::expr::Expr>],
      ) -> String {
        use crate::ix::ixon::constant::MutConst;
        let expanded = expand_shares_member(member, sharing);
        match expanded {
          MutConst::Defn(def) => {
            format!(
              "def typ={} val={}",
              expr_hash_prefix(&def.typ),
              expr_hash_prefix(&def.value)
            )
          },
          MutConst::Indc(ind) => {
            let ctors: Vec<String> =
              ind.ctors.iter().map(|c| expr_hash_prefix(&c.typ)).collect();
            format!("ind typ={} ctors={ctors:?}", expr_hash_prefix(&ind.typ))
          },
          MutConst::Recr(rec) => {
            let rules: Vec<String> =
              rec.rules.iter().map(|r| expr_hash_prefix(&r.rhs)).collect();
            format!("rec typ={} rules={rules:?}", expr_hash_prefix(&rec.typ))
          },
        }
      }

      let proj = match stt.env.get_const(addr).map(|c| c.info) {
        Some(crate::ix::ixon::constant::ConstantInfo::RPrj(p)) => p,
        _ => return None,
      };
      let block = stt.env.get_const(&proj.block)?;
      let member_count_for_names = match &block.info {
        crate::ix::ixon::constant::ConstantInfo::Muts(ms) => ms.len(),
        _ => 0,
      };
      let proj_names: Vec<String> = (0..member_count_for_names)
        .map(|idx| {
          let idx = idx as u64;
          let mut names: Vec<String> = stt
            .aux_name_to_addr
            .iter()
            .chain(stt.name_to_addr.iter())
            .filter_map(|entry| {
              match stt.env.get_const(entry.value()).map(|c| c.info) {
                Some(crate::ix::ixon::constant::ConstantInfo::RPrj(p))
                  if p.block == proj.block && p.idx == idx =>
                {
                  Some(entry.key().pretty())
                },
                Some(crate::ix::ixon::constant::ConstantInfo::IPrj(p))
                  if p.block == proj.block && p.idx == idx =>
                {
                  Some(entry.key().pretty())
                },
                Some(crate::ix::ixon::constant::ConstantInfo::DPrj(p))
                  if p.block == proj.block && p.idx == idx =>
                {
                  Some(entry.key().pretty())
                },
                _ => None,
              }
            })
            .collect();
          names.sort();
          names.dedup();
          format!("{idx}:{names:?}")
        })
        .collect();
      let refs: Vec<_> = block
        .refs
        .iter()
        .map(|addr| {
          let name = stt
            .name_to_addr
            .iter()
            .find_map(|entry| {
              (entry.value() == addr).then(|| entry.key().pretty())
            })
            .or_else(|| {
              stt.aux_name_to_addr.iter().find_map(|entry| {
                (entry.value() == addr).then(|| entry.key().pretty())
              })
            })
            .unwrap_or_else(|| "?".to_string());
          format!("{}:{}", &addr.hex()[..12], name)
        })
        .collect();
      let (members, per_member_hashes) = match &block.info {
        crate::ix::ixon::constant::ConstantInfo::Muts(ms) => {
          let per: Vec<String> = ms
            .iter()
            .map(|m| {
              // Compute a per-member byte hash for quick diffing.
              let mut buf = Vec::new();
              m.put(&mut buf);
              let h = crate::ix::address::Address::hash(&buf);
              let expanded = expand_shares_member(m, &block.sharing);
              let mut expanded_buf = Vec::new();
              expanded.put(&mut expanded_buf);
              let expanded_h = crate::ix::address::Address::hash(&expanded_buf);
              let tag = match m {
                crate::ix::ixon::constant::MutConst::Defn(_) => "Defn",
                crate::ix::ixon::constant::MutConst::Indc(_) => "Indc",
                crate::ix::ixon::constant::MutConst::Recr(_) => "Recr",
              };
              let parts = member_parts_summary(m, &block.sharing);
              format!(
                "{}:{} expanded:{}",
                tag,
                &h.hex()[..12],
                &expanded_h.hex()[..12],
              ) + &format!(" {parts}")
            })
            .collect();
          (ms.len(), per)
        },
        _ => (0, Vec::new()),
      };
      // Full-block hex for deep debugging. Truncate to first 64 bytes to
      // keep output readable.
      let mut block_bytes = Vec::new();
      block.put(&mut block_bytes);
      let hex_prefix: String =
        block_bytes.iter().take(96).map(|b| format!("{b:02x}")).collect();
      Some(format!(
        "block {:.12}: members={}, proj_names={:?}, per_member={:?}, refs={:?}, univs={}, sharing={}, bytes_len={}, hex_prefix={}",
        proj.block.hex(),
        members,
        proj_names,
        per_member_hashes,
        refs,
        block.univs.len(),
        block.sharing.len(),
        block_bytes.len(),
        hex_prefix,
      ))
    }

    let groups: &[&[&str]] = &[
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.b",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.b",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.recOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.X.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin2.Y.brecOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.A.node",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.X.node",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.B.node",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.Y.node",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedTwin2.Y.rec",
      ],
      // ── Twin 3: OverMerge (non-alpha-equivalent mutuals) ──
      // A/X are structurally equivalent across namespaces.
      // B/Y are structurally equivalent across namespaces.
      // A and B are NOT alpha-equivalent (B has 2 fields).
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.a",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.b",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.b",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.recOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.recOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.X.brecOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin1.B.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceOverMergeTwin2.Y.brecOn",
      ],
      // ── Twin 4: Alpha3 (3-way alpha-collapse cycle) ──
      // All 6 types alpha-collapse: A≅B≅C and X≅Y≅Z, and A≅X.
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.b",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.c",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.b",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.c",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.recOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.B.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin1.C.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.X.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Y.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceAlpha3Twin2.Z.brecOn",
      ],
      // ── Twin 5: NestedParam (α vs β parameter rename + List nesting) ──
      // A≅B and X≅Y within each namespace (alpha-collapse).
      // A≅X across namespaces (binder rename α→β is erased).
      // Nested through List, so follow nested convention (inductives + ctors + rec).
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.X",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.A.leaf",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.B.leaf",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.X.leaf",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.Y.leaf",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.A.fromB",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.B.fromA",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.X.fromB",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.Y.fromA",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.A.node",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.B.node",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.X.node",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.Y.node",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceParamTwin2.Y.rec",
      ],
      // ── Twin 6: NestedAuxOrdering (3 types × 3 containers) ──
      // All 6 types alpha-collapse: A≅B≅C and X≅Y≅Z, and A≅X.
      // Nested through Array/Option/List, so follow nested convention.
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.C",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.X",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Y",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.A.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.B.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.C.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.X.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Y.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Z.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin1.C.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Y.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin2.Z.rec",
      ],
      // ── Twin 6b: NestedAuxOrdering (3 types, non-alpha, different decl order) ──
      // A≇B≇C (3/2/1 containers), so each pair gets its own group.
      // Twin3.A ↔ Twin4.X, Twin3.B ↔ Twin4.Y, Twin3.C ↔ Twin4.Z.
      // Nested convention (no casesOn/below/brecOn).
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.C",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.A.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.X.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.B.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Y.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.C.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Z.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Y.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin3.C.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin4.Z.rec",
      ],
      // ── Twin 6c: NestedAuxOrdering split-mutual variant ──
      // Same structure as Twin3/4 but C/Z are declared outside the mutual
      // block. Twin5.A↔Twin6.X, Twin5.B↔Twin6.Y (mutual pair referencing
      // external C/Z), Twin5.C↔Twin6.Z (standalone non-mutual).
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.B",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.C",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.A.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.X.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.B.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Y.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.C.mk",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Z.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.B.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Y.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin5.C.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceNestedOrderTwin6.Z.rec",
      ],
      // ── Twin 7: HigherOrderRec (single inductive, HO recursive field) ──
      // Non-mutual, non-nested. Full derived suite.
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.leaf",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.leaf",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.sup",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.sup",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.recOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.recOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.below",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceHOTwin2.X.brecOn",
      ],
      // ── Twin 8: Self-ref collapse (cross-fixture) ──
      // A single self-referential `A | a : A → A` should compile to the
      // same canonical form as a mutual pair that alpha-collapses.
      // Compares Canonicity.SelfRefTwin1.A against both
      // Canonicity.SelfRefTwin2.{X,Y} and Canonicity.CrossNamespaceTwin1.{A,B}.
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X.a",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y.b",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.b",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.CrossNamespaceTwin1.B.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X.casesOn",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A.below",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X.below",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SelfRefTwin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.X.brecOn",
        "Tests.Ix.Compile.Canonicity.SelfRefTwin2.Y.brecOn",
      ],
      // ── Twin 9: OverMerge + alpha-collapse (partial collapse) ──
      // A≅B and X≅Y alpha-collapse; C and Z do not collapse with them.
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B.b",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X.a",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y.b",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C.c",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z.c",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C.rec",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A.casesOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B.casesOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X.casesOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C.casesOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z.casesOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A.below",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B.below",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X.below",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C.below",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z.below",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.A.brecOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.B.brecOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.X.brecOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Y.brecOn",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin1.C.brecOn",
        "Tests.Ix.Compile.Canonicity.OverMergeAlphaCollapseTwin2.Z.brecOn",
      ],
      // ── Twin 10: Nested + non-alpha-equiv mutuals ──
      // A/B NOT alpha-equivalent (B has extra field), both nest through List.
      // Nested convention: inductives + constructors + recursors.
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.A",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.B",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.Y",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.A.a",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.X.a",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.B.b",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.Y.b",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.X.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.NestedOverMergeTwin2.Y.rec",
      ],
      // ── Twin 11: Binary container nesting (Prod) ──
      // All 6 types alpha-collapse. Nested through Prod (arity-2 spec_params).
      &[
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.A",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.B",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.C",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.X",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Y",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Z",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.A.mk",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.B.mk",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.C.mk",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.X.mk",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Y.mk",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Z.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.B.rec",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin1.C.rec",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.X.rec",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Y.rec",
        "Tests.Ix.Compile.Canonicity.ProdNestedTwin2.Z.rec",
      ],
      // ── Twin 12: Simple nested (single inductive + List) ──
      // Non-mutual, non-alpha-collapse. Nested convention.
      &[
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin1.A",
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin2.X",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin1.A.leaf",
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin2.X.leaf",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin1.A.node",
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin2.X.node",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin1.A.rec",
        "Tests.Ix.Compile.Canonicity.SimpleNestedTwin2.X.rec",
      ],
      // ── Twin 13: Structures ──
      // Structures generate projections; SC/XC are structures, SP/XP are
      // plain inductives. SC≅XC and SP≅XP across namespaces.
      // SC and SP are NOT alpha-equivalent (different field counts/types).
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SC",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XC",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SP",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XP",
      ],
      // Structure constructors use _private-mangled names in Lean 4
      // mutual blocks. The `0` component is Name::num, handled by mk_name.
      &[
        "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.StructureTwin1.SC.mk",
        "_private.Tests.Ix.Compile.Canonicity.0.Tests.Ix.Compile.Canonicity.StructureTwin2.XC.mk",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SP.base",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XP.base",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SP.combine",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XP.combine",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SC.rec",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XC.rec",
      ],
      &[
        "Tests.Ix.Compile.Canonicity.StructureTwin1.SP.rec",
        "Tests.Ix.Compile.Canonicity.StructureTwin2.XP.rec",
      ],
    ];

    for group in groups {
      let addrs: Vec<_> = group
        .iter()
        .map(|name| (*name, stt.resolve_addr(&mk_name(name))))
        .collect();

      let Some((_, Some(first_addr))) =
        addrs.iter().find(|(_, addr)| addr.is_some())
      else {
        // Phase 4b fixtures live in `Tests.Ix.Compile.Canonicity`. The
        // standalone `ix validate --path <file>` command can run against
        // arbitrary environments (e.g. Mathlib smoke tests) that do not
        // import those test declarations. Treat fully-absent fixture groups
        // as not applicable; partial presence below remains a real failure.
        continue;
      };

      let missing: Vec<_> = addrs
        .iter()
        .filter_map(|(name, addr)| addr.is_none().then_some(*name))
        .collect();
      if !missing.is_empty() {
        p4b.record_fail(format!(
          "missing names: {}; group: {}",
          missing.join(", "),
          group.join(", ")
        ));
        continue;
      }

      if addrs.iter().all(|(_, addr)| addr.as_ref() == Some(first_addr)) {
        p4b.record_pass();
      } else {
        let detail: Vec<_> = addrs
          .iter()
          .map(|(name, addr)| {
            format!(
              "{}={} {}",
              name,
              addr
                .as_ref()
                .map_or("MISSING".to_string(), |addr| format!("{addr:?}")),
              addr
                .as_ref()
                .map_or(String::new(), |addr| describe_addr(&stt, addr))
            )
          })
          .collect();
        let blocks: Vec<_> = addrs
          .iter()
          .filter_map(|(_, addr)| {
            addr.as_ref().and_then(|addr| describe_rprj_block(&stt, addr))
          })
          .collect();
        p4b.record_fail(format!(
          "cross-namespace addrs differ: {}; {}",
          detail.join(", "),
          blocks.join("; ")
        ));
      }
    }
  }
  p4b.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 5: Decompile with debug info
  // ══════════════════════════════════════════════════════════════════════
  let mut p5 = PhaseResult::new("5. Decompile (with debug)");
  println!("{VALIDATE_PREFIX} phase 5: decompiling (with debug)...");
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
      p5.record_fail(format!("decompile_env FAILED: {e:?}"));
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
        p5.pass = r.matches;
        if r.mismatches > 0 {
          p5.record_fail(format!("{} hash mismatches", r.mismatches));
        }
        if r.missing > 0 {
          p5.record_fail(format!("{} not in original", r.missing));
          for name in &r.extra_names {
            p5.record_fail(format!("  extra: {name}"));
          }
        }
      },
      Err(e) => {
        p5.record_fail(format!("check_decompile FAILED: {e:?}"));
      },
    }
  }
  p5.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 6: Aux congruence (post-compilation roundtrip)
  // ══════════════════════════════════════════════════════════════════════
  let mut p6 = PhaseResult::new("6. Aux congruence (roundtrip)");

  if let (Some(dstt_ref), Some(lean_env)) = (&dstt, &stt.lean_env) {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let passes = AtomicUsize::new(0);
    let fails = AtomicUsize::new(0);
    let fail_msgs: Mutex<Vec<String>> = Mutex::new(Vec::new());

    let push_fail = |msg: String| {
      fails.fetch_add(1, Ordering::Relaxed);
      let mut msgs = fail_msgs.lock().unwrap();
      if msgs.len() < 20 {
        msgs.push(msg);
      }
    };

    // Parallel alpha-equivalence check per aux_gen extra name. Reads are
    // against DashMap-backed lean_env and dstt_ref.env; `const_alpha_eq`
    // is pure and thread-safe.
    stt.aux_gen_extra_names.par_iter().for_each(|entry| {
      let name = entry.key();
      let orig_ci = match lean_env.get(name) {
        Some(ci) => ci,
        None => {
          push_fail(format!("{}: not in original Lean env", name.pretty()));
          return;
        },
      };
      let dec_ci = match dstt_ref.env.get(name) {
        Some(ci) => ci,
        None => {
          push_fail(format!("{}: not in decompiled env", name.pretty()));
          return;
        },
      };
      match const_alpha_eq(dec_ci.value(), orig_ci) {
        Ok(()) => {
          passes.fetch_add(1, Ordering::Relaxed);
        },
        Err(e) => {
          push_fail(format!("{}: {e}", name.pretty()));
        },
      }
    });

    p6.pass = passes.load(Ordering::Relaxed);
    p6.fail = fails.load(Ordering::Relaxed);
    p6.failures = fail_msgs.into_inner().unwrap();
  } else {
    if dstt.is_none() {
      p6.record_fail("skipped: decompilation failed in Phase 5".into());
    }
    if stt.lean_env.is_none() {
      p6.record_fail("skipped: lean_env not available".into());
    }
  }
  p6.report();

  // ── Free Phase 1-6 state before Phase 7 ──────────────────────────────
  //
  // On Mathlib this is the single most important memory optimization in
  // the whole validator. By the end of Phase 6 we have:
  //   - `stt`: ~30–40 GB — especially `stt.kctx` which decompile_env
  //     (Phase 5) populated with a kernel-ingress cache for every
  //     constant it checked. After Phase 6, nothing past Phase 7's
  //     serialize needs any of stt *except* stt.env.
  //   - `dstt`: ~30 GB — 707k owned `LeanConstantInfo` entries in a
  //     DashMap. Phase 7 builds a fresh `dstt2`; the old `dstt` is dead.
  //
  // If we kept stt + dstt alive through Phase 7, serialize's 3 GB buffer
  // plus the live kctx + dstt would push peak RSS past RAM, forcing swap
  // and slowing `Env::put` Section 2 from ~18 s (observed in `ix compile`)
  // to 90+ s.
  //
  // The trick: `std::mem::take(&mut stt.env)` moves the Env out of stt,
  // leaving an empty Env behind. Then we drop the remnants of stt — the
  // kctx, name_to_addr, blocks, etc. stop being rooted and their memory
  // is returned.
  //
  // We always genuinely `drop()` here (no `mem::forget`). `mem::forget`
  // *leaks* — it skips the destructor, but the allocation stays pinned,
  // which is the opposite of what we need mid-function. `mem::forget` is
  // only useful at function exit when the process is about to terminate
  // and the OS will reclaim the pages immediately; see the end of this
  // function for that use. The destructor cost mid-function is real but
  // unavoidable if we want to free the memory for subsequent phases.
  //
  // Parallel drop: `dstt` (~30 GB, DashMap of 700k LeanConstantInfo
  // entries) and the remainder of `stt` (kctx kernel cache, blocks, etc.,
  // ~10 GB after we take the env out) own independent allocations, so we
  // can run both destructors on rayon workers simultaneously. On Mathlib
  // this roughly halves the drop wall-clock from ~5–10 s to 2–5 s; more
  // importantly, the other 30 cores no longer idle while one thread
  // chases every Arc.
  let compile_env_only = std::mem::take(&mut stt.env);
  rayon::join(|| drop(dstt), || drop(stt));

  // ══════════════════════════════════════════════════════════════════════
  // Phase 7: Decompile without debug info (serialize → deserialize)
  // ══════════════════════════════════════════════════════════════════════
  //
  // Memory-tight structure:
  //   - `compile_env_only` holds just the Ixon env (no kctx). Serialize it.
  //   - Drop/forget `compile_env_only` as soon as `serialized` is built.
  //   - Deserialize `fresh_env` from `serialized`, then drop `serialized`.
  //   - Build `fresh_stt` from `fresh_env`, decompile to `dstt2`.
  //   - Forget `fresh_stt` on the way out of the Phase 7 block (its own
  //     kctx accumulated during decompile is the heavy part).
  //
  // Net peak RAM through Phase 7: env + compile_env_only + serialized +
  // fresh_stt + dstt2, released as each step completes. Nowhere near the
  // old worst case.
  let mut p7 = PhaseResult::new("7. Decompile (without debug)");
  println!("{VALIDATE_PREFIX} phase 7: serializing...");
  let t2 = std::time::Instant::now();

  let mut serialized = Vec::new();
  if let Err(e) = compile_env_only.put(&mut serialized) {
    p7.record_fail(format!("serialize FAILED: {e}"));
    p7.report();
    let total = p1.fail
      + p2.fail
      + p3.fail
      + p4.fail
      + p4b.fail
      + p5.fail
      + p6.fail
      + p7.fail;
    println!("{VALIDATE_PREFIX} RESULT: {total} total failures");
    return total;
  }
  println!(
    "{VALIDATE_PREFIX} serialized {} bytes in {:.2}s",
    serialized.len(),
    t2.elapsed().as_secs_f32()
  );

  // Compile-env's job is done — free ~30 GB before we allocate the
  // fresh_stt + dstt2 that Phase 7's deserialize-and-re-decompile needs.
  // Spawn the drop on a background thread so the destructor walk
  // (DashMap shards, 700k Arc refcounts) runs concurrently with the
  // deserialize + re-decompile phase that follows. The main thread does
  // not wait; on Linux with overcommit, allocations for `fresh_stt` /
  // `dstt2` proceed immediately while the drop walks shards in parallel.
  std::thread::spawn(move || drop(compile_env_only));

  println!("{VALIDATE_PREFIX} deserializing and re-decompiling...");
  let t3 = std::time::Instant::now();
  let dstt2 = {
    // Deserialize inside a short sub-scope so the borrow on `serialized`
    // ends before we drop it.
    let fresh_env = {
      let mut buf: &[u8] = &serialized;
      match crate::ix::ixon::env::Env::get(&mut buf) {
        Ok(fe) => Some(fe),
        Err(e) => {
          p7.record_fail(format!("deserialize FAILED: {e}"));
          None
        },
      }
    };
    // Free the 3 GB buffer before allocating fresh_stt + dstt2.
    drop(serialized);

    match fresh_env {
      Some(fresh_env) => {
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
        let result = match decompile_env(&fresh_stt) {
          Ok(dstt2) => {
            println!(
              "{VALIDATE_PREFIX} re-decompiled in {:.2}s ({} constants)",
              t3.elapsed().as_secs_f32(),
              dstt2.env.len()
            );
            match check_decompile(env.as_ref(), &fresh_stt, &dstt2) {
              Ok(r) => {
                p7.pass = r.matches;
                if r.mismatches > 0 {
                  p7.record_fail(format!("{} hash mismatches", r.mismatches));
                }
                if r.missing > 0 {
                  p7.record_fail(format!("{} not in original", r.missing));
                  for name in &r.extra_names {
                    p7.record_fail(format!("  extra: {name}"));
                  }
                }
              },
              Err(e) => {
                p7.record_fail(format!("check_decompile FAILED: {e:?}"));
              },
            }
            Some(dstt2)
          },
          Err(e) => {
            p7.record_fail(format!("re-decompile FAILED: {e:?}"));
            None
          },
        };
        // `fresh_stt` is no longer needed. Its env is duplicated in
        // `dstt2`, and its kctx (populated during decompile_env) is the
        // single biggest contributor to Phase 7's peak RAM aside from the
        // decompiled state itself. Free it before Phase 7b starts
        // iterating all 700k constants — on a background thread so the
        // destructor walk happens concurrently with Phase 7b's parallel
        // roundtrip scan rather than stalling the main thread.
        std::thread::spawn(move || drop(fresh_stt));
        result
      },
      None => None,
    }
  };
  p7.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 7b: Per-constant roundtrip fidelity (out-of-band)
  // ══════════════════════════════════════════════════════════════════════
  // Post-hoc comparison of each no-debug decompiled constant against the
  // original Lean env. This is independent of the decompiler's internal
  // checks — it catches any corruption that `check_decompile` might miss
  // and gives per-constant pass/fail granularity.
  let mut p7b = PhaseResult::new("7b. Roundtrip fidelity (per-constant)");
  if let Some(ref dstt2) = dstt2 {
    use std::sync::Mutex;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let orig = env.as_ref();
    let passes = AtomicUsize::new(0);
    let fails = AtomicUsize::new(0);
    let fail_msgs: Mutex<Vec<String>> = Mutex::new(Vec::new());

    // Parallel scan: every original constant must appear in the
    // roundtripped env with matching type hash (and value hash if
    // present). `get_hash()` reads are pure — ok to run concurrently.
    orig.par_iter().for_each(|(name, orig_ci)| match dstt2.env.get(name) {
      Some(dec_entry) => {
        let dec_ci = dec_entry.value();
        let type_ok =
          dec_ci.get_type().get_hash() == orig_ci.get_type().get_hash();
        let val_ok = match (dec_ci.get_value(), orig_ci.get_value()) {
          (Some(d), Some(o)) => d.get_hash() == o.get_hash(),
          (None, None) => true,
          _ => false,
        };
        if type_ok && val_ok {
          passes.fetch_add(1, Ordering::Relaxed);
        } else {
          fails.fetch_add(1, Ordering::Relaxed);
          let mut msgs = fail_msgs.lock().unwrap();
          if msgs.len() < 20 {
            let mut parts = Vec::new();
            if !type_ok {
              parts.push(format!(
                "type: dec={} orig={}",
                dec_ci.get_type().pretty(),
                orig_ci.get_type().pretty(),
              ));
            }
            if !val_ok {
              parts.push("value hash mismatch".to_string());
            }
            msgs.push(format!("{}: {}", name.pretty(), parts.join("; ")));
          }
        }
      },
      None => {
        fails.fetch_add(1, Ordering::Relaxed);
        let mut msgs = fail_msgs.lock().unwrap();
        if msgs.len() < 20 {
          msgs
            .push(format!("{}: missing from roundtripped env", name.pretty(),));
        }
      },
    });

    p7b.pass = passes.load(Ordering::Relaxed);
    p7b.fail = fails.load(Ordering::Relaxed);
    p7b.failures = fail_msgs.into_inner().unwrap();
  } else {
    p7b.record_fail("skipped: phase 7 decompilation failed".into());
  }
  p7b.report();

  // ══════════════════════════════════════════════════════════════════════
  // Phase 8: Nested detection verification
  // ══════════════════════════════════════════════════════════════════════
  let mut p8 = PhaseResult::new("8. Nested detection");
  {
    use crate::ix::compile::aux_gen::nested::build_compile_flat_block;
    use crate::ix::env::ConstantInfo;

    /// Build a dotted Lean name from a dot-separated string.
    /// Numeric components (e.g. the `0` in `_private.Foo.0.Bar`) are
    /// created as `Name::num` so that private-prefix names resolve
    /// correctly.
    fn mk_name(s: &str) -> Name {
      let mut name = Name::anon();
      for part in s.split('.') {
        if let Ok(n) = part.parse::<u64>() {
          name = Name::num(name, Nat::from(n));
        } else {
          name = Name::str(name, part.to_string());
        }
      }
      name
    }

    // Expected nested auxiliary detections for known test fixtures.
    // Each entry: (list of original dotted names, expected auxiliary names).
    let test_cases: Vec<(Vec<&str>, Vec<&str>)> = vec![
      // NestedSimple.Tree: single inductive nesting List.
      // Flat block should detect List as an auxiliary.
      (vec!["Tests.Ix.Compile.Mutual.NestedSimple.Tree"], vec!["List"]),
      // NestedAlphaCollapse: TreeA ≅ TreeB, both nest List.
      // Detection runs on the class representative (TreeA); one List auxiliary.
      (vec!["Tests.Ix.Compile.Mutual.NestedAlphaCollapse.TreeA"], vec!["List"]),
      // NestedParam: RoseA α ≅ RoseB α, both nest List.
      // Parameterized nesting: spec_params should include the block parameter.
      (vec!["Tests.Ix.Compile.Mutual.NestedParam.RoseA"], vec!["List"]),
      // NestedOverMerge: A/B form SCC (not alpha-equiv), C separate.
      // A nests List(A), B nests List(B) — distinct spec_params, so two
      // List auxiliaries. Lean's rec confirms: motive_4 : List A, motive_5 : List B.
      (
        vec![
          "Tests.Ix.Compile.Mutual.NestedOverMerge.A",
          "Tests.Ix.Compile.Mutual.NestedOverMerge.B",
        ],
        vec!["List", "List"],
      ),
      // NestedOverMergeAlphaCollapse: A ≅ B, C separate.
      // Detection on {A} (representative) should find one List auxiliary.
      (
        vec!["Tests.Ix.Compile.Mutual.NestedOverMergeAlphaCollapse.A"],
        vec!["List"],
      ),
      // Non-nested controls: these should produce NO auxiliaries.
      (vec!["Tests.Ix.Compile.Mutual.AlphaCollapse.A"], vec![]),
      (
        vec![
          "Tests.Ix.Compile.Mutual.OverMerge.A",
          "Tests.Ix.Compile.Mutual.OverMerge.B",
        ],
        vec![],
      ),
    ];

    for (original_strs, expected_aux_strs) in &test_cases {
      let originals: Vec<Name> =
        original_strs.iter().map(|s| mk_name(s)).collect();

      // Skip if any name is missing from the env (fixture not compiled).
      let all_present = originals
        .iter()
        .all(|n| matches!(env.get(n), Some(ConstantInfo::InductInfo(_))));
      if !all_present {
        continue;
      }

      let flat = build_compile_flat_block(&originals, &env).unwrap_or_default();
      let n_originals = originals.len();
      let aux_names: Vec<String> =
        flat.iter().skip(n_originals).map(|m| m.name.pretty()).collect();

      let expected_aux: Vec<String> =
        expected_aux_strs.iter().map(|s| s.to_string()).collect();

      if aux_names == expected_aux {
        p8.record_pass();
      } else {
        let label = original_strs.join(", ");
        p8.record_fail(format!(
          "{{{label}}}: expected auxiliaries {expected_aux:?}, got {aux_names:?}"
        ));
      }
    }
  }
  p8.report();

  // ══════════════════════════════════════════════════════════════════════
  // Summary
  // ══════════════════════════════════════════════════════════════════════
  let total = p1.fail
    + p2.fail
    + p3.fail
    + p4.fail
    + p4b.fail
    + p5.fail
    + p6.fail
    + p7.fail
    + p7b.fail
    + p8.fail;
  println!(
    "{VALIDATE_PREFIX} done ({:.2}s total)",
    t_total.elapsed().as_secs_f32()
  );
  println!("{VALIDATE_PREFIX} RESULT: {total} total failures");

  // Skip destructors on the CLI path. Mirrors the `rs_compile_env`
  // treatment (`src/ffi/compile.rs`). On Mathlib the remaining live state
  // — `env` (~1–2 GB), `dstt2` (~30 GB) — would otherwise take 60+ seconds
  // to drop serially across DashMap shards and `Arc<NameData>` chains, and
  // the process exits moments after this function returns anyway.
  //
  // Escape hatch: set `IX_SKIP_DROPS=0` for tests that assert clean
  // teardown under the validate-aux test runner.
  if std::env::var("IX_SKIP_DROPS").ok().as_deref() != Some("0") {
    std::mem::forget(dstt2);
    std::mem::forget(env);
  }

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
///
/// Simple best-effort parser for `analyze_const_size`'s CLI-like input —
/// splits on `.` and stores each segment as a string component. Does NOT
/// handle Lean's `«…»` escape syntax, so it's unsuitable for names
/// containing special characters; callers that receive Lean-originated
/// names should instead pass the structured `Lean.Name` across FFI and
/// use `decode_name`, as done by `src/ffi/kernel.rs`.
#[cfg(feature = "test-ffi")]
pub fn parse_name(s: &str) -> Name {
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
