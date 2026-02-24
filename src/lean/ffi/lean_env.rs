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
use std::ffi::c_void;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::{
  ix::compile::compile_env,
  ix::decompile::{check_decompile, decompile_env},
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, DataValue,
    DefinitionSafety, DefinitionVal, Env, Expr, InductiveVal, Int, Level,
    Literal, Name, OpaqueVal, QuotKind, QuotVal, RecursorRule, RecursorVal,
    ReducibilityHints, SourceInfo, Substring, Syntax, SyntaxPreresolved,
    TheoremVal,
  },
  lean::{
    array::LeanArrayObject, as_ref_unsafe, collect_list, ctor::LeanCtorObject,
    lean_is_scalar, nat::Nat, string::LeanStringObject,
  },
  lean_unbox,
};

const PARALLEL_THRESHOLD: usize = 100;

/// Wrapper to allow sending raw pointers across threads. The underlying Lean
/// objects must remain valid for the entire duration of parallel decoding
#[derive(Clone, Copy)]
struct SendPtr(*const c_void);

unsafe impl Send for SendPtr {}
unsafe impl Sync for SendPtr {}

impl SendPtr {
  #[inline]
  fn get(self) -> *const c_void {
    self.0
  }
}

/// Global cache for Names, shared across all threads.
#[derive(Default)]
pub struct GlobalCache {
  names: DashMap<*const c_void, Name>,
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
  univs: FxHashMap<*const c_void, Level>,
  exprs: FxHashMap<*const c_void, Expr>,
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

fn collect_list_ptrs(mut ptr: *const c_void) -> Vec<*const c_void> {
  let mut ptrs = Vec::new();
  while !lean_is_scalar(ptr) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [head_ptr, tail_ptr] = ctor.objs();
    ptrs.push(head_ptr);
    ptr = tail_ptr;
  }
  ptrs
}

// Name decoding with global cache
pub fn lean_ptr_to_name(ptr: *const c_void, global: &GlobalCache) -> Name {
  // Fast path: check if already cached
  if let Some(name) = global.names.get(&ptr) {
    return name.clone();
  }

  // Compute the name
  let name = if lean_is_scalar(ptr) {
    Name::anon()
  } else {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [pre_ptr, pos_ptr] = ctor.objs();
    // Recursive call - will also use global cache
    let pre = lean_ptr_to_name(pre_ptr, global);
    match ctor.tag() {
      1 => {
        let str_obj: &LeanStringObject = as_ref_unsafe(pos_ptr.cast());
        Name::str(pre, str_obj.as_string())
      },
      2 => Name::num(pre, Nat::from_ptr(pos_ptr)),
      _ => unreachable!(),
    }
  };

  // Insert and return (entry API handles races gracefully)
  global.names.entry(ptr).or_insert(name).clone()
}

fn lean_ptr_to_level(ptr: *const c_void, cache: &mut Cache<'_>) -> Level {
  if let Some(cached) = cache.local.univs.get(&ptr) {
    return cached.clone();
  }
  let level = if lean_is_scalar(ptr) {
    Level::zero()
  } else {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    match ctor.tag() {
      1 => {
        let [u] = ctor.objs().map(|p| lean_ptr_to_level(p, cache));
        Level::succ(u)
      },
      2 => {
        let [u, v] = ctor.objs().map(|p| lean_ptr_to_level(p, cache));
        Level::max(u, v)
      },
      3 => {
        let [u, v] = ctor.objs().map(|p| lean_ptr_to_level(p, cache));
        Level::imax(u, v)
      },
      4 => {
        let [name] = ctor.objs().map(|p| lean_ptr_to_name(p, cache.global));
        Level::param(name)
      },
      5 => {
        let [name] = ctor.objs().map(|p| lean_ptr_to_name(p, cache.global));
        Level::mvar(name)
      },
      _ => unreachable!(),
    }
  };
  cache.local.univs.insert(ptr, level.clone());
  level
}

fn lean_ptr_to_substring(ptr: *const c_void) -> Substring {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [str_ptr, start_pos_ptr, stop_pos_ptr] = ctor.objs();
  let str: &LeanStringObject = as_ref_unsafe(str_ptr.cast());
  let str = str.as_string();
  let start_pos = Nat::from_ptr(start_pos_ptr);
  let stop_pos = Nat::from_ptr(stop_pos_ptr);
  Substring { str, start_pos, stop_pos }
}

fn lean_ptr_to_source_info(ptr: *const c_void) -> SourceInfo {
  if lean_is_scalar(ptr) {
    return SourceInfo::None;
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let [leading_ptr, pos_ptr, trailing_ptr, end_pos_ptr] = ctor.objs();
      let leading = lean_ptr_to_substring(leading_ptr);
      let pos = Nat::from_ptr(pos_ptr);
      let trailing = lean_ptr_to_substring(trailing_ptr);
      let end_pos = Nat::from_ptr(end_pos_ptr);
      SourceInfo::Original(leading, pos, trailing, end_pos)
    },
    1 => {
      let [pos_ptr, end_pos_ptr, canonical_ptr] = ctor.objs();
      let pos = Nat::from_ptr(pos_ptr);
      let end_pos = Nat::from_ptr(end_pos_ptr);
      let canonical = canonical_ptr as usize == 1;
      SourceInfo::Synthetic(pos, end_pos, canonical)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_syntax_preresolved(
  ptr: *const c_void,
  cache: &mut Cache<'_>,
) -> SyntaxPreresolved {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let [name_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache.global);
      SyntaxPreresolved::Namespace(name)
    },
    1 => {
      let [name_ptr, fields_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache.global);
      let fields = collect_list(fields_ptr, |p| {
        let str: &LeanStringObject = as_ref_unsafe(p.cast());
        str.as_string()
      });
      SyntaxPreresolved::Decl(name, fields)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_syntax(ptr: *const c_void, cache: &mut Cache<'_>) -> Syntax {
  if lean_is_scalar(ptr) {
    return Syntax::Missing;
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    1 => {
      let [info_ptr, kind_ptr, args_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let kind = lean_ptr_to_name(kind_ptr, cache.global);
      let args_array: &LeanArrayObject = as_ref_unsafe(args_ptr.cast());
      let args: Vec<_> = args_array
        .data()
        .iter()
        .map(|&p| lean_ptr_to_syntax(p, cache))
        .collect();
      Syntax::Node(info, kind, args)
    },
    2 => {
      let [info_ptr, val_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let val_str: &LeanStringObject = as_ref_unsafe(val_ptr.cast());
      Syntax::Atom(info, val_str.as_string())
    },
    3 => {
      let [info_ptr, raw_val_ptr, val_ptr, preresolved_ptr] = ctor.objs();
      let info = lean_ptr_to_source_info(info_ptr);
      let raw_val = lean_ptr_to_substring(raw_val_ptr);
      let val = lean_ptr_to_name(val_ptr, cache.global);
      let preresolved = collect_list_ptrs(preresolved_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_syntax_preresolved(p, cache))
        .collect();
      Syntax::Ident(info, raw_val, val, preresolved)
    },
    _ => unreachable!(),
  }
}

fn lean_ptr_to_name_data_value(
  ptr: *const c_void,
  cache: &mut Cache<'_>,
) -> (Name, DataValue) {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, data_value_ptr] = ctor.objs();
  let name = lean_ptr_to_name(name_ptr, cache.global);
  let data_value_ctor: &LeanCtorObject = as_ref_unsafe(data_value_ptr.cast());
  let [inner_ptr] = data_value_ctor.objs();
  let data_value = match data_value_ctor.tag() {
    0 => {
      let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
      DataValue::OfString(str.as_string())
    },
    1 => DataValue::OfBool(inner_ptr as usize == 1),
    2 => DataValue::OfName(lean_ptr_to_name(inner_ptr, cache.global)),
    3 => DataValue::OfNat(Nat::from_ptr(inner_ptr)),
    4 => {
      let int_ctor: &LeanCtorObject = as_ref_unsafe(inner_ptr.cast());
      let [nat_ptr] = int_ctor.objs();
      let nat = Nat::from_ptr(nat_ptr);
      let int = match int_ctor.tag() {
        0 => Int::OfNat(nat),
        1 => Int::NegSucc(nat),
        _ => unreachable!(),
      };
      DataValue::OfInt(int)
    },
    5 => DataValue::OfSyntax(lean_ptr_to_syntax(inner_ptr, cache).into()),
    _ => unreachable!(),
  };
  (name, data_value)
}

pub fn lean_ptr_to_expr(ptr: *const c_void, cache: &mut Cache<'_>) -> Expr {
  if let Some(cached) = cache.local.exprs.get(&ptr) {
    return cached.clone();
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let expr = match ctor.tag() {
    0 => {
      let [nat_ptr, _hash_ptr] = ctor.objs();
      let nat = Nat::from_ptr(nat_ptr.cast());
      Expr::bvar(nat)
    },
    1 => {
      let [name_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache.global);
      Expr::fvar(name)
    },
    2 => {
      let [name_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache.global);
      Expr::mvar(name)
    },
    3 => {
      let [u_ptr, _hash_ptr] = ctor.objs();
      let u = lean_ptr_to_level(u_ptr, cache);
      Expr::sort(u)
    },
    4 => {
      let [name_ptr, levels_ptr, _hash_ptr] = ctor.objs();
      let name = lean_ptr_to_name(name_ptr, cache.global);
      let levels = collect_list_ptrs(levels_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_level(p, cache))
        .collect();
      Expr::cnst(name, levels)
    },
    5 => {
      let [f_ptr, a_ptr, _hash_ptr] = ctor.objs();
      let f = lean_ptr_to_expr(f_ptr, cache);
      let a = lean_ptr_to_expr(a_ptr, cache);
      Expr::app(f, a)
    },
    6 => {
      let [
        binder_name_ptr,
        binder_typ_ptr,
        body_ptr,
        _hash_ptr,
        binder_info_ptr,
      ] = ctor.objs();
      let binder_name = lean_ptr_to_name(binder_name_ptr, cache.global);
      let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let binder_info = match binder_info_ptr as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::lam(binder_name, binder_typ, body, binder_info)
    },
    7 => {
      let [
        binder_name_ptr,
        binder_typ_ptr,
        body_ptr,
        _hash_ptr,
        binder_info_ptr,
      ] = ctor.objs();
      let binder_name = lean_ptr_to_name(binder_name_ptr, cache.global);
      let binder_typ = lean_ptr_to_expr(binder_typ_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let binder_info = match binder_info_ptr as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Expr::all(binder_name, binder_typ, body, binder_info)
    },
    8 => {
      let [decl_name_ptr, typ_ptr, value_ptr, body_ptr, _hash_ptr, nondep_ptr] =
        ctor.objs();
      let decl_name = lean_ptr_to_name(decl_name_ptr, cache.global);
      let typ = lean_ptr_to_expr(typ_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let body = lean_ptr_to_expr(body_ptr, cache);
      let nondep = nondep_ptr as usize == 1;
      Expr::letE(decl_name, typ, value, body, nondep)
    },
    9 => {
      let [literal_ptr, _hash_ptr] = ctor.objs();
      let literal: &LeanCtorObject = as_ref_unsafe(literal_ptr.cast());
      let [inner_ptr] = literal.objs();
      match literal.tag() {
        0 => {
          let nat = Nat::from_ptr(inner_ptr);
          Expr::lit(Literal::NatVal(nat))
        },
        1 => {
          let str: &LeanStringObject = as_ref_unsafe(inner_ptr.cast());
          Expr::lit(Literal::StrVal(str.as_string()))
        },
        _ => unreachable!(),
      }
    },
    10 => {
      let [data_ptr, expr_ptr] = ctor.objs();
      let kv_map: Vec<_> = collect_list_ptrs(data_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name_data_value(p, cache))
        .collect();
      let expr = lean_ptr_to_expr(expr_ptr, cache);
      Expr::mdata(kv_map, expr)
    },
    11 => {
      let [typ_name_ptr, idx_ptr, struct_ptr] = ctor.objs();
      let typ_name = lean_ptr_to_name(typ_name_ptr, cache.global);
      let idx = Nat::from_ptr(idx_ptr);
      let struct_expr = lean_ptr_to_expr(struct_ptr, cache);
      Expr::proj(typ_name, idx, struct_expr)
    },
    _ => unreachable!(),
  };
  cache.local.exprs.insert(ptr, expr.clone());
  expr
}

fn lean_ptr_to_recursor_rule(
  ptr: *const c_void,
  cache: &mut Cache<'_>,
) -> RecursorRule {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [ctor_ptr, n_fields_ptr, rhs_ptr] = ctor.objs();
  let ctor = lean_ptr_to_name(ctor_ptr, cache.global);
  let n_fields = Nat::from_ptr(n_fields_ptr);
  let rhs = lean_ptr_to_expr(rhs_ptr, cache);
  RecursorRule { ctor, n_fields, rhs }
}

fn lean_ptr_to_constant_val(
  ptr: *const c_void,
  cache: &mut Cache<'_>,
) -> ConstantVal {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, level_params_ptr, typ_ptr] = ctor.objs();
  let name = lean_ptr_to_name(name_ptr, cache.global);
  let level_params: Vec<_> = collect_list_ptrs(level_params_ptr)
    .into_iter()
    .map(|p| lean_ptr_to_name(p, cache.global))
    .collect();
  let typ = lean_ptr_to_expr(typ_ptr, cache);
  ConstantVal { name, level_params, typ }
}

pub fn lean_ptr_to_constant_info(
  ptr: *const c_void,
  cache: &mut Cache<'_>,
) -> ConstantInfo {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner_val_ptr] = ctor.objs();
  let inner_val: &LeanCtorObject = as_ref_unsafe(inner_val_ptr.cast());

  match ctor.tag() {
    0 => {
      let [constant_val_ptr, is_unsafe_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let is_unsafe = is_unsafe_ptr as usize == 1;
      ConstantInfo::AxiomInfo(AxiomVal { cnst: constant_val, is_unsafe })
    },
    1 => {
      let [constant_val_ptr, value_ptr, hints_ptr, all_ptr, safety_ptr] =
        inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let hints = if lean_is_scalar(hints_ptr) {
        match lean_unbox!(usize, hints_ptr) {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          _ => unreachable!(),
        }
      } else {
        let hints_ctor: &LeanCtorObject = as_ref_unsafe(hints_ptr.cast());
        let [height_ptr] = hints_ctor.objs();
        ReducibilityHints::Regular(height_ptr as u32)
      };
      let all: Vec<_> = collect_list_ptrs(all_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      let safety = match safety_ptr as usize {
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
      let [constant_val_ptr, value_ptr, all_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let all: Vec<_> = collect_list_ptrs(all_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      ConstantInfo::ThmInfo(TheoremVal { cnst: constant_val, value, all })
    },
    3 => {
      let [constant_val_ptr, value_ptr, all_ptr, is_unsafe_ptr] =
        inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let value = lean_ptr_to_expr(value_ptr, cache);
      let all: Vec<_> = collect_list_ptrs(all_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      let is_unsafe = is_unsafe_ptr as usize == 1;
      ConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: constant_val,
        value,
        is_unsafe,
        all,
      })
    },
    4 => {
      let [constant_val_ptr, kind_ptr] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let kind = match kind_ptr as usize {
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
        constant_val_ptr,
        num_params_ptr,
        num_indices_ptr,
        all_ptr,
        ctors_ptr,
        num_nested_ptr,
        bools_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_indices = Nat::from_ptr(num_indices_ptr);
      let all: Vec<_> = collect_list_ptrs(all_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      let ctors: Vec<_> = collect_list_ptrs(ctors_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      let num_nested = Nat::from_ptr(num_nested_ptr);
      let [is_rec, is_unsafe, is_reflexive, ..] =
        (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
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
      let [
        constant_val_ptr,
        induct_ptr,
        cidx_ptr,
        num_params_ptr,
        num_fields_ptr,
        is_unsafe_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let induct = lean_ptr_to_name(induct_ptr, cache.global);
      let cidx = Nat::from_ptr(cidx_ptr);
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_fields = Nat::from_ptr(num_fields_ptr);
      let is_unsafe = is_unsafe_ptr as usize == 1;
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
        constant_val_ptr,
        all_ptr,
        num_params_ptr,
        num_indices_ptr,
        num_motives_ptr,
        num_minors_ptr,
        rules_ptr,
        bools_ptr,
      ] = inner_val.objs();
      let constant_val = lean_ptr_to_constant_val(constant_val_ptr, cache);
      let all: Vec<_> = collect_list_ptrs(all_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_name(p, cache.global))
        .collect();
      let num_params = Nat::from_ptr(num_params_ptr);
      let num_indices = Nat::from_ptr(num_indices_ptr);
      let num_motives = Nat::from_ptr(num_motives_ptr);
      let num_minors = Nat::from_ptr(num_minors_ptr);
      let rules: Vec<_> = collect_list_ptrs(rules_ptr)
        .into_iter()
        .map(|p| lean_ptr_to_recursor_rule(p, cache))
        .collect();
      let [k, is_unsafe, ..] =
        (bools_ptr as usize).to_le_bytes().map(|b| b == 1);
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
  ptr: *const c_void,
  global: &GlobalCache,
) -> (Name, ConstantInfo) {
  let mut cache = Cache::new(global);
  let prod_ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [name_ptr, constant_info_ptr] = prod_ctor.objs();
  let name = lean_ptr_to_name(name_ptr, global);
  let constant_info = lean_ptr_to_constant_info(constant_info_ptr, &mut cache);
  (name, constant_info)
}

// Decode a Lean environment in parallel with hybrid caching.
pub fn lean_ptr_to_env(ptr: *const c_void) -> Env {
  // Phase 1: Collect pointers (sequential)
  let ptrs = collect_list_ptrs(ptr);

  if ptrs.len() < PARALLEL_THRESHOLD {
    return lean_ptr_to_env_sequential(ptr);
  }

  // Estimate: ~3 unique names per constant on average
  let global = GlobalCache::with_capacity(ptrs.len() * 3);

  // Phase 2: Decode in parallel with shared global name cache
  let pairs: Vec<(Name, ConstantInfo)> = ptrs
    .into_iter()
    .map(SendPtr)              // Wrap each *const c_void in SendPtr
    .collect::<Vec<_>>()       // Collect into Vec<SendPtr>
    .into_par_iter()           // Now Rayon can use it (SendPtr is Send+Sync)
    .map(|p| decode_name_constant_info(p.get(), &global))  // Unwrap with .get()
    .collect();

  // Phase 3: Build final map
  let mut env = Env::default();
  env.reserve(pairs.len());
  for (name, constant_info) in pairs {
    env.insert(name, constant_info);
  }
  env
}

/// Sequential fallback for small environments.
pub fn lean_ptr_to_env_sequential(ptr: *const c_void) -> Env {
  let ptrs = collect_list_ptrs(ptr);
  let global = GlobalCache::new();
  let mut env = Env::default();
  env.reserve(ptrs.len());

  for p in ptrs {
    let (name, constant_info) = decode_name_constant_info(p, &global);
    env.insert(name, constant_info);
  }
  env
}

//#[unsafe(no_mangle)]
//pub extern "C" fn rs_decode_env(ptr: *const c_void) -> usize {
//  let env = lean_ptr_to_env(ptr);
//  env.len()
//}

// Debug/analysis entry point invoked via the `rust-compile` test flag in
// `Tests/FFI/Basic.lean`. Exercises the full compile→decompile→check→serialize
// roundtrip and size analysis. Output is intentionally suppressed; re-enable
// individual `eprintln!` lines when debugging locally.
#[unsafe(no_mangle)]
extern "C" fn rs_tmp_decode_const_map(ptr: *const c_void) -> usize {
  // Enable hash-consed size tracking for debugging
  // TODO: Make this configurable via CLI instead of hardcoded
  crate::ix::compile::TRACK_HASH_CONSED_SIZE
    .store(true, std::sync::atomic::Ordering::Relaxed);

  // Enable verbose sharing analysis for debugging pathological blocks
  // TODO: Make this configurable via CLI instead of hardcoded
  crate::ix::compile::ANALYZE_SHARING
    .store(false, std::sync::atomic::Ordering::Relaxed);

  let env = lean_ptr_to_env(ptr);
  let env = Arc::new(env);
  if let Ok(stt) = compile_env(&env) {
    if let Ok(dstt) = decompile_env(&stt) {
      let _ = check_decompile(env.as_ref(), &stt, &dstt);
    }

    // Measure serialized size (after roundtrip, not counted in total time)
    let _ = stt.env.serialized_size_breakdown();

    // Analyze serialized size of "Nat.add_comm" and its transitive dependencies
    analyze_const_size(&stt, "Nat.add_comm");

    // Analyze hash-consing vs serialization efficiency
    analyze_block_size_stats(&stt);

    // Test decompilation from serialized bytes (simulating "over the wire")
    let mut serialized = Vec::new();
    stt.env.put(&mut serialized).expect("Env serialization failed");

    // Deserialize to a fresh Env
    let mut buf: &[u8] = &serialized;
    if let Ok(fresh_env) = crate::ix::ixon::env::Env::get(&mut buf) {
      // Build a fresh CompileState from the deserialized Env
      let fresh_stt = crate::ix::compile::CompileState {
        env: fresh_env,
        name_to_addr: DashMap::new(),
        blocks: dashmap::DashSet::new(),
        block_stats: DashMap::new(),
      };

      // Populate name_to_addr from env.named
      for entry in fresh_stt.env.named.iter() {
        fresh_stt
          .name_to_addr
          .insert(entry.key().clone(), entry.value().addr.clone());
      }

      // Populate blocks from constants that are mutual blocks
      for entry in fresh_stt.env.consts.iter() {
        if matches!(
          &entry.value().info,
          crate::ix::ixon::constant::ConstantInfo::Muts(_)
        ) {
          fresh_stt.blocks.insert(entry.key().clone());
        }
      }

      // Decompile from the fresh state
      if let Ok(dstt2) = decompile_env(&fresh_stt) {
        // Verify against original environment
        let _ = check_decompile(env.as_ref(), &fresh_stt, &dstt2);
      }
    }
  }
  env.as_ref().len()
}

/// Size breakdown for a constant: alpha-invariant vs metadata
#[derive(Default, Clone)]
struct ConstSizeBreakdown {
  alpha_size: usize, // Alpha-invariant constant data
  meta_size: usize,  // Metadata (names, binder info, etc.)
}

impl ConstSizeBreakdown {
  fn total(&self) -> usize {
    self.alpha_size + self.meta_size
  }
}

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
      // Get the name for this dependency
      let dep_name_opt = stt.env.get_name_by_addr(&dep_addr);
      let dep_name_str = dep_name_opt
        .as_ref()
        .map_or_else(|| format!("{:?}", dep_addr), |n| n.pretty());

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
fn parse_name(s: &str) -> Name {
  let parts: Vec<&str> = s.split('.').collect();
  let mut name = Name::anon();
  for part in parts {
    name = Name::str(name, part.to_string());
  }
  name
}

/// Compute the serialized size of a constant.
fn serialized_const_size(
  constant: &crate::ix::ixon::constant::Constant,
) -> usize {
  let mut buf = Vec::new();
  constant.put(&mut buf);
  buf.len()
}

/// Analyze block size statistics: hash-consing vs serialization.
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
fn truncate_name(name: &str, max_len: usize) -> String {
  if name.len() <= max_len {
    name.to_string()
  } else {
    format!("...{}", &name[name.len() - max_len + 3..])
  }
}
