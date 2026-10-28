//! Decode Lean kernel objects from their in-memory C representation.
//!
//! Provides functions to walk Lean object pointers and decode them into
//! the Rust `Name`, `Level`, `Expr`, and `ConstantInfo` types defined in
//! `ix_common::env`. Used by the compilation pipeline to read the Lean
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
use ix_compile::compile::{CompileOptions, compile_env_with_options};
#[cfg(feature = "test-ffi")]
use ix_compile::decompile::{check_decompile, decompile_env};
use std::sync::Arc;

use lean_ffi::nat::Nat;
use lean_ffi::object::LeanNat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanList, LeanOwned, LeanRef, LeanShared,
};

use crate::lean::{
  LeanIxAxiomVal, LeanIxConstantInfo, LeanIxConstantVal, LeanIxConstructorVal,
  LeanIxDataValue, LeanIxDefinitionVal, LeanIxExpr, LeanIxInductiveVal,
  LeanIxLevel, LeanIxLiteral, LeanIxName, LeanIxOpaqueVal, LeanIxQuotVal,
  LeanIxRecursorRule, LeanIxRecursorVal, LeanIxReducibilityHints,
  LeanIxSourceInfo, LeanIxSubstring, LeanIxSyntax, LeanIxSyntaxPreresolved,
  LeanIxTheoremVal,
};

use ix_common::env::{
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
    let n = LeanIxName::from_ctor(obj.as_ctor());
    let pre = decode_name(n.get_obj(0), global);
    let pos = n.get_obj(1);
    match n.as_ctor().tag() {
      1 => Name::str(pre, pos.as_string().to_string()),
      2 => Name::num(pre, LeanNat::to_nat(&pos)),
      tag => unreachable!("Invalid Lean.Name tag: {tag}"),
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
    let l = LeanIxLevel::from_ctor(obj.as_ctor());
    match l.as_ctor().tag() {
      1 => Level::succ(decode_level(l.get_obj(0), cache)),
      2 => Level::max(
        decode_level(l.get_obj(0), cache),
        decode_level(l.get_obj(1), cache),
      ),
      3 => Level::imax(
        decode_level(l.get_obj(0), cache),
        decode_level(l.get_obj(1), cache),
      ),
      4 => Level::param(decode_name(l.get_obj(0), cache.global)),
      5 => Level::mvar(decode_name(l.get_obj(0), cache.global)),
      tag => unreachable!("Invalid Lean.Level tag: {tag}"),
    }
  };
  cache.local.univs.insert(ptr, level.clone());
  level
}

fn decode_substring(obj: LeanBorrowed<'_>) -> Substring {
  let s = LeanIxSubstring::from_ctor(obj.as_ctor());
  let str = s.get_obj(0).as_string().to_string();
  let start_pos = LeanNat::to_nat(&s.get_obj(1));
  let stop_pos = LeanNat::to_nat(&s.get_obj(2));
  Substring { str, start_pos, stop_pos }
}

fn decode_source_info(obj: LeanBorrowed<'_>) -> SourceInfo {
  if obj.is_scalar() {
    return SourceInfo::None;
  }
  let si = LeanIxSourceInfo::from_ctor(obj.as_ctor());
  match si.as_ctor().tag() {
    0 => {
      let leading = decode_substring(si.get_obj(0));
      let pos = LeanNat::to_nat(&si.get_obj(1));
      let trailing = decode_substring(si.get_obj(2));
      let end_pos = LeanNat::to_nat(&si.get_obj(3));
      SourceInfo::Original(leading, pos, trailing, end_pos)
    },
    1 => {
      let pos = LeanNat::to_nat(&si.get_obj(0));
      let end_pos = LeanNat::to_nat(&si.get_obj(1));
      let canonical = si.get_num_8(0) != 0;
      SourceInfo::Synthetic(pos, end_pos, canonical)
    },
    tag => unreachable!("Invalid Lean.SourceInfo tag: {tag}"),
  }
}

fn decode_syntax_preresolved(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> SyntaxPreresolved {
  let p = LeanIxSyntaxPreresolved::from_ctor(obj.as_ctor());
  match p.as_ctor().tag() {
    0 => {
      let name = decode_name(p.get_obj(0), cache.global);
      SyntaxPreresolved::Namespace(name)
    },
    1 => {
      let name = decode_name(p.get_obj(0), cache.global);
      let fields: Vec<String> = p
        .get_obj(1)
        .as_list()
        .iter()
        .map(|o| o.as_string().to_string())
        .collect();
      SyntaxPreresolved::Decl(name, fields)
    },
    tag => unreachable!("Invalid Lean.Syntax.Preresolved tag: {tag}"),
  }
}

fn decode_syntax(obj: LeanBorrowed<'_>, cache: &mut Cache<'_>) -> Syntax {
  if obj.is_scalar() {
    return Syntax::Missing;
  }
  let s = LeanIxSyntax::from_ctor(obj.as_ctor());
  match s.as_ctor().tag() {
    1 => {
      let info = decode_source_info(s.get_obj(0));
      let kind = decode_name(s.get_obj(1), cache.global);
      let args: Vec<_> = s
        .get_obj(2)
        .as_array()
        .iter()
        .map(|o| decode_syntax(o, cache))
        .collect();
      Syntax::Node(info, kind, args)
    },
    2 => {
      let info = decode_source_info(s.get_obj(0));
      Syntax::Atom(info, s.get_obj(1).as_string().to_string())
    },
    3 => {
      let info = decode_source_info(s.get_obj(0));
      let raw_val = decode_substring(s.get_obj(1));
      let val = decode_name(s.get_obj(2), cache.global);
      let preresolved = collect_list_borrowed(s.get_obj(3).as_list())
        .into_iter()
        .map(|o| decode_syntax_preresolved(o, cache))
        .collect();
      Syntax::Ident(info, raw_val, val, preresolved)
    },
    tag => unreachable!("Invalid Lean.Syntax tag: {tag}"),
  }
}

fn decode_name_data_value(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> (Name, DataValue) {
  // Outer Prod (Name × DataValue) has no public LeanProd<LeanBorrowed>
  // constructor, so read the two fields through the raw ctor.
  let pair = obj.as_ctor();
  let name = decode_name(pair.get(0), cache.global);
  let dv = LeanIxDataValue::from_ctor(pair.get(1).as_ctor());
  let data_value = match dv.as_ctor().tag() {
    0 => DataValue::OfString(dv.get_obj(0).as_string().to_string()),
    1 => DataValue::OfBool(dv.get_num_8(0) != 0),
    2 => DataValue::OfName(decode_name(dv.get_obj(0), cache.global)),
    3 => DataValue::OfNat(LeanNat::to_nat(&dv.get_obj(0))),
    4 => {
      // `Lean.Int` is a builtin runtime type sharing `Nat`'s
      // representation — a tagged scalar or a GMP mpz object, never an
      // `ofNat`/`negSucc` ctor cell (`Int.ofNat` compiles to the
      // identity `lean_nat_to_int`). Decode by value and rebuild the
      // ctor view; `LeanIxInt` describes only the `Ix.Int` mirror
      // inductive, which really is a two-ctor object.
      let iobj = dv.get_obj(0);
      let int = if iobj.is_scalar() {
        // Scalars box `v` as `(v << 1) | 1`; an arithmetic shift
        // recovers the signed value.
        let v = (iobj.as_raw() as isize) >> 1;
        // Both magnitudes below are non-negative by construction -- the
        // branch settles the sign, and `negSucc n = -(n + 1)` so `n` is
        // `-(v + 1)` for `v < 0` -- and an `isize` magnitude always fits
        // `u64` on supported targets, so neither conversion can fail.
        let mag =
          |n: isize| u64::try_from(n).expect("isize magnitude fits u64");
        if v >= 0 {
          Int::OfNat(Nat::from(mag(v)))
        } else {
          Int::NegSucc(Nat::from(mag(-(v + 1))))
        }
      } else {
        let neg = unsafe {
          lean_ffi::include::lean_int_dec_lt(
            iobj.as_raw(),
            lean_ffi::include::lean_box(0),
          )
        } != 0;
        let abs = unsafe {
          LeanOwned::from_raw(lean_ffi::include::lean_nat_abs(iobj.as_raw()))
        };
        let mag = LeanNat::to_nat(&abs);
        if neg {
          // negSucc n = -(n + 1), so n = |v| - 1 (|v| ≥ 1 here).
          Int::NegSucc(Nat(mag.0 - 1u32))
        } else {
          Int::OfNat(mag)
        }
      };
      DataValue::OfInt(int)
    },
    5 => DataValue::OfSyntax(decode_syntax(dv.get_obj(0), cache).into()),
    tag => unreachable!("Invalid Lean.DataValue tag: {tag}"),
  };
  (name, data_value)
}

pub fn decode_expr(obj: LeanBorrowed<'_>, cache: &mut Cache<'_>) -> Expr {
  let ptr = obj.as_raw();
  if let Some(cached) = cache.local.exprs.get(&ptr) {
    return cached.clone();
  }
  let e = LeanIxExpr::from_ctor(obj.as_ctor());
  let decode_binder_info = |b: u8| match b {
    0 => BinderInfo::Default,
    1 => BinderInfo::Implicit,
    2 => BinderInfo::StrictImplicit,
    3 => BinderInfo::InstImplicit,
    _ => unreachable!("Invalid Lean.BinderInfo tag: {b}"),
  };
  let expr = match e.as_ctor().tag() {
    0 => Expr::bvar(LeanNat::to_nat(&e.get_obj(0))),
    1 => Expr::fvar(decode_name(e.get_obj(0), cache.global)),
    2 => Expr::mvar(decode_name(e.get_obj(0), cache.global)),
    3 => Expr::sort(decode_level(e.get_obj(0), cache)),
    4 => {
      let name = decode_name(e.get_obj(0), cache.global);
      let levels = collect_list_borrowed(e.get_obj(1).as_list())
        .into_iter()
        .map(|o| decode_level(o, cache))
        .collect();
      Expr::cnst(name, levels)
    },
    5 => {
      let f = decode_expr(e.get_obj(0), cache);
      let a = decode_expr(e.get_obj(1), cache);
      Expr::app(f, a)
    },
    6 => {
      let binder_name = decode_name(e.get_obj(0), cache.global);
      let binder_typ = decode_expr(e.get_obj(1), cache);
      let body = decode_expr(e.get_obj(2), cache);
      let binder_info = decode_binder_info(e.get_num_8(0));
      Expr::lam(binder_name, binder_typ, body, binder_info)
    },
    7 => {
      let binder_name = decode_name(e.get_obj(0), cache.global);
      let binder_typ = decode_expr(e.get_obj(1), cache);
      let body = decode_expr(e.get_obj(2), cache);
      let binder_info = decode_binder_info(e.get_num_8(0));
      Expr::all(binder_name, binder_typ, body, binder_info)
    },
    8 => {
      let decl_name = decode_name(e.get_obj(0), cache.global);
      let typ = decode_expr(e.get_obj(1), cache);
      let value = decode_expr(e.get_obj(2), cache);
      let body = decode_expr(e.get_obj(3), cache);
      let nondep = e.get_num_8(0) != 0;
      Expr::letE(decl_name, typ, value, body, nondep)
    },
    9 => {
      let lit = LeanIxLiteral::from_ctor(e.get_obj(0).as_ctor());
      let inner = lit.get_obj(0);
      match lit.as_ctor().tag() {
        0 => Expr::lit(Literal::NatVal(LeanNat::to_nat(&inner))),
        1 => Expr::lit(Literal::StrVal(inner.as_string().to_string())),
        tag => unreachable!("Invalid Lean.Literal tag: {tag}"),
      }
    },
    10 => {
      let kv_map: Vec<_> = collect_list_borrowed(e.get_obj(0).as_list())
        .into_iter()
        .map(|o| decode_name_data_value(o, cache))
        .collect();
      let expr = decode_expr(e.get_obj(1), cache);
      Expr::mdata(kv_map, expr)
    },
    11 => {
      let typ_name = decode_name(e.get_obj(0), cache.global);
      let idx = LeanNat::to_nat(&e.get_obj(1));
      let struct_expr = decode_expr(e.get_obj(2), cache);
      Expr::proj(typ_name, idx, struct_expr)
    },
    tag => unreachable!("Invalid Lean.Expr tag: {tag}"),
  };
  cache.local.exprs.insert(ptr, expr.clone());
  expr
}

fn decode_recursor_rule(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> RecursorRule {
  let r = LeanIxRecursorRule::from_ctor(obj.as_ctor());
  let ctor_name = decode_name(r.get_obj(0), cache.global);
  let n_fields = LeanNat::to_nat(&r.get_obj(1));
  let rhs = decode_expr(r.get_obj(2), cache);
  RecursorRule { ctor: ctor_name, n_fields, rhs }
}

fn decode_constant_val(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> ConstantVal {
  let cv = LeanIxConstantVal::from_ctor(obj.as_ctor());
  let name = decode_name(cv.get_obj(0), cache.global);
  let level_params: Vec<_> = collect_list_borrowed(cv.get_obj(1).as_list())
    .into_iter()
    .map(|o| decode_name(o, cache.global))
    .collect();
  let typ = decode_expr(cv.get_obj(2), cache);
  ConstantVal { name, level_params, typ }
}

pub fn decode_constant_info(
  obj: LeanBorrowed<'_>,
  cache: &mut Cache<'_>,
) -> ConstantInfo {
  let outer = LeanIxConstantInfo::from_ctor(obj.as_ctor());
  let inner_obj = outer.get_obj(0);

  match outer.as_ctor().tag() {
    0 => {
      let inner = LeanIxAxiomVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let is_unsafe = inner.get_num_8(0) != 0;
      ConstantInfo::AxiomInfo(AxiomVal { cnst: constant_val, is_unsafe })
    },
    1 => {
      let inner = LeanIxDefinitionVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let value = decode_expr(inner.get_obj(1), cache);
      let hints_obj = inner.get_obj(2);
      let hints = if hints_obj.is_scalar() {
        match hints_obj.unbox_usize() {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          tag => unreachable!("Invalid scalar ReducibilityHints tag: {tag}"),
        }
      } else {
        let h = LeanIxReducibilityHints::from_ctor(hints_obj.as_ctor());
        ReducibilityHints::Regular(h.get_num_32(0))
      };
      let all: Vec<_> = collect_list_borrowed(inner.get_obj(3).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let safety = match inner.get_num_8(0) {
        0 => DefinitionSafety::Unsafe,
        1 => DefinitionSafety::Safe,
        2 => DefinitionSafety::Partial,
        b => unreachable!("Invalid DefinitionSafety byte: {b}"),
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
      let inner = LeanIxTheoremVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let value = decode_expr(inner.get_obj(1), cache);
      let all: Vec<_> = collect_list_borrowed(inner.get_obj(2).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      ConstantInfo::ThmInfo(TheoremVal { cnst: constant_val, value, all })
    },
    3 => {
      let inner = LeanIxOpaqueVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let value = decode_expr(inner.get_obj(1), cache);
      let all: Vec<_> = collect_list_borrowed(inner.get_obj(2).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let is_unsafe = inner.get_num_8(0) != 0;
      ConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: constant_val,
        value,
        is_unsafe,
        all,
      })
    },
    4 => {
      let inner = LeanIxQuotVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let kind = match inner.get_num_8(0) {
        0 => QuotKind::Type,
        1 => QuotKind::Ctor,
        2 => QuotKind::Lift,
        3 => QuotKind::Ind,
        b => unreachable!("Invalid QuotKind byte: {b}"),
      };
      ConstantInfo::QuotInfo(QuotVal { cnst: constant_val, kind })
    },
    5 => {
      let inner = LeanIxInductiveVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let num_params = LeanNat::to_nat(&inner.get_obj(1));
      let num_indices = LeanNat::to_nat(&inner.get_obj(2));
      let all: Vec<_> = collect_list_borrowed(inner.get_obj(3).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let ctors: Vec<_> = collect_list_borrowed(inner.get_obj(4).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let num_nested = LeanNat::to_nat(&inner.get_obj(5));
      let is_rec = inner.get_num_8(0) != 0;
      let is_unsafe = inner.get_num_8(1) != 0;
      let is_reflexive = inner.get_num_8(2) != 0;
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
      let inner = LeanIxConstructorVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let induct = decode_name(inner.get_obj(1), cache.global);
      let cidx = LeanNat::to_nat(&inner.get_obj(2));
      let num_params = LeanNat::to_nat(&inner.get_obj(3));
      let num_fields = LeanNat::to_nat(&inner.get_obj(4));
      let is_unsafe = inner.get_num_8(0) != 0;
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
      let inner = LeanIxRecursorVal::from_ctor(inner_obj.as_ctor());
      let constant_val = decode_constant_val(inner.get_obj(0), cache);
      let all: Vec<_> = collect_list_borrowed(inner.get_obj(1).as_list())
        .into_iter()
        .map(|o| decode_name(o, cache.global))
        .collect();
      let num_params = LeanNat::to_nat(&inner.get_obj(2));
      let num_indices = LeanNat::to_nat(&inner.get_obj(3));
      let num_motives = LeanNat::to_nat(&inner.get_obj(4));
      let num_minors = LeanNat::to_nat(&inner.get_obj(5));
      let rules: Vec<_> = collect_list_borrowed(inner.get_obj(6).as_list())
        .into_iter()
        .map(|o| decode_recursor_rule(o, cache))
        .collect();
      let k = inner.get_num_8(0) != 0;
      let is_unsafe = inner.get_num_8(1) != 0;
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
    tag => unreachable!("Invalid Lean.ConstantInfo tag: {tag}"),
  }
}

/// Decode a single (Name, ConstantInfo) pair.
fn decode_name_constant_info(
  obj: LeanBorrowed<'_>,
  global: &GlobalCache,
) -> (Name, ConstantInfo) {
  let mut cache = Cache::new(global);
  // Outer Prod (Name × ConstantInfo) has no public LeanProd<LeanBorrowed>
  // constructor, so read the two fields through the raw ctor.
  let pair = obj.as_ctor();
  let name = decode_name(pair.get(0), global);
  let constant_info = decode_constant_info(pair.get(1), &mut cache);
  (name, constant_info)
}

/// Resident-decoded-constant bound for [`decode_env_lazy`]'s cache.
///
/// Sized by sweep, not by hit rate: on FLT (511k consts) wall time is
/// flat from 4096 through 1M entries (60–67 s; misses hide in the
/// scheduler's dependency-stall slack) while peak RSS climbs from
/// 11.5 GiB (4k) → 13.0 (64k) → 24.7 (1M); Mathlib (737k consts)
/// confirms parity at this size (87.5 s / 17.0 GiB vs 87.3 s /
/// 18.3 GiB at 64k). So the cache buys RAM, not speed, and the bound
/// sits at the small end with headroom over the 4k floor measured to
/// still not thrash.
const LAZY_ENV_CACHE_ENTRIES: usize = 16384;

/// Decode for the production compile FFI entries: an on-demand view
/// that avoids materializing the full Rust copy of the environment —
/// the eager copy is the single largest memory term at scale. The
/// on-demand decode costs a few percent of wall (per-constant fetches
/// vs one batched decode); `IX_COMPILE_EAGER=1` buys that back on
/// machines with RAM to spare. Measured on FLT: −8 % wall for
/// +13 GiB peak; Mathlib eager exceeds a 56 GB machine outright
/// (the copy sits alongside the Lean-held env). Test and roundtrip
/// entries keep [`decode_env`] (they re-read the env structurally
/// throughout).
pub fn decode_env_for_compile(list: LeanList<LeanBorrowed<'_>>) -> Env {
  if std::env::var("IX_COMPILE_EAGER").as_deref() == Ok("1") {
    return decode_env(list);
  }
  decode_env_lazy(list, LAZY_ENV_CACHE_ENTRIES)
}

/// Lazy variant of [`decode_env`]: decode only the *names* eagerly,
/// keep a per-constant `LeanShared` handle, and decode `ConstantInfo`s
/// on demand through `Env`'s bounded cache.
///
/// Thread-safety is identical to the eager path, which already decodes
/// in parallel: `lean_mark_mt` (via `LeanShared::new`) transitions the
/// reachable graph to atomic refcounting, structural reads through
/// `LeanBorrowed` accessors are refcount-silent, and each element's
/// owned handle keeps its Lean objects alive for the `Env`'s lifetime
/// regardless of what the Lean side does after the FFI call.
pub fn decode_env_lazy(
  list: LeanList<LeanBorrowed<'_>>,
  cache_entries: usize,
) -> Env {
  let shared_list = LeanShared::new(list.inner().to_owned_ref());
  let objs = collect_list_shared(shared_list.borrow().as_list());
  let global = Arc::new(GlobalCache::with_capacity(objs.len() * 3));

  // Name index (parallel; bodies untouched). Each element is a
  // `Prod (Name × ConstantInfo)` ctor — field 0 is the name.
  let named: Vec<(Name, LeanShared)> = objs
    .into_par_iter()
    .map(|o| {
      let name = decode_name(o.borrow().as_ctor().get(0), &global);
      (name, o)
    })
    .collect();
  let names: Vec<Name> = named.iter().map(|(n, _)| n.clone()).collect();
  let handles: FxHashMap<Name, LeanShared> = named.into_iter().collect();

  let fetch = move |name: &Name| {
    let obj = handles.get(name)?;
    let mut cache = Cache::new(&global);
    Some(decode_constant_info(obj.borrow().as_ctor().get(1), &mut cache))
  };
  Env::new_lazy(names, Box::new(fetch), cache_entries)
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
  let env = decode_env(obj);
  let n = env.len();
  let env = Arc::new(env);
  let t0 = std::time::Instant::now();

  // Phase 1: Compile
  eprintln!("[rust-compile] Phase 1: Compiling {n} constants...");
  let stt = match compile_env_with_options(&env, CompileOptions::default()) {
    Ok(s) => s,
    Err(e) => {
      eprintln!("[rust-compile] Phase 1 FAILED: {e:?}");
      return n;
    },
  };
  if !stt.ungrounded.is_empty() {
    eprintln!(
      "[rust-compile] Phase 1 FAILED: {} ungrounded input declarations",
      stt.ungrounded.len(),
    );
    let mut refusals: Vec<_> = stt
      .ungrounded
      .iter()
      .map(|entry| (entry.key().pretty(), entry.value().clone()))
      .collect();
    refusals.sort();
    for (name, reason) in refusals.iter().take(16) {
      eprintln!("[rust-compile] ungrounded {name}: {reason}");
    }
    return n;
  }
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

  // Phase 3: Check roundtrip. `failures` accumulates roundtrip breakage
  // here and in Phase 6; the function returns it, so a non-zero total fails
  // the Lean `rust-compile` test. (Fatal phase aborts above return `n`,
  // which is likewise non-zero — an abort is also a failure.)
  eprintln!("[rust-compile] Phase 3: Checking decompile roundtrip...");
  let t2 = std::time::Instant::now();
  let mut failures = match check_decompile(env.as_ref(), &stt, &dstt) {
    Ok(c) => c.failures(|_| false),
    Err(e) => {
      eprintln!("[rust-compile] Phase 3 check FAILED: {e:?}");
      1
    },
  };
  eprintln!(
    "[rust-compile] Phase 3 done in {:.2}s",
    t2.elapsed().as_secs_f32()
  );

  // Phase 4: Size analysis
  eprintln!("[rust-compile] Phase 4: Size analysis...");
  let _ = stt.env.serialized_size_breakdown();
  analyze_const_size(&stt, "Nat.add_comm");

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
  match ixon::env::Env::get(&mut buf) {
    Ok(fresh_env) => {
      let fresh_stt = ix_compile::compile::CompileState {
        env: fresh_env,
        sharing_limits: stt.sharing_limits.clone(),
        ..Default::default()
      };
      for entry in fresh_stt.env.named.iter() {
        fresh_stt
          .name_to_addr
          .insert(entry.key().clone(), entry.value().addr.clone());
      }
      match decompile_env(&fresh_stt) {
        Ok(dstt2) => match check_decompile(env.as_ref(), &fresh_stt, &dstt2) {
          Ok(c) => failures += c.failures(|_| false),
          Err(e) => {
            eprintln!("[rust-compile] Phase 6 check FAILED: {e:?}");
            failures += 1;
          },
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
    "[rust-compile] All phases complete. Total: {:.2}s ({failures} roundtrip failure(s))",
    t0.elapsed().as_secs_f32()
  );
  failures
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
fn analyze_const_size(stt: &ix_compile::compile::CompileState, name_str: &str) {
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

  // Get the constant (materialize from the lazy entry).
  let constant = match stt.env.get_const(&addr) {
    Some(c) => c,
    None => {
      println!("\n=== Size analysis for {} ===", name_str);
      println!("  Constant data not found at address");
      return;
    },
  };

  // Compute direct sizes (alpha-invariant and metadata)
  let direct_breakdown =
    compute_const_size_breakdown(&constant, &name, stt, &name_index);

  // Reuse the shared transitive-closure walker on Env.
  let dep_addrs = stt.env.transitive_deps_excl(&addr);
  let mut dep_breakdowns: Vec<(String, ConstSizeBreakdown)> = Vec::new();
  for dep_addr in dep_addrs {
    let Some(dep_const) = stt.env.get_const(&dep_addr) else {
      continue;
    };
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
  }

  // Sort by total size descending
  dep_breakdowns.sort_by_key(|entry| std::cmp::Reverse(entry.1.total()));

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
  stt: &ix_compile::compile::CompileState,
) -> ixon::metadata::NameIndex {
  use ix_common::address::Address;
  use ixon::metadata::NameIndex;

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
  constant: &ixon::constant::Constant,
  name: &Name,
  stt: &ix_compile::compile::CompileState,
  name_index: &ixon::metadata::NameIndex,
) -> ConstSizeBreakdown {
  // Alpha-invariant size
  let alpha_size = serialized_const_size(constant);

  // Metadata size
  let meta_size = if let Some(named) = stt.env.named.get(name) {
    serialized_meta_size(&named.meta(), name_index)
  } else {
    0
  };

  ConstSizeBreakdown { alpha_size, meta_size }
}

/// Compute the serialized size of constant metadata.
#[cfg(feature = "test-ffi")]
fn serialized_meta_size(
  meta: &ixon::metadata::ConstantMeta,
  name_index: &ixon::metadata::NameIndex,
) -> usize {
  let mut buf = Vec::new();
  meta
    .put_with(ixon::metadata::NamePut::Indexed(name_index), &mut buf)
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
/// use `decode_name`, as done by `crates/ffi/src/kernel.rs`.
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
fn serialized_const_size(constant: &ixon::constant::Constant) -> usize {
  let mut buf = Vec::new();
  constant.put(&mut buf);
  buf.len()
}
