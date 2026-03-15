//! Deconversion from kernel types back to Lean env types.
//!
//! Converts `KExpr<Meta>`/`KLevel<Meta>`/`KConstantInfo<Meta>` back to
//! `env::Expr`/`env::Level`/`env::ConstantInfo` for roundtrip verification.
//!
//! With perfect metadata preservation (Meta mode), the deconverted expressions
//! produce identical blake3 hashes to the originals, enabling O(1) verification.

use std::sync::atomic::AtomicBool;

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::compile::CompileState;
use crate::ix::decompile::decompile_env;
use crate::ix::env::{
  self, AxiomVal, ConstantInfo as LeanConstantInfo, ConstantVal,
  ConstructorVal, DefinitionVal, InductiveVal, Name, OpaqueVal,
  QuotVal, RecursorRule as LeanRecursorRule, RecursorVal, TheoremVal,
};
use crate::lean::nat::Nat;

use super::types::*;

// ============================================================================
// Level deconversion
// ============================================================================

/// Convert a kernel level back to a Lean level.
fn deconvert_level(level: &KLevel<Meta>, level_params: &[Name]) -> env::Level {
  match level.data() {
    KLevelData::Zero => env::Level::zero(),
    KLevelData::Succ(l) => env::Level::succ(deconvert_level(l, level_params)),
    KLevelData::Max(a, b) => {
      env::Level::max(deconvert_level(a, level_params), deconvert_level(b, level_params))
    }
    KLevelData::IMax(a, b) => {
      env::Level::imax(deconvert_level(a, level_params), deconvert_level(b, level_params))
    }
    KLevelData::Param(idx, _) => {
      let name = level_params
        .get(*idx)
        .cloned()
        .unwrap_or_else(Name::anon);
      env::Level::param(name)
    }
  }
}

fn deconvert_levels(levels: &[KLevel<Meta>], level_params: &[Name]) -> Vec<env::Level> {
  levels.iter().map(|l| deconvert_level(l, level_params)).collect()
}

// ============================================================================
// Expression deconversion
// ============================================================================

type ExprDeconvertCache = FxHashMap<usize, env::Expr>;

/// Convert a kernel expression back to a Lean expression.
/// Caches by Rc pointer address for O(1) sharing.
fn deconvert_expr(
  expr: &KExpr<Meta>,
  level_params: &[Name],
  cache: &mut ExprDeconvertCache,
) -> env::Expr {
  let ptr = expr.ptr_id();
  if let Some(cached) = cache.get(&ptr) {
    return cached.clone();
  }

  let inner = match expr.data() {
    KExprData::BVar(idx, _) => env::Expr::bvar(Nat::from(*idx as u64)),
    KExprData::Sort(l) => env::Expr::sort(deconvert_level(l, level_params)),
    KExprData::Const(mid, levels) => {
      let name = mid.name.clone();
      let lvls = deconvert_levels(levels, level_params);
      env::Expr::cnst(name, lvls)
    }
    KExprData::App(f, a) => {
      let kf = deconvert_expr(f, level_params, cache);
      let ka = deconvert_expr(a, level_params, cache);
      env::Expr::app(kf, ka)
    }
    KExprData::Lam(ty, body, name, bi) => {
      let kty = deconvert_expr(ty, level_params, cache);
      let kbody = deconvert_expr(body, level_params, cache);
      env::Expr::lam(name.clone(), kty, kbody, bi.clone())
    }
    KExprData::ForallE(ty, body, name, bi) => {
      let kty = deconvert_expr(ty, level_params, cache);
      let kbody = deconvert_expr(body, level_params, cache);
      env::Expr::all(name.clone(), kty, kbody, bi.clone())
    }
    KExprData::LetE(ty, val, body, name, nd) => {
      let kty = deconvert_expr(ty, level_params, cache);
      let kval = deconvert_expr(val, level_params, cache);
      let kbody = deconvert_expr(body, level_params, cache);
      env::Expr::letE(name.clone(), kty, kval, kbody, *nd)
    }
    KExprData::Lit(l) => env::Expr::lit(l.clone()),
    KExprData::Proj(mid, idx, s) => {
      let ks = deconvert_expr(s, level_params, cache);
      env::Expr::proj(mid.name.clone(), Nat::from(*idx as u64), ks)
    }
  };

  // Re-wrap with mdata layers (outermost first)
  let result = expr.mdata_layers().iter().rev().fold(inner, |acc, kvs| {
    env::Expr::mdata(kvs.clone(), acc)
  });

  cache.insert(ptr, result.clone());
  result
}

// ============================================================================
// Constant deconversion
// ============================================================================

/// Extract level param names from a KConstantVal.
fn get_level_params(cv: &KConstantVal<Meta>) -> Vec<Name> {
  cv.level_params.clone()
}

/// Convert a KConstantVal back to an env::ConstantVal.
fn deconvert_cv(
  cv: &KConstantVal<Meta>,
  cache: &mut ExprDeconvertCache,
) -> ConstantVal {
  let level_params = get_level_params(cv);
  ConstantVal {
    name: cv.name.clone(),
    level_params: level_params.clone(),
    typ: deconvert_expr(&cv.typ, &level_params, cache),
  }
}

/// Extract names from a Vec<MetaId<Meta>>.
fn meta_ids_to_names(ids: &[MetaId<Meta>]) -> Vec<Name> {
  ids.iter().map(|mid| mid.name.clone()).collect()
}

/// Convert a KConstantInfo back to a Lean ConstantInfo.
pub fn deconvert_constant_info(ci: &KConstantInfo<Meta>) -> LeanConstantInfo {
  let mut cache = ExprDeconvertCache::default();

  match ci {
    KConstantInfo::Axiom(v) => {
      LeanConstantInfo::AxiomInfo(AxiomVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        is_unsafe: v.is_unsafe,
      })
    }

    KConstantInfo::Definition(v) => {
      let level_params = get_level_params(&v.cv);
      LeanConstantInfo::DefnInfo(DefinitionVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        value: deconvert_expr(&v.value, &level_params, &mut cache),
        hints: v.hints,
        safety: v.safety,
        all: meta_ids_to_names(&v.lean_all),
      })
    }

    KConstantInfo::Theorem(v) => {
      let level_params = get_level_params(&v.cv);
      LeanConstantInfo::ThmInfo(TheoremVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        value: deconvert_expr(&v.value, &level_params, &mut cache),
        all: meta_ids_to_names(&v.lean_all),
      })
    }

    KConstantInfo::Opaque(v) => {
      let level_params = get_level_params(&v.cv);
      LeanConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        value: deconvert_expr(&v.value, &level_params, &mut cache),
        is_unsafe: v.is_unsafe,
        all: meta_ids_to_names(&v.lean_all),
      })
    }

    KConstantInfo::Quotient(v) => {
      LeanConstantInfo::QuotInfo(QuotVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        kind: v.kind,
      })
    }

    KConstantInfo::Inductive(v) => {
      LeanConstantInfo::InductInfo(InductiveVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        num_params: Nat::from(v.num_params as u64),
        num_indices: Nat::from(v.num_indices as u64),
        all: meta_ids_to_names(
          &v.lean_all,
        ),
        ctors: meta_ids_to_names(&v.ctors),
        num_nested: Nat::from(v.num_nested as u64),
        is_rec: v.is_rec,
        is_unsafe: v.is_unsafe,
        is_reflexive: v.is_reflexive,
      })
    }

    KConstantInfo::Constructor(v) => {
      LeanConstantInfo::CtorInfo(ConstructorVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        induct: v.induct.name.clone(),
        cidx: Nat::from(v.cidx as u64),
        num_params: Nat::from(v.num_params as u64),
        num_fields: Nat::from(v.num_fields as u64),
        is_unsafe: v.is_unsafe,
      })
    }

    KConstantInfo::Recursor(v) => {
      let level_params = get_level_params(&v.cv);
      let rules: Vec<LeanRecursorRule> = v
        .rules
        .iter()
        .map(|r| LeanRecursorRule {
          ctor: r.ctor.name.clone(),
          n_fields: Nat::from(r.nfields as u64),
          rhs: deconvert_expr(&r.rhs, &level_params, &mut cache),
        })
        .collect();
      LeanConstantInfo::RecInfo(RecursorVal {
        cnst: deconvert_cv(&v.cv, &mut cache),
        all: meta_ids_to_names(&v.lean_all),
        num_params: Nat::from(v.num_params as u64),
        num_indices: Nat::from(v.num_indices as u64),
        num_motives: Nat::from(v.num_motives as u64),
        num_minors: Nat::from(v.num_minors as u64),
        rules,
        k: v.k,
        is_unsafe: v.is_unsafe,
      })
    }
  }
}

// ============================================================================
// Roundtrip verification
// ============================================================================

static PRINT_FIRST_DETAIL: AtomicBool = AtomicBool::new(true);

/// Debug-print an env::Expr tree with indentation.
fn debug_expr(e: &env::Expr, depth: usize) -> String {
  use env::ExprData;
  let indent = "  ".repeat(depth);
  match e.as_data() {
    ExprData::Bvar(i, _) => format!("{indent}bvar({i})"),
    ExprData::Sort(l, _) => format!("{indent}sort(hash={})", l.get_hash()),
    ExprData::Const(n, ls, _) => format!("{indent}const({}, lvls={})", n.pretty(), ls.len()),
    ExprData::App(f, a, _) => format!("{indent}app\n{}\n{}", debug_expr(f, depth+1), debug_expr(a, depth+1)),
    ExprData::Lam(n, t, b, bi, _) => format!("{indent}lam({}, {bi:?})\n{}\n{}", n.pretty(), debug_expr(t, depth+1), debug_expr(b, depth+1)),
    ExprData::ForallE(n, t, b, bi, _) => format!("{indent}forall({}, {bi:?})\n{}\n{}", n.pretty(), debug_expr(t, depth+1), debug_expr(b, depth+1)),
    ExprData::LetE(n, t, v, b, nd, _) => format!("{indent}let({}, nd={nd})\n{}\n{}\n{}", n.pretty(), debug_expr(t, depth+1), debug_expr(v, depth+1), debug_expr(b, depth+1)),
    ExprData::Lit(l, _) => format!("{indent}lit({l:?})"),
    ExprData::Proj(n, i, s, _) => format!("{indent}proj({}, {i})\n{}", n.pretty(), debug_expr(s, depth+1)),
    ExprData::Mdata(kvs, inner, _) => format!("{indent}mdata({} entries)\n{}", kvs.len(), debug_expr(inner, depth+1)),
    ExprData::Fvar(n, _) => format!("{indent}fvar({n})"),
    ExprData::Mvar(n, _) => format!("{indent}mvar({n})"),
  }
}

/// Verify the KEnv roundtrip by comparing deconverted kernel types against
/// Ixon-decompiled types. This isolates bugs to the from_ixon → deconvert
/// path, since Ixon compile/decompile is independently validated.
pub fn verify_roundtrip(
  stt: &CompileState,
  kenv: &KEnv<Meta>,
) -> Vec<(String, String)> {
  // Run the Ixon decompiler to get the reference env
  let t0 = std::time::Instant::now();
  let decomp = match decompile_env(stt) {
    Ok(d) => d,
    Err(e) => return vec![("<decompile>".to_string(), format!("decompile failed: {e}"))],
  };
  eprintln!("[verify_roundtrip] decompile: {:>8.1?} ({} consts)", t0.elapsed(), decomp.env.len());

  // Build name_hash → KConstantInfo index from kenv
  let mut name_index: FxHashMap<blake3::Hash, &KConstantInfo<Meta>> =
    FxHashMap::default();
  for (id, ci) in kenv.iter() {
    name_index.insert(*id.name.get_hash(), ci);
  }

  // Collect decompiled entries for parallel comparison
  let ref_entries: Vec<_> = decomp.env.iter()
    .map(|entry| (entry.key().clone(), entry.value().clone()))
    .collect();

  let t1 = std::time::Instant::now();
  let mut errors: Vec<(String, String)> = ref_entries
    .into_par_iter()
    .flat_map(|(name, ref_ci)| {
      let pretty = name.pretty();
      let name_hash = *name.get_hash();

      let kci = match name_index.get(&name_hash) {
        Some(kci) => *kci,
        None => return vec![(pretty, "missing from kenv".to_string())],
      };

      let deconverted = deconvert_constant_info(kci);
      let mut errs = Vec::new();

      // Compare type hashes (deconverted vs Ixon-decompiled)
      let ref_type_hash = ref_ci.cnst_val().typ.get_hash();
      let deconv_type_hash = deconverted.cnst_val().typ.get_hash();
      if ref_type_hash != deconv_type_hash {
        let detail = find_first_diff(&ref_ci.cnst_val().typ, &deconverted.cnst_val().typ, "type");
        if PRINT_FIRST_DETAIL.swap(false, std::sync::atomic::Ordering::Relaxed) {
          eprintln!("\n=== FIRST MISMATCH: {} ===", pretty);
          eprintln!("  detail: {detail}");
          // Print the divergent subtrees
          let (ref_sub, deconv_sub) = find_divergent_subtrees(
            &ref_ci.cnst_val().typ, &deconverted.cnst_val().typ
          );
          if let (Some(r), Some(d)) = (ref_sub, deconv_sub) {
            eprintln!("--- ref subtree ---\n{}", debug_expr(&r, 0));
            eprintln!("--- deconv subtree ---\n{}", debug_expr(&d, 0));
          }
        }
        errs.push((pretty.clone(), format!("type hash mismatch: {detail}")));
        return errs;
      }

      // Compare value hashes
      match (&ref_ci, &deconverted) {
        (LeanConstantInfo::DefnInfo(v1), LeanConstantInfo::DefnInfo(v2)) => {
          if v1.value.get_hash() != v2.value.get_hash() {
            let d = find_first_diff(&v1.value, &v2.value, "val");
            if PRINT_FIRST_DETAIL.swap(false, std::sync::atomic::Ordering::Relaxed) {
              eprintln!("\n=== FIRST VALUE MISMATCH: {} ===", pretty);
              eprintln!("  detail: {d}");
              let (ref_sub, deconv_sub) = find_divergent_subtrees(&v1.value, &v2.value);
              if let (Some(r), Some(dc)) = (ref_sub, deconv_sub) {
                eprintln!("--- ref subtree ---\n{}", debug_expr(&r, 0));
                eprintln!("--- deconv subtree ---\n{}", debug_expr(&dc, 0));
              }
            }
            errs.push((pretty, format!("value hash mismatch: {d}")));
          }
        }
        (LeanConstantInfo::ThmInfo(v1), LeanConstantInfo::ThmInfo(v2)) => {
          if v1.value.get_hash() != v2.value.get_hash() {
            let d = find_first_diff(&v1.value, &v2.value, "val");
            errs.push((pretty, format!("value hash mismatch: {d}")));
          }
        }
        (LeanConstantInfo::OpaqueInfo(v1), LeanConstantInfo::OpaqueInfo(v2)) => {
          if v1.value.get_hash() != v2.value.get_hash() {
            let d = find_first_diff(&v1.value, &v2.value, "val");
            errs.push((pretty, format!("value hash mismatch: {d}")));
          }
        }
        (LeanConstantInfo::RecInfo(v1), LeanConstantInfo::RecInfo(v2)) => {
          for (i, (r1, r2)) in v1.rules.iter().zip(v2.rules.iter()).enumerate() {
            if r1.rhs.get_hash() != r2.rhs.get_hash() {
              let d = find_first_diff(&r1.rhs, &r2.rhs, &format!("rule[{i}].rhs"));
              errs.push((pretty.clone(), format!("{d}")));
            }
          }
        }
        _ => {}
      }
      errs
    })
    .collect();
  eprintln!("[verify_roundtrip] compare:   {:>8.1?}", t1.elapsed());

  // Check size match
  if kenv.len() != decomp.env.len() {
    errors.push((
      "<env>".to_string(),
      format!("size mismatch: decomp={} kenv={}", decomp.env.len(), kenv.len()),
    ));
  }

  errors
}

/// Helper trait to access common constant fields (mirrors convert.rs).
trait CnstVal {
  fn cnst_val(&self) -> &ConstantVal;
}

impl CnstVal for LeanConstantInfo {
  fn cnst_val(&self) -> &ConstantVal {
    match self {
      LeanConstantInfo::AxiomInfo(v) => &v.cnst,
      LeanConstantInfo::DefnInfo(v) => &v.cnst,
      LeanConstantInfo::ThmInfo(v) => &v.cnst,
      LeanConstantInfo::OpaqueInfo(v) => &v.cnst,
      LeanConstantInfo::QuotInfo(v) => &v.cnst,
      LeanConstantInfo::InductInfo(v) => &v.cnst,
      LeanConstantInfo::CtorInfo(v) => &v.cnst,
      LeanConstantInfo::RecInfo(v) => &v.cnst,
    }
  }
}

/// Walk two expressions in parallel and find the first structural difference.
fn find_first_diff(a: &env::Expr, b: &env::Expr, path: &str) -> String {
  use env::ExprData;
  if a.get_hash() == b.get_hash() {
    return format!("{path}: hashes match (should not happen)");
  }
  match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => {
      format!("{path}: bvar {i} vs {j}")
    }
    (ExprData::Sort(l1, _), ExprData::Sort(l2, _)) => {
      format!("{path}: sort level hash {} vs {}", l1.get_hash(), l2.get_hash())
    }
    (ExprData::Const(n1, ls1, _), ExprData::Const(n2, ls2, _)) => {
      if n1 != n2 {
        format!("{path}: const name {} vs {}", n1.pretty(), n2.pretty())
      } else {
        format!("{path}: const {} levels differ ({} vs {})", n1.pretty(), ls1.len(), ls2.len())
      }
    }
    (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      if f1.get_hash() != f2.get_hash() {
        find_first_diff(f1, f2, &format!("{path}.app.fn"))
      } else {
        find_first_diff(a1, a2, &format!("{path}.app.arg"))
      }
    }
    (ExprData::Lam(n1, t1, b1, bi1, _), ExprData::Lam(n2, t2, b2, bi2, _)) => {
      if n1 != n2 { return format!("{path}: lam name {} vs {}", n1.pretty(), n2.pretty()); }
      if bi1 != bi2 { return format!("{path}: lam bi {:?} vs {:?}", bi1, bi2); }
      if t1.get_hash() != t2.get_hash() {
        find_first_diff(t1, t2, &format!("{path}.lam.ty"))
      } else {
        find_first_diff(b1, b2, &format!("{path}.lam.body"))
      }
    }
    (ExprData::ForallE(n1, t1, b1, bi1, _), ExprData::ForallE(n2, t2, b2, bi2, _)) => {
      if n1 != n2 { return format!("{path}: forall name {} vs {}", n1.pretty(), n2.pretty()); }
      if bi1 != bi2 { return format!("{path}: forall bi {:?} vs {:?}", bi1, bi2); }
      if t1.get_hash() != t2.get_hash() {
        find_first_diff(t1, t2, &format!("{path}.forall.ty"))
      } else {
        find_first_diff(b1, b2, &format!("{path}.forall.body"))
      }
    }
    (ExprData::LetE(n1, t1, v1, b1, nd1, _), ExprData::LetE(n2, t2, v2, b2, nd2, _)) => {
      if n1 != n2 { return format!("{path}: let name {} vs {}", n1.pretty(), n2.pretty()); }
      if nd1 != nd2 { return format!("{path}: let nonDep {nd1} vs {nd2}"); }
      if t1.get_hash() != t2.get_hash() {
        find_first_diff(t1, t2, &format!("{path}.let.ty"))
      } else if v1.get_hash() != v2.get_hash() {
        find_first_diff(v1, v2, &format!("{path}.let.val"))
      } else {
        find_first_diff(b1, b2, &format!("{path}.let.body"))
      }
    }
    (ExprData::Mdata(_, inner1, _), _) => {
      format!("{path}: orig has mdata wrapper, deconv doesn't")
    }
    (_, ExprData::Mdata(_, inner2, _)) => {
      format!("{path}: deconv has mdata wrapper, orig doesn't")
    }
    (ExprData::Lit(l1, _), ExprData::Lit(l2, _)) => {
      format!("{path}: lit {l1:?} vs {l2:?}")
    }
    (ExprData::Proj(n1, i1, _, _), ExprData::Proj(n2, i2, _, _)) => {
      format!("{path}: proj {}.{} vs {}.{}", n1.pretty(), i1, n2.pretty(), i2)
    }
    _ => {
      format!("{path}: node kind mismatch: {} vs {}", expr_kind(a), expr_kind(b))
    }
  }
}

/// Walk two expression trees and return the first pair of subtrees that differ.
fn find_divergent_subtrees(a: &env::Expr, b: &env::Expr) -> (Option<env::Expr>, Option<env::Expr>) {
  use env::ExprData;
  if a.get_hash() == b.get_hash() { return (None, None); }
  match (a.as_data(), b.as_data()) {
    (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      if f1.get_hash() != f2.get_hash() { return find_divergent_subtrees(f1, f2); }
      if a1.get_hash() != a2.get_hash() { return find_divergent_subtrees(a1, a2); }
      (Some(a.clone()), Some(b.clone()))
    }
    (ExprData::Lam(_, t1, b1, _, _), ExprData::Lam(_, t2, b2, _, _))
    | (ExprData::ForallE(_, t1, b1, _, _), ExprData::ForallE(_, t2, b2, _, _)) => {
      if t1.get_hash() != t2.get_hash() { return find_divergent_subtrees(t1, t2); }
      if b1.get_hash() != b2.get_hash() { return find_divergent_subtrees(b1, b2); }
      (Some(a.clone()), Some(b.clone()))
    }
    (ExprData::LetE(_, t1, v1, b1, _, _), ExprData::LetE(_, t2, v2, b2, _, _)) => {
      if t1.get_hash() != t2.get_hash() { return find_divergent_subtrees(t1, t2); }
      if v1.get_hash() != v2.get_hash() { return find_divergent_subtrees(v1, v2); }
      if b1.get_hash() != b2.get_hash() { return find_divergent_subtrees(b1, b2); }
      (Some(a.clone()), Some(b.clone()))
    }
    // When one side has mdata and the other doesn't, show both
    (ExprData::Mdata(kvs, inner, _), _) => {
      eprintln!("  mdata on ref side: {} entries, inner={}", kvs.len(), expr_kind(inner));
      for (k, v) in kvs {
        eprintln!("    key={} val_kind={}", k.pretty(), match v {
          env::DataValue::OfString(_) => "OfString",
          env::DataValue::OfBool(_) => "OfBool",
          env::DataValue::OfName(_) => "OfName",
          env::DataValue::OfNat(_) => "OfNat",
          env::DataValue::OfInt(_) => "OfInt",
          env::DataValue::OfSyntax(_) => "OfSyntax",
        });
      }
      eprintln!("  ref expr: {}", debug_expr(a, 2));
      eprintln!("  deconv expr: {}", debug_expr(b, 2));
      (Some(a.clone()), Some(b.clone()))
    }
    (_, ExprData::Mdata(kvs, inner, _)) => {
      eprintln!("  mdata on deconv side: {} entries, inner={}", kvs.len(), expr_kind(inner));
      (Some(a.clone()), Some(b.clone()))
    }
    _ => (Some(a.clone()), Some(b.clone()))
  }
}

fn expr_kind(e: &env::Expr) -> &'static str {
  use env::ExprData;
  match e.as_data() {
    ExprData::Bvar(..) => "bvar",
    ExprData::Sort(..) => "sort",
    ExprData::Const(..) => "const",
    ExprData::App(..) => "app",
    ExprData::Lam(..) => "lam",
    ExprData::ForallE(..) => "forall",
    ExprData::LetE(..) => "let",
    ExprData::Lit(..) => "lit",
    ExprData::Proj(..) => "proj",
    ExprData::Mdata(..) => "mdata",
    ExprData::Fvar(..) => "fvar",
    ExprData::Mvar(..) => "mvar",
  }
}
