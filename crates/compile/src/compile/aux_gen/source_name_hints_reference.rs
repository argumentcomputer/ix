//! Frozen pre-cache source-name hint traversal for differential tests.
//! The legacy u64 key is intentionally retained here, including its collision
//! behavior; collision regressions test the new exact matcher separately.

use super::*;

pub(super) fn source_name_hint_candidate(expr: &LeanExpr) -> bool {
  matches!(expr.as_data(), ExprData::App(..) | ExprData::Proj(..))
}

/// Name-erased structural content key for the source-name hint map.
///
/// Mirrors the equivalence of the Lean pipeline's `Ix.Tc.KExpr` content
/// addresses (`toKexprStatic ... |>.addr` in `Ix/AuxGen/Kernel.lean`) and
/// of the kernel's `ExprKey`/`structural_eq`: display names, binder
/// names, binder infos, and mdata are excluded; `Const`/`Prj` contribute
/// their resolved content address, universes their index structure. Two
/// spellings of one alias pair (`Paths V` / `Symmetrify V`) therefore
/// agree on this key — which is the whole point of the hint map.
///
/// `KExpr::hash_key()` is NOT usable here: it is the intern-assigned uid,
/// fresh for every un-interned construction, and `to_kexpr_static` does
/// not intern — so the collect-time and restore-time keys of two
/// content-equal subterms never matched, and the hint map restored
/// nothing (the Mathlib `Quiver.FreeGroupoid.redStep` metadata
/// divergence, canonicity §10.5).
pub(super) fn kexpr_content_key(e: &ix_kernel::expr::KExpr<Meta>) -> u64 {
  use std::hash::Hasher;
  let mut h = rustc_hash::FxHasher::default();
  kexpr_content_hash(e, &mut h);
  h.finish()
}

pub(super) fn kuniv_content_hash(
  u: &ix_kernel::level::KUniv<Meta>,
  h: &mut rustc_hash::FxHasher,
) {
  use ix_kernel::level::UnivData as UD;
  use std::hash::Hasher;
  match u.data() {
    UD::Zero(_) => h.write_u8(0),
    UD::Succ(a, _) => {
      h.write_u8(1);
      kuniv_content_hash(a, h);
    },
    UD::Max(a, b, _) => {
      h.write_u8(2);
      kuniv_content_hash(a, h);
      kuniv_content_hash(b, h);
    },
    UD::IMax(a, b, _) => {
      h.write_u8(3);
      kuniv_content_hash(a, h);
      kuniv_content_hash(b, h);
    },
    UD::Param(idx, _, _) => {
      h.write_u8(4);
      h.write_u64(*idx);
    },
  }
}

pub(super) fn kexpr_content_hash(
  e: &ix_kernel::expr::KExpr<Meta>,
  h: &mut rustc_hash::FxHasher,
) {
  use ix_kernel::expr::ExprData as KED;
  use std::hash::Hasher;
  match e.data() {
    KED::Var(i, _, _) => {
      h.write_u8(0);
      h.write_u64(*i);
    },
    KED::FVar(id, _, _) => {
      h.write_u8(1);
      h.write_u64(id.0);
    },
    KED::Sort(u, _) => {
      h.write_u8(2);
      kuniv_content_hash(u, h);
    },
    KED::Const(id, us, _) => {
      h.write_u8(3);
      h.write(id.addr.as_bytes());
      h.write_u64(us.len() as u64);
      for u in us.iter() {
        kuniv_content_hash(u, h);
      }
    },
    KED::App(f, a, _) => {
      h.write_u8(4);
      kexpr_content_hash(f, h);
      kexpr_content_hash(a, h);
    },
    KED::Lam(_, _, t, b, _) => {
      h.write_u8(5);
      kexpr_content_hash(t, h);
      kexpr_content_hash(b, h);
    },
    KED::All(_, _, t, b, _) => {
      h.write_u8(6);
      kexpr_content_hash(t, h);
      kexpr_content_hash(b, h);
    },
    KED::Let(_, t, v, b, nd, _) => {
      h.write_u8(7);
      h.write_u8(u8::from(*nd));
      kexpr_content_hash(t, h);
      kexpr_content_hash(v, h);
      kexpr_content_hash(b, h);
    },
    KED::Prj(id, f, v, _) => {
      h.write_u8(8);
      h.write(id.addr.as_bytes());
      h.write_u64(*f);
      kexpr_content_hash(v, h);
    },
    KED::Nat(_, ba, _) => {
      h.write_u8(9);
      h.write(ba.as_bytes());
    },
    KED::Str(_, ba, _) => {
      h.write_u8(10);
      h.write(ba.as_bytes());
    },
  }
}

/// Collect source-shaped subterms that WHNF may copy into a reduct.
///
/// Keys use the kernel content hash so alpha-collapsed aliases like
/// `CategoryTheory.Paths V` and `Quiver.Symmetrify V` line up, while values
/// keep the Lean display names from the caller. We skip BVar-containing terms:
/// WHNF may lift copied arguments under freshly-exposed binders, so matching
/// those by raw de Bruijn indices would be unstable.
pub(super) fn collect_lean_source_name_hints(
  source: &LeanExpr,
  fvar_levels: &FxHashMap<Name, usize>,
  depth: usize,
  param_names: &[Name],
  stt: &crate::compile::CompileState,
  out: &mut FxHashMap<ix_kernel::env::Addr, LeanExpr>,
) {
  if source_name_hint_candidate(source) && !expr_has_bvar(source) {
    let key = kexpr_content_key(&to_kexpr_static(
      source,
      fvar_levels,
      depth,
      param_names,
      stt,
    ));
    out.entry(key).or_insert_with(|| source.clone());
  }

  match source.as_data() {
    ExprData::Mdata(_, inner, _) => collect_lean_source_name_hints(
      inner,
      fvar_levels,
      depth,
      param_names,
      stt,
      out,
    ),
    ExprData::App(f, a, _) => {
      collect_lean_source_name_hints(
        f,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
      collect_lean_source_name_hints(
        a,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
    },
    ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
      collect_lean_source_name_hints(
        d,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
      collect_lean_source_name_hints(
        b,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      collect_lean_source_name_hints(
        t,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
      collect_lean_source_name_hints(
        v,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
      collect_lean_source_name_hints(
        b,
        fvar_levels,
        depth,
        param_names,
        stt,
        out,
      );
    },
    ExprData::Proj(_, _, v, _) => collect_lean_source_name_hints(
      v,
      fvar_levels,
      depth,
      param_names,
      stt,
      out,
    ),
    _ => {},
  }
}

/// Restore source spellings for copied subterms after a real WHNF reduction.
///
/// This is intentionally subterm-based rather than whole-expression based:
/// unfolding a reducible alias such as `HomRel (Paths (Symmetrify V))` should
/// keep the expanded `∀` telescope, but the repeated argument subterms inside
/// that telescope should retain the caller's `Symmetrify` spelling instead of
/// whichever same-address alias the kernel cache/intern table already held.
pub(super) fn restore_lean_source_name_hints(
  generated: &LeanExpr,
  fvar_levels: &FxHashMap<Name, usize>,
  depth: usize,
  param_names: &[Name],
  stt: &crate::compile::CompileState,
  hints: &FxHashMap<ix_kernel::env::Addr, LeanExpr>,
) -> LeanExpr {
  if source_name_hint_candidate(generated) && !expr_has_bvar(generated) {
    let key = kexpr_content_key(&to_kexpr_static(
      generated,
      fvar_levels,
      depth,
      param_names,
      stt,
    ));
    if let Some(source) = hints.get(&key) {
      return source.clone();
    }
  }

  match generated.as_data() {
    ExprData::App(f, a, _) => LeanExpr::app(
      restore_lean_source_name_hints(
        f,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      restore_lean_source_name_hints(
        a,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
    ),
    ExprData::ForallE(n, d, b, bi, _) => LeanExpr::all(
      n.clone(),
      restore_lean_source_name_hints(
        d,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      restore_lean_source_name_hints(
        b,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      bi.clone(),
    ),
    ExprData::Lam(n, d, b, bi, _) => LeanExpr::lam(
      n.clone(),
      restore_lean_source_name_hints(
        d,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      restore_lean_source_name_hints(
        b,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      restore_lean_source_name_hints(
        t,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      restore_lean_source_name_hints(
        v,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      restore_lean_source_name_hints(
        b,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
      *nd,
    ),
    ExprData::Proj(n, i, v, _) => LeanExpr::proj(
      n.clone(),
      i.clone(),
      restore_lean_source_name_hints(
        v,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
    ),
    ExprData::Mdata(kvs, v, _) => LeanExpr::mdata(
      kvs.clone(),
      restore_lean_source_name_hints(
        v,
        fvar_levels,
        depth,
        param_names,
        stt,
        hints,
      ),
    ),
    _ => generated.clone(),
  }
}

pub(super) fn expr_has_bvar(expr: &LeanExpr) -> bool {
  match expr.as_data() {
    ExprData::Bvar(..) => true,
    ExprData::App(f, a, _) => expr_has_bvar(f) || expr_has_bvar(a),
    ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
      expr_has_bvar(d) || expr_has_bvar(b)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      expr_has_bvar(t) || expr_has_bvar(v) || expr_has_bvar(b)
    },
    ExprData::Proj(_, _, v, _) | ExprData::Mdata(_, v, _) => expr_has_bvar(v),
    _ => false,
  }
}
