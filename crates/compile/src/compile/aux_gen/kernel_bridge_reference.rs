//! Frozen pre-memoization bridge transforms for small differential fixtures.

use crate::compile::nat_conv::nat_to_u64;
use bignat::Nat;
use ix_common::address::Address;
use ix_common::env::{Expr as LeanExpr, ExprData, Level, Name};
use ix_kernel::ingress::{lean_level_to_kuniv, resolve_lean_name_addr};
use ix_kernel::mode::Meta;
use rustc_hash::FxHashMap;

pub(super) fn kexpr_to_lean(
  expr: &ix_kernel::expr::KExpr<Meta>,
  outer_depth: usize,
  fvar_levels: &FxHashMap<Name, usize>,
  local_depth: usize,
  param_names: &[Name],
) -> LeanExpr {
  use ix_kernel::expr::ExprData as KED;

  // Reverse `fvar_levels` lazily via linear search — the FVar context is
  // small in practice (a handful of param/motive/minor/index binders),
  // so an O(n) scan per Var hit is cheaper than maintaining an inverse
  // map alongside `TcScope`.
  let lookup_fvar = |level: usize| -> Option<Name> {
    fvar_levels.iter().find_map(|(name, &lvl)| {
      if lvl == level { Some(name.clone()) } else { None }
    })
  };

  let inner = match expr.data() {
    KED::Var(i, _, _) => {
      let i = *i as usize;
      if i < local_depth {
        LeanExpr::bvar(Nat::from(i as u64))
      } else {
        let fvar_idx_from_top = i - local_depth;
        let level = outer_depth
          .checked_sub(fvar_idx_from_top + 1)
          .expect("kexpr_to_lean: Var index out of range of outer context");
        let name = lookup_fvar(level).unwrap_or_else(|| {
          // Unregistered FVar — indicates mismatched `fvar_levels` vs.
          // the expression's Var indices. Use a synthetic placeholder
          // rather than panic so diagnostics can surface the issue.
          Name::str(Name::anon(), format!("_dangling_fvar_{level}"))
        });
        LeanExpr::fvar(name)
      }
    },
    // Kernel-side FVar nodes (introduced by binder opening during type
    // checking) should never appear in the inputs of `kexpr_to_lean`,
    // which converts ingressed/compile-time expressions back to Lean
    // syntax. If one does appear, it indicates a path leaked an open
    // expression past its abstraction step — treat it as a synthetic
    // free variable named after its id so diagnostics can surface it.
    KED::FVar(id, _, _) => {
      LeanExpr::fvar(Name::str(Name::anon(), format!("_kernel_fvar_{}", id.0)))
    },
    KED::Sort(u, _) => {
      LeanExpr::sort(super::below::kuniv_to_level(u, param_names))
    },
    KED::Const(kid, us, _) => {
      let levels: Vec<Level> = us
        .iter()
        .map(|u| super::below::kuniv_to_level(u, param_names))
        .collect();
      LeanExpr::cnst(kid.name.clone(), levels)
    },
    KED::App(f, a, _) => LeanExpr::app(
      kexpr_to_lean(f, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(a, outer_depth, fvar_levels, local_depth, param_names),
    ),
    KED::All(name, bi, d, b, _) => LeanExpr::all(
      name.clone(),
      kexpr_to_lean(d, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(b, outer_depth, fvar_levels, local_depth + 1, param_names),
      bi.clone(),
    ),
    KED::Lam(name, bi, d, b, _) => LeanExpr::lam(
      name.clone(),
      kexpr_to_lean(d, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(b, outer_depth, fvar_levels, local_depth + 1, param_names),
      bi.clone(),
    ),
    KED::Let(name, ty, val, body, nd, _) => LeanExpr::letE(
      name.clone(),
      kexpr_to_lean(ty, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(val, outer_depth, fvar_levels, local_depth, param_names),
      kexpr_to_lean(
        body,
        outer_depth,
        fvar_levels,
        local_depth + 1,
        param_names,
      ),
      *nd,
    ),
    KED::Prj(kid, field, val, _) => LeanExpr::proj(
      kid.name.clone(),
      Nat::from(*field),
      kexpr_to_lean(val, outer_depth, fvar_levels, local_depth, param_names),
    ),
    KED::Nat(n, _, _) => {
      use ix_common::env::Literal;
      LeanExpr::lit(Literal::NatVal(n.clone()))
    },
    KED::Str(s, _, _) => {
      use ix_common::env::Literal;
      LeanExpr::lit(Literal::StrVal(s.clone()))
    },
  };

  // Re-wrap mdata layers, outermost first (matching egress_expr's order).
  expr
    .mdata()
    .iter()
    .rev()
    .fold(inner, |acc, kvs| LeanExpr::mdata(kvs.clone(), acc))
}

pub(super) fn restore_source_names_same_content(
  generated: &LeanExpr,
  source: &LeanExpr,
  stt: &crate::compile::CompileState,
) -> LeanExpr {
  let source = strip_mdata_ref(source);

  match generated.as_data() {
    ExprData::Mdata(kvs, inner, _) => LeanExpr::mdata(
      kvs.clone(),
      restore_source_names_same_content(inner, source, stt),
    ),
    _ => restore_source_names_same_content_inner(generated, source, stt),
  }
}

fn restore_source_names_same_content_inner(
  generated: &LeanExpr,
  source: &LeanExpr,
  stt: &crate::compile::CompileState,
) -> LeanExpr {
  match (generated.as_data(), source.as_data()) {
    (
      ExprData::Const(gen_name, gen_lvls, _),
      ExprData::Const(source_name, _, _),
    ) if same_resolved_name_addr(gen_name, source_name, stt) => {
      LeanExpr::cnst(source_name.clone(), gen_lvls.clone())
    },
    (ExprData::App(gen_f, gen_a, _), ExprData::App(source_f, source_a, _)) => {
      LeanExpr::app(
        restore_source_names_same_content(gen_f, source_f, stt),
        restore_source_names_same_content(gen_a, source_a, stt),
      )
    },
    (
      ExprData::ForallE(_, gen_dom, gen_body, gen_bi, _),
      ExprData::ForallE(source_name, source_dom, source_body, _, _),
    ) => LeanExpr::all(
      source_name.clone(),
      restore_source_names_same_content(gen_dom, source_dom, stt),
      restore_source_names_same_content(gen_body, source_body, stt),
      gen_bi.clone(),
    ),
    (
      ExprData::Lam(_, gen_dom, gen_body, gen_bi, _),
      ExprData::Lam(source_name, source_dom, source_body, _, _),
    ) => LeanExpr::lam(
      source_name.clone(),
      restore_source_names_same_content(gen_dom, source_dom, stt),
      restore_source_names_same_content(gen_body, source_body, stt),
      gen_bi.clone(),
    ),
    (
      ExprData::LetE(_, gen_ty, gen_val, gen_body, gen_nd, _),
      ExprData::LetE(source_name, source_ty, source_val, source_body, _, _),
    ) => LeanExpr::letE(
      source_name.clone(),
      restore_source_names_same_content(gen_ty, source_ty, stt),
      restore_source_names_same_content(gen_val, source_val, stt),
      restore_source_names_same_content(gen_body, source_body, stt),
      *gen_nd,
    ),
    (
      ExprData::Proj(gen_name, gen_field, gen_val, _),
      ExprData::Proj(source_name, source_field, source_val, _),
    ) if gen_field == source_field
      && same_resolved_name_addr(gen_name, source_name, stt) =>
    {
      LeanExpr::proj(
        source_name.clone(),
        gen_field.clone(),
        restore_source_names_same_content(gen_val, source_val, stt),
      )
    },
    _ => generated.clone(),
  }
}

fn strip_mdata_ref(mut expr: &LeanExpr) -> &LeanExpr {
  while let ExprData::Mdata(_, inner, _) = expr.as_data() {
    expr = inner;
  }
  expr
}

fn same_resolved_name_addr(
  a: &Name,
  b: &Name,
  stt: &crate::compile::CompileState,
) -> bool {
  if a == b {
    return true;
  }
  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  resolve_lean_name_addr(a, n2a, aux_n2a)
    == resolve_lean_name_addr(b, n2a, aux_n2a)
}

/// Static version of `to_kexpr` that takes borrowed references.
///
/// Identical to the closure-based `to_kexpr` in `get_level`, but as a
/// standalone function so it can be called from both `PreparedTC::new`
/// and `get_level_with_tc`.
pub(super) fn to_kexpr_static(
  expr: &LeanExpr,
  fvar_levels: &FxHashMap<Name, usize>,
  ctx_depth: usize,
  param_names: &[Name],
  stt: &crate::compile::CompileState,
) -> ix_kernel::expr::KExpr<Meta> {
  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  use ix_kernel::expr::KExpr;
  use ix_kernel::id::KId;
  use ix_kernel::level::KUniv;

  match expr.as_data() {
    ExprData::Fvar(fname, _) => {
      if let Some(&level) = fvar_levels.get(fname) {
        KExpr::var((ctx_depth - level - 1) as u64, Name::anon())
      } else {
        KExpr::sort(KUniv::zero())
      }
    },
    ExprData::Bvar(idx, _) => KExpr::var(nat_to_u64(idx), Name::anon()),
    ExprData::Sort(lvl, _) => {
      KExpr::sort(lean_level_to_kuniv(lvl, param_names))
    },
    ExprData::Const(cname, us, _) => {
      let addr = resolve_lean_name_addr(cname, n2a, aux_n2a);
      let zid = KId::new(addr, cname.clone());
      let zus: Box<[KUniv<Meta>]> =
        us.iter().map(|u| lean_level_to_kuniv(u, param_names)).collect();
      KExpr::cnst(zid, zus)
    },
    ExprData::App(f, a, _) => {
      let kf = to_kexpr_static(f, fvar_levels, ctx_depth, param_names, stt);
      let ka = to_kexpr_static(a, fvar_levels, ctx_depth, param_names, stt);
      KExpr::app(kf, ka)
    },
    ExprData::ForallE(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::all(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::Lam(binder_name, dom, body, bi, _) => {
      let kd = to_kexpr_static(dom, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::lam(binder_name.clone(), bi.clone(), kd, kb)
    },
    ExprData::LetE(binder_name, ty, val, body, nd, _) => {
      let kt = to_kexpr_static(ty, fvar_levels, ctx_depth, param_names, stt);
      let kv = to_kexpr_static(val, fvar_levels, ctx_depth, param_names, stt);
      let kb =
        to_kexpr_static(body, fvar_levels, ctx_depth + 1, param_names, stt);
      KExpr::let_(binder_name.clone(), kt, kv, kb, *nd)
    },
    ExprData::Proj(pname, idx, e, _) => {
      let addr = resolve_lean_name_addr(pname, n2a, aux_n2a);
      let zid = KId::new(addr, pname.clone());
      let ke = to_kexpr_static(e, fvar_levels, ctx_depth, param_names, stt);
      KExpr::prj(zid, nat_to_u64(idx), ke)
    },
    ExprData::Lit(lit, _) => {
      use ix_common::env::Literal;
      match lit {
        Literal::NatVal(n) => {
          let addr = Address::hash(&nat_to_u64(n).to_le_bytes());
          KExpr::nat(n.clone(), addr)
        },
        Literal::StrVal(s) => {
          let addr = Address::hash(s.as_bytes());
          KExpr::str(s.clone(), addr)
        },
      }
    },
    ExprData::Mdata(_, inner, _) => {
      to_kexpr_static(inner, fvar_levels, ctx_depth, param_names, stt)
    },
    _ => KExpr::sort(KUniv::zero()),
  }
}
