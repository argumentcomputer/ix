//! The source side of a Lean block's auxiliaries, read by the compiler's
//! passes: the application telescope, and the split-minor helpers of O2 and
//! O11a (`pass3::opt`): the nested motives of a source recursor
//! ([`aux_motive_sigs`]), the constructor a source minor eliminates
//! ([`source_ctor_for_minor`]), its type in caller terms
//! ([`source_minor_type`]), binder peeling ([`peel_binders`]) and the
//! recursive target of a minor's field ([`find_source_rec_target`]). Lean:
//! `Ix/AuxSource.lean`.
//!
//! History: until M6R slice 6 (2026-10-07) these lived in `surgery.rs`, the
//! legacy call-site surgery (`IX_PASS3=off`), which rewrote the call sites of
//! a changed block by plans. Pass 3 replaced it (the flip, M6) and slice 6
//! deleted it; O2 and O11a read a split block's source minors with the same
//! helpers, which is why they stay.

use ix_common::env::{
  ConstantInfo as LeanConstantInfo, ConstructorVal, Env as LeanEnv,
  Expr as LeanExpr, ExprData, Level, Name, RecursorVal,
};

use super::{
  aux_gen::expr_utils::{
    LocalDecl, consume_type_annotations, decompose_apps, fresh_fvar,
    instantiate_rev, instantiate1, subst_levels,
  },
  nat_conv::nat_to_usize,
};

/// Collect a Lean App telescope: peel App nodes to get `(head, [a1, ..., aN])`.
///
/// Arguments are returned in application order (leftmost first).
pub fn collect_lean_telescope<'a>(
  e: &'a LeanExpr,
) -> (&'a LeanExpr, Vec<&'a LeanExpr>) {
  let mut args: Vec<&'a LeanExpr> = Vec::new();
  let mut cur = e;
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a);
    cur = f;
  }
  args.reverse();
  (cur, args)
}

pub(crate) fn source_ctor_for_minor(
  src_minor_idx: usize,
  rec: &RecursorVal,
  lean_env: &LeanEnv,
  aux_sigs: &[AuxMotiveSig],
) -> Option<(usize, ConstructorVal)> {
  let mut offset = 0usize;
  for (source_pos, ind_name) in rec.all.iter().enumerate() {
    let ind_info = lean_env.get(ind_name)?;
    let ind = match &*ind_info {
      LeanConstantInfo::InductInfo(ind) => ind,
      _ => return None,
    };
    let n_ctors = ind.ctors.len();
    if src_minor_idx < offset + n_ctors {
      let ctor_name = &ind.ctors[src_minor_idx - offset];
      let ctor = match &*lean_env.get(ctor_name)? {
        LeanConstantInfo::CtorInfo(ctor) => ctor.clone(),
        _ => return None,
      };
      return Some((source_pos, ctor));
    }
    offset += n_ctors;
  }
  // Aux minor bands follow the user bands, one per source aux in source
  // order. The ctor list is the external inductive's own (the aux is the
  // external applied at spec args, so field counts match).
  for sig in aux_sigs {
    let ext_entry = lean_env.get(&sig.ext_name);
    let Some(LeanConstantInfo::InductInfo(ind)) = ext_entry.as_deref() else {
      return None;
    };
    let n_ctors = ind.ctors.len();
    if src_minor_idx < offset + n_ctors {
      let ctor_name = &ind.ctors[src_minor_idx - offset];
      let ctor = match &*lean_env.get(ctor_name)? {
        LeanConstantInfo::CtorInfo(ctor) => ctor.clone(),
        _ => return None,
      };
      return Some((sig.source_pos, ctor));
    }
    offset += n_ctors;
  }
  None
}

/// Signature of a nested-aux motive read off a source recursor's type:
/// motive `source_pos` targets `ext_name specs… idx…`. Spec args are
/// concrete (the recursor type is instantiated with call-site params
/// before extraction), so field types can be matched against them by hash.
pub(crate) struct AuxMotiveSig {
  source_pos: usize,
  ext_name: Name,
  ext_n_params: usize,
  specs: Vec<LeanExpr>,
}

/// Extract [`AuxMotiveSig`]s for every aux motive position (`>= all.len()`)
/// of `rec`, by walking its type instantiated with the call site's levels,
/// params, and motives.
pub(crate) fn aux_motive_sigs(
  rec: &RecursorVal,
  rec_levels: &[Level],
  params: &[LeanExpr],
  motives: &[LeanExpr],
  lean_env: &LeanEnv,
) -> Vec<AuxMotiveSig> {
  let n_user = rec.all.len();
  let n_motives = nat_to_usize(&rec.num_motives);
  let mut out = Vec::new();
  if n_motives <= n_user {
    return out;
  }
  let mut cur = subst_levels(&rec.cnst.typ, &rec.cnst.level_params, rec_levels);
  for arg in params {
    match cur.as_data() {
      // Shift-aware substitution — args may reference the caller's
      // telescope (see `source_minor_type`).
      ExprData::ForallE(_, _, body, _, _) => {
        cur = instantiate_rev(body, std::slice::from_ref(arg));
      },
      _ => return out,
    }
  }
  for (m_idx, motive) in motives.iter().enumerate().take(n_motives) {
    let next = match cur.as_data() {
      ExprData::ForallE(_, dom, body, _, _) => {
        if m_idx >= n_user {
          // dom = `∀ idx…, Ext specs… idx… → Sort _` — the major's type is
          // the last peeled domain.
          let mut d = consume_type_annotations(dom);
          let mut last_dom: Option<LeanExpr> = None;
          let mut i = 0usize;
          while let ExprData::ForallE(_, dd, db, _, _) = d.as_data() {
            last_dom = Some(consume_type_annotations(dd));
            let (_, fv) = fresh_fvar("aux_sig_idx", m_idx * 64 + i);
            d = instantiate1(db, &fv);
            i += 1;
          }
          if let Some(t) = last_dom {
            let (head, t_args) = decompose_apps(&t);
            if let ExprData::Const(ext_name, _, _) = head.as_data()
              && let Some(LeanConstantInfo::InductInfo(ind)) =
                lean_env.get(ext_name).as_deref()
            {
              let ext_n_params = nat_to_usize(&ind.num_params);
              if t_args.len() >= ext_n_params {
                out.push(AuxMotiveSig {
                  source_pos: m_idx,
                  ext_name: ext_name.clone(),
                  ext_n_params,
                  specs: t_args.into_iter().take(ext_n_params).collect(),
                });
              }
            }
          }
        }
        instantiate_rev(body, std::slice::from_ref(motive))
      },
      _ => return out,
    };
    cur = next;
  }
  out
}

pub(crate) fn source_minor_type(
  rec: &RecursorVal,
  rec_levels: &[Level],
  params: &[LeanExpr],
  motives: &[LeanExpr],
  minors: &[LeanExpr],
  src_minor_idx: usize,
) -> Option<LeanExpr> {
  let mut cur = subst_levels(&rec.cnst.typ, &rec.cnst.level_params, rec_levels);
  for arg in
    params.iter().chain(motives.iter()).chain(minors.iter().take(src_minor_idx))
  {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        // `instantiate_rev`, not `instantiate1`: call-site args may carry
        // loose BVars into the caller's telescope (rec applications under
        // binders, e.g. `.brecOn_N.go` bodies) and must be lifted when
        // substituted under the type's remaining binders.
        cur = instantiate_rev(body, std::slice::from_ref(arg));
      },
      _ => return None,
    }
  }
  match cur.as_data() {
    ExprData::ForallE(_, dom, _, _, _) => Some(consume_type_annotations(dom)),
    _ => None,
  }
}

pub(crate) fn peel_binders(
  mut cur: LeanExpr,
  n: usize,
  prefix: &str,
  offset: usize,
) -> Option<(Vec<LocalDecl>, Vec<LeanExpr>, LeanExpr)> {
  let mut decls = Vec::with_capacity(n);
  let mut fvars = Vec::with_capacity(n);
  for i in 0..n {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar(prefix, offset + i);
        let decl = LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: consume_type_annotations(dom),
          info: bi.clone(),
        };
        cur = instantiate1(body, &fv);
        fvars.push(fv);
        decls.push(decl);
      },
      _ => return None,
    }
  }
  Some((decls, fvars, cur))
}

#[derive(Clone)]
pub(crate) struct SourceRecTarget {
  pub(crate) source_pos: usize,
  pub(crate) idx_args: Vec<LeanExpr>,
  pub(crate) xs_decls: Vec<LocalDecl>,
  pub(crate) xs_fvars: Vec<LeanExpr>,
}

pub(crate) fn find_source_rec_target(
  dom: &LeanExpr,
  original_all: &[Name],
  params: &[LeanExpr],
  lean_env: &LeanEnv,
  prefix: &str,
  field_idx: usize,
  aux_sigs: &[AuxMotiveSig],
) -> Option<SourceRecTarget> {
  let mut cur = consume_type_annotations(dom);
  let mut xs_decls = Vec::new();
  let mut xs_fvars = Vec::new();

  while let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() {
    let (fv_name, fv) =
      fresh_fvar(prefix, field_idx.saturating_mul(1024) + xs_fvars.len());
    let decl = LocalDecl {
      fvar_name: fv_name,
      binder_name: name.clone(),
      domain: consume_type_annotations(dom),
      info: bi.clone(),
    };
    cur = instantiate1(body, &fv);
    xs_fvars.push(fv);
    xs_decls.push(decl);
  }

  let (head, args) = decompose_apps(&cur);
  let ExprData::Const(target_name, _, _) = head.as_data() else {
    return None;
  };
  if let Some(source_pos) = original_all.iter().position(|n| n == target_name) {
    let target_n_params = match &*lean_env.get(target_name)? {
      LeanConstantInfo::InductInfo(ind) => nat_to_usize(&ind.num_params),
      _ => return None,
    };
    if args.len() < target_n_params || params.len() < target_n_params {
      return None;
    }
    if !args[..target_n_params]
      .iter()
      .zip(params.iter())
      .all(|(arg, param)| arg.get_hash() == param.get_hash())
    {
      return None;
    }
    return Some(SourceRecTarget {
      source_pos,
      idx_args: args.into_iter().skip(target_n_params).collect(),
      xs_decls,
      xs_fvars,
    });
  }
  // Nested-aux target: the field's type is an external-inductive
  // application matching one of the recursor's aux motive signatures
  // (`List B` targeting motive `n_user + j`). Spec args are compared by
  // hash — both sides are instantiated with the same call-site params.
  let matched = aux_sigs.iter().find(|sig| {
    *target_name == sig.ext_name
      && args.len() >= sig.ext_n_params
      && args[..sig.ext_n_params]
        .iter()
        .zip(sig.specs.iter())
        .all(|(arg, spec)| arg.get_hash() == spec.get_hash())
  })?;
  Some(SourceRecTarget {
    source_pos: matched.source_pos,
    idx_args: args.into_iter().skip(matched.ext_n_params).collect(),
    xs_decls,
    xs_fvars,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use bignat::Nat;

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  #[test]
  fn test_collect_lean_telescope() {
    let f = LeanExpr::cnst(n("f"), vec![]);
    let a1 = LeanExpr::bvar(Nat::from(0u64));
    let a2 = LeanExpr::bvar(Nat::from(1u64));
    let a3 = LeanExpr::bvar(Nat::from(2u64));
    let app = LeanExpr::app(
      LeanExpr::app(LeanExpr::app(f.clone(), a1.clone()), a2.clone()),
      a3.clone(),
    );
    let (head, args) = collect_lean_telescope(&app);
    assert_eq!(head.get_hash(), f.get_hash());
    assert_eq!(args.len(), 3);
    assert_eq!(args[0].get_hash(), a1.get_hash());
    assert_eq!(args[1].get_hash(), a2.get_hash());
    assert_eq!(args[2].get_hash(), a3.get_hash());
  }
}
