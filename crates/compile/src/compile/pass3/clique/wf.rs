//! The well-founded transport (a port of `Ix/Compile/Clique/WF.lean`,
//! `WFSchema.lean`, `WFMatcher.lean` and `WFConjugation.lean`).

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::*;
use super::packing::*;
use super::telescope::*;
use crate::compile::pass3::expr::{get_app_fn_args, strip_mdata, subst_levels};

/// `WFLayout`.
#[derive(Clone, Debug)]
pub struct WfLayout {
  pub n: usize,
  pub sigma: Vec<usize>,
  pub mutual_name: Name,
  pub new_mutual_name: Name,
  pub num_fixed: usize,
  pub fixed_perm: Vec<usize>,
  pub leaves: Vec<Expr>,
  pub proof_perm: FxHashMap<Name, Vec<usize>>,
  pub member_fixed: Vec<Vec<usize>>,
}

impl WfLayout {
  pub fn is_clique(&self, s: &Spine) -> bool {
    s.size() == self.n
      && match_packing_leaves(&s.leaves, &self.leaves).is_some()
  }
}

pub fn n_inv_image() -> Name {
  ln("InvImage")
}
pub fn n_wf_relation() -> Name {
  ln("WellFoundedRelation")
}

/// `memberFixedArgs`.
pub fn member_fixed_args(
  mutual_name: &Name,
  m: usize,
  member: &Decl,
) -> R<(Vec<usize>, Expr)> {
  let (ps, body) = peel_lams(lam_arity(&member.value), &member.value);
  let mn = name_to_string(&member.name);
  let Some((h, _, args)) = const_app(&body) else {
    return Err(format!(
      "member {mn}: not an application of the packed function"
    ));
  };
  if !(h == *mutual_name && args.len() == m + 1) {
    return Err(format!(
      "member {mn}: not an application of the packed function"
    ));
  }
  let mut qs = Vec::new();
  for a in args.iter().take(m) {
    match bvar_idx(&strip_mdata(a)) {
      Some(b) => {
        if b < ps.len() {
          qs.push(ps.len() - 1 - b)
        } else {
          return Err(format!("member {mn}: fixed argument out of scope"));
        }
      },
      None => {
        return Err(format!(
          "member {mn}: a fixed argument is not a parameter"
        ));
      },
    }
  }
  if !no_dups(&qs) {
    return Err(format!(
      "member {mn}: distinct fixed parameters alias the same binder"
    ));
  }
  Ok((qs, args[m].clone()))
}

/// `wfLayout`.
pub fn wf_layout(
  members: &[Decl],
  mut_decl: &Decl,
  sigma: &[usize],
  new_mutual_name: &Name,
) -> R<WfLayout> {
  let n = members.len();
  if !(n >= 2 && sigma.len() == n && is_perm(sigma)) {
    return Err("wfLayout: bad permutation".into());
  }
  let ar = forall_arity(&mut_decl.typ);
  if ar < 1 {
    return Err("wfLayout: the packed function has no argument".into());
  }
  let m = ar - 1;
  let (bs, _) = peel_foralls(ar, &mut_decl.typ);
  let Some((_, alpha, _)) = bs.get(m) else {
    return Err("wfLayout: no packed argument".into());
  };
  let Some(s) = decode_spine(PackKind::Psum, n, alpha) else {
    return Err(
      "wfLayout: the packed domain is not Lean's PSum packing".into(),
    );
  };
  let mut qss: Vec<Vec<usize>> = Vec::new();
  for (i, member) in members.iter().enumerate() {
    let (qs, arg) = member_fixed_args(&mut_decl.name, m, member)?;
    match decode_inj(n, &arg) {
      Some((_, j, _)) => {
        if j != i {
          return Err(format!(
            "wfLayout: member {i} injects at summand {j} (not Lean's order)"
          ));
        }
      },
      None => {
        return Err(format!(
          "wfLayout: member {i}'s argument is not an injection"
        ));
      },
    }
    qss.push(qs);
  }
  if !eq_sorted(&qss[0]) {
    return Err(
      "wfLayout: the fixed parameters are not in the first member's order"
        .into(),
    );
  }
  let g = inv_perm(sigma)[0];
  let qg = qss[g].clone();
  let fixed_perm = sort_idx_by_key(m, &|a| qg[a]);
  Ok(WfLayout {
    n,
    sigma: sigma.to_vec(),
    mutual_name: mut_decl.name.clone(),
    new_mutual_name: new_mutual_name.clone(),
    num_fixed: m,
    fixed_perm,
    leaves: s.leaves,
    proof_perm: FxHashMap::default(),
    member_fixed: qss,
  })
}

/// `scanProofs`.
pub fn scan_proofs(
  proofs: &FxHashSet<Name>,
  fixed: &[Name],
  e: &Expr,
  acc: &mut FxHashMap<Name, Vec<usize>>,
) {
  fn visit(
    proofs: &FxHashSet<Name>,
    fixed: &[Name],
    e: &Expr,
    acc: &mut FxHashMap<Name, Vec<usize>>,
    seen: &mut FxHashSet<Hash>,
  ) {
    if !seen.insert(*e.get_hash()) {
      return;
    }

    match e.as_data() {
      ExprData::App(f, a, _) => {
        let (h, args) = get_app_fn_args(e);
        if let ExprData::Const(c, _, _) = h.as_data()
          && proofs.contains(c)
          && !acc.contains_key(c)
        {
          let mut out = Vec::new();
          for x in &args {
            match strip_mdata(x).as_data() {
              ExprData::Fvar(y, _) => match fixed.iter().position(|z| z == y) {
                Some(i) => out.push(i),
                None => break,
              },
              _ => break,
            }
          }
          acc.insert(c.clone(), out);
        }
        visit(proofs, fixed, f, acc, seen);
        visit(proofs, fixed, a, acc, seen);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        visit(proofs, fixed, t, acc, seen);
        visit(proofs, fixed, b, acc, seen);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        visit(proofs, fixed, t, acc, seen);
        visit(proofs, fixed, v, acc, seen);
        visit(proofs, fixed, b, acc, seen);
      },
      ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
        visit(proofs, fixed, x, acc, seen)
      },
      _ => {},
    }
  }
  visit(proofs, fixed, e, acc, &mut FxHashSet::default());
}

/// One constant's outcome (`Transported`).
#[derive(Clone, Debug)]
pub struct Transported {
  pub decl: Decl,
  pub fallback: Option<String>,
}

impl Transported {
  pub fn ok(decl: Decl) -> Self {
    Transported { decl, fallback: None }
  }
}

/// `WFOutput`.
pub struct WfOutput {
  pub decls: Vec<Transported>,
  pub renames: Vec<(Name, Name)>,
}

/// `stripId`.
pub fn strip_id(e: &Expr) -> Expr {
  match const_app(e) {
    Some((h, _, args)) => {
      if h == ln("id") && args.len() == 2 {
        args[1].clone()
      } else {
        e.clone()
      }
    },
    None => e.clone(),
  }
}

/// `eqDefFixStep`.
pub fn eq_def_fix_step(eq_def: &Decl, m: usize, xs: &[Expr]) -> R<Expr> {
  let (bs, body) = peel_lams(m + 1, &eq_def.value);
  if bs.len() != m + 1 {
    return Err(
      "eq_def: the proof does not bind the fixed parameters and the argument"
        .into(),
    );
  }
  let body = inst_locals(&body, xs);
  match const_app(&strip_id(&body)) {
    Some((h, _, args)) if h == ln("Eq.trans") && args.len() == 6 => {
      Ok(args[4].clone())
    },
    _ => Err("eq_def: the proof is not `Eq.trans (fix_eq …) …`".into()),
  }
}

/// `splitPSigma`.
pub fn split_psigma(
  tm: &mut Tm,
  motive: &dyn Fn(Expr) -> Expr,
  leaf: &dyn Fn(Expr) -> Expr,
  fuel: usize,
  ty: &Expr,
  mk: &dyn Fn(Expr) -> Expr,
  major: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("eq_def: PSigma nesting bound exhausted".into());
  }
  let fuel = fuel - 1;
  if let Some((h, us, args)) = const_app(ty)
    && args.len() == 2
  {
    if h == n_psigma() && us.len() == 2 {
      let alpha = args[0].clone();
      let beta = args[1].clone();
      let a = tm.fresh();
      let b = tm.fresh();
      let la = local(a.clone(), root("a"), alpha.clone(), BinderInfo::Default);
      let bty = match strip_mdata(&beta).as_data() {
        ExprData::Lam(_, _, body, _, _) => instantiate_rev(body, &[fvar(&a)]),
        _ => Expr::app(beta.clone(), fvar(&a)),
      };
      let lb = local(b.clone(), root("b"), bty.clone(), BinderInfo::Default);
      let (alpha2, beta2, us2, a2) =
        (alpha.clone(), beta.clone(), us.clone(), a.clone());
      let pair = move |t: Expr| -> Expr {
        mk_app_n(
          cnst(&ln("PSigma.mk"), &us2),
          &[alpha2.clone(), beta2.clone(), fvar(&a2), t],
        )
      };
      let mk2 = |t: Expr| mk(pair(t));
      let inner = split_psigma(tm, motive, leaf, fuel, &bty, &mk2, &fvar(&b))?;
      let t = tm.fresh();
      let lt = local(t.clone(), root("t"), ty.clone(), BinderInfo::Default);
      let mot = mk_lambda(&[lt], &motive(mk(fvar(&t))));
      return Ok(mk_app_n(
        cnst(
          &ln("PSigma.casesOn"),
          &[Level::zero(), us[0].clone(), us[1].clone()],
        ),
        &[alpha, beta, mot, major.clone(), mk_lambda(&[la, lb], &inner)],
      ));
    }
    return Ok(leaf(mk(major.clone())));
  }
  Ok(leaf(mk(major.clone())))
}

/// `onlyCalls`.
pub fn only_calls(fuel: usize, d: usize, e: &Expr) -> bool {
  if fuel == 0 {
    return false;
  }
  let fuel = fuel - 1;
  match e.as_data() {
    ExprData::App(..) => {
      let (h, args) = get_app_fn_args(e);
      let head_ok = match h.as_data() {
        ExprData::Bvar(..) => true,
        _ => only_calls(fuel, d, &h),
      };
      head_ok
        && args.iter().all(|x| {
          let xs = strip_mdata(x);
          !is_bvar(&xs, d) && only_calls(fuel, d, x)
        })
    },
    ExprData::Bvar(..) => !is_bvar(e, d),
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      only_calls(fuel, d, t) && only_calls(fuel, d + 1, b)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      only_calls(fuel, d, t)
        && only_calls(fuel, d, v)
        && only_calls(fuel, d + 1, b)
    },
    ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
      only_calls(fuel, d, x)
    },
    _ => true,
  }
}

/// `leafReduces`.
pub fn leaf_reduces(fuel: usize, e: &Expr) -> bool {
  if fuel == 0 {
    return false;
  }
  let fuel = fuel - 1;
  let (bs, body) = peel_lams(lam_arity(e), e);
  if bs.is_empty() {
    return false;
  }
  match const_app(&body) {
    Some((h, _, args)) => {
      if h == ln("PSigma.casesOn")
        && args.len() == 6
        && is_bvar(&strip_mdata(&args[5]), 0)
      {
        leaf_reduces(fuel, &args[4])
      } else {
        only_calls(DEFAULT_FUEL, 0, &body)
      }
    },
    None => only_calls(DEFAULT_FUEL, 0, &body),
  }
}

// ---------------------------------------------------------------------------
// WFSchema
// ---------------------------------------------------------------------------

/// `applyWFCase`.
pub fn apply_wf_case(function: &Expr, argument: &Expr) -> Expr {
  match strip_mdata(function).as_data() {
    ExprData::Lam(_, _, body, _, _) => {
      instantiate_rev(body, std::slice::from_ref(argument))
    },
    _ => Expr::app(function.clone(), argument.clone()),
  }
}

/// `decodeWFCase`.
pub fn decode_wf_case(
  tm: &mut Tm,
  spine: &Spine,
  sigma: &[usize],
  function: &Expr,
) -> R<Expr> {
  let (locals, body) = open_binders(tm, true, 1, function)?;
  let Some(argument) = locals.first().cloned() else {
    return Err("WF schema: missing case function argument".into());
  };
  if !alpha_eq(&argument.typ, &spine.typ()) {
    return Err("WF schema: case function has a foreign domain".into());
  }
  let body2 = if !mentions_fvar(&argument.fvar, &body) {
    body
  } else {
    let Some(tree) = decode_tree(spine.size(), &body) else {
      return Err(
        "WF schema: input-dependent function is not a case tree".into(),
      );
    };
    if !(alpha_eq(&tree.spine.typ(), &spine.typ())
      && alpha_eq(&tree.major, &argument.expr())
      && tree.extras.is_empty())
    {
      return Err(
        "WF schema: case function has foreign entry identities".into(),
      );
    }
    if tree.leaves.iter().any(|l| mentions_fvar(&argument.fvar, l))
      || mentions_fvar(&argument.fvar, &tree.motive_body)
    {
      return Err(
        "WF schema: case function captures its input outside the decoded major"
          .into(),
      );
    }
    let Some(value) = tree.permute(sigma).build() else {
      return Err("WF schema: case function reconstruction failed".into());
    };
    value
  };
  close_binders(
    true,
    &[Local { typ: spine.permute(sigma).typ(), ..argument }],
    &body2,
  )
}

/// `WFRootSchema`.
#[derive(Clone, Debug)]
pub struct WfRootSchema {
  pub source_spine: Spine,
  pub target_spine: Spine,
  pub source_codomain: Expr,
  pub target_codomain: Expr,
  pub source_measure: Expr,
  pub target_measure: Expr,
  pub head: Expr,
  pub source_arguments: Vec<Expr>,
  pub target_arguments: Vec<Expr>,
  pub source_relation: Option<Expr>,
  pub target_relation: Option<Expr>,
}

impl WfRootSchema {
  pub fn map_expressions(&self, f: &dyn Fn(&Expr) -> Expr) -> WfRootSchema {
    WfRootSchema {
      source_spine: self.source_spine.map_leaves(f),
      target_spine: self.target_spine.map_leaves(f),
      source_codomain: f(&self.source_codomain),
      target_codomain: f(&self.target_codomain),
      source_measure: f(&self.source_measure),
      target_measure: f(&self.target_measure),
      head: self.head.clone(),
      source_arguments: self.source_arguments.iter().map(f).collect(),
      target_arguments: self.target_arguments.iter().map(f).collect(),
      source_relation: self.source_relation.as_ref().map(f),
      target_relation: self.target_relation.as_ref().map(f),
    }
  }
}

/// `rewriteWFObligations`.
pub fn rewrite_wf_obligations(
  schema: &WfRootSchema,
  sigma: &[usize],
  fuel: usize,
  expression: &Expr,
) -> R<Expr> {
  fn visit(
    schema: &WfRootSchema,
    sigma: &[usize],
    fuel: usize,
    expression: &Expr,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> R<Expr> {
    let memo_key = (*expression.get_hash(), fuel);
    if let Some(result) = memo.get(&memo_key) {
      return Ok(result.clone());
    }

    let result = (|| {
      if fuel == 0 {
        return Err("WF obligation: recursion bound".into());
      }
      let fuel = fuel - 1;
      let go = |memo: &mut FxHashMap<(Hash, usize), Expr>, x: &Expr| {
        visit(schema, sigma, fuel, x, memo)
      };
      let (head, args) = get_app_fn_args(expression);
      let relation: Option<(Expr, Expr, Expr)> = (|| {
        if let (Some(source), Some(target)) =
          (&schema.source_relation, &schema.target_relation)
          && alpha_eq(&head, source)
          && args.len() == 2
        {
          return Some((target.clone(), args[0].clone(), args[1].clone()));
        }
        if let Some((name, levels, a)) = const_app(expression)
          && name == n_inv_image()
          && a.len() == 6
          && alpha_eq(&a[0], &schema.source_spine.typ())
          && alpha_eq(&a[3], &schema.source_measure)
        {
          return Some((
            mk_app_n(
              cnst(&name, &levels),
              &[
                schema.target_spine.typ(),
                a[1].clone(),
                a[2].clone(),
                schema.target_measure.clone(),
              ],
            ),
            a[4].clone(),
            a[5].clone(),
          ));
        }
        None
      })();
      if let Some((relation, first, second)) = relation {
        let n = schema.source_spine.size();
        if let Some((fs, fi, fp)) = decode_inj(n, &first)
          && let Some((ss, si, sp)) = decode_inj(n, &second)
          && alpha_eq(&fs.typ(), &schema.source_spine.typ())
          && alpha_eq(&ss.typ(), &schema.source_spine.typ())
        {
          let a = mk_inj(&schema.target_spine, sigma[fi], &go(memo, &fp)?);
          let b = mk_inj(&schema.target_spine, sigma[si], &go(memo, &sp)?);
          return Ok(mk_app_n(relation, &[a, b]));
        }
      }
      Ok(match expression.as_data() {
        ExprData::App(f, a, _) => Expr::app(go(memo, f)?, go(memo, a)?),
        ExprData::Lam(n, t, b, bi, _) => {
          Expr::lam(n.clone(), go(memo, t)?, go(memo, b)?, bi.clone())
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          Expr::all(n.clone(), go(memo, t)?, go(memo, b)?, bi.clone())
        },
        ExprData::LetE(n, t, v, b, nd, _) => {
          Expr::letE(n.clone(), go(memo, t)?, go(memo, v)?, go(memo, b)?, *nd)
        },
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), go(memo, x)?)
        },
        ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(memo, x)?),
        _ => expression.clone(),
      })
    })();

    if let Ok(value) = &result {
      memo.insert(memo_key, value.clone());
    }

    result
  }
  visit(schema, sigma, fuel, expression, &mut FxHashMap::default())
}

/// `decodeWFRoot`.
pub fn decode_wf_root(
  tm: &mut Tm,
  l: &WfLayout,
  value: &Expr,
) -> R<WfRootSchema> {
  let Some((name, levels, args)) = const_app(&strip_mdata(value)) else {
    return Err("WF schema: root is not a fixpoint application".into());
  };
  let is_nat = name == ln("WellFounded.Nat.fix");
  if !((is_nat && args.len() == 4)
    || (name == ln("WellFounded.fix") && args.len() == 5))
  {
    return Err("WF schema: unsupported fixpoint root".into());
  }
  let Some(spine) = decode_spine(PackKind::Psum, l.n, &args[0]) else {
    return Err("WF schema: root has no sum packing".into());
  };
  if !l.is_clique(&spine) {
    return Err("WF schema: root has a foreign packing".into());
  }
  let target_spine = spine.permute(&l.sigma);
  let codomain = decode_wf_case(tm, &spine, &l.sigma, &args[1])?;
  let (measure, target_args) = if is_nat {
    let measure2 = decode_wf_case(tm, &spine, &l.sigma, &args[2])?;
    (args[2].clone(), vec![target_spine.typ(), codomain.clone(), measure2])
  } else {
    let (structure_name, field, relation) =
      match strip_mdata(&args[2]).as_data() {
        ExprData::Proj(s, i, r, _) => {
          (s.clone(), crate::compile::pass3::expr::nat_usize(i), r.clone())
        },
        _ => {
          return Err(
            "WF schema: general relation is not the owned projection".into(),
          );
        },
      };
    if !(structure_name == n_wf_relation() && field == 0) {
      return Err(
        "WF schema: general relation projects another structure".into(),
      );
    }
    let Some((rel_name, rel_levels, rel_args)) = const_app(&relation) else {
      return Err("WF schema: general relation is not invImage".into());
    };
    if !(rel_name == ln("invImage")
      && rel_args.len() == 4
      && alpha_eq(&rel_args[0], &spine.typ()))
    {
      return Err(
        "WF schema: general relation has foreign invImage domain".into(),
      );
    }
    let measure2 = decode_wf_case(tm, &spine, &l.sigma, &rel_args[2])?;
    let target_rel = mk_app_n(
      cnst(&rel_name, &rel_levels),
      &[target_spine.typ(), rel_args[1].clone(), measure2, rel_args[3].clone()],
    );
    let target_relation = proj(&n_wf_relation(), 0, target_rel.clone());
    let mut proof = proj(&n_wf_relation(), 1, target_rel);
    if let Some((wrapper, wrapper_levels, wrapper_args)) = const_app(&args[3])
      && wrapper == ln("Lean.opaqueId")
      && wrapper_args.len() == 2
    {
      let Some(domain_level) = levels.first().cloned() else {
        return Err("WF schema: missing domain universe".into());
      };
      let source_goal = mk_app_n(
        cnst(&ln("WellFounded"), std::slice::from_ref(&domain_level)),
        &[spine.typ(), args[2].clone()],
      );
      if !(alpha_eq(&wrapper_args[0], &source_goal)
        && alpha_eq(
          &wrapper_args[1],
          &proj(&n_wf_relation(), 1, relation.clone()),
        ))
      {
        return Err(
          "WF schema: inline well-founded witness differs from the exact root relation"
            .into(),
        );
      }
      let target_goal = mk_app_n(
        cnst(&ln("WellFounded"), &[domain_level]),
        &[target_spine.typ(), target_relation.clone()],
      );
      proof = mk_app_n(cnst(&wrapper, &wrapper_levels), &[target_goal, proof]);
    }
    (
      rel_args[2].clone(),
      vec![target_spine.typ(), codomain.clone(), target_relation, proof],
    )
  };
  let target_measure = decode_wf_case(tm, &spine, &l.sigma, &measure)?;
  Ok(WfRootSchema {
    source_spine: spine,
    target_spine,
    source_codomain: args[1].clone(),
    target_codomain: codomain,
    source_measure: measure,
    target_measure,
    head: cnst(&name, &levels),
    source_relation: if is_nat { None } else { Some(args[2].clone()) },
    target_relation: if is_nat { None } else { Some(target_args[2].clone()) },
    source_arguments: args,
    target_arguments: target_args,
  })
}

/// `ownedWFRecType`.
pub fn owned_wf_rec_type(
  tm: &mut Tm,
  schema: &WfRootSchema,
  source_point: &Expr,
  target_point: &Expr,
  typ: &Expr,
) -> R<Expr> {
  let (locals, result) = open_binders(tm, false, 2, typ)?;
  if locals.len() != 2 {
    return Err("WF schema: incomplete recursive telescope".into());
  }
  let argument = locals[0].clone();
  let proof = locals[1].clone();
  if !alpha_eq(&argument.typ, &schema.source_spine.typ()) {
    return Err("WF schema: recursive argument has a foreign domain".into());
  }
  let relation = match (&schema.source_relation, &schema.target_relation) {
    (Some(source), Some(target)) => {
      let (head, args) = get_app_fn_args(&proof.typ);
      if !(alpha_eq(&head, source)
        && args.len() == 2
        && alpha_eq(&args[0], &argument.expr())
        && alpha_eq(&args[1], source_point))
      {
        return Err(
          "WF schema: decreasing obligation has a foreign root relation or argument identity"
            .into(),
        );
      }
      mk_app_n(target.clone(), &[argument.expr(), target_point.clone()])
    },
    _ => {
      let Some((name, levels, args)) = const_app(&proof.typ) else {
        return Err("WF schema: decreasing obligation is not invImage".into());
      };
      if !(name == n_inv_image()
        && args.len() == 6
        && alpha_eq(&args[0], &schema.source_spine.typ())
        && alpha_eq(&args[3], &schema.source_measure)
        && alpha_eq(&args[4], &argument.expr())
        && alpha_eq(&args[5], source_point))
      {
        return Err(
          "WF schema: decreasing obligation has foreign measure or argument identities"
            .into(),
        );
      }
      mk_app_n(
        cnst(&name, &levels),
        &[
          schema.target_spine.typ(),
          args[1].clone(),
          args[2].clone(),
          schema.target_measure.clone(),
          argument.expr(),
          target_point.clone(),
        ],
      )
    },
  };
  if !alpha_eq(
    &result,
    &apply_wf_case(&schema.source_codomain, &argument.expr()),
  ) {
    return Err(
      "WF schema: recursive result differs from the root codomain".into(),
    );
  }
  let ae = argument.expr();
  close_binders(
    false,
    &[
      Local { typ: schema.target_spine.typ(), ..argument },
      Local { typ: relation, ..proof },
    ],
    &apply_wf_case(&schema.target_codomain, &ae),
  )
}

// ---------------------------------------------------------------------------
// WFMatcher
// ---------------------------------------------------------------------------

/// `decodeWFNatMatcher`: the zero expression of a declaration-checked Nat
/// dispatcher.
pub fn decode_wf_nat_matcher(
  tm: &mut Tm,
  const_of: ConstOf<'_>,
  name: &Name,
  levels: &[Level],
) -> R<Expr> {
  let Some(declaration) = const_of(name).and_then(|c| Decl::of_ci(&c)) else {
    return Err(format!(
      "WF matcher: source declaration {} unavailable",
      name_to_string(name)
    ));
  };
  if declaration.name != *name {
    return Err(
      "WF matcher: lookup returned another source declaration identity".into(),
    );
  }
  if levels.len() != declaration.level_params.len() {
    return Err(
      "WF matcher: universe arity differs from source declaration".into(),
    );
  }
  let value =
    subst_levels(&declaration.level_params, levels, &declaration.value);
  let (parameters, body) = open_binders(tm, true, 4, &value)?;
  let motive = parameters[0].clone();
  let major = parameters[1].clone();
  let zero_minor = parameters[2].clone();
  let succ_minor = parameters[3].clone();
  let nat_t = cnst(&ln("Nat"), &[]);
  let unit = cnst(&ln("Unit"), &[]);
  let (motive_args, motive_sort) = open_binders(tm, false, 1, &motive.typ)?;
  if !alpha_eq(&motive_args[0].typ, &nat_t) {
    return Err("WF matcher: motive domain is not Nat".into());
  }
  let result_level = match strip_mdata(&motive_sort).as_data() {
    ExprData::Sort(l, _) => l.clone(),
    _ => return Err("WF matcher: motive does not return a sort".into()),
  };
  if !alpha_eq(&major.typ, &nat_t) {
    return Err("WF matcher: major domain is not Nat".into());
  }
  let (zero_args, zero_result) = open_binders(tm, false, 1, &zero_minor.typ)?;
  if !alpha_eq(&zero_args[0].typ, &unit) {
    return Err("WF matcher: zero minor has a foreign argument".into());
  }
  let (zero_head, zero) = match strip_mdata(&zero_result).as_data() {
    ExprData::App(h, z, _) => (h.clone(), z.clone()),
    _ => {
      return Err("WF matcher: zero minor does not return its motive".into());
    },
  };
  if !(alpha_eq(&zero_head, &motive.expr())
    && !parameters
      .iter()
      .chain(zero_args.iter())
      .any(|p| mentions_fvar(&p.fvar, &zero)))
  {
    return Err(
      "WF matcher: zero minor has a foreign motive or dependent index".into(),
    );
  }
  let (succ_args, succ_result) = open_binders(tm, false, 1, &succ_minor.typ)?;
  if !(alpha_eq(&succ_args[0].typ, &nat_t)
    && alpha_eq(
      &succ_result,
      &Expr::app(
        motive.expr(),
        Expr::app(cnst(&ln("Nat.succ"), &[]), succ_args[0].expr()),
      ),
    ))
  {
    return Err(
      "WF matcher: successor minor has a foreign motive or index".into(),
    );
  }
  let expected_motive =
    mk_lambda(&motive_args, &Expr::app(motive.expr(), motive_args[0].expr()));
  let expected_succ =
    mk_lambda(&succ_args, &Expr::app(succ_minor.expr(), succ_args[0].expr()));
  let expected = mk_app_n(
    cnst(&ln("Nat.casesOn"), &[result_level]),
    &[
      expected_motive,
      major.expr(),
      Expr::app(zero_minor.expr(), cnst(&ln("Unit.unit"), &[])),
      expected_succ,
    ],
  );
  if !alpha_eq(&body, &expected) {
    return Err(
      "WF matcher: body is not the exact symbolic Nat dispatch".into(),
    );
  }
  let declared_type =
    subst_levels(&declaration.level_params, levels, &declaration.typ);
  if !alpha_eq(
    &declared_type,
    &mk_forall(&parameters, &Expr::app(motive.expr(), major.expr())),
  ) {
    return Err(
      "WF matcher: declaration telescope differs from the symbolic dispatch"
        .into(),
    );
  }
  Ok(zero)
}

// ---------------------------------------------------------------------------
// WFConjugation
// ---------------------------------------------------------------------------

/// `ownedWFCalls`.
pub fn owned_wf_calls(
  l: &WfLayout,
  adapter: &Expr,
  fuel: usize,
  depth: usize,
  e: &Expr,
) -> R<Expr> {
  fn visit(
    l: &WfLayout,
    adapter: &Expr,
    fuel: usize,
    depth: usize,
    e: &Expr,
    memo: &mut FxHashMap<(Hash, usize, usize), Expr>,
  ) -> R<Expr> {
    let memo_key = (*e.get_hash(), fuel, depth);
    if let Some(result) = memo.get(&memo_key) {
      return Ok(result.clone());
    }

    let result = (|| {
      if fuel == 0 {
        return Err("WF ownership: body recursion bound".into());
      }
      let fuel = fuel - 1;
      if l.sigma == id_perm(l.n) {
        return Ok(e.clone());
      }
      let go = |memo: &mut FxHashMap<(Hash, usize, usize), Expr>, x: &Expr| {
        visit(l, adapter, fuel, depth, x, memo)
      };
      if let ExprData::App(..) = e.as_data() {
        let (head, args) = get_app_fn_args(e);
        if alpha_eq(&head, &mk_bvar(depth)) {
          if args.len() < 2 {
            let a2: R<Vec<Expr>> = args.iter().map(|x| go(memo, x)).collect();
            return Ok(mk_app_n(lift(adapter, depth), &a2?));
          }
          let Some((spine, index, payload)) = decode_inj(l.n, &args[0]) else {
            let a2: R<Vec<Expr>> = args.iter().map(|x| go(memo, x)).collect();
            return Ok(mk_app_n(lift(adapter, depth), &a2?));
          };
          if !l.is_clique(&spine) {
            return Err("WF ownership: foreign recursive injection".into());
          }
          let argument = mk_inj(
            &spine.permute(&l.sigma),
            l.sigma[index],
            &go(memo, &payload)?,
          );
          let proof = go(memo, &args[1])?;
          let mut out = vec![argument, proof];
          for x in &args[2..] {
            out.push(go(memo, x)?);
          }
          return Ok(mk_app_n(head, &out));
        }
      }
      Ok(match e.as_data() {
        ExprData::Bvar(..) => {
          if is_bvar(e, depth) {
            lift(adapter, depth)
          } else {
            e.clone()
          }
        },
        ExprData::App(f, a, _) => Expr::app(go(memo, f)?, go(memo, a)?),
        ExprData::Lam(n, t, b, bi, _) => Expr::lam(
          n.clone(),
          go(memo, t)?,
          visit(l, adapter, fuel, depth + 1, b, memo)?,
          bi.clone(),
        ),
        ExprData::ForallE(n, t, b, bi, _) => Expr::all(
          n.clone(),
          go(memo, t)?,
          visit(l, adapter, fuel, depth + 1, b, memo)?,
          bi.clone(),
        ),
        ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
          n.clone(),
          go(memo, t)?,
          go(memo, v)?,
          visit(l, adapter, fuel, depth + 1, b, memo)?,
          *nd,
        ),
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), go(memo, x)?)
        },
        ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(memo, x)?),
        _ => e.clone(),
      })
    })();

    if let Ok(value) = &result {
      memo.insert(memo_key, value.clone());
    }

    result
  }
  visit(l, adapter, fuel, depth, e, &mut FxHashMap::default())
}

/// `ownedWFRecAdapter`.
pub fn owned_wf_rec_adapter(
  tm: &mut Tm,
  l: &WfLayout,
  spine: &Spine,
  w: &Level,
  recursive: &Local,
) -> R<Expr> {
  let (arguments, result) = open_binders(tm, false, 1, &recursive.typ)?;
  let Some(argument) = arguments.first().cloned() else {
    return Err("WF ownership: missing recursive argument".into());
  };
  if !alpha_eq(&argument.typ, &spine.typ()) {
    return Err("WF ownership: wrong recursive argument domain".into());
  }
  let mut leaves = Vec::new();
  for j in 0..l.n {
    let payload_name = tm.fresh();
    let payload = local(
      payload_name,
      root("value"),
      spine.leaves[j].clone(),
      BinderInfo::Default,
    );
    let at_constructor = inst_locals(
      &abstract_fvars(std::slice::from_ref(&argument.fvar), &result),
      &[mk_inj(spine, j, &payload.expr())],
    );
    let (proofs, _) = open_binders(tm, false, 1, &at_constructor)?;
    let Some(proof) = proofs.first().cloned() else {
      return Err("WF ownership: missing decreasing proof binder".into());
    };
    let value = mk_app_n(
      recursive.expr(),
      &[
        mk_inj(&spine.permute(&l.sigma), l.sigma[j], &payload.expr()),
        proof.expr(),
      ],
    );
    leaves.push(close_binders(true, &[payload, proof], &value)?);
  }
  let tree = Tree {
    spine: spine.clone(),
    w: w.clone(),
    motive_name: argument.user_name.clone(),
    motive_body: abstract_fvars(std::slice::from_ref(&argument.fvar), &result),
    major: argument.expr(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  let Some(body) = tree.build() else {
    return Err("WF ownership: inverse-input case tree failed".into());
  };
  close_binders(true, &[argument], &body)
}

/// `substituteWFLocal`.
pub fn substitute_wf_local(
  identity: &Name,
  value: &Expr,
  replacement: &Expr,
) -> Expr {
  inst_locals(
    &abstract_fvars(std::slice::from_ref(identity), value),
    std::slice::from_ref(replacement),
  )
}

/// `ownedWFBody`.
#[allow(clippy::too_many_arguments)]
pub fn owned_wf_body(
  tm: &mut Tm,
  l: &WfLayout,
  schema: &WfRootSchema,
  w: &Level,
  const_of: ConstOf<'_>,
  fuel: usize,
  payload: &Local,
  recursive: &Local,
  source_point: &Expr,
  target_point: &Expr,
  body: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("WF ownership: payload refinement recursion bound".into());
  }
  let fuel = fuel - 1;
  if let Some((name, levels, args)) = const_app(body) {
    if name == ln("PSigma.casesOn")
      && args.len() == 6
      && alpha_eq(&args[3], &payload.expr())
      && alpha_eq(&args[5], &recursive.expr())
      && !mentions_fvar(&recursive.fvar, &args[2])
      && !mentions_fvar(&recursive.fvar, &args[4])
    {
      let Some((payload_name, payload_levels, payload_args)) =
        const_app(&payload.typ)
      else {
        return Err(
          "WF ownership: refined payload is not a dependent pair".into(),
        );
      };
      if !(payload_name == n_psigma()
        && payload_args.len() == 2
        && alpha_eq(&payload_args[0], &args[0])
        && alpha_eq(&payload_args[1], &args[1]))
      {
        return Err(
          "WF ownership: dependent-pair eliminator has a foreign payload type"
            .into(),
        );
      }
      let (motive_locals, motive_body) = open_binders(tm, true, 1, &args[2])?;
      let motive_payload = motive_locals[0].clone();
      let (motive_binders, motive_result) =
        open_binders(tm, false, 1, &motive_body)?;
      let motive_recursive = motive_binders[0].clone();
      if mentions_fvar(&motive_recursive.fvar, &motive_result) {
        return Err(
          "WF ownership: refinement result depends on its recursive value"
            .into(),
        );
      }
      let motive_rec_type = owned_wf_rec_type(
        tm,
        schema,
        &substitute_wf_local(
          &payload.fvar,
          source_point,
          &motive_payload.expr(),
        ),
        &substitute_wf_local(
          &payload.fvar,
          target_point,
          &motive_payload.expr(),
        ),
        &motive_recursive.typ,
      )?;
      let motive_body = close_binders(
        false,
        &[Local { typ: motive_rec_type, ..motive_recursive }],
        &motive_result,
      )?;
      let motive = close_binders(true, &motive_locals, &motive_body)?;
      let (minor_locals, minor_body) = open_binders(tm, true, 3, &args[4])?;
      let first = minor_locals[0].clone();
      let second = minor_locals[1].clone();
      let minor_recursive = minor_locals[2].clone();
      let pair = mk_app_n(
        cnst(&ln("PSigma.mk"), &payload_levels),
        &[
          payload_args[0].clone(),
          payload_args[1].clone(),
          first.expr(),
          second.expr(),
        ],
      );
      let sp = substitute_wf_local(&payload.fvar, source_point, &pair);
      let tp = substitute_wf_local(&payload.fvar, target_point, &pair);
      let rec_type =
        owned_wf_rec_type(tm, schema, &sp, &tp, &minor_recursive.typ)?;
      let minor_body = owned_wf_body(
        tm,
        l,
        schema,
        w,
        const_of,
        fuel,
        &second,
        &minor_recursive,
        &sp,
        &tp,
        &minor_body,
      )?;
      let minor = close_binders(
        true,
        &[first, second, Local { typ: rec_type, ..minor_recursive }],
        &minor_body,
      )?;
      return Ok(mk_app_n(
        cnst(&name, &levels),
        &[
          args[0].clone(),
          args[1].clone(),
          motive,
          args[3].clone(),
          minor,
          args[5].clone(),
        ],
      ));
    }
    if args.len() == 5
      && alpha_eq(&args[1], &payload.expr())
      && alpha_eq(&args[4], &recursive.expr())
      && !args[..4].iter().any(|a| mentions_fvar(&recursive.fvar, a))
    {
      let saved = tm.next;
      match decode_wf_nat_matcher(tm, const_of, &name, &levels) {
        Err(reason) => {
          tm.next = saved;
          tm.trace(format!(
            "{reason}; retaining the faithful recursive-input adapter"
          ));
        },
        Ok(zero) => {
          let (motive_locals, motive_body) =
            open_binders(tm, true, 1, &args[0])?;
          let motive_payload = motive_locals[0].clone();
          if !alpha_eq(&motive_payload.typ, &payload.typ) {
            return Err(
              "WF matcher: motive payload differs from owned input".into(),
            );
          }
          let (motive_binders, motive_result) =
            open_binders(tm, false, 1, &motive_body)?;
          let motive_recursive = motive_binders[0].clone();
          if mentions_fvar(&motive_recursive.fvar, &motive_result) {
            return Err(
              "WF matcher: result depends on the recursive value".into(),
            );
          }
          let motive_rec_type = owned_wf_rec_type(
            tm,
            schema,
            &substitute_wf_local(
              &payload.fvar,
              source_point,
              &motive_payload.expr(),
            ),
            &substitute_wf_local(
              &payload.fvar,
              target_point,
              &motive_payload.expr(),
            ),
            &motive_recursive.typ,
          )?;
          let motive_body = close_binders(
            false,
            &[Local { typ: motive_rec_type, ..motive_recursive }],
            &motive_result,
          )?;
          let motive = close_binders(true, &motive_locals, &motive_body)?;
          let mut minors = Vec::new();
          for index in 0..2 {
            let (locals, minor_body) =
              open_binders(tm, true, 2, &args[index + 2])?;
            let branch_argument = locals[0].clone();
            let minor_recursive = locals[1].clone();
            let point = if index == 0 {
              zero.clone()
            } else {
              Expr::app(cnst(&ln("Nat.succ"), &[]), branch_argument.expr())
            };
            let sp = substitute_wf_local(&payload.fvar, source_point, &point);
            let tp = substitute_wf_local(&payload.fvar, target_point, &point);
            let rec_type =
              owned_wf_rec_type(tm, schema, &sp, &tp, &minor_recursive.typ)?;
            let minor_body = owned_wf_body(
              tm,
              l,
              schema,
              w,
              const_of,
              fuel,
              &branch_argument,
              &minor_recursive,
              &sp,
              &tp,
              &minor_body,
            )?;
            minors.push(close_binders(
              true,
              &[branch_argument, Local { typ: rec_type, ..minor_recursive }],
              &minor_body,
            )?);
          }
          return Ok(mk_app_n(
            cnst(&name, &levels),
            &[
              motive,
              args[1].clone(),
              minors[0].clone(),
              minors[1].clone(),
              args[4].clone(),
            ],
          ));
        },
      }
    }
  }
  let body = rewrite_wf_obligations(schema, &l.sigma, DEFAULT_FUEL, body)?;
  let adapter =
    owned_wf_rec_adapter(tm, l, &schema.source_spine, w, recursive)?;
  let rf = std::slice::from_ref(&recursive.fvar);
  let adapter = abstract_fvars(rf, &adapter);
  let transformed =
    owned_wf_calls(l, &adapter, DEFAULT_FUEL, 0, &abstract_fvars(rf, &body))?;
  Ok(inst_locals(&transformed, &[recursive.expr()]))
}

/// `conjugateWFRoot`.
pub fn conjugate_wf_root(
  tm: &mut Tm,
  l: &WfLayout,
  value: &Expr,
  const_of: ConstOf<'_>,
) -> R<Expr> {
  let schema = decode_wf_root(tm, l, value)?;
  let Some(functional) = schema.source_arguments.last().cloned() else {
    return Err("WF ownership: missing root functional".into());
  };
  let (locals, body) = open_binders(tm, true, 2, &functional)?;
  let x = locals[0].clone();
  let recursive = locals[1].clone();
  if !alpha_eq(&x.typ, &schema.source_spine.typ()) {
    return Err("WF ownership: functional domain differs from root".into());
  }
  let recursive_type =
    owned_wf_rec_type(tm, &schema, &x.expr(), &x.expr(), &recursive.typ)?;
  let Some(tree) = decode_tree(l.n, &body) else {
    return Err("WF ownership: missing root refinement tree".into());
  };
  if !(alpha_eq(&tree.spine.typ(), &schema.source_spine.typ())
    && alpha_eq(&tree.major, &x.expr())
    && tree.extras.len() == 1
    && alpha_eq(&tree.extras[0], &recursive.expr()))
  {
    return Err(
      "WF ownership: root refinement has foreign entry identities".into(),
    );
  }
  let xf = std::slice::from_ref(&x.fvar);
  let rec_abs = abstract_fvars(xf, &recursive.typ);
  let source_type_at =
    |point: &Expr| inst_locals(&rec_abs, std::slice::from_ref(point));
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let leaf = tree.leaves[index].clone();
    if mentions_fvar(&x.fvar, &leaf) || mentions_fvar(&recursive.fvar, &leaf) {
      return Err(
        "WF ownership: leaf captures an unthreaded root identity".into(),
      );
    }
    let (entry, leaf_body) = open_binders(tm, true, 2, &leaf)?;
    let payload = entry[0].clone();
    let recursor = entry[1].clone();
    if !alpha_eq(&payload.typ, &schema.source_spine.leaves[index]) {
      return Err(
        "WF ownership: leaf payload differs from root summand".into(),
      );
    }
    let source_point = mk_inj(&schema.source_spine, index, &payload.expr());
    let target_point =
      mk_inj(&schema.target_spine, l.sigma[index], &payload.expr());
    if !alpha_eq(&recursor.typ, &source_type_at(&source_point)) {
      return Err(
        "WF ownership: leaf recursive binder differs from root telescope"
          .into(),
      );
    }
    let target_type = owned_wf_rec_type(
      tm,
      &schema,
      &source_point,
      &target_point,
      &recursor.typ,
    )?;
    let transformed = owned_wf_body(
      tm,
      l,
      &schema,
      &tree.w,
      const_of,
      DEFAULT_FUEL,
      &payload,
      &recursor,
      &source_point,
      &target_point,
      &leaf_body,
    )?;
    leaves.push(close_binders(
      true,
      &[payload, Local { typ: target_type, ..recursor }],
      &transformed,
    )?);
  }
  let point_name = tm.fresh();
  let point = fvar(&point_name);
  let source_motive = mk_forall(
    &[Local { typ: source_type_at(&point), ..recursive.clone() }],
    &apply_wf_case(&schema.source_codomain, &point),
  );
  let pn = std::slice::from_ref(&point_name);
  if !alpha_eq(&tree.motive_body, &abstract_fvars(pn, &source_motive)) {
    return Err(
      "WF ownership: refinement motive differs from root telescope".into(),
    );
  }
  let tt =
    owned_wf_rec_type(tm, &schema, &point, &point, &source_type_at(&point))?;
  let target_motive = mk_forall(
    &[Local { typ: tt, ..recursive.clone() }],
    &apply_wf_case(&schema.target_codomain, &point),
  );
  let tree2 =
    Tree { leaves, motive_body: abstract_fvars(pn, &target_motive), ..tree };
  let Some(body) = tree2.permute(&l.sigma).build() else {
    return Err("WF ownership: root refinement reconstruction failed".into());
  };
  let functional = close_binders(
    true,
    &[
      Local { typ: schema.target_spine.typ(), ..x },
      Local { typ: recursive_type, ..recursive },
    ],
    &body,
  )?;
  let mut ta = schema.target_arguments.clone();
  ta.push(functional);
  Ok(mk_app_n(schema.head.clone(), &ta))
}

/// `conjugateWFType`.
pub fn conjugate_wf_type(tm: &mut Tm, l: &WfLayout, typ: &Expr) -> R<Expr> {
  let (name, domain, body, bi) = match strip_mdata(typ).as_data() {
    ExprData::ForallE(n, d, b, bi, _) => {
      (n.clone(), d.clone(), b.clone(), bi.clone())
    },
    _ => return Err("WF schema: packed type has no input binder".into()),
  };
  let Some(spine) = decode_spine(PackKind::Psum, l.n, &domain) else {
    return Err("WF schema: packed type has no sum domain".into());
  };
  if !l.is_clique(&spine) {
    return Err("WF schema: packed type has a foreign domain".into());
  }
  let transformed =
    decode_wf_case(tm, &spine, &l.sigma, &Expr::lam(name, domain, body, bi))?;
  match transformed.as_data() {
    ExprData::Lam(n, d, b, bi, _) => {
      Ok(Expr::all(n.clone(), d.clone(), b.clone(), bi.clone()))
    },
    _ => Err("WF schema: transformed codomain has no binder".into()),
  }
}

/// `wfPackedDomain`.
pub fn wf_packed_domain(
  l: &WfLayout,
  packed: &Decl,
  levels: &[Level],
  fixed: &[Expr],
) -> R<(Spine, Expr, Level)> {
  if fixed.len() != l.num_fixed {
    return Err("WF adapter: incomplete fixed arguments".into());
  }
  let typ = subst_levels(&packed.level_params, levels, &packed.typ);
  let (_, result) = peel_foralls(l.num_fixed, &typ);
  let result = inst_locals(&result, fixed);
  let (domain, codomain) = match strip_mdata(&result).as_data() {
    ExprData::ForallE(_, d, c, _, _) => (d.clone(), c.clone()),
    _ => return Err("WF adapter: packed type has no dependent input".into()),
  };
  let Some(spine) = decode_spine(PackKind::Psum, l.n, &domain) else {
    return Err("WF adapter: missing source sum domain".into());
  };
  let value = subst_levels(&packed.level_params, levels, &packed.value);
  let (_, rt) = peel_lams(l.num_fixed, &value);
  let Some((_, root_levels, _)) = const_app(&strip_mdata(&rt)) else {
    return Err("WF adapter: missing fixpoint root".into());
  };
  let Some(result_level) = root_levels.get(1).cloned() else {
    return Err("WF adapter: missing result universe".into());
  };
  Ok((spine, codomain, result_level))
}

/// `applyWFPackedAdapter`.
pub fn apply_wf_packed_adapter(
  tm: &mut Tm,
  l: &WfLayout,
  packed: &Decl,
  levels: &[Level],
  fixed: &[Expr],
  argument: &Expr,
) -> R<Expr> {
  let (spine, codomain, result_level) =
    wf_packed_domain(l, packed, levels, fixed)?;
  let target = spine.permute(&l.sigma);
  let call = |index: usize, payload: &Expr| -> Expr {
    let mut a: Vec<Expr> =
      l.fixed_perm.iter().map(|&i| fixed[i].clone()).collect();
    a.push(mk_inj(&target, l.sigma[index], payload));
    mk_app_n(cnst(&l.new_mutual_name, levels), &a)
  };
  if let Some((actual, index, payload)) = decode_inj(l.n, argument) {
    if !alpha_eq(&actual.typ(), &spine.typ()) {
      return Err("WF adapter: injected argument has a foreign type".into());
    }
    return Ok(call(index, &payload));
  }
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let name = tm.fresh();
    let payload = local(
      name,
      root("payload"),
      spine.leaves[index].clone(),
      BinderInfo::Default,
    );
    let pe = payload.expr();
    leaves.push(mk_lambda(&[payload], &call(index, &pe)));
  }
  let tree = Tree {
    spine,
    w: result_level,
    motive_name: root("input"),
    motive_body: codomain,
    major: argument.clone(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  tree.build().ok_or_else(|| {
    "WF adapter: dependent input case reconstruction failed".into()
  })
}

/// `rewriteOwnedWFUses`.
pub fn rewrite_owned_wf_uses(
  tm: &mut Tm,
  l: &WfLayout,
  packed: &Decl,
  fuel: usize,
  e: &Expr,
) -> R<Expr> {
  fn visit(
    tm: &mut Tm,
    l: &WfLayout,
    packed: &Decl,
    fuel: usize,
    e: &Expr,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> R<Expr> {
    let memo_key = (*e.get_hash(), fuel);
    if let Some(result) = memo.get(&memo_key) {
      return Ok(result.clone());
    }
    let before = tm.next;
    let result = (|| {
      if fuel == 0 {
        return Err("WF ownership: constant-use recursion bound".into());
      }
      let fuel = fuel - 1;
      fn packed_use(
        tm: &mut Tm,
        l: &WfLayout,
        packed: &Decl,
        fuel: usize,
        levels: &[Level],
        args: &[Expr],
        memo: &mut FxHashMap<(Hash, usize), Expr>,
      ) -> R<Expr> {
        if args.len() < l.num_fixed {
          return Err(
            "WF ownership: partial fixed prefix of packed root".into(),
          );
        }
        let mut a2 = Vec::new();
        for x in args {
          a2.push(visit(tm, l, packed, fuel, x, memo)?);
        }
        let fixed = a2[..l.num_fixed].to_vec();
        if a2.len() == l.num_fixed {
          let (spine, _, _) = wf_packed_domain(l, packed, levels, &fixed)?;
          let identity = tm.fresh();
          let argument =
            local(identity, root("input"), spine.typ(), BinderInfo::Default);
          let value = apply_wf_packed_adapter(
            tm,
            l,
            packed,
            levels,
            &fixed,
            &argument.expr(),
          )?;
          return Ok(mk_lambda(&[argument], &value));
        }
        let value = apply_wf_packed_adapter(
          tm,
          l,
          packed,
          levels,
          &fixed,
          &a2[l.num_fixed],
        )?;
        Ok(mk_app_n(value, &a2[l.num_fixed + 1..]))
      }
      let go = |memo: &mut FxHashMap<(Hash, usize), Expr>,
                tm: &mut Tm,
                x: &Expr| visit(tm, l, packed, fuel, x, memo);
      Ok(match e.as_data() {
        ExprData::App(..) => {
          let (head, args) = get_app_fn_args(e);
          if let ExprData::Const(name, levels, _) = head.as_data() {
            if *name == l.mutual_name {
              return packed_use(tm, l, packed, fuel, levels, &args, memo);
            }
            if let Some(permutation) = l.proof_perm.get(name) {
              if args.len() < permutation.len() {
                return Err("WF ownership: partial proof use".into());
              }
              let mut a2 = Vec::new();
              for x in &args {
                a2.push(go(memo, tm, x)?);
              }
              let mut out: Vec<Expr> =
                permutation.iter().map(|&i| a2[i].clone()).collect();
              out.extend(a2[permutation.len()..].iter().cloned());
              return Ok(mk_app_n(head.clone(), &out));
            }
          }
          let h2 = go(memo, tm, &head)?;
          let mut a2 = Vec::new();
          for x in &args {
            a2.push(go(memo, tm, x)?);
          }
          mk_app_n(h2, &a2)
        },
        ExprData::Const(name, levels, _) => {
          if *name == l.mutual_name {
            return packed_use(tm, l, packed, fuel, levels, &[], memo);
          }
          if let Some(permutation) = l.proof_perm.get(name)
            && !permutation.is_empty()
          {
            return Err("WF ownership: bare proof use".into());
          }
          e.clone()
        },
        ExprData::Lam(n, t, b, bi, _) => {
          let t2 = go(memo, tm, t)?;
          Expr::lam(n.clone(), t2, go(memo, tm, b)?, bi.clone())
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          let t2 = go(memo, tm, t)?;
          Expr::all(n.clone(), t2, go(memo, tm, b)?, bi.clone())
        },
        ExprData::LetE(n, t, v, b, nd, _) => {
          let t2 = go(memo, tm, t)?;
          let v2 = go(memo, tm, v)?;
          Expr::letE(n.clone(), t2, v2, go(memo, tm, b)?, *nd)
        },
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), go(memo, tm, x)?)
        },
        ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(memo, tm, x)?),
        _ => e.clone(),
      })
    })();
    if before == tm.next
      && let Ok(value) = &result
    {
      memo.insert(memo_key, value.clone());
    }
    result
  }
  visit(tm, l, packed, fuel, e, &mut FxHashMap::default())
}

/// `transportOwnedWFEqDef`.
pub fn transport_owned_wf_eq_def(
  tm: &mut Tm,
  l: &WfLayout,
  packed: &Decl,
  target: &Decl,
  equation: &Decl,
  new_name: &Name,
) -> R<Decl> {
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &equation.typ,
    &mut |_, x| Ok(x.clone()),
    &mut |tm, x| rewrite_owned_wf_uses(tm, l, packed, DEFAULT_FUEL, x),
  )?;
  let (parameters, statement) = open_binders(tm, false, l.num_fixed + 1, &typ)?;
  let point = parameters[l.num_fixed].clone();
  let inverse = inv_perm(&l.fixed_perm);
  let source_fixed: Vec<Expr> =
    (0..l.num_fixed).map(|i| parameters[inverse[i]].expr()).collect();
  let target_fixed: Vec<Expr> =
    parameters[..l.num_fixed].iter().map(|p| p.expr()).collect();
  let mut sfx = source_fixed.clone();
  sfx.push(point.expr());
  let source_step = eq_def_fix_step(equation, l.num_fixed, &sfx)?;
  let (source_binders, source_body) = peel_lams(l.num_fixed, &packed.value);
  let (target_binders, target_body) = peel_lams(l.num_fixed, &target.value);
  if !(source_binders.len() == l.num_fixed
    && target_binders.len() == l.num_fixed)
  {
    return Err(
      "WF equation: packed fixed telescope differs from its layout".into(),
    );
  }
  let source_root = inst_locals(&source_body, &source_fixed);
  let target_root = inst_locals(&target_body, &target_fixed);
  let Some((root_name, root_levels, source_args)) = const_app(&source_root)
  else {
    return Err("WF equation: source root is not a fixpoint".into());
  };
  let Some((_, _, target_args)) = const_app(&target_root) else {
    return Err("WF equation: target root is not a fixpoint".into());
  };
  let Some((step_name, step_levels, step_args)) =
    const_app(&strip_id(&source_step))
  else {
    return Err("WF equation: source proof has no fix_eq step".into());
  };
  let expected_step = if root_name == ln("WellFounded.Nat.fix") {
    ln("WellFounded.Nat.fix_eq")
  } else if root_name == ln("WellFounded.fix") {
    ln("WellFounded.fix_eq")
  } else {
    Name::anon()
  };
  if !(step_name == expected_step
    && step_levels == root_levels
    && step_args.len() == source_args.len() + 1
    && step_args[..source_args.len()]
      .iter()
      .zip(source_args.iter())
      .all(|(a, b)| alpha_eq(a, b)))
  {
    return Err(
      "WF equation: fix_eq does not refer to the exact decoded source root"
        .into(),
    );
  }
  if !alpha_eq(&step_args[source_args.len()], &point.expr()) {
    return Err("WF equation: fix_eq uses a foreign input identity".into());
  }
  let Some(spine) = decode_spine(PackKind::Psum, l.n, &point.typ) else {
    return Err("WF equation: source equation has no sum input".into());
  };
  if !alpha_eq(&spine.typ(), &source_args[0]) {
    return Err("WF equation: equation input differs from source root".into());
  }
  let target_spine = spine.permute(&l.sigma);
  if !alpha_eq(&target_spine.typ(), &target_args[0]) {
    return Err("WF equation: target domain differs from permutation".into());
  }
  let at_point =
    |argument: &Expr| substitute_wf_local(&point.fvar, &statement, argument);
  let mut leaves = Vec::new();
  for index in 0..l.n {
    let name = tm.fresh();
    let payload = local(
      name,
      root("payload"),
      spine.leaves[index].clone(),
      BinderInfo::Default,
    );
    let sp = spine.clone();
    let tsp = target_spine.clone();
    let tidx = l.sigma[index];
    let motive = |value: Expr| at_point(&mk_inj(&sp, index, &value));
    let ta = target_args.clone();
    let (sn, sl) = (step_name.clone(), step_levels.clone());
    let leaf = move |value: Expr| {
      let mut a = ta.clone();
      a.push(mk_inj(&tsp, tidx, &value));
      mk_app_n(cnst(&sn, &sl), &a)
    };
    let body = split_psigma(
      tm,
      &motive,
      &leaf,
      64,
      &payload.typ,
      &|x| x,
      &payload.expr(),
    )?;
    leaves.push(mk_lambda(&[payload], &body));
  }
  let tree = Tree {
    spine,
    w: Level::zero(),
    motive_name: point.user_name.clone(),
    motive_body: abstract_fvars(std::slice::from_ref(&point.fvar), &statement),
    major: point.expr(),
    leaves,
    extras: Vec::new(),
    alt_names: Vec::new(),
  };
  let Some(body) = tree.build() else {
    return Err("WF equation: source-domain case reconstruction failed".into());
  };
  let value = close_binders(true, &parameters, &body)?;
  Ok(Decl { name: new_name.clone(), typ, value, ..equation.clone() })
}

/// `transportWF`.
#[allow(clippy::too_many_arguments)]
pub fn transport_wf(
  tm: &mut Tm,
  members: &[Decl],
  packed: &Decl,
  proofs: &[Decl],
  sigma: &[usize],
  new_name: &Name,
  lemmas: &[(Decl, Name)],
  const_of: ConstOf<'_>,
) -> R<WfOutput> {
  let initial = wf_layout(members, packed, sigma, new_name)?;
  let proof_names: FxHashSet<Name> =
    proofs.iter().map(|p| p.name.clone()).collect();
  let (fixed, body) = open_binders(tm, true, initial.num_fixed, &packed.value)?;
  let fixed_names: Vec<Name> = fixed.iter().map(|f| f.fvar.clone()).collect();
  let mut uses: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
  scan_proofs(&proof_names, &fixed_names, &body, &mut uses);
  let inverse = inv_perm(&initial.fixed_perm);
  let mut proof_perm: FxHashMap<Name, Vec<usize>> = FxHashMap::default();
  for (name, positions) in &uses {
    proof_perm.insert(
      name.clone(),
      sort_idx_by_key(positions.len(), &|i| inverse[positions[i]]),
    );
  }
  let is_packed_lemma = |name: &Name| match name.as_data() {
    ix_common::env::NameData::Str(p, _, _) => *p == packed.name,
    _ => false,
  };
  for (declaration, _) in lemmas {
    if is_packed_lemma(&declaration.name) {
      proof_perm.insert(declaration.name.clone(), initial.fixed_perm.clone());
    }
  }
  let l = WfLayout { proof_perm: proof_perm.clone(), ..initial };
  let schema = decode_wf_root(tm, &l, &body)?;
  let mut well_founded_proof: Option<(Name, Expr, Expr)> = None;
  if schema.source_arguments.len() == 5
    && let Some((name, levels, arguments)) =
      const_app(&schema.source_arguments[3])
    && let Some(declaration) = proofs.iter().find(|p| p.name == name)
  {
    let lp: Vec<Level> = declaration
      .level_params
      .iter()
      .map(|p| Level::param(p.clone()))
      .collect();
    if levels != lp {
      return Err(
        "WF ownership: well-founded proof uses a nonidentity universe substitution"
          .into(),
      );
    }
    let mut parameters: Vec<Local> = Vec::new();
    for argument in &arguments {
      let identity = match strip_mdata(argument).as_data() {
        ExprData::Fvar(n, _) => n.clone(),
        _ => {
          return Err(
            "WF ownership: well-founded proof argument is not a fixed parameter"
              .into(),
          );
        },
      };
      let Some(parameter) = fixed.iter().find(|f| f.fvar == identity) else {
        return Err(
          "WF ownership: well-founded proof uses a foreign parameter".into(),
        );
      };
      parameters.push(parameter.clone());
    }
    let permutation = proof_perm.get(&name).cloned().unwrap_or_default();
    if permutation.len() != parameters.len() {
      return Err(
        "WF ownership: well-founded proof prefix differs from its decoded application"
          .into(),
      );
    }
    let ExprData::Const(_, root_levels, _) = schema.head.as_data() else {
      return Err("WF ownership: missing fixpoint universe".into());
    };
    let Some(domain_level) = root_levels.first().cloned() else {
      return Err("WF ownership: missing domain universe".into());
    };
    let goal = mk_app_n(
      cnst(&ln("WellFounded"), &[domain_level]),
      &[schema.target_spine.typ(), schema.target_arguments[2].clone()],
    );
    let witness = mk_app_n(
      cnst(&ln("Lean.opaqueId"), &[Level::zero()]),
      &[goal.clone(), schema.target_arguments[3].clone()],
    );
    let reordered = reorder(&permutation, &parameters);
    well_founded_proof = Some((
      name,
      close_binders(false, &reordered, &goal)?,
      close_binders(true, &reordered, &witness)?,
    ));
  }
  let value = with_reordered_binders2(
    tm,
    true,
    l.num_fixed,
    &l.fixed_perm,
    &packed.value,
    &mut |_, x| Ok(x.clone()),
    &mut |tm, value| {
      let transformed = conjugate_wf_root(tm, &l, value, const_of)?;
      let transformed = match &well_founded_proof {
        Some(_) => {
          let (_, source_args) = get_app_fn_args(value);
          let (head, mut target_args) = get_app_fn_args(&transformed);
          target_args[3] = source_args[3].clone();
          mk_app_n(head, &target_args)
        },
        None => transformed,
      };
      rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &transformed)
    },
  )?;
  let typ = with_reordered_binders2(
    tm,
    false,
    l.num_fixed,
    &l.fixed_perm,
    &packed.typ,
    &mut |_, x| Ok(x.clone()),
    &mut |tm, x| conjugate_wf_type(tm, &l, x),
  )?;
  let mut output: Vec<Transported> = vec![Transported::ok(Decl {
    name: new_name.clone(),
    typ: typ.clone(),
    value: value.clone(),
    ..packed.clone()
  })];
  for proof in proofs {
    if let Some((name, t, v)) = &well_founded_proof
      && *name == proof.name
    {
      output.push(Transported::ok(Decl {
        typ: t.clone(),
        value: v.clone(),
        ..proof.clone()
      }));
      continue;
    }
    let permutation = proof_perm.get(&proof.name).cloned().unwrap_or_default();
    let positions = uses.get(&proof.name).cloned().unwrap_or_default();
    let transform = |tm: &mut Tm, is_lam: bool, expression: &Expr| -> R<Expr> {
      let (parameters, body) =
        open_binders(tm, is_lam, permutation.len(), expression)?;
      if positions.len() != parameters.len() {
        return Err(
          "WF obligation: proof prefix disagrees with its use".into(),
        );
      }
      let mut arguments: Vec<Expr> = fixed.iter().map(|f| f.expr()).collect();
      for i in 0..positions.len() {
        if positions[i] >= arguments.len() {
          return Err(
            "WF obligation: fixed proof argument is out of scope".into(),
          );
        }
        arguments[positions[i]] = parameters[i].expr();
      }
      let instantiate =
        |x: &Expr| inst_locals(&abstract_fvars(&fixed_names, x), &arguments);
      let proof_schema = schema.map_expressions(&instantiate);
      let body =
        rewrite_wf_obligations(&proof_schema, &l.sigma, DEFAULT_FUEL, &body)?;
      let body = rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &body)?;
      close_binders(is_lam, &reorder(&permutation, &parameters), &body)
    };
    let t = transform(tm, false, &proof.typ)?;
    let v = transform(tm, true, &proof.value)?;
    output.push(Transported::ok(Decl { typ: t, value: v, ..proof.clone() }));
  }
  for member in members {
    let t = rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &member.typ)?;
    let v = rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &member.value)?;
    output.push(Transported::ok(Decl { typ: t, value: v, ..member.clone() }));
  }
  let packed_target = Decl {
    name: new_name.clone(),
    typ,
    value: value.clone(),
    ..packed.clone()
  };
  for (lemma, name) in lemmas {
    if lemma.name == mk_str(&packed.name, "eq_def") {
      let Some(functional) = schema.source_arguments.last() else {
        return Err("WF equation: missing functional".into());
      };
      let (_, body) = peel_lams(2, functional);
      let Some(tree) = decode_tree(l.n, &body) else {
        return Err("WF equation: missing source refinement tree".into());
      };
      if !tree.leaves.iter().all(|x| leaf_reduces(64, x)) {
        return Err(
          "WF equation: source matcher needs argument-pushing proof reconstruction"
            .into(),
        );
      }
      output.push(Transported::ok(transport_owned_wf_eq_def(
        tm,
        &l,
        packed,
        &packed_target,
        lemma,
        name,
      )?));
    } else if is_packed_lemma(&lemma.name) {
      let t = with_reordered_binders2(
        tm,
        false,
        l.num_fixed,
        &l.fixed_perm,
        &lemma.typ,
        &mut |_, x| Ok(x.clone()),
        &mut |tm, x| rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, x),
      )?;
      let v = with_reordered_binders2(
        tm,
        true,
        l.num_fixed,
        &l.fixed_perm,
        &lemma.value,
        &mut |_, x| Ok(x.clone()),
        &mut |tm, x| rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, x),
      )?;
      output.push(Transported::ok(Decl {
        name: name.clone(),
        typ: t,
        value: v,
        ..lemma.clone()
      }));
    } else {
      let t = rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &lemma.typ)?;
      let v =
        rewrite_owned_wf_uses(tm, &l, packed, DEFAULT_FUEL, &lemma.value)?;
      output.push(Transported::ok(Decl {
        name: name.clone(),
        typ: t,
        value: v,
        ..lemma.clone()
      }));
    }
  }
  let used = const_occurrences(&|n| proof_names.contains(n), &value);
  let rest: Vec<Name> = proofs
    .iter()
    .map(|p| p.name.clone())
    .filter(|n| !used.contains(n))
    .collect();
  let numbered: Vec<(Name, Name)> = used
    .iter()
    .chain(rest.iter())
    .enumerate()
    .map(|(i, n)| (n.clone(), mk_str(new_name, &format!("_proof_{}", i + 1))))
    .collect();
  let lemma_renames: Vec<(Name, Name)> = lemmas
    .iter()
    .filter(|(d, n)| d.name != *n)
    .map(|(d, n)| (d.name.clone(), n.clone()))
    .collect();
  Ok(finish_renames(output, packed, new_name, numbered, lemma_renames))
}

/// The final renaming of `transportWF`/`transportPF`.
pub fn finish_renames(
  output: Vec<Transported>,
  packed: &Decl,
  new_name: &Name,
  numbered: Vec<(Name, Name)>,
  lemma_renames: Vec<(Name, Name)>,
) -> WfOutput {
  let mut names: FxHashMap<Name, Name> = FxHashMap::default();
  for (o, n) in numbered.iter().chain(lemma_renames.iter()) {
    names.insert(o.clone(), n.clone());
  }
  let get = |n: &Name| names.get(n).cloned();
  let renamed = output
    .into_iter()
    .map(|item| Transported {
      decl: Decl {
        name: names
          .get(&item.decl.name)
          .cloned()
          .unwrap_or(item.decl.name.clone()),
        typ: rename_consts(&get, &item.decl.typ),
        value: rename_consts(&get, &item.decl.value),
        ..item.decl
      },
      fallback: item.fallback,
    })
    .collect();
  let mut renames = vec![(packed.name.clone(), new_name.clone())];
  renames.extend(numbered);
  renames.extend(lemma_renames);
  WfOutput { decls: renamed, renames }
}

// These neighbours distinguish fuel-sensitive and stateful visits even when
// the same expression occurs more than once in the DAG.
#[cfg(test)]
mod dag_tests {
  use super::*;

  fn layout_and_packed() -> (WfLayout, Decl) {
    let spine = Spine {
      kind: PackKind::Psum,
      leaves: vec![sort0(), sort0()],
      lvls: vec![Level::zero(), Level::zero()],
    };
    let layout = WfLayout {
      n: 2,
      sigma: vec![1, 0],
      mutual_name: root("source"),
      new_mutual_name: root("target"),
      num_fixed: 0,
      fixed_perm: vec![],
      leaves: spine.leaves.clone(),
      proof_perm: FxHashMap::default(),
      member_fixed: vec![],
    };
    let packed = Decl {
      name: layout.mutual_name.clone(),
      level_params: vec![],
      typ: Expr::all(root("input"), spine.typ(), sort0(), BinderInfo::Default),
      value: cnst(&ln("WellFounded.Nat.fix"), &[Level::zero(), Level::zero()]),
      is_thm: false,
    };
    (layout, packed)
  }

  #[test]
  fn shared_visits_preserve_fuel_refusal_and_success() {
    let (layout, _) = layout_and_packed();
    let shared = Expr::app(cnst(&root("f"), &[]), cnst(&root("a"), &[]));
    let term = Expr::app(shared.clone(), Expr::app(shared.clone(), shared));
    assert_eq!(
      owned_wf_calls(&layout, &mk_bvar(0), 3, 0, &term),
      Err("WF ownership: body recursion bound".into())
    );
    assert_eq!(owned_wf_calls(&layout, &mk_bvar(0), 4, 0, &term), Ok(term));
  }

  #[test]
  fn shared_allocating_visits_preserve_fresh_counter() {
    let (layout, packed) = layout_and_packed();
    let use_packed = cnst(&layout.mutual_name, &[]);
    let term =
      mk_app_n(cnst(&root("consume"), &[]), &[use_packed.clone(), use_packed]);
    let mut tm = Tm::default();
    assert!(
      rewrite_owned_wf_uses(&mut tm, &layout, &packed, 10, &term).is_ok()
    );
    assert_eq!(tm.next, 6);
    let plain = Expr::app(cnst(&root("f"), &[]), cnst(&root("x"), &[]));
    assert_eq!(
      rewrite_owned_wf_uses(&mut tm, &layout, &packed, 10, &plain),
      Ok(plain)
    );
    assert_eq!(tm.next, 6);
  }
}
