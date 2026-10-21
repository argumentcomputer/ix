//! The plan of a definition clique ([`plan_clique`]), and the canonical
//! constants and transported members as input constants ([`canon_const`],
//! [`with_value`]) (a port of `Ix/Compile/Pass/Clique/PlanClique.lean`).
//!
//! **The plan** is a function of the clique (`all`, Lean's order), its
//! carried equation lemmas, the input constants (the environment) and the
//! addresses of the clique's external references (`addr`): every block that
//! plans the clique computes the same one. It is not an encoded clique (a
//! single member, a member that is not a safe definition or a theorem,
//! members of another clique or referencing each other, no encoding
//! recognised); unchanged (the canonical order is Lean's and no member is an
//! alias); the baseline (the order is undetermined, [`Cause::NoSpec`], or the
//! transport kept Lean's form, [`Cause::Shape`]); or transported
//! ([`CliquePlan`]).
//!
//! **Structural cliques** need the block's authenticated `below`/`brecOn`
//! family ([`Input::family`]): [`authenticated_family`] reads it from the
//! first member's `brecOn` head ([`family_candidates`]) and keeps the names
//! [`filter_heads`] authenticates (the twin of Lean's
//! `Ix.AuxGen.SourceFamily.filterHeads`).
//!
//! Total and pure: the closures over the packed constant's proofs and
//! equation lemmas run on [`EQ_LEMMA_BOUND`] (exhaustion is a refusal), no
//! panicking access. Pretty-name sorts are stable here and Lean's `qsort` is
//! not: two distinct names with one pretty form (a string component `"1"`
//! and a number component `1`) may come in another order than Lean's; Lean
//! never generates such a pair (as in [`super::table`]).

use std::slice;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{
  ConstantInfo, ConstantVal, DataValue, DefinitionSafety, DefinitionVal, Env,
  Expr, Name, NameData, ReducibilityHints, TheoremVal,
};

use super::basic::{
  Cause, ConstOf, Decl, R, alpha_eq_skip_mdata, const_occurrences, inv_perm,
  mk_str, strip_all_mdata,
};
use super::bounds::EQ_LEMMA_BOUND;
use super::order::AddrOf;
use super::plan::{CliqueOutcome, CliquePlan, Encoding};
use super::recover::clique_order;
use super::structural::{family_candidates, member_shape, mentions_where};
use super::table::{
  all_of, clique_decl, clique_ix_name, clique_key, is_encoding_marker,
  last_str, private_user_name, rename_decl,
};
use super::telescope::id_perm;
use super::transport::{Input, find_packed, transport};
use crate::compile::aux_gen::source_family::filter_heads;
use crate::compile::pass3::names::IX_COMPONENT;

// ---------------------------------------------------------------------------
// Closures over named constants
// ---------------------------------------------------------------------------
//
// A worklist is a `Vec` whose top is its last element (Lean's list, top
// first, reversed).

/// `pushStack`: push `xs` onto `stack`: the last element of `xs` ends on
/// top.
pub fn push_stack(stack: &mut Vec<Name>, xs: Vec<Name>) {
  stack.extend(xs);
}

/// `popUnseen`: pop names off `stack` until one that is not in `seen`.
pub fn pop_unseen(
  seen: &FxHashSet<Name>,
  stack: &mut Vec<Name>,
) -> Option<Name> {
  while let Some(n) = stack.pop() {
    if !seen.contains(&n) {
      return Some(n);
    }
  }
  None
}

/// `reachDecls`: the declarations reached from `stack`: pop a name, skip it
/// when seen, else mark it, look it up and keep its declaration, then push
/// the names `next` gives for that declaration. At most `fuel` names are
/// marked; `None` when one more is due (an exhausted bound is a refusal).
pub fn reach_decls(
  const_of: ConstOf<'_>,
  next: &dyn Fn(&Decl) -> Vec<Name>,
  fuel: usize,
  mut stack: Vec<Name>,
  mut seen: FxHashSet<Name>,
  mut out: Vec<Decl>,
) -> Option<Vec<Decl>> {
  let mut fuel = fuel;
  loop {
    let Some(n) = pop_unseen(&seen, &mut stack) else { return Some(out) };
    fuel = fuel.checked_sub(1)?;
    let d = const_of(&n).and_then(|c| Decl::of_constant_info(&c));
    seen.insert(n);
    if let Some(d) = d {
      push_stack(&mut stack, next(&d));
      out.push(d);
    }
  }
}

/// `sortDeclsByPretty`: declarations in pretty-name order (see the module
/// note on ties).
pub fn sort_decls_by_pretty(mut ds: Vec<Decl>) -> Vec<Decl> {
  ds.sort_by_cached_key(|d| d.name.pretty());
  ds
}

// ---------------------------------------------------------------------------
// The plan of a clique
// ---------------------------------------------------------------------------

/// `encodingProofs`: the abstracted proofs of a packed constant
/// (`p._proof_k`), reached from its type and value and from each other, in
/// pretty-name order. At most [`EQ_LEMMA_BOUND`] proof names are visited
/// (as many as the clique table reads of a member's numbered equation
/// lemmas); `None` past it.
pub fn encoding_proofs(
  const_of: ConstOf<'_>,
  packed: &Decl,
) -> Option<Vec<Decl>> {
  let is_proof = |n: &Name| match n.as_data() {
    NameData::Str(q, s, _) => *q == packed.name && s.starts_with("_proof_"),
    _ => false,
  };
  let next = |d: &Decl| {
    let mut ns = const_occurrences(&is_proof, &d.typ);
    ns.extend(const_occurrences(&is_proof, &d.value));
    ns
  };
  let mut stack = Vec::new();
  push_stack(&mut stack, next(packed));
  reach_decls(
    const_of,
    &next,
    EQ_LEMMA_BOUND,
    stack,
    FxHashSet::default(),
    Vec::new(),
  )
  .map(sort_decls_by_pretty)
}

/// `encodingOf`: the encoding of a clique and its constants besides the
/// members:
/// * `all₀._mutual`, when the first member applies it: well-founded, with
///   its abstracted proofs;
/// * `all₀.mutual`, when the first member projects out of it:
///   `partial_fixpoint`, with its proofs;
/// * structural: the functionals `m._f` of every member, then the candidate
///   below matchers; or, when no member has a functional and every member
///   references an encoding marker (the inductive-predicate route), the
///   candidate matchers alone.
///
/// The candidate matchers are the constants whose last component starts
/// with `match_` that the members' values reference, each once, in
/// pretty-name order. They are candidates only: the structural transport's
/// `matcher_shape` decides from each declaration which of them are below
/// matchers (the others are ordinary constants of the encoding). `None`: no
/// encoding, or the proofs' bound exhausted.
pub fn encoding_of(
  const_of: ConstOf<'_>,
  all: &[Name],
  members: &[Decl],
) -> Option<(Encoding, Vec<Decl>)> {
  let all0 = all.first()?;
  let decl_of = |n: &Name| const_of(n).and_then(|c| Decl::of_constant_info(&c));
  let packed_of = |s: &str| -> Option<Decl> {
    let d = decl_of(&mk_str(all0, s))?;
    let p = find_packed(members, slice::from_ref(&d))?;
    (p.name == d.name).then_some(d)
  };
  if let Some(d) = packed_of("_mutual") {
    let proofs = encoding_proofs(const_of, &d)?;
    let mut v = vec![d];
    v.extend(proofs);
    return Some((Encoding::WellFounded, v));
  }
  if let Some(d) = packed_of("mutual") {
    let proofs = encoding_proofs(const_of, &d)?;
    let mut v = vec![d];
    v.extend(proofs);
    return Some((Encoding::PartialFixpoint, v));
  }
  // structural: the functionals, and the candidate below matchers
  let fs: Vec<Decl> =
    all.iter().filter_map(|m| decl_of(&mk_str(m, "_f"))).collect();
  let mut matchers: Vec<Name> = Vec::new();
  for d in members {
    for n in
      const_occurrences(&|n: &Name| last_str(n).starts_with("match_"), &d.value)
    {
      if !matchers.contains(&n) {
        matchers.push(n);
      }
    }
  }
  matchers.sort_by_cached_key(Name::pretty);
  let ms: Vec<Decl> = matchers.iter().filter_map(decl_of).collect();
  if fs.len() == all.len() {
    let mut v = fs;
    v.extend(ms);
    return Some((Encoding::Structural, v));
  }
  if fs.is_empty()
    && members.iter().all(|d| {
      mentions_where(&|n: &Name| is_encoding_marker(const_of, n), &d.value)
    })
  {
    return Some((Encoding::Structural, ms));
  }
  None
}

/// `packedLemmas`: the equation lemmas of the packed constant `p` that the
/// carried lemmas reach (`p.eq_def`, `p.eq_unfold`, `p.eq_<k>`),
/// transitively, in pretty-name order. At most [`EQ_LEMMA_BOUND`] lemma
/// names are visited; `None` past it.
pub fn packed_lemmas(
  const_of: ConstOf<'_>,
  p: &Name,
  carried: &[Decl],
) -> Option<Vec<Decl>> {
  let is_packed_eq = |n: &Name| match n.as_data() {
    NameData::Str(q, s, _) => {
      q == p && (s == "eq_def" || s == "eq_unfold" || s.starts_with("eq_"))
    },
    _ => false,
  };
  let mut start: Vec<Name> = Vec::new();
  for d in carried {
    start.extend(const_occurrences(&is_packed_eq, &d.value));
  }
  let mut stack = Vec::new();
  push_stack(&mut stack, start);
  reach_decls(
    const_of,
    &|d: &Decl| const_occurrences(&is_packed_eq, &d.value),
    EQ_LEMMA_BOUND,
    stack,
    FxHashSet::default(),
    Vec::new(),
  )
  .map(sort_decls_by_pretty)
}

/// `authenticatedFamily`: the authenticated `below`/`brecOn` family of a
/// structural clique's block ([`Input::family`]): the candidates
/// [`family_candidates`] lists for the first member's `brecOn` head, kept by
/// [`filter_heads`] (each name equal to what Lean's generators build from
/// the block's source recursors). Empty when the head is not under a
/// recursive inductive of the input (the structural transport then
/// refuses). An error when the first member is not a `brecOn` application
/// ([`member_shape`]): the clique is then not encoded.
pub fn authenticated_family(
  env: &Arc<Env>,
  members: &[Decl],
) -> R<FxHashSet<Name>> {
  let Some(m0) = members.first() else { return Err("no member".into()) };
  let sh = member_shape(m0)?;
  let const_of = |n: &Name| env.get(n).map(|e| e.cloned());
  Ok(match family_candidates(&const_of, &sh.brec_on_name) {
    None => FxHashSet::default(),
    Some((all, candidates)) => {
      filter_heads(env, &all, candidates).into_iter().collect()
    },
  })
}

/// The baseline of a clique whose transport kept Lean's form
/// ([`Cause::Shape`]).
pub fn baseline(enc: Encoding, why: String) -> CliqueOutcome {
  CliqueOutcome::Baseline(enc, Cause::Shape, why)
}

/// `planClique`: the plan of a clique (`all`, Lean's order) with its carried
/// equation lemmas (pure; every block of the clique computes the same one).
/// `env` is the input, `addr` the addresses of the clique's external
/// references (the order compares them by address).
pub fn plan_clique(
  env: &Arc<Env>,
  addr: AddrOf<'_>,
  all: &[Name],
  carried: &[Name],
) -> CliqueOutcome {
  let lookup = |n: &Name| env.get(n).map(|e| e.cloned());
  let const_of: ConstOf<'_> = &lookup;
  if all.len() < 2 {
    return CliqueOutcome::NotEncoded("a single member".into());
  }
  let mut members: Vec<Decl> = Vec::new();
  for m in all {
    let Some(cm) = const_of(m) else {
      return CliqueOutcome::NotEncoded(format!(
        "member {} is not in the input",
        m.pretty()
      ));
    };
    let Some(d) = clique_decl(&cm) else {
      return CliqueOutcome::NotEncoded(format!(
        "member {} is not a safe definition or a theorem",
        m.pretty()
      ));
    };
    if all_of(&cm).as_slice() != all {
      return CliqueOutcome::NotEncoded(format!(
        "member {} has another clique",
        m.pretty()
      ));
    }
    members.push(d);
  }
  // a kernel mutual block (members referencing each other) is not encoded
  let member_set: FxHashSet<Name> = all.iter().cloned().collect();
  for d in &members {
    if mentions_where(&|n: &Name| member_set.contains(n), &d.value) {
      return CliqueOutcome::NotEncoded(
        "members reference each other (a kernel mutual block)".into(),
      );
    }
  }
  let Some((enc, aux)) = encoding_of(const_of, all, &members) else {
    return CliqueOutcome::NotEncoded("no encoding recognised".into());
  };
  // the authenticated family of a structural clique's block
  let mut family: FxHashSet<Name> = FxHashSet::default();
  if enc == Encoding::Structural {
    match authenticated_family(env, &members) {
      Ok(f) => family = f,
      Err(why) => {
        return CliqueOutcome::NotEncoded(format!("structural: {why}"));
      },
    }
  }
  let Some(all0) = all.first() else {
    return CliqueOutcome::NotEncoded("a single member".into());
  };
  let inp0 = Input {
    encoding: enc,
    members: members.clone(),
    aux: aux.clone(),
    sigma: id_perm(all.len()),
    new_enc_name: all0.clone(),
    const_of,
    lemmas: Vec::new(),
    family,
  };
  let (sigma, classes, source) = match clique_order(addr, &inp0) {
    Ok(x) => x,
    Err(why) => return CliqueOutcome::Baseline(enc, Cause::NoSpec, why),
  };
  // the members of a class of two or more (equal specifications) are one
  // constant, the representative's (the first of the class in the canonical
  // order); not when one of them carries an equation lemma, whose proof
  // unfolds that member
  let mut carried_owners: FxHashSet<Name> = FxHashSet::default();
  for c in carried {
    let u = private_user_name(c).unwrap_or_else(|| c.clone());
    if let NameData::Str(p, _, _) = u.as_data() {
      carried_owners.insert(p.clone());
    }
  }
  let mut aliases: Vec<(Name, Name)> = Vec::new();
  for cls in &classes {
    let Some(rep) = cls.first() else { continue };
    let Some(rep_decl) = members.iter().find(|d| d.name == *rep) else {
      continue;
    };
    if cls.len() < 2 || cls.iter().any(|x| carried_owners.contains(x)) {
      continue;
    }
    for m in cls.iter().skip(1) {
      let Some(md) = members.iter().find(|d| d.name == *m) else { continue };
      if md.level_params == rep_decl.level_params
        && alpha_eq_skip_mdata(
          &strip_all_mdata(&md.typ),
          &strip_all_mdata(&rep_decl.typ),
        )
      {
        aliases.push((m.clone(), rep.clone()));
      }
    }
  }
  let identity = sigma == id_perm(sigma.len());
  if identity && aliases.is_empty() {
    return CliqueOutcome::Unchanged(enc, source);
  }
  if identity {
    // the order is Lean's, but classes merge: the aliases alone
    let mut transported: FxHashMap<Name, Decl> = FxHashMap::default();
    for (m, rep) in &aliases {
      if let Some(rd) = members.iter().find(|d| d.name == *rep) {
        transported.insert(m.clone(), Decl { name: m.clone(), ..rd.clone() });
      }
    }
    return CliqueOutcome::Transported(Box::new(CliquePlan {
      all: all.to_vec(),
      encoding: enc,
      sigma,
      classes,
      source,
      members: transported,
      canon: Vec::new(),
      functionals: Vec::new(),
      causes: Vec::new(),
      aliases,
    }));
  }
  // the first canonical member names the canonical encoding
  let Some(g) = inv_perm(&sigma)
    .and_then(|inv| inv.first().copied())
    .and_then(|i| all.get(i))
  else {
    return baseline(
      enc,
      "the canonical order is not a permutation of the members".into(),
    );
  };
  let new_enc_name = match enc {
    Encoding::WellFounded => mk_str(&mk_str(g, IX_COMPONENT), "_mutual"),
    Encoding::PartialFixpoint => mk_str(&mk_str(g, IX_COMPONENT), "mutual"),
    Encoding::Structural => g.clone(),
  };
  // the carried lemmas: the members' own (Lean names), and the packed
  // constant's that they reach (canonical names)
  let mut carried_decls: Vec<Decl> = Vec::new();
  for c in carried {
    let Some(d) = const_of(c).and_then(|x| Decl::of_constant_info(&x)) else {
      return baseline(
        enc,
        format!("carried lemma {} is not a theorem", c.pretty()),
      );
    };
    carried_decls.push(d);
  }
  let packed_name = match aux.first() {
    Some(d) if enc != Encoding::Structural => d.name.clone(),
    _ => Name::anon(),
  };
  let packed_ls = if carried.is_empty() || enc == Encoding::Structural {
    Some(Vec::new())
  } else {
    packed_lemmas(const_of, &packed_name, &carried_decls)
  };
  let Some(packed_ls) = packed_ls else {
    return baseline(
      enc,
      format!(
        "the equation lemmas of {} exceed the bound",
        packed_name.pretty()
      ),
    );
  };
  let mut lemmas: Vec<(Decl, Name)> =
    carried_decls.iter().map(|d| (d.clone(), d.name.clone())).collect();
  for d in &packed_ls {
    lemmas.push((d.clone(), mk_str(&new_enc_name, last_str(&d.name))));
  }
  let carried_set: FxHashSet<Name> = carried.iter().cloned().collect();
  let out = transport(&Input {
    sigma: sigma.clone(),
    new_enc_name: new_enc_name.clone(),
    lemmas,
    ..inp0
  });
  if out.baseline {
    let why = out
      .causes
      .first()
      .map_or_else(|| "the transport kept Lean's form".into(), |c| c.2.clone());
    return baseline(enc, why);
  }
  // Lean's encoding constant ↦ its canonical name
  let mut ren: FxHashMap<Name, Name> = FxHashMap::default();
  let mut origin: FxHashMap<Name, Name> = FxHashMap::default();
  for (a, b) in &out.renames {
    origin.insert(b.clone(), a.clone());
  }
  if enc == Encoding::Structural {
    for d in &aux {
      if let Some(x) = clique_ix_name(all, &d.name) {
        ren.insert(d.name.clone(), x.clone());
        origin.insert(x, d.name.clone());
      }
    }
  }
  let decls: Vec<Decl> =
    out.decls.iter().map(|d| rename_decl(&ren, d)).collect();
  let causes: Vec<(Name, Cause, String)> = out
    .causes
    .iter()
    .map(|(c, k, why)| {
      (ren.get(c).cloned().unwrap_or_else(|| c.clone()), *k, why.clone())
    })
    .collect();
  let mut transported: FxHashMap<Name, Decl> = FxHashMap::default();
  let mut canon: Vec<(Decl, Name)> = Vec::new();
  for d in &decls {
    if member_set.contains(&d.name) || carried_set.contains(&d.name) {
      // a member or a member's lemma keeps its Lean name and Lean's type
      let Some(lean) =
        members.iter().chain(&carried_decls).find(|x| x.name == d.name)
      else {
        continue;
      };
      if !alpha_eq_skip_mdata(
        &strip_all_mdata(&d.typ),
        &strip_all_mdata(&lean.typ),
      ) {
        return baseline(
          enc,
          format!(
            "the transported {} does not have Lean's type",
            d.name.pretty()
          ),
        );
      }
      transported.insert(d.name.clone(), d.clone());
    } else {
      let src = origin.get(&d.name).cloned().unwrap_or_else(|| d.name.clone());
      if src == d.name {
        return baseline(
          enc,
          format!(
            "an encoding constant {} kept its Lean name",
            d.name.pretty()
          ),
        );
      }
      canon.push((d.clone(), src));
    }
  }
  if transported.len() != all.len() + carried.len() {
    return baseline(
      enc,
      "the transport did not return every member and carried lemma".into(),
    );
  }
  for (m, rep) in &aliases {
    if let Some(rd) = transported.get(rep).cloned() {
      transported.insert(m.clone(), Decl { name: m.clone(), ..rd });
    }
  }
  // a carried lemma must be transported exactly: a verbatim proof body would
  // prove Lean's statement about Lean's encoding
  if !causes.is_empty()
    && !carried.is_empty()
    && causes.iter().any(|(c, _, _)| {
      carried_set.contains(c) || packed_ls.iter().any(|d| d.name == *c)
    })
  {
    return baseline(
      enc,
      "a carried equation lemma is outside the grammar".into(),
    );
  }
  // a constant the transport introduced (the composition fallback, a
  // regenerated case split) must be in the input: otherwise Lean's form
  let mut lean_refs: FxHashSet<Name> = FxHashSet::default();
  for d in members.iter().chain(&carried_decls).chain(&aux).chain(&packed_ls) {
    lean_refs.extend(const_occurrences(&|_| true, &d.typ));
    lean_refs.extend(const_occurrences(&|_| true, &d.value));
  }
  let produced: FxHashSet<Name> =
    decls.iter().map(|d| d.name.clone()).collect();
  let introduced = |c: &Name| !lean_refs.contains(c) && !produced.contains(c);
  for d in &decls {
    let mut cs = const_occurrences(&introduced, &d.typ);
    cs.extend(const_occurrences(&introduced, &d.value));
    for c in cs {
      if const_of(&c).is_none() {
        return baseline(
          enc,
          format!(
            "{} needs {}, which is not in the input",
            d.name.pretty(),
            c.pretty()
          ),
        );
      }
    }
  }
  let functionals = match enc {
    Encoding::Structural => canon
      .iter()
      .filter(|(d, _)| last_str(&d.name) == "_f")
      .map(|(d, _)| d.name.clone())
      .collect(),
    _ => vec![new_enc_name],
  };
  CliqueOutcome::Transported(Box::new(CliquePlan {
    all: all.to_vec(),
    encoding: enc,
    sigma,
    classes,
    source,
    members: transported,
    canon,
    functionals,
    causes,
    aliases,
  }))
}

// ---------------------------------------------------------------------------
// Input constants
// ---------------------------------------------------------------------------

/// `valueOf?`: the value of a definition or theorem.
pub fn value_of(ci: &ConstantInfo) -> Option<&Expr> {
  match ci {
    ConstantInfo::DefnInfo(v) => Some(&v.value),
    ConstantInfo::ThmInfo(v) => Some(&v.value),
    _ => None,
  }
}

/// `withValue`: Lean's constant with another value (a definition or
/// theorem; any other constant unchanged).
pub fn with_value(ci: &ConstantInfo, e: Expr) -> ConstantInfo {
  match ci {
    ConstantInfo::DefnInfo(v) => {
      ConstantInfo::DefnInfo(DefinitionVal { value: e, ..v.clone() })
    },
    ConstantInfo::ThmInfo(v) => {
      ConstantInfo::ThmInfo(TheoremVal { value: e, ..v.clone() })
    },
    _ => ci.clone(),
  }
}

/// `canonConst`: a canonical constant as an input constant: a theorem, or a
/// safe definition with the hints of the Lean constant `src` it transports.
/// With `record = Some(r)` (a canonical functional,
/// [`CliquePlan::functionals`]), the value is wrapped in the side-car record
/// `[(clique_key, OfString(r))]`, where `r` is the plan's
/// [`CliquePlan::record`].
pub fn canon_const(
  const_of: ConstOf<'_>,
  d: &Decl,
  src: &Name,
  record: Option<String>,
) -> ConstantInfo {
  let value = match record {
    Some(r) => {
      Expr::mdata(vec![(clique_key(), DataValue::OfString(r))], d.value.clone())
    },
    None => d.value.clone(),
  };
  let cnst = ConstantVal {
    name: d.name.clone(),
    level_params: d.level_params.clone(),
    typ: d.typ.clone(),
  };
  if d.is_thm {
    ConstantInfo::ThmInfo(TheoremVal { cnst, value, all: vec![d.name.clone()] })
  } else {
    let hints = match const_of(src) {
      Some(ConstantInfo::DefnInfo(v)) => v.hints,
      _ => ReducibilityHints::Opaque,
    };
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst,
      value,
      hints,
      safety: DefinitionSafety::Safe,
      all: vec![d.name.clone()],
    })
  }
}

#[cfg(test)]
pub(crate) mod tests {
  use std::sync::Arc;

  use rustc_hash::FxHashSet;

  use ix_common::address::Address;
  use ix_common::env::{
    AxiomVal, ConstantInfo, ConstantVal, DataValue, DefinitionSafety,
    DefinitionVal, Env, Expr, Name, ReducibilityHints, TheoremVal,
  };

  use super::{
    authenticated_family, canon_const, encoding_proofs, packed_lemmas,
    plan_clique, reach_decls, value_of, with_value,
  };
  use crate::compile::pass3::clique::basic::{
    Cause, Decl, bvar, dotted, sort0,
  };
  use crate::compile::pass3::clique::plan::{
    CliqueOutcome, CliquePlan, Encoding, OrderSource,
  };
  use crate::compile::pass3::clique::table::clique_key;
  use crate::compile::pass3::clique::transport::tests::{
    Fixture, c, def, lam, pi, struct_clique, struct_env, wf_clique,
  };
  use crate::compile::pass3::clique::transport::{Input, transport};

  pub(crate) fn names(xs: &[&str]) -> Vec<Name> {
    xs.iter().map(|x| dotted(x)).collect()
  }

  /// The environment of the given constants.
  pub(crate) fn env_of(cs: Vec<ConstantInfo>) -> Arc<Env> {
    let mut env = Env::default();
    for ci in cs {
      env.insert(ci.get_name().clone(), ci);
    }
    Arc::new(env)
  }

  /// A declaration as an input constant of the clique `all` (a safe
  /// definition or a theorem).
  pub(crate) fn input_const(d: &Decl, all: &[Name]) -> ConstantInfo {
    let cnst = ConstantVal {
      name: d.name.clone(),
      level_params: d.level_params.clone(),
      typ: d.typ.clone(),
    };
    if d.is_thm {
      ConstantInfo::ThmInfo(TheoremVal {
        cnst,
        value: d.value.clone(),
        all: all.to_vec(),
      })
    } else {
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst,
        value: d.value.clone(),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: all.to_vec(),
      })
    }
  }

  /// The input of a clique: its members (Lean's `all`), each other
  /// constant of the encoding on its own, and `extra`.
  pub(crate) fn clique_env(
    k: &Fixture,
    all: &[Name],
    extra: Vec<ConstantInfo>,
  ) -> Arc<Env> {
    let mut cs: Vec<ConstantInfo> =
      k.members.iter().map(|d| input_const(d, all)).collect();
    cs.extend(
      k.aux.iter().map(|d| input_const(d, std::slice::from_ref(&d.name))),
    );
    cs.extend(extra);
    env_of(cs)
  }

  /// Addresses by name hash; the canonical (`_ix`) constants are not
  /// compiled yet.
  pub(crate) fn addr_of(n: &Name) -> Option<Address> {
    if n.pretty().split('.').any(|s| s == "_ix") {
      None
    } else {
      Some(Address::from_blake3_hash(*n.get_hash()))
    }
  }

  /// The well-founded clique `f, g` in its two presentations: Lean's order
  /// `f, g` (packed `f._mutual`), and the transported one, Lean's order
  /// `g, f` (packed `g._mutual`). One of them is in the canonical order.
  pub(crate) fn wf_presentations() -> [(Arc<Env>, Vec<Name>, Fixture); 2] {
    let k = wf_clique();
    let all = names(&["f", "g"]);
    let out = transport(&Input::new(
      Encoding::WellFounded,
      k.members.clone(),
      k.aux.clone(),
      vec![1, 0],
      dotted("g._mutual"),
    ));
    assert!(!out.baseline);
    let [p, q, f, g] = out.decls.as_slice() else { panic!("four constants") };
    let k2 = Fixture {
      members: vec![g.clone(), f.clone()],
      aux: vec![p.clone(), q.clone()],
    };
    let all2 = names(&["g", "f"]);
    [
      (clique_env(&k, &all, vec![]), all, k),
      (clique_env(&k2, &all2, vec![]), all2, k2),
    ]
  }

  /// The presentation of the well-founded clique that is transported, its
  /// plan, and the one that is unchanged.
  pub(crate) fn wf_transported()
  -> ((Arc<Env>, Vec<Name>, Fixture), CliquePlan, (Arc<Env>, Vec<Name>)) {
    let [a, b] = wf_presentations();
    let oa = plan_clique(&a.0, &addr_of, &a.1, &[]);
    let ob = plan_clique(&b.0, &addr_of, &b.1, &[]);
    let unchanged = |o: &CliqueOutcome| {
      matches!(
        o,
        CliqueOutcome::Unchanged(
          Encoding::WellFounded,
          OrderSource::Specification
        )
      )
    };
    match (oa, ob) {
      (CliqueOutcome::Transported(p), o) if unchanged(&o) => {
        (a, *p, (b.0, b.1))
      },
      (o, CliqueOutcome::Transported(p)) if unchanged(&o) => {
        (b, *p, (a.0, a.1))
      },
      (oa, ob) => panic!("{} / {}", oa.tag(), ob.tag()),
    }
  }

  #[test]
  fn plans_a_well_founded_clique() {
    let ((env, all, k), plan, _) = wf_transported();
    let (Some(all0), Some(all1)) = (all.first(), all.get(1)) else {
      panic!("two members")
    };
    // the canonical order puts Lean's second member first
    assert_eq!(plan.all, all);
    assert_eq!(plan.encoding, Encoding::WellFounded);
    assert_eq!(plan.sigma, vec![1, 0]);
    assert_eq!(plan.source, OrderSource::Specification);
    assert_eq!(plan.classes, vec![vec![all1.clone()], vec![all0.clone()]]);
    assert!(plan.aliases.is_empty() && plan.causes.is_empty());
    // the canonical encoding is named after the first canonical member
    let enc = format!("{}._ix._mutual", all1.pretty());
    let proof = format!("{enc}._proof_1");
    let lean_enc = format!("{}._mutual", all0.pretty());
    let canon: Vec<(Name, Name)> =
      plan.canon.iter().map(|(d, s)| (d.name.clone(), s.clone())).collect();
    assert_eq!(
      canon,
      vec![
        (dotted(&enc), dotted(&lean_enc)),
        (dotted(&proof), dotted(&format!("{lean_enc}._proof_1")))
      ]
    );
    assert_eq!(plan.functionals, vec![dotted(&enc)]);
    // the members keep their names and Lean's types
    assert_eq!(plan.members.len(), 2);
    for m in &k.members {
      let Some(d) = plan.members.get(&m.name) else { panic!("transported") };
      assert_eq!(d.typ, m.typ);
      assert_ne!(d.value, m.value);
    }
    // a carried lemma that is not in the input: Lean's form
    let carried = [dotted(&format!("{}.eq_1", all0.pretty()))];
    let o = plan_clique(&env, &addr_of, &all, &carried);
    let CliqueOutcome::Baseline(Encoding::WellFounded, Cause::Shape, why) = o
    else {
      panic!("{}", o.tag())
    };
    assert_eq!(
      why,
      format!("carried lemma {} is not a theorem", carried[0].pretty())
    );
  }

  #[test]
  fn not_encoded_cliques() {
    let k = wf_clique();
    let all = names(&["f", "g"]);
    let env = clique_env(&k, &all, vec![]);
    let plan =
      |env: &Arc<Env>, all: &[Name]| plan_clique(env, &addr_of, all, &[]);
    let not_encoded = |o: CliqueOutcome| match o {
      CliqueOutcome::NotEncoded(why) => why,
      o => panic!("{}", o.tag()),
    };
    assert_eq!(not_encoded(plan(&env, &all[..1])), "a single member");
    assert_eq!(
      not_encoded(plan(&env, &names(&["g", "f"]))),
      "member g has another clique"
    );
    // a member missing from the input
    let fh = names(&["f", "h"]);
    let env2 = clique_env(
      &Fixture { members: k.members[..1].to_vec(), aux: vec![] },
      &fh,
      vec![],
    );
    assert_eq!(not_encoded(plan(&env2, &fh)), "member h is not in the input");
    // an unsafe member
    let unsafe_f = match input_const(&k.members[0], &all) {
      ConstantInfo::DefnInfo(v) => ConstantInfo::DefnInfo(DefinitionVal {
        safety: DefinitionSafety::Unsafe,
        ..v
      }),
      ci => ci,
    };
    let env3 = clique_env(
      &Fixture { members: k.members[1..].to_vec(), aux: vec![] },
      &all,
      vec![unsafe_f],
    );
    assert_eq!(
      not_encoded(plan(&env3, &all)),
      "member f is not a safe definition or a theorem"
    );
    // members referencing each other: a kernel mutual block
    let nat_fn = pi("n", c("Nat"), c("Nat"));
    let mutual = Fixture {
      members: vec![
        def("f", nat_fn.clone(), lam("n", c("Nat"), Expr::app(c("g"), c("z")))),
        def("g", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
      ],
      aux: vec![],
    };
    assert_eq!(
      not_encoded(plan(&clique_env(&mutual, &all, vec![]), &all)),
      "members reference each other (a kernel mutual block)"
    );
    // no encoding
    let plain = Fixture {
      members: vec![
        def("f", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
        def("g", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
      ],
      aux: vec![],
    };
    assert_eq!(
      not_encoded(plan(&clique_env(&plain, &all, vec![]), &all)),
      "no encoding recognised"
    );
    // functionals, but the first member is not a `brecOn` application
    let functionals = Fixture {
      members: vec![
        def("f", nat_fn.clone(), lam("n", c("Nat"), bvar(0))),
        def("g", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
      ],
      aux: vec![
        def("f._f", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
        def("g._f", nat_fn.clone(), lam("n", c("Nat"), c("z"))),
      ],
    };
    assert_eq!(
      not_encoded(plan(&clique_env(&functionals, &all, vec![]), &all)),
      "structural: member f: not a brecOn application"
    );
  }

  #[test]
  fn nospec_baseline() {
    // equal statements, and a packed function the recovery cannot read
    let nat_fn = pi("n", c("Nat"), c("Nat"));
    let call = lam("n", c("Nat"), Expr::app(c("f._mutual"), bvar(0)));
    let k = Fixture {
      members: vec![
        def("f", nat_fn.clone(), call.clone()),
        def("g", nat_fn.clone(), call),
      ],
      aux: vec![def("f._mutual", nat_fn, lam("n", c("Nat"), c("z")))],
    };
    let all = names(&["f", "g"]);
    let o = plan_clique(&clique_env(&k, &all, vec![]), &addr_of, &all, &[]);
    let CliqueOutcome::Baseline(Encoding::WellFounded, Cause::NoSpec, why) = o
    else {
      panic!("{}", o.tag())
    };
    assert_eq!(
      why,
      "NOSPEC: wfLayout: the packed domain is not Lean's PSum packing; the \
       statements tie"
    );
  }

  #[test]
  fn structural_cliques_read_the_authenticated_family() {
    let k = struct_clique(false, "f._f");
    let all = names(&["f", "g"]);
    let env = clique_env(&k, &all, struct_env());
    // the hand-built `T.below` is not what Lean's generators build: nothing
    // is authenticated
    assert_eq!(
      authenticated_family(&env, &k.members),
      Ok(FxHashSet::default())
    );
    assert_eq!(authenticated_family(&env, &[]), Err("no member".to_string()));
    // a `brecOn` head that is not under an inductive of the input
    let bare = clique_env(&k, &all, vec![]);
    assert_eq!(
      authenticated_family(&bare, &k.members),
      Ok(FxHashSet::default())
    );
    // so the specification is not recovered: the statements order the
    // clique, Lean's order here
    let why = "T.below: not in the block's authenticated below/brecOn family";
    let o = plan_clique(&env, &addr_of, &all, &[]);
    let CliqueOutcome::Unchanged(
      Encoding::Structural,
      OrderSource::Statements(w),
    ) = o
    else {
      panic!("{}", o.tag())
    };
    assert_eq!(w, why);
    // the other presentation (Lean's order `g, f`, packing `PProd B A`) is
    // reordered, and the transport refuses: Lean's form
    let mut k2 = struct_clique(true, "f._f");
    k2.members.reverse();
    let all2 = names(&["g", "f"]);
    let env2 = clique_env(&k2, &all2, struct_env());
    let o = plan_clique(&env2, &addr_of, &all2, &[]);
    let CliqueOutcome::Baseline(Encoding::Structural, Cause::Shape, w) = o
    else {
      panic!("{}", o.tag())
    };
    assert_eq!(w, why);
  }

  #[test]
  fn closures_are_bounded() {
    let k = wf_clique();
    let all = names(&["f", "g"]);
    let env = clique_env(&k, &all, vec![]);
    let const_of = |n: &Name| env.get(n).map(|e| e.cloned());
    let Some(packed) = k.aux.first() else { panic!("a packed function") };
    let proofs = encoding_proofs(&const_of, packed)
      .map(|ds| ds.into_iter().map(|d| d.name).collect::<Vec<_>>());
    assert_eq!(proofs, Some(names(&["f._mutual._proof_1"])));
    // the worklist: the top first, unknown names marked but not kept
    let next = |_: &Decl| Vec::new();
    let reach = |fuel: usize| {
      reach_decls(
        &const_of,
        &next,
        fuel,
        names(&["g", "nope", "f"]),
        FxHashSet::default(),
        Vec::new(),
      )
      .map(|ds| ds.into_iter().map(|d| d.name).collect::<Vec<_>>())
    };
    assert_eq!(reach(3), Some(names(&["f", "g"])));
    assert_eq!(reach(2), None);
    // the packed constant's lemmas the carried ones reach, transitively
    let lemma = |n: &str, v: Expr| Decl { is_thm: true, ..def(n, sort0(), v) };
    let env = env_of(
      [
        lemma("P.eq_def", c("x")),
        lemma("P.eq_1", c("P.eq_def")),
        lemma("P.eq_unfold", c("x")),
      ]
      .iter()
      .map(|d| input_const(d, std::slice::from_ref(&d.name)))
      .collect(),
    );
    let const_of = |n: &Name| env.get(n).map(|e| e.cloned());
    let carried = [lemma("f.eq_1", Expr::app(c("P.eq_1"), c("Q.eq_def")))];
    let ls = packed_lemmas(&const_of, &dotted("P"), &carried)
      .map(|ds| ds.into_iter().map(|d| d.name).collect::<Vec<_>>());
    assert_eq!(ls, Some(names(&["P.eq_1", "P.eq_def"])));
  }

  #[test]
  fn canonical_constants_as_input_constants() {
    let src =
      input_const(&def("f._mutual", sort0(), c("x")), &names(&["f._mutual"]));
    let env = env_of(vec![src]);
    let const_of = |n: &Name| env.get(n).map(|e| e.cloned());
    let d = def("g._ix._mutual", sort0(), c("y"));
    let record = "well-founded; lean order #[f, g]".to_string();
    // a functional carries the side-car record and Lean's hints
    let ConstantInfo::DefnInfo(v) =
      canon_const(&const_of, &d, &dotted("f._mutual"), Some(record.clone()))
    else {
      panic!("a definition")
    };
    assert_eq!(
      v.value,
      Expr::mdata(vec![(clique_key(), DataValue::OfString(record))], c("y"))
    );
    assert_eq!(v.hints, ReducibilityHints::Regular(1));
    assert_eq!(v.safety, DefinitionSafety::Safe);
    assert_eq!(v.all, names(&["g._ix._mutual"]));
    assert_eq!((v.cnst.name, v.cnst.typ), (d.name.clone(), sort0()));
    // another constant: no record; no Lean definition: opaque
    let ConstantInfo::DefnInfo(v) =
      canon_const(&const_of, &d, &dotted("nope"), None)
    else {
      panic!("a definition")
    };
    assert_eq!((v.value, v.hints), (c("y"), ReducibilityHints::Opaque));
    let t = Decl { is_thm: true, ..d };
    let ConstantInfo::ThmInfo(v) =
      canon_const(&const_of, &t, &dotted("f._mutual"), None)
    else {
      panic!("a theorem")
    };
    assert_eq!((v.value, v.all), (c("y"), names(&["g._ix._mutual"])));
    // values
    let ci = input_const(&def("f", sort0(), c("x")), &names(&["f"]));
    assert_eq!(value_of(&ci), Some(&c("x")));
    assert_eq!(value_of(&with_value(&ci, c("y"))), Some(&c("y")));
    let ax = ConstantInfo::AxiomInfo(AxiomVal {
      cnst: ConstantVal {
        name: dotted("a"),
        level_params: vec![],
        typ: sort0(),
      },
      is_unsafe: false,
    });
    assert_eq!(value_of(&ax), None);
    assert!(matches!(with_value(&ax, c("y")), ConstantInfo::AxiomInfo(_)));
  }
}
