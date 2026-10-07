//! Pass 3's changed definition cliques: the clique table and its scheduling
//! edges, the plan of a clique, the callers' refusal and the hook before a
//! block compiles (a port of `Ix/Compile/Pass/Cliques.lean`).

use rustc_hash::{FxHashMap, FxHashSet};

use bignat::Nat;
use ix_common::address::Address;
use ix_common::env::{
  ConstantInfo, ConstantVal, DataValue, DefinitionSafety, DefinitionVal, Expr,
  ExprData, Name, NameData, ReducibilityHints, TheoremVal,
};

use super::basic::*;
use super::recover::clique_order;
use super::transport::{
  CliqueOutcome, CliquePlan, Encoding, Input, find_packed, transport,
};
use crate::compile::pass3::expr::{Comp, append_comps, strip_prefix};
use crate::compile::pass3::names::{IX_COMPONENT, inline_key};
use crate::condense::CondensedBlocks;
use crate::graph::NameSet;

/// `cliqueKey`: `_ix.clique`.
pub fn clique_key() -> Name {
  mk_str(&root(IX_COMPONENT), "clique")
}

/// `cliqueRecordBase`.
pub const CLIQUE_RECORD_BASE: usize = 1 << 40;

fn last_str(n: &Name) -> String {
  match n.as_data() {
    NameData::Str(_, s, _) => s.clone(),
    _ => String::new(),
  }
}

/// `cliqueIxName`.
pub fn clique_ix_name(all: &[Name], a: &Name) -> Option<Name> {
  let (x, rest) = all.iter().find_map(|x| match strip_prefix(x, a) {
    Some(rest) if !rest.is_empty() => Some((x.clone(), rest)),
    _ => None,
  })?;
  Some(append_comps(&mk_str(&x, IX_COMPONENT), &rest))
}

/// `constsWhere`: the constants of `e` satisfying `p`, each once (a walk
/// over distinct nodes, in Lean's stack order).
pub fn consts_where(p: &dyn Fn(&Name) -> bool, e: &Expr) -> Vec<Name> {
  let mut seen: FxHashSet<Hash> = FxHashSet::default();
  let mut found: FxHashSet<Name> = FxHashSet::default();
  let mut out = Vec::new();
  let mut stack = vec![e.clone()];
  while let Some(x) = stack.pop() {
    if !seen.insert(*x.get_hash()) {
      continue;
    }
    match x.as_data() {
      ExprData::Const(n, _, _) => {
        if p(n) && found.insert(n.clone()) {
          out.push(n.clone());
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        stack.push(s.clone())
      },
      _ => {},
    }
  }
  out
}

fn rename_decl(m: &FxHashMap<Name, Name>, d: &Decl) -> Decl {
  if m.is_empty() {
    return d.clone();
  }
  let get = |n: &Name| m.get(n).cloned();
  Decl {
    name: m.get(&d.name).cloned().unwrap_or_else(|| d.name.clone()),
    typ: rename_consts(&get, &d.typ),
    value: rename_consts(&get, &d.value),
    ..d.clone()
  }
}

/// `allOf`.
pub fn all_of(ci: &ConstantInfo) -> Vec<Name> {
  match ci {
    ConstantInfo::DefnInfo(v) => v.all.clone(),
    ConstantInfo::ThmInfo(v) => v.all.clone(),
    _ => Vec::new(),
  }
}

/// `cliqueDecl?`.
pub fn clique_decl(ci: &ConstantInfo) -> Option<Decl> {
  match ci {
    ConstantInfo::DefnInfo(v) => {
      if v.safety == DefinitionSafety::Safe {
        Decl::of_ci(ci)
      } else {
        None
      }
    },
    ConstantInfo::ThmInfo(_) => Decl::of_ci(ci),
    _ => None,
  }
}

/// `isEncodingMarker`.
pub fn is_encoding_marker(const_of: ConstOf<'_>, n: &Name) -> bool {
  match n.as_data() {
    NameData::Str(p, s, _) => {
      s == "_mutual"
        || s == "mutual"
        || s == "_f"
        || (s == "brecOn"
          && matches!(
            const_of(&mk_str(p, "below")),
            Some(ConstantInfo::InductInfo(_))
          ))
    },
    _ => false,
  }
}

/// `isEncodingName`.
pub fn is_encoding_name(all: &[Name], n: &Name) -> bool {
  let Some(all0) = all.first() else { return false };
  strip_prefix(&mk_str(all0, "_mutual"), n).is_some()
    || strip_prefix(&mk_str(all0, "mutual"), n).is_some()
    || match n.as_data() {
      NameData::Str(p, s, _) => s == "_f" && all.contains(p),
      _ => false,
    }
}

fn transport_prereqs() -> Vec<Name> {
  [
    "Lean.Order.monotone_compose",
    "PSigma.casesOn",
    "PSigma.mk",
    "PSum.casesOn",
    "PSum.inl",
    "PSum.inr",
    "Eq",
    "Eq.trans",
    "id",
  ]
  .iter()
  .map(|s| ln(s))
  .collect()
}

/// `privateUserName?`.
pub fn private_user_name(n: &Name) -> Option<Name> {
  let cs = crate::compile::pass3::expr::comps(n);
  match cs.first() {
    Some(Comp::S(s)) if s == "_private" => {
      let rest = &cs[1..];
      let zero = Nat::from(0u64);
      let i = rest.iter().position(|c| match c {
        Comp::N(k) => *k == zero,
        Comp::S(s) => s == "0",
      })?;
      Some(append_comps(&Name::anon(), &rest[i + 1..]))
    },
    _ => None,
  }
}

/// `isEqSuffix`.
pub fn is_eq_suffix(s: &str) -> bool {
  s == "eq_def"
    || s == "eq_unfold"
    || (s.starts_with("eq_")
      && s.len() > 3
      && s[3..].chars().all(|c| c.is_ascii_digit()))
}

/// `memberEqLemmas`.
fn member_eq_lemmas(
  const_of: ConstOf<'_>,
  privs: &FxHashMap<Name, Vec<Name>>,
  m: &Name,
) -> Vec<Name> {
  let present = |n: &Name| -> Vec<Name> {
    let mut out = Vec::new();
    if const_of(n).is_some() {
      out.push(n.clone());
    }
    let mut ps = privs.get(n).cloned().unwrap_or_default();
    ps.sort_by_key(|x| x.pretty());
    out.extend(ps);
    out
  };
  let mut out = Vec::new();
  for s in ["eq_def", "eq_unfold"] {
    out.extend(present(&mk_str(m, s)));
  }
  for k in 1..1_000_000usize {
    let found = present(&mk_str(m, &format!("eq_{k}")));
    if found.is_empty() {
      break;
    }
    out.extend(found);
  }
  out
}

/// `encodingOwner?`.
pub fn encoding_owner<'a>(
  roots: &'a FxHashMap<Name, Vec<Name>>,
  n: &Name,
) -> Option<&'a Vec<Name>> {
  let mut cur = n.clone();
  for _ in 0..64 {
    if let Some(all) = roots.get(&cur)
      && is_encoding_name(all, n)
    {
      return Some(all);
    }
    let next = match cur.as_data() {
      NameData::Str(p, _, _) | NameData::Num(p, _, _) => p.clone(),
      NameData::Anonymous(_) => return None,
    };
    cur = next;
  }
  None
}

/// The clique table: member or carried lemma ↦ (Lean's `all`, the carried
/// lemmas).
pub type CliqueTable = FxHashMap<Name, (Vec<Name>, Vec<Name>)>;

/// `scheduleCliques`: the table, the encoding roots, and the scheduling
/// edges added to `condensed.block_refs`.
pub fn schedule_cliques(
  const_of: ConstOf<'_>,
  condensed: &mut CondensedBlocks,
) -> (CliqueTable, FxHashMap<Name, Vec<Name>>) {
  // `inputCliques`
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut cliques: Vec<Vec<Name>> = Vec::new();
  let mut los_sorted: Vec<&Name> = condensed.blocks.keys().collect();
  los_sorted.sort_by_key(|n| n.pretty());
  for lo in los_sorted {
    let mems = &condensed.blocks[lo];
    let refs = condensed.block_refs.get(lo);
    if !refs.is_some_and(|r| r.iter().any(|x| is_encoding_marker(const_of, x)))
    {
      continue;
    }
    let mut ms: Vec<&Name> = mems.iter().collect();
    ms.sort_by_key(|n| n.pretty());
    for m in ms {
      if seen.contains(m) {
        continue;
      }
      let Some(ci) = const_of(m) else { continue };
      let all = all_of(&ci);
      if all.len() < 2 || clique_decl(&ci).is_none() {
        continue;
      }
      for a in &all {
        seen.insert(a.clone());
      }
      let los: Vec<&Name> =
        all.iter().filter_map(|a| condensed.low_links.get(a)).collect();
      if los.len() != all.len() {
        continue;
      }
      let lo_set: FxHashSet<&Name> = los.iter().copied().collect();
      if lo_set.len() != all.len() {
        continue;
      }
      cliques.push(all);
    }
  }
  let mut table: CliqueTable = FxHashMap::default();
  let mut roots: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
  if cliques.is_empty() {
    return (table, roots);
  }
  // `privateEqLemmas`
  let mut privs: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
  for mems in condensed.blocks.values() {
    for n in mems {
      let Some(u) = private_user_name(n) else { continue };
      if let NameData::Str(_, s, _) = u.as_data()
        && is_eq_suffix(s)
      {
        privs.entry(u.clone()).or_default().push(n.clone());
      }
    }
  }
  let mut orig: FxHashMap<Name, NameSet> = FxHashMap::default();
  let refs_of = |orig: &FxHashMap<Name, NameSet>,
                 c: &CondensedBlocks,
                 lo: &Name|
   -> NameSet {
    orig
      .get(lo)
      .cloned()
      .or_else(|| c.block_refs.get(lo).cloned())
      .unwrap_or_default()
  };
  for all in &cliques {
    if let Some(all0) = all.first() {
      roots.insert(mk_str(all0, "_mutual"), all.clone());
      roots.insert(mk_str(all0, "mutual"), all.clone());
    }
    for m in all {
      roots.insert(mk_str(m, "_f"), all.clone());
    }
    let mut found: Vec<Name> = Vec::new();
    for m in all {
      for c in member_eq_lemmas(const_of, &privs, m) {
        let Some(lo) = condensed.low_links.get(&c).cloned() else { continue };
        let refs = refs_of(&orig, condensed, &lo);
        if refs.iter().any(|r| is_encoding_name(all, r))
          && refs.iter().any(|r| all.contains(r))
        {
          found.push(c);
        }
      }
    }
    let mut carried = found;
    carried.sort_by_key(|x| x.pretty());
    for m in all {
      table.insert(m.clone(), (all.clone(), carried.clone()));
    }
    for c in &carried {
      table.insert(c.clone(), (all.clone(), carried.clone()));
    }
    // the edges
    let members: FxHashSet<&Name> = all.iter().collect();
    let los: Vec<Name> =
      all.iter().filter_map(|a| condensed.low_links.get(a).cloned()).collect();
    let mut union: Vec<Name> = Vec::new();
    for p in transport_prereqs() {
      if condensed.low_links.contains_key(&p) {
        union.push(p);
      }
    }
    for lo in &los {
      for r in refs_of(&orig, condensed, lo) {
        if !members.contains(&r) {
          union.push(r);
        }
      }
    }
    let all0 = all.first().cloned();
    let planner_lo =
      all0.as_ref().and_then(|a| condensed.low_links.get(a).cloned());
    let mut targets = los.clone();
    targets.extend(
      carried.iter().filter_map(|c| condensed.low_links.get(c).cloned()),
    );
    for lo in targets {
      let own = condensed.blocks.get(&lo).cloned().unwrap_or_default();
      if !orig.contains_key(&lo) {
        let cur = condensed.block_refs.get(&lo).cloned().unwrap_or_default();
        orig.insert(lo.clone(), cur);
      }
      let rs = condensed.block_refs.entry(lo.clone()).or_default();
      for r in &union {
        if !own.contains(r) {
          rs.insert(r.clone());
        }
      }
      if let Some(a0) = &all0
        && planner_lo.as_ref() != Some(&lo)
        && !own.contains(a0)
      {
        rs.insert(a0.clone());
      }
    }
  }
  (table, roots)
}

/// `encodingProofs`.
fn encoding_proofs(const_of: ConstOf<'_>, packed: &Decl) -> Vec<Decl> {
  let pn = packed.name.clone();
  let is_proof = |n: &Name| match n.as_data() {
    NameData::Str(q, s, _) => *q == pn && s.starts_with("_proof_"),
    _ => false,
  };
  let mut todo = consts_where(&is_proof, &packed.typ);
  todo.extend(consts_where(&is_proof, &packed.value));
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut out: Vec<Decl> = Vec::new();
  while let Some(n) = todo.pop() {
    if !seen.insert(n.clone()) {
      continue;
    }
    let Some(d) = const_of(&n).and_then(|c| Decl::of_ci(&c)) else { continue };
    todo.extend(consts_where(&is_proof, &d.typ));
    todo.extend(consts_where(&is_proof, &d.value));
    out.push(d);
  }
  out.sort_by_key(|d| d.name.pretty());
  out
}

/// `encodingOf`.
fn encoding_of(
  const_of: ConstOf<'_>,
  all: &[Name],
  members: &[Decl],
) -> Option<(Encoding, Vec<Decl>)> {
  let all0 = all.first()?;
  let packed_of = |s: &str| -> Option<Decl> {
    let d = const_of(&mk_str(all0, s)).and_then(|c| Decl::of_ci(&c))?;
    let p = find_packed(members, std::slice::from_ref(&d))?;
    if p.name == d.name { Some(d) } else { None }
  };
  if let Some(d) = packed_of("_mutual") {
    let mut v = vec![d.clone()];
    v.extend(encoding_proofs(const_of, &d));
    return Some((Encoding::WellFounded, v));
  }
  if let Some(d) = packed_of("mutual") {
    let mut v = vec![d.clone()];
    v.extend(encoding_proofs(const_of, &d));
    return Some((Encoding::PartialFixpoint, v));
  }
  let fs: Vec<Decl> = all
    .iter()
    .filter_map(|m| const_of(&mk_str(m, "_f")).and_then(|c| Decl::of_ci(&c)))
    .collect();
  let mut matchers: Vec<Name> = Vec::new();
  for d in members {
    for n in consts_where(&|n| last_str(n).starts_with("match_"), &d.value) {
      if !matchers.contains(&n) {
        matchers.push(n);
      }
    }
  }
  matchers.sort_by_key(|n| n.pretty());
  let ms: Vec<Decl> = matchers
    .iter()
    .filter_map(|n| const_of(n).and_then(|c| Decl::of_ci(&c)))
    .collect();
  if fs.len() == all.len() {
    let mut v = fs;
    v.extend(ms);
    return Some((Encoding::Structural, v));
  }
  if fs.is_empty()
    && members.iter().all(|d| {
      !consts_where(&|n| is_encoding_marker(const_of, n), &d.value).is_empty()
    })
  {
    return Some((Encoding::Structural, ms));
  }
  None
}

/// `packedLemmas`.
fn packed_lemmas(
  const_of: ConstOf<'_>,
  p: &Name,
  carried: &[Decl],
) -> Vec<Decl> {
  let is_packed_eq = |n: &Name| match n.as_data() {
    NameData::Str(q, s, _) => {
      q == p && (s == "eq_def" || s == "eq_unfold" || s.starts_with("eq_"))
    },
    _ => false,
  };
  let mut todo: Vec<Name> = Vec::new();
  for d in carried {
    todo.extend(consts_where(&is_packed_eq, &d.value));
  }
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut out = Vec::new();
  while let Some(n) = todo.pop() {
    if !seen.insert(n.clone()) {
      continue;
    }
    let Some(d) = const_of(&n).and_then(|c| Decl::of_ci(&c)) else { continue };
    todo.extend(consts_where(&is_packed_eq, &d.value));
    out.push(d);
  }
  out.sort_by_key(|d| d.name.pretty());
  out
}

fn baseline(enc: Encoding, why: String) -> CliqueOutcome {
  CliqueOutcome::Baseline(enc, "SHAPE".into(), why)
}

/// `planClique`.
pub fn plan_clique(
  const_of: ConstOf<'_>,
  addr: &dyn Fn(&Name) -> Option<Address>,
  all: &[Name],
  carried: &[Name],
) -> CliqueOutcome {
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
    if all_of(&cm) != all {
      return CliqueOutcome::NotEncoded(format!(
        "member {} has another clique",
        m.pretty()
      ));
    }
    members.push(d);
  }
  let member_set: FxHashSet<Name> = all.iter().cloned().collect();
  for d in &members {
    if !consts_where(&|n| member_set.contains(n), &d.value).is_empty() {
      return CliqueOutcome::NotEncoded(
        "members reference each other (a kernel mutual block)".into(),
      );
    }
  }
  let Some((enc, aux)) = encoding_of(const_of, all, &members) else {
    return CliqueOutcome::NotEncoded("no encoding recognised".into());
  };
  let inp0 = Input {
    encoding: enc,
    members: members.clone(),
    aux: aux.clone(),
    sigma: id_perm(all.len()),
    new_enc_name: all[0].clone(),
    const_of,
    lemmas: Vec::new(),
  };
  let (sigma, classes, source) = match clique_order(addr, &inp0) {
    Err(why) => return CliqueOutcome::Baseline(enc, "NOSPEC".into(), why),
    Ok(x) => x,
  };
  // O17
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
    for m in &cls[1..] {
      let Some(md) = members.iter().find(|d| d.name == *m) else { continue };
      if md.level_params == rep_decl.level_params
        && alpha_eq(&strip_all_mdata(&md.typ), &strip_all_mdata(&rep_decl.typ))
      {
        aliases.push((m.clone(), rep.clone()));
      }
    }
  }
  let identity = sigma.iter().enumerate().all(|(i, &s)| s == i);
  if identity && aliases.is_empty() {
    return CliqueOutcome::Unchanged(enc, source);
  }
  if identity {
    let mut transported: FxHashMap<Name, Decl> = FxHashMap::default();
    for (m, rep) in &aliases {
      if let Some(rd) = members.iter().find(|d| d.name == *rep) {
        transported.insert(m.clone(), rd.with_name(m.clone()));
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
  let g = all[inv_perm(&sigma)[0]].clone();
  let new_enc_name = match enc {
    Encoding::WellFounded => mk_str(&mk_str(&g, IX_COMPONENT), "_mutual"),
    Encoding::PartialFixpoint => mk_str(&mk_str(&g, IX_COMPONENT), "mutual"),
    Encoding::Structural => g.clone(),
  };
  let mut carried_decls: Vec<Decl> = Vec::new();
  for c in carried {
    let Some(d) = const_of(c).and_then(|x| Decl::of_ci(&x)) else {
      return baseline(
        enc,
        format!("carried lemma {} is not a theorem", c.pretty()),
      );
    };
    carried_decls.push(d);
  }
  let packed_name = match aux.first() {
    Some(d) => {
      if enc == Encoding::Structural {
        Name::anon()
      } else {
        d.name.clone()
      }
    },
    None => Name::anon(),
  };
  let packed_ls = if carried.is_empty() || enc == Encoding::Structural {
    Vec::new()
  } else {
    packed_lemmas(const_of, &packed_name, &carried_decls)
  };
  let mut lemmas: Vec<(Decl, Name)> =
    carried_decls.iter().map(|d| (d.clone(), d.name.clone())).collect();
  for d in &packed_ls {
    lemmas.push((d.clone(), mk_str(&new_enc_name, &last_str(&d.name))));
  }
  let carried_set: FxHashSet<Name> = carried.iter().cloned().collect();
  let inp = Input {
    sigma: sigma.clone(),
    new_enc_name: new_enc_name.clone(),
    lemmas,
    ..inp0
  };
  let out = transport(&inp);
  if out.baseline {
    let why = out
      .causes
      .first()
      .map_or_else(|| "the transport kept Lean's form".into(), |c| c.2.clone());
    return baseline(enc, why);
  }
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
      let Some(lean) =
        members.iter().chain(carried_decls.iter()).find(|x| x.name == d.name)
      else {
        continue;
      };
      if !alpha_eq(&strip_all_mdata(&d.typ), &strip_all_mdata(&lean.typ)) {
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
      transported.insert(m.clone(), rd.with_name(m.clone()));
    }
  }
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
  let mut lean_refs: FxHashSet<Name> = FxHashSet::default();
  for d in members
    .iter()
    .chain(carried_decls.iter())
    .chain(aux.iter())
    .chain(packed_ls.iter())
  {
    lean_refs.extend(consts_where(&|_| true, &d.typ));
    lean_refs.extend(consts_where(&|_| true, &d.value));
  }
  let produced: FxHashSet<Name> =
    decls.iter().map(|d| d.name.clone()).collect();
  for d in &decls {
    let p = |c: &Name| !lean_refs.contains(c) && !produced.contains(c);
    let mut cs = consts_where(&p, &d.typ);
    cs.extend(consts_where(&p, &d.value));
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
    _ => vec![new_enc_name.clone()],
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

/// `canonConst`.
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

/// `withValue`.
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

pub fn value_of(ci: &ConstantInfo) -> Option<Expr> {
  match ci {
    ConstantInfo::DefnInfo(v) => Some(v.value.clone()),
    ConstantInfo::ThmInfo(v) => Some(v.value.clone()),
    _ => None,
  }
}

/// What the hook gives a block.
#[derive(Default)]
pub struct CliquePrep {
  /// The transported members (Lean's type, the transported value under
  /// the decompile record of Lean's value).
  pub overlay: FxHashMap<Name, ConstantInfo>,
  /// The decompile sources of the records, by placeholder index.
  pub sources: Vec<(usize, Expr)>,
  /// The canonical constants this block reaches, as input constants.
  pub canon: FxHashMap<Name, ConstantInfo>,
  /// Their names in the order the block wants them.
  pub wanted: Vec<Name>,
}

/// The clique hook's read of the compile state.
pub struct HookEnv<'a> {
  pub const_of: ConstOf<'a>,
  pub addr: &'a dyn Fn(&Name) -> Option<Address>,
  pub table: &'a CliqueTable,
  pub roots: &'a FxHashMap<Name, Vec<Name>>,
  /// The plan table (a memo of `planClique`, keyed by `all[0]`).
  pub plans: &'a dashmap::DashMap<Name, CliqueOutcome>,
}

impl HookEnv<'_> {
  /// `cliquePlanFor` (without the check mode).
  pub fn plan_for(&self, cl: &[Name], carried: &[Name]) -> CliqueOutcome {
    let Some(key) = cl.first() else {
      return plan_clique(self.const_of, self.addr, cl, carried);
    };
    if let Some(o) = self.plans.get(key) {
      return o.clone();
    }
    let o = plan_clique(self.const_of, self.addr, cl, carried);
    self.plans.entry(key.clone()).or_insert(o).clone()
  }

  /// `cliqueCallers`: the refusal of a block outside a transported clique's
  /// unit that references a member and an encoding constant.
  pub fn callers(&self, all: &NameSet, refs: &[Name]) -> Option<String> {
    if self.roots.is_empty() {
      return None;
    }
    let mut seen: FxHashSet<Name> = FxHashSet::default();
    for r in refs {
      let Some(cl) = encoding_owner(self.roots, r) else { continue };
      let Some(key) = cl.first() else { continue };
      if !seen.insert(key.clone()) {
        continue;
      }
      let carried =
        self.table.get(key).map(|x| x.1.clone()).unwrap_or_default();
      if all.iter().any(|n| {
        cl.contains(n) || carried.contains(n) || is_encoding_name(cl, n)
      }) {
        continue;
      }
      let Some(m) = refs.iter().find(|x| cl.contains(x)) else { continue };
      if let CliqueOutcome::Transported(plan) = self.plan_for(cl, &carried) {
        let mut callers: Vec<String> = all.iter().map(|n| n.pretty()).collect();
        callers.sort();
        let s = if callers.len() == 1 { "s" } else { "" };
        return Some(format!(
          "Pass 3 cliques: caller refused (block rule, callers adapt): {} reference{} {} and Lean's encoding constant {} of the transported clique {} (sigma {}); a caller may not unfold Lean's encoding of a transported clique",
          list_str(&callers),
          s,
          m.pretty(),
          r.pretty(),
          arr_str(&cl.iter().map(|n| n.pretty()).collect::<Vec<_>>()),
          arr_nat(&plan.sigma)
        ));
      }
    }
    None
  }

  /// `prepareCliques` (planning only; the driver compiles the canonical
  /// constants). `Err` is a refusal or a failure of the block.
  pub fn prepare(
    &self,
    all: &NameSet,
    refs: &[Name],
  ) -> Result<CliquePrep, String> {
    let mut prep = CliquePrep::default();
    if self.table.is_empty() {
      return Ok(prep);
    }
    if let Some(refusal) = self.callers(all, refs) {
      return Err(refusal);
    }
    let mut names: Vec<&Name> = all.iter().collect();
    names.sort_by_key(|n| n.pretty());
    let mut k = 0usize;
    for n in names {
      let Some((cl, carried)) = self.table.get(n) else { continue };
      let CliqueOutcome::Transported(plan) = self.plan_for(cl, carried) else {
        continue;
      };
      let Some(md) = plan.members.get(n) else { continue };
      let Some(ci) = (self.const_of)(n) else { continue };
      let Some(lean_value) = value_of(&ci) else { continue };
      let idx = CLIQUE_RECORD_BASE + k;
      k += 1;
      prep.overlay.insert(
        n.clone(),
        with_value(
          &ci,
          Expr::mdata(
            vec![(inline_key(), DataValue::OfNat(Nat::from(idx as u64)))],
            md.value.clone(),
          ),
        ),
      );
      prep.sources.push((idx, lean_value));
      let canon_names: FxHashSet<Name> =
        plan.canon.iter().map(|(d, _)| d.name.clone()).collect();
      for (d, src) in &plan.canon {
        if !prep.canon.contains_key(&d.name) {
          let record = if plan.functionals.contains(&d.name) {
            Some(plan.record())
          } else {
            None
          };
          prep
            .canon
            .insert(d.name.clone(), canon_const(self.const_of, d, src, record));
        }
      }
      let mut todo = consts_where(&|x| canon_names.contains(x), &md.value);
      while let Some(c) = todo.pop() {
        if prep.wanted.contains(&c) {
          continue;
        }
        prep.wanted.push(c.clone());
        if let Some(cc) = prep.canon.get(&c) {
          todo
            .extend(consts_where(&|x| canon_names.contains(x), cc.get_type()));
          if let Some(v) = value_of(cc) {
            todo.extend(consts_where(&|x| canon_names.contains(x), &v));
          }
        }
      }
    }
    Ok(prep)
  }
}
