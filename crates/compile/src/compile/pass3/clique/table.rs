//! The definition cliques of the input, the changed-clique table and the
//! scheduling edges, and the reserved names of a clique's canonical
//! constants (a port of `Ix/Compile/Pass/Clique/Table.lean`).
//!
//! **The clique of a member.** Lean's `all` of a safe definition or a
//! theorem, when it has two or more members, each in its own block, and some
//! block references an encoding marker (`_mutual`, `mutual`, `_f`, or the
//! `brecOn` of an inductive predicate whose `below` is an inductive). A
//! kernel mutual block is one block, so it is not an encoded clique; neither
//! is a `partial` or `unsafe` clique.
//!
//! **The table.** Every member of an input clique, and every carried
//! equation lemma, ↦ (Lean's `all`, the carried lemmas) ([`schedule_cliques`]).
//! The form of a clique is decided from the clique, its own logical unit and
//! its dependencies only: no caller is read.
//!
//! **The edges** only order blocks (each member block can plan the clique
//! alone, and the first member's block plans it first); they change no byte.
//!
//! Total: loops over finite collections and two bounds of [`super::bounds`]
//! ([`EQ_LEMMA_BOUND`], [`ENCODING_OWNER_DEPTH`]). Wherever Lean orders names
//! (blocks, members, lemmas) it sorts them by [`Name::pretty`] (Lean's
//! `Ix.Name.pretty`), never by a hash map's order; so does this port.

use bignat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{ConstantInfo, DefinitionSafety, Name, NameData};

use super::basic::{ConstOf, Decl, dotted, mk_str, rename_consts, root_name};
use super::bounds::{ENCODING_OWNER_DEPTH, EQ_LEMMA_BOUND};
use crate::compile::pass3::names::{
  Comp, IX_COMPONENT, append_comps, comps, strip_prefix,
};
use crate::condense::CondensedBlocks;
use crate::graph::NameSet;

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

/// `cliqueKey`: the side-car record key on a canonical functional,
/// `_ix.clique`.
pub fn clique_key() -> Name {
  mk_str(&root_name(IX_COMPONENT), "clique")
}

/// `cliqueRecordBase`: the decompile records of transported members use
/// placeholder indices from here (the call-site rewrite's indices start at
/// `0` in every block).
pub const CLIQUE_RECORD_BASE: u64 = 1 << 40;

/// `lastStr`: the last string component (empty for a numeric or anonymous
/// name).
pub fn last_str(n: &Name) -> &str {
  match n.as_data() {
    NameData::Str(_, s, _) => s,
    _ => "",
  }
}

/// `cliqueIxName`: the display name of a Lean encoding constant `x.rest`
/// (`x` a member, the first in `all` that is a proper prefix): `x._ix.rest`.
pub fn clique_ix_name(all: &[Name], a: &Name) -> Option<Name> {
  let (x, rest) = all.iter().find_map(|x| match strip_prefix(x, a) {
    Some(rest) if !rest.is_empty() => Some((x, rest)),
    _ => None,
  })?;
  Some(append_comps(&mk_str(x, IX_COMPONENT), &rest))
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------
//
// The constants of a term satisfying a predicate are `const_occurrences`
// (`basic`): distinct names, in first-occurrence pre-order.

/// `renameDecl`: rename a declaration's name and the constants of its type
/// and value ([`rename_consts`]).
pub fn rename_decl(m: &FxHashMap<Name, Name>, d: &Decl) -> Decl {
  if m.is_empty() {
    return d.clone();
  }
  let get = |n: &Name| m.get(n).cloned();
  Decl {
    name: get(&d.name).unwrap_or_else(|| d.name.clone()),
    typ: rename_consts(&get, &d.typ),
    value: rename_consts(&get, &d.value),
    ..d.clone()
  }
}

// ---------------------------------------------------------------------------
// The clique of a member
// ---------------------------------------------------------------------------

/// `allOf`: Lean's `all` (empty for a constant that is neither a definition
/// nor a theorem).
pub fn all_of(ci: &ConstantInfo) -> Vec<Name> {
  match ci {
    ConstantInfo::DefnInfo(v) => v.all.clone(),
    ConstantInfo::ThmInfo(v) => v.all.clone(),
    _ => Vec::new(),
  }
}

/// `cliqueDecl?`: a safe definition or a theorem, as the transport's
/// declaration.
pub fn clique_decl(ci: &ConstantInfo) -> Option<Decl> {
  match ci {
    ConstantInfo::DefnInfo(v) if v.safety == DefinitionSafety::Safe => {
      Decl::of_constant_info(ci)
    },
    ConstantInfo::ThmInfo(_) => Decl::of_constant_info(ci),
    _ => None,
  }
}

/// `isEncodingMarker`: a name that marks a clique encoding in a reference
/// set: `_mutual` (well-founded), `mutual` (`partial_fixpoint`), `_f`
/// (structural), or the `brecOn` of an inductive predicate whose `below` is
/// an inductive (the inductive-predicate route).
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

// ---------------------------------------------------------------------------
// The clique table and the scheduling edges
// ---------------------------------------------------------------------------

/// `inputCliques`: the cliques of the input whose members are separate
/// blocks, by Lean's `all`. Only blocks that reference an encoding marker
/// are read: those blocks first, then sorted by their name, each block's
/// members sorted by name (pretty names, not the hash maps' order).
pub fn input_cliques(
  const_of: ConstOf<'_>,
  blocks: &CondensedBlocks,
) -> Vec<Vec<Name>> {
  let mut seen: FxHashSet<Name> = FxHashSet::default();
  let mut out: Vec<Vec<Name>> = Vec::new();
  let mut marked: Vec<(&Name, &NameSet)> = blocks
    .blocks
    .iter()
    .filter(|(lo, _)| {
      blocks.block_refs.get(*lo).is_some_and(|refs| {
        refs.iter().any(|r| is_encoding_marker(const_of, r))
      })
    })
    .collect();
  marked.sort_by_cached_key(|(lo, _)| lo.pretty());
  for (_, mems) in marked {
    let mut mems: Vec<&Name> = mems.iter().collect();
    mems.sort_by_cached_key(|m| m.pretty());
    for m in mems {
      if seen.contains(m) {
        continue;
      }
      let Some(ci) = const_of(m) else { continue };
      let all = all_of(&ci);
      if all.len() < 2 || clique_decl(&ci).is_none() {
        continue;
      }
      seen.extend(all.iter().cloned());
      // every member present, each in its own block
      let los: Vec<&Name> =
        all.iter().filter_map(|a| blocks.low_links.get(a)).collect();
      if los.len() != all.len() {
        continue;
      }
      let lo_set: FxHashSet<&Name> = los.iter().copied().collect();
      if lo_set.len() != all.len() {
        continue;
      }
      out.push(all);
    }
  }
  out
}

/// `isEncodingName`: a Lean encoding constant of a clique, by name:
/// `all₀._mutual` and `all₀.mutual` with everything under them (proofs,
/// equation lemmas), `m._f`.
pub fn is_encoding_name(all: &[Name], n: &Name) -> bool {
  let Some(all0) = all.first() else { return false };
  strip_prefix(&mk_str(all0, "_mutual"), n).is_some()
    || strip_prefix(&mk_str(all0, "mutual"), n).is_some()
    || matches!(n.as_data(), NameData::Str(p, s, _) if s == "_f" && all.contains(p))
}

/// `transportPrereqs`: the library constants the transport may introduce
/// (the composition fallback of `partial_fixpoint`, the case split of a
/// regenerated equation lemma): every clique block waits for them too, when
/// the input has them.
pub fn transport_prereqs() -> Vec<Name> {
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
  .into_iter()
  .map(dotted)
  .collect()
}

/// `privateUserName?`: `_private.<module>.0.<n>` ↦ `n` (Lean's
/// `privateToUserName?`): the module system realises an on-demand lemma of
/// a public definition under a private name when a private declaration asks
/// for it. The marker is the number `0` (Lean) or, in names that went
/// through a string form, the component `"0"`: the first one after
/// `_private`.
pub fn private_user_name(n: &Name) -> Option<Name> {
  let cs = comps(n);
  let (Comp::S(first), rest) = cs.split_first()? else { return None };
  if first != "_private" {
    return None;
  }
  let zero = Nat::from(0u64);
  let i = rest.iter().position(|c| match c {
    Comp::N(k) => *k == zero,
    Comp::S(s) => s == "0",
  })?;
  Some(append_comps(&Name::anon(), rest.get(i + 1..)?))
}

/// `isEqSuffix`: an equation lemma's last component: `eq_def`, `eq_unfold`,
/// `eq_<k>` (`k` ASCII digits, as Lean's `Char.isDigit`).
pub fn is_eq_suffix(s: &str) -> bool {
  s == "eq_def"
    || s == "eq_unfold"
    || s
      .strip_prefix("eq_")
      .is_some_and(|k| !k.is_empty() && k.chars().all(|c| c.is_ascii_digit()))
}

/// `privateEqLemmas`: the equation lemmas the input has under a private
/// name, by their user name ([`private_user_name`]). An index of names only:
/// a clique reads the entries of its own members' lemma names (each entry in
/// the blocks' order, which [`member_eq_lemmas`] sorts).
pub fn private_eq_lemmas(
  blocks: &CondensedBlocks,
) -> FxHashMap<Name, Vec<Name>> {
  let mut out: FxHashMap<Name, Vec<Name>> = FxHashMap::default();
  for mems in blocks.blocks.values() {
    for n in mems {
      let Some(u) = private_user_name(n) else { continue };
      if let NameData::Str(_, s, _) = u.as_data()
        && is_eq_suffix(s)
      {
        out.entry(u).or_default().push(n.clone());
      }
    }
  }
  out
}

/// `memberEqLemmas`: the equation lemmas of a member that the input has, by
/// name: `m.eq_def`, `m.eq_unfold` and `m.eq_1`, `m.eq_2`, … (numbered from
/// 1 without gaps, as Lean realises them, below [`EQ_LEMMA_BOUND`]), under
/// that name or under a private name whose user name it is (`privs`,
/// [`private_eq_lemmas`]). They are on-demand auxiliaries of the clique's
/// own unit: reading them is reading the unit.
pub fn member_eq_lemmas(
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
    ps.sort_by_cached_key(Name::pretty);
    out.extend(ps);
    out
  };
  let mut out = Vec::new();
  for s in ["eq_def", "eq_unfold"] {
    out.extend(present(&mk_str(m, s)));
  }
  for k in 1..EQ_LEMMA_BOUND {
    let found = present(&mk_str(m, &format!("eq_{k}")));
    if found.is_empty() {
      break;
    }
    out.extend(found);
  }
  out
}

/// The encoding roots (`all₀._mutual`, `all₀.mutual`, `m._f`) ↦ their
/// clique (Lean's `all`).
pub type EncodingRoots = FxHashMap<Name, Vec<Name>>;

/// `encodingOwner?`: the clique whose Lean encoding constant `n` is
/// ([`is_encoding_name`]): `n` or one of its prefixes is a root. The first
/// [`ENCODING_OWNER_DEPTH`] names (`n`, its parent, …) are looked up,
/// nearest first.
pub fn encoding_owner<'a>(
  roots: &'a EncodingRoots,
  n: &Name,
) -> Option<&'a Vec<Name>> {
  let mut cur = n.clone();
  for _ in 0..ENCODING_OWNER_DEPTH {
    if let Some(all) = roots.get(&cur)
      && is_encoding_name(all, n)
    {
      return Some(all);
    }
    cur = match cur.as_data() {
      NameData::Str(p, _, _) | NameData::Num(p, _, _) => p.clone(),
      NameData::Anonymous(_) => return None,
    };
  }
  None
}

/// The changed-clique table: member or carried lemma ↦ (Lean's `all`, the
/// carried lemmas).
pub type CliqueTable = FxHashMap<Name, (Vec<Name>, Vec<Name>)>;

/// `scheduleCliques`: the changed-clique table and the scheduling edges
/// (called once per compile, before the schedule). The form of a clique is
/// decided from the clique, its own logical unit and its dependencies only:
/// no caller is read. Adds the edges to `condensed.block_refs` (Lean returns
/// the blocks with them) and returns the table and the encoding roots.
///
/// * **The table.** Every member of an input clique ([`input_cliques`]) ↦
///   (Lean's `all`, the carried lemmas). The **carried lemmas** are the
///   members' own equation lemmas ([`member_eq_lemmas`], read by name: the
///   clique's unit) whose block references a member and one of Lean's
///   encoding constants of the clique ([`is_encoding_name`]): their proofs
///   unfold the members to Lean's encoding, so they are transported with the
///   clique (each carried lemma is in the table too), or the clique stays in
///   Lean's form when one cannot be carried.
/// * **The encoding roots.** `all₀._mutual`, `all₀.mutual` and every `m._f`
///   ↦ the clique, so that a block can tell that it references a clique's
///   encoding ([`encoding_owner`]).
/// * **The edges.** Every member block, and every carried lemma's block,
///   also waits for everything any member's block references and for the
///   input's [`transport_prereqs`], so that each such block can plan the
///   clique alone. The clique's other blocks also wait for the block of its
///   first member (`all₀`), which plans the clique first. These edges only
///   order blocks; they change no byte. The carried lemmas and the union are
///   read from the input's references (the references a block had before
///   this call), the edges accumulate over the cliques.
pub fn schedule_cliques(
  const_of: ConstOf<'_>,
  condensed: &mut CondensedBlocks,
) -> (CliqueTable, EncodingRoots) {
  let cliques = input_cliques(const_of, condensed);
  let mut table: CliqueTable = FxHashMap::default();
  let mut roots: EncodingRoots = FxHashMap::default();
  if cliques.is_empty() {
    return (table, roots);
  }
  let privs = private_eq_lemmas(condensed);
  // the input's references of every block this call extends, as they were
  // before it extended them (Lean reads the input's `blockRefs` throughout)
  let mut input: FxHashMap<Name, NameSet> = FxHashMap::default();
  let input_refs = |input: &FxHashMap<Name, NameSet>,
                    condensed: &CondensedBlocks,
                    lo: &Name|
   -> NameSet {
    input
      .get(lo)
      .or_else(|| condensed.block_refs.get(lo))
      .cloned()
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
    // the carried lemmas: the members' equation lemmas over Lean's encoding
    let mut found: Vec<Name> = Vec::new();
    for m in all {
      for c in member_eq_lemmas(const_of, &privs, m) {
        let Some(lo) = condensed.low_links.get(&c) else { continue };
        let refs = input_refs(&input, condensed, lo);
        if refs.iter().any(|r| is_encoding_name(all, r))
          && refs.iter().any(|r| all.contains(r))
        {
          found.push(c);
        }
      }
    }
    let mut carried = found;
    carried.sort_by_cached_key(Name::pretty);
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
    let mut union: NameSet = NameSet::default();
    for p in transport_prereqs() {
      if condensed.low_links.contains_key(&p) {
        union.insert(p);
      }
    }
    for lo in &los {
      for r in input_refs(&input, condensed, lo) {
        if !members.contains(&r) {
          union.insert(r);
        }
      }
    }
    // one block plans the clique first (the block of `all₀`); the clique's
    // other blocks also wait for it, so that they take the plan from the
    // plan table instead of planning it again in its wave
    let all0 = all.first();
    let planner_lo = all0.and_then(|a| condensed.low_links.get(a)).cloned();
    let mut targets = los.clone();
    targets.extend(
      carried.iter().filter_map(|c| condensed.low_links.get(c).cloned()),
    );
    for lo in targets {
      let own = condensed.blocks.get(&lo).cloned().unwrap_or_default();
      if !input.contains_key(&lo) {
        let refs = condensed.block_refs.get(&lo).cloned().unwrap_or_default();
        input.insert(lo.clone(), refs);
      }
      let rs = condensed.block_refs.entry(lo.clone()).or_default();
      for r in &union {
        if !own.contains(r) {
          rs.insert(r.clone());
        }
      }
      if let Some(all0) = all0
        && planner_lo.as_ref() != Some(&lo)
        && !own.contains(all0)
      {
        rs.insert(all0.clone());
      }
    }
  }
  (table, roots)
}

#[cfg(test)]
mod tests {
  use rustc_hash::FxHashMap;

  use ix_common::env::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Name,
    ReducibilityHints, TheoremVal,
  };

  use super::{
    CLIQUE_RECORD_BASE, EncodingRoots, clique_ix_name, clique_key,
    encoding_owner, is_encoding_name, is_eq_suffix, last_str,
    private_user_name, schedule_cliques,
  };
  use crate::compile::pass3::clique::basic::{
    cnst, dotted, mk_str, root_name, sort0,
  };
  use crate::compile::pass3::expr::nat;
  use crate::condense::CondensedBlocks;
  use crate::graph::NameSet;

  fn names(xs: &[&str]) -> Vec<Name> {
    xs.iter().map(|x| dotted(x)).collect()
  }

  #[test]
  fn private_user_names() {
    // the number `0` marker
    let n = Name::num(mk_str(&root_name("_private"), "Mod"), nat(0));
    let n = mk_str(&mk_str(&n, "f"), "eq_1");
    assert_eq!(private_user_name(&n), Some(dotted("f.eq_1")));
    // the string `"0"` marker, and only the first marker counts
    let n = dotted("_private.A.B.0.f.0.eq_2");
    assert_eq!(private_user_name(&n), Some(dotted("f.0.eq_2")));
    // nothing after the marker: the anonymous name
    assert_eq!(private_user_name(&dotted("_private.A.0")), Some(Name::anon()));
    // no marker, or not private
    assert_eq!(private_user_name(&dotted("_private.A.f")), None);
    assert_eq!(private_user_name(&dotted("f.eq_1")), None);
    assert_eq!(private_user_name(&Name::num(Name::anon(), nat(0))), None);
    assert_eq!(private_user_name(&Name::anon()), None);
  }

  #[test]
  fn eq_suffixes() {
    for s in ["eq_def", "eq_unfold", "eq_1", "eq_12", "eq_007"] {
      assert!(is_eq_suffix(s), "{s}");
    }
    // `Char.isDigit` is ASCII only
    for s in ["eq_", "eq_1a", "eq_x", "eqn_1", "eq_١", "eq_def_1", "", "eq"] {
      assert!(!is_eq_suffix(s), "{s}");
    }
  }

  #[test]
  fn reserved_names() {
    let all = names(&["f", "g"]);
    assert_eq!(
      clique_ix_name(&all, &dotted("f._mutual._proof_1")),
      Some(dotted("f._ix._mutual._proof_1"))
    );
    assert_eq!(
      clique_ix_name(&all, &dotted("g.eq_1")),
      Some(dotted("g._ix.eq_1"))
    );
    // a member itself, or a foreign name, has none
    assert_eq!(clique_ix_name(&all, &dotted("f")), None);
    assert_eq!(clique_ix_name(&all, &dotted("h.x")), None);
    assert_eq!(clique_ix_name(&[], &dotted("f.x")), None);
    // the first member in `all` that is a proper prefix
    assert_eq!(
      clique_ix_name(&names(&["f.g", "f"]), &dotted("f.g.x")),
      Some(dotted("f.g._ix.x"))
    );
    assert_eq!(
      clique_ix_name(&names(&["f", "f.g"]), &dotted("f.g.x")),
      Some(dotted("f._ix.g.x"))
    );
    assert_eq!(clique_key(), dotted("_ix.clique"));
    assert_eq!(CLIQUE_RECORD_BASE, 1_099_511_627_776);
    assert_eq!(last_str(&dotted("a.b")), "b");
    assert_eq!(last_str(&Name::num(dotted("a"), nat(1))), "");
  }

  #[test]
  fn encoding_owners() {
    let all = names(&["f", "g"]);
    let mut roots: EncodingRoots = FxHashMap::default();
    roots.insert(dotted("f._mutual"), all.clone());
    roots.insert(dotted("g._f"), all.clone());
    roots.insert(dotted("k._mutual"), names(&["h", "k"]));
    // a root, and names under `all₀._mutual`, nearest root first
    assert_eq!(encoding_owner(&roots, &dotted("f._mutual")), Some(&all));
    assert_eq!(
      encoding_owner(&roots, &dotted("f._mutual._proof_1")),
      Some(&all)
    );
    assert_eq!(encoding_owner(&roots, &dotted("g._f")), Some(&all));
    // under `m._f` is not an encoding name; nor is a root of another clique's
    // first member
    assert_eq!(encoding_owner(&roots, &dotted("g._f.x")), None);
    assert_eq!(encoding_owner(&roots, &dotted("k._mutual.x")), None);
    assert!(!is_encoding_name(&names(&["h", "k"]), &dotted("k._mutual.x")));
    assert_eq!(encoding_owner(&roots, &dotted("f")), None);
    assert_eq!(encoding_owner(&roots, &Name::anon()), None);
    // the walk looks up 64 names: the root is found 63 components below it,
    // not 64
    let under =
      |k: usize| (0..k).fold(dotted("f._mutual"), |n, i| Name::num(n, nat(i)));
    assert_eq!(encoding_owner(&roots, &under(63)), Some(&all));
    assert_eq!(encoding_owner(&roots, &under(64)), None);
  }

  fn defn(name: &str, all: &[&str], safety: DefinitionSafety) -> ConstantInfo {
    ConstantInfo::DefnInfo(DefinitionVal {
      cnst: ConstantVal {
        name: dotted(name),
        level_params: vec![],
        typ: sort0(),
      },
      value: sort0(),
      hints: ReducibilityHints::Opaque,
      safety,
      all: names(all),
    })
  }

  fn thm(name: &str) -> ConstantInfo {
    ConstantInfo::ThmInfo(TheoremVal {
      cnst: ConstantVal {
        name: dotted(name),
        level_params: vec![],
        typ: sort0(),
      },
      value: cnst(&dotted("f"), &[]),
      all: names(&[name]),
    })
  }

  fn set(xs: &[&str]) -> NameSet {
    xs.iter().map(|x| dotted(x)).collect()
  }

  #[test]
  fn schedules_a_clique() {
    // a well-founded clique `f, g` (each its own block), its packed function,
    // `f`'s equation lemma over the encoding (carried) and `g`'s over the
    // members only (not carried); an unsafe clique `u, v`; a caller `c`
    let consts: FxHashMap<Name, ConstantInfo> = [
      ("f", defn("f", &["f", "g"], DefinitionSafety::Safe)),
      ("g", defn("g", &["f", "g"], DefinitionSafety::Safe)),
      ("f._mutual", defn("f._mutual", &["f._mutual"], DefinitionSafety::Safe)),
      ("f.eq_1", thm("f.eq_1")),
      ("g.eq_1", thm("g.eq_1")),
      ("u", defn("u", &["u", "v"], DefinitionSafety::Unsafe)),
      ("v", defn("v", &["u", "v"], DefinitionSafety::Unsafe)),
      ("c", defn("c", &["c"], DefinitionSafety::Safe)),
      ("PSum.inl", defn("PSum.inl", &["PSum.inl"], DefinitionSafety::Safe)),
    ]
    .into_iter()
    .map(|(n, ci)| (dotted(n), ci))
    .collect();
    let const_of = |n: &Name| consts.get(n).cloned();
    let blocks =
      ["f", "g", "f._mutual", "f.eq_1", "g.eq_1", "u", "v", "c", "PSum.inl"];
    let refs = [
      ("f", set(&["f._mutual"])),
      ("g", set(&["f._mutual", "Nat"])),
      ("f._mutual", set(&["PSum.inl"])),
      ("f.eq_1", set(&["f", "f._mutual"])),
      ("g.eq_1", set(&["g", "f"])),
      ("u", set(&["u._mutual"])),
      ("v", set(&["u._mutual"])),
      ("c", set(&["f"])),
    ];
    let mut condensed = CondensedBlocks {
      low_links: blocks.iter().map(|b| (dotted(b), dotted(b))).collect(),
      blocks: blocks.iter().map(|b| (dotted(b), set(&[b]))).collect(),
      block_refs: refs.iter().map(|(b, r)| (dotted(b), r.clone())).collect(),
    };
    let (table, roots) = schedule_cliques(&const_of, &mut condensed);
    let all = names(&["f", "g"]);
    let entry = (all.clone(), names(&["f.eq_1"]));
    let want: FxHashMap<Name, (Vec<Name>, Vec<Name>)> =
      ["f", "g", "f.eq_1"].iter().map(|n| (dotted(n), entry.clone())).collect();
    assert_eq!(table, want);
    let want: EncodingRoots = ["f._mutual", "f.mutual", "f._f", "g._f"]
      .iter()
      .map(|n| (dotted(n), all.clone()))
      .collect();
    assert_eq!(roots, want);
    // the member blocks and the carried lemma's wait for the members'
    // references and the prerequisites the input has; the non-planning ones
    // also for `f`
    let refs_of = |b: &str| condensed.block_refs.get(&dotted(b)).cloned();
    assert_eq!(refs_of("f"), Some(set(&["f._mutual", "Nat", "PSum.inl"])));
    assert_eq!(refs_of("g"), Some(set(&["f._mutual", "Nat", "PSum.inl", "f"])));
    assert_eq!(
      refs_of("f.eq_1"),
      Some(set(&["f", "f._mutual", "Nat", "PSum.inl"]))
    );
    // the other blocks are unchanged
    assert_eq!(refs_of("g.eq_1"), Some(set(&["g", "f"])));
    assert_eq!(refs_of("c"), Some(set(&["f"])));
    assert_eq!(refs_of("u"), Some(set(&["u._mutual"])));
    assert_eq!(refs_of("PSum.inl"), None);
  }
}
