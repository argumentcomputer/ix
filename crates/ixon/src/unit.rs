//! Logical units (design document §6.2-§6.3): the Rust port of the unit
//! view of `Ix/Common.lean` (`Lean.UnitView`, `unitAuxComponent`,
//! `unitReservedComponent`, `UnitView.auxOwner?`/`key`/`index`/`members`)
//! and of its compiled-environment source `Ix.Cli.PackCmd.ixonUnitView`,
//! with `missingUnitMembers` (M6R slice 5).
//!
//! The **logical unit** of a block is the block with all of its auxiliaries:
//! the constants Lean generates mechanically from it, eagerly (with the
//! declaration) or on demand (when a later declaration first asks for them).
//! A closure producer must carry, for every block in the closure, the whole
//! unit, on-demand auxiliaries included (§6.3, "On-demand auxiliaries"), so
//! that a block that reads its own unit (a clique its equation lemmas, O11a
//! its sibling's size instance) compiles in a closure as in the whole
//! environment.
//!
//! Auxiliaries are recognised by name, under the declaration they belong to
//! (the **owner**): `X.s…` where `X` is a constant and the component `s` is
//! one Lean's generators use for `X`'s kind ([`unit_aux_component`]), with
//! anything below it (`T.brecOn.go`, `f.match_1.splitter`, `f.match_1.eq_2`).
//! Private auxiliaries (`_private.M.0.f.match_1.eq_1`,
//! `_private.M.0.T.casesOn._arg_pusher`) are matched through their user name.
//! A name with a reserved component of Pass 3 ([`unit_reserved_component`]:
//! `c._ix`, `f._ix.fg`, `p._ix_retyped._f`, `x._ix._f`, `g._ix._mutual`, the
//! display names `x._ix.rec`, O11b's `T.noConfusionType._ix`) is a
//! compiler-generated auxiliary of the declaration it hangs under and belongs
//! to that declaration's unit (orchestrator's ruling, INT-fix, 2026-10-06).
//! The set is a name convention, so a user declaration that happens to use
//! one of these names under a constant of the matching kind is carried too: a
//! superset of the unit, which only enlarges a closure.
//!
//! Where the Lean side reads units from two sources (a Lean environment,
//! `Lean.leanUnitView`, for the selected closures of the Lean input, and a
//! compiled environment, `ixonUnitView`, for `ix pack`), the Rust side has
//! only the second: the selected closures are computed in Lean
//! (`Ix.EnvScope.collectSelectedDeps`) and handed to either compiler, and the
//! only Rust closure producer that carries units is the pack
//! ([`crate::env::Env::prune_to_closure_units`] and its streaming and
//! anonymous variants).

use ix_common::address::Address;
use ix_common::env::{Name, NameData};
use rustc_hash::FxHashMap;

use crate::env::{Env, Named};
use crate::metadata::ConstantMetaInfo;

/// The kind of declaration an auxiliary can hang under (`Lean.UnitOwnerKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnitOwnerKind {
  Induct,
  Ctor,
  Defn,
}

/// `s` is `pre` followed by a non-empty run of digits
/// (`numberedComponent`).
fn numbered_component(s: &str, pre: &str) -> bool {
  match s.strip_prefix(pre) {
    Some(r) => !r.is_empty() && r.chars().all(|c| c.is_ascii_digit()),
    None => false,
  }
}

/// Is `s`, directly under a constant of kind `k`, the first component of a
/// Lean-generated auxiliary of it? (`Lean.unitAuxComponent`, the kinds Lean
/// 4.34.1 generates.)
pub fn unit_aux_component(k: UnitOwnerKind, s: &str) -> bool {
  match k {
    UnitOwnerKind::Induct => {
      [
        "rec",
        "casesOn",
        "recOn",
        "below",
        "brecOn",
        "binductionOn",
        "ibelow",
        "noConfusionType",
        "noConfusion",
        "_sizeOf_inst",
        "ctorIdx",
        "toCtorIdx",
        "ctorElim",
        "ctorElimType",
        "congr_simp",
        "enumToBitVec",
        "eq_iff_enumToBitVec_eq",
        "enumToBitVec_le",
      ]
      .contains(&s)
        || [
          "rec_",
          "below_",
          "brecOn_",
          "_sizeOf_",
          "_sparseCasesOn_",
          "hcongr_",
        ]
        .iter()
        .any(|p| numbered_component(s, p))
    },
    UnitOwnerKind::Ctor => {
      [
        "elim",
        "inj",
        "injEq",
        "hinj",
        "sizeOf_spec",
        "noConfusion",
        "congr_simp",
      ]
      .contains(&s)
        || numbered_component(s, "hcongr_")
    },
    UnitOwnerKind::Defn => {
      [
        "eq_def",
        "eq_unfold",
        "_unary",
        "_binary",
        "_mutual",
        "mutual",
        "_f",
        "_sunfold",
        "_unsafe_rec",
        "induct",
        "mutual_induct",
        "fun_cases",
        "induct_unfolding",
        "fixpoint_induct",
        "partial_correctness",
        "congr_simp",
        "_arg_pusher",
        "splitter",
        "match_eq_cond",
      ]
      .contains(&s)
        || ["eq_", "match_", "_proof_", "proof_", "hcongr_", "congr_eq_"]
          .iter()
          .any(|p| numbered_component(s, p))
    },
  }
}

/// Is `s` a reserved component of Pass 3 (`_ix`, `_ix_retyped`, `_ix_rule`,
/// …)? A name with one is a compiler-generated auxiliary of the declaration
/// it hangs under (`c._ix`, `f._ix.fg`, `p._ix_retyped._f`, `x._ix._f`,
/// `g._ix._mutual`) and belongs to that declaration's logical unit
/// (`Lean.unitReservedComponent`). A Lean environment has no such name (the
/// compiler refuses an input with one), so only a compiled environment's view
/// meets it.
pub fn unit_reserved_component(s: &str) -> bool {
  s == "_ix" || s.starts_with("_ix_")
}

/// `Lean.isPrivateName`: the name's first component is the string
/// `_private`.
fn is_private_name(n: &Name) -> bool {
  match n.as_data() {
    NameData::Str(p, s, _) => {
      (s == "_private" && matches!(p.as_data(), NameData::Anonymous(_)))
        || is_private_name(p)
    },
    NameData::Num(p, _, _) => is_private_name(p),
    NameData::Anonymous(_) => false,
  }
}

/// `Lean.isPrivatePrefix`: `n` is `_private.<module>.0`.
fn is_private_prefix(n: &Name) -> bool {
  fn go(n: &Name) -> bool {
    match n.as_data() {
      NameData::Str(p, s, _) => {
        (s == "_private" && matches!(p.as_data(), NameData::Anonymous(_)))
          || go(p)
      },
      _ => false,
    }
  }
  match n.as_data() {
    NameData::Num(p, i, _) => i.to_u64() == Some(0) && go(p),
    _ => false,
  }
}

/// `privateToUserNameAux`.
fn private_to_user_name_aux(n: &Name) -> Name {
  match n.as_data() {
    NameData::Str(p, s, _) => Name::str(private_to_user_name_aux(p), s.clone()),
    NameData::Num(p, i, _) => {
      if is_private_prefix(n) {
        Name::anon()
      } else {
        Name::num(private_to_user_name_aux(p), i.clone())
      }
    },
    NameData::Anonymous(_) => Name::anon(),
  }
}

/// `Lean.privateToUserName?`: the user name of a private name.
pub fn private_to_user_name(n: &Name) -> Option<Name> {
  if is_private_name(n) { Some(private_to_user_name_aux(n)) } else { None }
}

/// Every auxiliary of the environment by the key of its owner's unit
/// (`Lean.UnitIndex`). Built once per closure walk (a pass over the names).
pub type UnitIndex = FxHashMap<Name, Vec<Name>>;

/// What a logical unit is read from (`Lean.UnitView`): the kind of a
/// declaration as an owner of auxiliaries, the roots of its unit, and the
/// names of the environment.
pub trait UnitView {
  /// The kind of `n` as an owner of auxiliaries (`kind?`).
  fn kind(&self, n: &Name) -> Option<UnitOwnerKind>;
  /// The roots of the unit of a declaration `o` (`roots`).
  fn roots(&self, o: &Name) -> Vec<Name>;
  /// Is `n` a name of the environment (`contains`)?
  fn contains(&self, n: &Name) -> bool;
  /// Every name (`names`).
  fn names(&self) -> Vec<Name>;

  /// The owner of `n` when `n` is an auxiliary by name
  /// (`UnitView.auxOwner?`): the shortest proper prefix `X` of `n` that is a
  /// declaration and whose next component is an auxiliary component for
  /// `X`'s kind, or a reserved component of Pass 3 (any kind). A private
  /// name is tried as itself and then through its user name.
  fn aux_owner(&self, n: &Name) -> Option<Name> {
    let walk = |m: &Name| -> Option<Name> {
      // The prefixes of `m` from the root: `prefixes[i]` ends with component
      // `i`. Lean extends `pre` component by component; names are
      // structural, so each extension is the prefix itself. The first
      // prefix is never an owner (Lean skips an anonymous `pre`).
      let mut prefixes: Vec<Name> = Vec::new();
      let mut cur = m.clone();
      loop {
        let parent = match cur.as_data() {
          NameData::Anonymous(_) => break,
          NameData::Str(p, ..) | NameData::Num(p, ..) => p.clone(),
        };
        prefixes.push(cur);
        cur = parent;
      }
      prefixes.reverse();
      for w in prefixes.windows(2) {
        let (pre, c) = (&w[0], &w[1]);
        if let NameData::Str(_, s, _) = c.as_data()
          && let Some(k) = self.kind(pre)
          && (unit_aux_component(k, s) || unit_reserved_component(s))
        {
          return Some(pre.clone());
        }
      }
      None
    };
    match walk(n) {
      Some(o) => Some(o),
      None => private_to_user_name(n).and_then(|u| walk(&u)),
    }
  }

  /// The key of the unit of a declaration `o` (the first root;
  /// `UnitView.key`).
  fn key(&self, o: &Name) -> Name {
    self.roots(o).into_iter().next().unwrap_or_else(|| o.clone())
  }

  /// Every auxiliary of the environment by the key of its owner's unit
  /// (`UnitView.index`).
  fn index(&self) -> UnitIndex {
    let mut idx: UnitIndex = FxHashMap::default();
    for n in self.names() {
      if let Some(o) = self.aux_owner(&n) {
        idx.entry(self.key(&o)).or_default().push(n);
      }
    }
    idx
  }

  /// The logical unit of `n`'s declaration: its roots and every auxiliary of
  /// them, eager or on demand, that exists (an auxiliary stands for its
  /// owner's unit; `UnitView.members`).
  fn members(&self, idx: &UnitIndex, n: &Name) -> Vec<Name> {
    let o = self.aux_owner(n).unwrap_or_else(|| n.clone());
    let mut out = self.roots(&o);
    if let Some(aux) = idx.get(&self.key(&o)) {
      out.extend(aux.iter().cloned());
    }
    out.retain(|m| self.contains(m));
    out
  }
}

/// The facts of a `Named` entry's metadata the compiled unit view reads.
#[derive(Clone, Debug)]
enum MetaFacts {
  Indc { all: Vec<Address>, ctors: Vec<Address> },
  Ctor { induct: Address },
  Defn { all: Vec<Address> },
  Other,
}

impl MetaFacts {
  fn of(info: &ConstantMetaInfo) -> Self {
    match info {
      ConstantMetaInfo::Indc { all, ctors, .. } => {
        MetaFacts::Indc { all: all.clone(), ctors: ctors.clone() }
      },
      ConstantMetaInfo::Ctor { induct, .. } => {
        MetaFacts::Ctor { induct: induct.clone() }
      },
      ConstantMetaInfo::Def { all, .. } => MetaFacts::Defn { all: all.clone() },
      _ => MetaFacts::Other,
    }
  }
}

/// The units of a compiled environment, read from its `Named` metadata
/// (`Ix.Cli.PackCmd.ixonUnitView`): an inductive's `all` and the members'
/// `ctors`, a constructor's inductive, a definition's `all` (`Lean.unitRoots`
/// over the Lean declarations).
pub struct IxonUnitView {
  /// Every `Named` entry: name ↦ its address and metadata facts.
  entries: FxHashMap<Name, (Address, MetaFacts)>,
  /// The name table (`Env.names`): name address ↦ name.
  names: FxHashMap<Address, Name>,
}

impl IxonUnitView {
  /// An empty view over the name table `names`.
  pub fn new(names: FxHashMap<Address, Name>) -> Self {
    IxonUnitView { entries: FxHashMap::default(), names }
  }

  /// Add one `Named` entry.
  pub fn insert(&mut self, name: Name, named: &Named) {
    let facts = MetaFacts::of(&named.meta().info);
    self.entries.insert(name, (named.addr.clone(), facts));
  }

  /// The view of an in-memory environment.
  pub fn of_env(env: &Env) -> Self {
    let names: FxHashMap<Address, Name> =
      env.names.iter().map(|e| (e.key().clone(), e.value().clone())).collect();
    let mut v = IxonUnitView::new(names);
    for e in env.named.iter() {
      v.insert(e.key().clone(), e.value());
    }
    v
  }

  /// The view of a lazily-loaded environment: one streamed pass over its §5
  /// entries ([`crate::serialize::NamedMetaCursor`]); `names` is the §4
  /// lookup of [`Env::parse_lazy_index_with_names`].
  pub fn of_lazy(
    index: &crate::env::LazyIndex,
    data: &[u8],
    names: &FxHashMap<Address, Name>,
  ) -> Result<Self, String> {
    let mut v = IxonUnitView::new(names.clone());
    let mut cursor = crate::serialize::NamedMetaCursor::open(data, index)?;
    let mut i = 0usize;
    while let Some((_, named)) = cursor.next_entry()? {
      let name = index.named[i].name.clone();
      i += 1;
      v.insert(name, &named);
    }
    Ok(v)
  }

  /// The address of `n`'s constant.
  pub fn addr_of(&self, n: &Name) -> Option<&Address> {
    self.entries.get(n).map(|(a, _)| a)
  }

  /// Every `(name, address)` entry.
  pub fn entries(&self) -> impl Iterator<Item = (&Name, &Address)> {
    self.entries.iter().map(|(n, (a, _))| (n, a))
  }

  fn name_of(&self, a: &Address) -> Option<Name> {
    self.names.get(a).cloned()
  }

  fn info(&self, n: &Name) -> &MetaFacts {
    match self.entries.get(n) {
      Some((_, f)) => f,
      None => &MetaFacts::Other,
    }
  }

  fn of_induct(&self, all: &[Address]) -> Vec<Name> {
    let ms: Vec<Name> = all.iter().filter_map(|a| self.name_of(a)).collect();
    let mut out = ms.clone();
    for m in &ms {
      if let MetaFacts::Indc { ctors, .. } = self.info(m) {
        out.extend(ctors.iter().filter_map(|a| self.name_of(a)));
      }
    }
    out
  }
}

fn or_self(o: &Name, l: Vec<Name>) -> Vec<Name> {
  if l.is_empty() { vec![o.clone()] } else { l }
}

impl UnitView for IxonUnitView {
  fn kind(&self, n: &Name) -> Option<UnitOwnerKind> {
    match self.info(n) {
      MetaFacts::Indc { .. } => Some(UnitOwnerKind::Induct),
      MetaFacts::Ctor { .. } => Some(UnitOwnerKind::Ctor),
      MetaFacts::Defn { .. } => Some(UnitOwnerKind::Defn),
      MetaFacts::Other => None,
    }
  }

  fn roots(&self, o: &Name) -> Vec<Name> {
    match self.info(o) {
      MetaFacts::Indc { all, .. } => or_self(o, self.of_induct(all)),
      MetaFacts::Ctor { induct } => {
        match self.name_of(induct).map(|i| self.info(&i).clone()) {
          Some(MetaFacts::Indc { all, .. }) => or_self(o, self.of_induct(&all)),
          _ => vec![o.clone()],
        }
      },
      MetaFacts::Defn { all } => {
        or_self(o, all.iter().filter_map(|a| self.name_of(a)).collect())
      },
      MetaFacts::Other => vec![o.clone()],
    }
  }

  fn contains(&self, n: &Name) -> bool {
    self.entries.contains_key(n)
  }

  fn names(&self) -> Vec<Name> {
    self.entries.keys().cloned().collect()
  }
}

/// The members of the units of the carried names that the bundle does not
/// carry (neither as a constant nor as a reached cut point)
/// (`Ix.Cli.PackCmd.missingUnitMembers`). A name is carried when the bundle
/// carries its constant. Sorted by name for a deterministic walk.
pub fn missing_unit_members(
  view: &IxonUnitView,
  idx: &UnitIndex,
  bundle: &Env,
) -> Vec<(Name, Address)> {
  let held = |a: &Address| {
    bundle.consts.contains_key(a) || bundle.assumptions.contains(a)
  };
  let mut out: Vec<(Name, Address)> = Vec::new();
  let mut seen: rustc_hash::FxHashSet<Name> = rustc_hash::FxHashSet::default();
  for (n, a) in view.entries() {
    if !bundle.consts.contains_key(a) {
      continue;
    }
    for m in view.members(idx, n) {
      if !seen.insert(m.clone()) {
        continue;
      }
      if let Some(ma) = view.addr_of(&m)
        && !held(ma)
      {
        out.push((m, ma.clone()));
      }
    }
  }
  out.sort_by(|x, y| x.0.cmp(&y.0));
  out
}

/// The whole-unit completion of a pack (`Ix.Cli.PackCmd.packWholeUnits`):
/// the rounds in which members were missing and the members added.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct UnitStats {
  pub rounds: usize,
  pub members: usize,
}

#[cfg(test)]
mod tests {
  use super::*;

  fn n(s: &str) -> Name {
    let mut out = Name::anon();
    for c in s.split('.') {
      out = match c.parse::<u64>() {
        Ok(i) => Name::num(out, i.into()),
        Err(_) => Name::str(out, c.to_string()),
      };
    }
    out
  }

  /// A view given by a kind table and roots table (as `leanUnitView` reads
  /// them off a Lean environment).
  struct TableView {
    kinds: FxHashMap<Name, UnitOwnerKind>,
    roots: FxHashMap<Name, Vec<Name>>,
    names: Vec<Name>,
  }

  impl UnitView for TableView {
    fn kind(&self, x: &Name) -> Option<UnitOwnerKind> {
      self.kinds.get(x).copied()
    }
    fn roots(&self, o: &Name) -> Vec<Name> {
      self.roots.get(o).cloned().unwrap_or_else(|| vec![o.clone()])
    }
    fn contains(&self, x: &Name) -> bool {
      self.names.contains(x)
    }
    fn names(&self) -> Vec<Name> {
      self.names.clone()
    }
  }

  fn table() -> TableView {
    let mut kinds = FxHashMap::default();
    let mut roots = FxHashMap::default();
    for (x, k) in [
      ("T", UnitOwnerKind::Induct),
      ("T.mk", UnitOwnerKind::Ctor),
      ("f", UnitOwnerKind::Defn),
      ("g", UnitOwnerKind::Defn),
      ("f.match_1", UnitOwnerKind::Defn),
    ] {
      kinds.insert(n(x), k);
    }
    roots.insert(n("T"), vec![n("T"), n("T.mk")]);
    roots.insert(n("T.mk"), vec![n("T"), n("T.mk")]);
    roots.insert(n("f"), vec![n("f"), n("g")]);
    roots.insert(n("g"), vec![n("f"), n("g")]);
    let names = [
      "T",
      "T.mk",
      "T.rec",
      "T.brecOn.go",
      "T.noConfusionType._ix",
      "T.mk.injEq",
      "T._sizeOf_1",
      "T._sizeOf_inst",
      "f",
      "g",
      "f.eq_1",
      "f.match_1",
      "f.match_1.splitter",
      "g._ix._mutual",
      "f._ix",
      "f._ix_retyped._f",
      "f._ix.fg",
      "_private.M.0.f.eq_def",
      "h",
      "T.user",
    ]
    .iter()
    .map(|x| n(x))
    .collect();
    TableView { kinds, roots, names }
  }

  #[test]
  fn components_by_kind() {
    assert!(unit_aux_component(UnitOwnerKind::Induct, "rec_12"));
    assert!(!unit_aux_component(UnitOwnerKind::Induct, "rec_"));
    assert!(!unit_aux_component(UnitOwnerKind::Induct, "rec_1a"));
    assert!(unit_aux_component(UnitOwnerKind::Ctor, "injEq"));
    assert!(!unit_aux_component(UnitOwnerKind::Ctor, "rec"));
    assert!(unit_aux_component(UnitOwnerKind::Defn, "match_3"));
    assert!(unit_aux_component(UnitOwnerKind::Defn, "_proof_2"));
    assert!(!unit_aux_component(UnitOwnerKind::Defn, "brecOn"));
    assert!(unit_reserved_component("_ix"));
    assert!(unit_reserved_component("_ix_retyped"));
    assert!(!unit_reserved_component("_ixx"));
    assert!(!unit_reserved_component("ix"));
  }

  #[test]
  fn private_names() {
    assert_eq!(
      private_to_user_name(&n("_private.M.N.0.f.eq_1")),
      Some(n("f.eq_1"))
    );
    assert_eq!(private_to_user_name(&n("f.eq_1")), None);
  }

  #[test]
  fn owners_and_units() {
    let v = table();
    // Lean auxiliaries, by kind
    assert_eq!(v.aux_owner(&n("T.rec")), Some(n("T")));
    assert_eq!(v.aux_owner(&n("T.brecOn.go")), Some(n("T")));
    assert_eq!(v.aux_owner(&n("T.mk.injEq")), Some(n("T.mk")));
    assert_eq!(v.aux_owner(&n("T._sizeOf_inst")), Some(n("T")));
    assert_eq!(v.aux_owner(&n("f.eq_1")), Some(n("f")));
    // the shortest owner: `f.match_1.splitter` hangs under `f` (`match_1`)
    assert_eq!(v.aux_owner(&n("f.match_1.splitter")), Some(n("f")));
    // Pass 3's reserved names, under any kind
    assert_eq!(v.aux_owner(&n("T.noConfusionType._ix")), Some(n("T")));
    assert_eq!(v.aux_owner(&n("g._ix._mutual")), Some(n("g")));
    assert_eq!(v.aux_owner(&n("f._ix")), Some(n("f")));
    assert_eq!(v.aux_owner(&n("f._ix_retyped._f")), Some(n("f")));
    assert_eq!(v.aux_owner(&n("f._ix.fg")), Some(n("f")));
    // private, through the user name
    assert_eq!(v.aux_owner(&n("_private.M.0.f.eq_def")), Some(n("f")));
    // not an auxiliary: a declaration itself, an unknown component, no owner
    assert_eq!(v.aux_owner(&n("T")), None);
    assert_eq!(v.aux_owner(&n("T.user")), None);
    assert_eq!(v.aux_owner(&n("h")), None);
    let idx = v.index();
    let mut unit_f = v.members(&idx, &n("g._ix._mutual"));
    unit_f.sort();
    let mut want: Vec<Name> = [
      "f",
      "g",
      "f.eq_1",
      "f.match_1",
      "f.match_1.splitter",
      "g._ix._mutual",
      "f._ix",
      "f._ix_retyped._f",
      "f._ix.fg",
      "_private.M.0.f.eq_def",
    ]
    .iter()
    .map(|x| n(x))
    .collect();
    want.sort();
    assert_eq!(unit_f, want);
    let mut unit_t = v.members(&idx, &n("T.mk"));
    unit_t.sort();
    let mut want_t: Vec<Name> = [
      "T",
      "T.mk",
      "T.rec",
      "T.brecOn.go",
      "T.noConfusionType._ix",
      "T.mk.injEq",
      "T._sizeOf_1",
      "T._sizeOf_inst",
    ]
    .iter()
    .map(|x| n(x))
    .collect();
    want_t.sort();
    assert_eq!(unit_t, want_t);
    // a name with no owner is its own unit
    assert_eq!(v.members(&idx, &n("h")), vec![n("h")]);
  }
}
