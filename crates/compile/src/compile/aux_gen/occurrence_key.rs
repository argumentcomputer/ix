//! Structural occurrence lookup. Cached hashes select candidates only.
//! Source keys retain names, binder annotations, raw levels, and metadata;
//! canonical expansion applies `addr_key` before reaching this table.

use blake3::Hash;
use ix_common::env::{
  DataValue, Expr, ExprData, Level, LevelData, Name, NameData, Syntax,
  SyntaxPreresolved,
};
use rustc_hash::FxHashMap;
use std::sync::Arc;

fn name_eq(a: &Name, b: &Name) -> bool {
  match (a.as_data(), b.as_data()) {
    (NameData::Anonymous(_), NameData::Anonymous(_)) => true,
    (NameData::Str(ap, av, _), NameData::Str(bp, bv, _)) => {
      av == bv && name_eq(ap, bp)
    },
    (NameData::Num(ap, av, _), NameData::Num(bp, bv, _)) => {
      av == bv && name_eq(ap, bp)
    },
    _ => false,
  }
}

fn slices_eq<T>(a: &[T], b: &[T], eq: impl Fn(&T, &T) -> bool) -> bool {
  a.len() == b.len() && a.iter().zip(b).all(|(a, b)| eq(a, b))
}

fn preresolved_eq(a: &SyntaxPreresolved, b: &SyntaxPreresolved) -> bool {
  match (a, b) {
    (SyntaxPreresolved::Namespace(a), SyntaxPreresolved::Namespace(b)) => {
      name_eq(a, b)
    },
    (SyntaxPreresolved::Decl(a, aa), SyntaxPreresolved::Decl(b, ba)) => {
      name_eq(a, b) && aa == ba
    },
    _ => false,
  }
}

fn syntax_eq(a: &Syntax, b: &Syntax) -> bool {
  match (a, b) {
    (Syntax::Missing, Syntax::Missing) => true,
    (Syntax::Node(ai, ak, aa), Syntax::Node(bi, bk, ba)) => {
      ai == bi && name_eq(ak, bk) && slices_eq(aa, ba, syntax_eq)
    },
    (Syntax::Atom(ai, av), Syntax::Atom(bi, bv)) => ai == bi && av == bv,
    (Syntax::Ident(ai, ar, av, ap), Syntax::Ident(bi, br, bv, bp)) => {
      ai == bi
        && ar == br
        && name_eq(av, bv)
        && slices_eq(ap, bp, preresolved_eq)
    },
    _ => false,
  }
}

fn data_eq(a: &DataValue, b: &DataValue) -> bool {
  match (a, b) {
    (DataValue::OfString(a), DataValue::OfString(b)) => a == b,
    (DataValue::OfBool(a), DataValue::OfBool(b)) => a == b,
    (DataValue::OfName(a), DataValue::OfName(b)) => name_eq(a, b),
    (DataValue::OfNat(a), DataValue::OfNat(b)) => a == b,
    (DataValue::OfInt(a), DataValue::OfInt(b)) => a == b,
    (DataValue::OfSyntax(a), DataValue::OfSyntax(b)) => syntax_eq(a, b),
    _ => false,
  }
}

/// Typed reference identities; no source spelling can equal an external address.
#[derive(Clone, Debug)]
pub(super) enum OccurrenceRef {
  Named(Name),
  External(ix_common::address::Address),
}

impl PartialEq for OccurrenceRef {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Named(a), Self::Named(b)) => name_eq(a, b),
      (Self::External(a), Self::External(b)) => a == b,
      _ => false,
    }
  }
}
impl Eq for OccurrenceRef {}

/// The full source structure, or its canonical normalization. Every cached
/// digest in names, levels and metadata is excluded from structural equality.
#[derive(Clone, Debug)]
pub(super) enum OccurrenceShape {
  Bvar(bignat::Nat),
  Fvar(Name),
  Mvar(Name),
  Sort(Level),
  Const(OccurrenceRef, Vec<Level>),
  App(Arc<Self>, Arc<Self>),
  Lam(Name, Arc<Self>, Arc<Self>, ix_common::env::BinderInfo),
  ForallE(Name, Arc<Self>, Arc<Self>, ix_common::env::BinderInfo),
  LetE(Name, Arc<Self>, Arc<Self>, Arc<Self>, bool),
  NatLit(bignat::Nat),
  StrLit(String),
  Mdata(Vec<(Name, DataValue)>, Arc<Self>),
  Proj(OccurrenceRef, bignat::Nat, Arc<Self>),
}

impl OccurrenceShape {
  /// One memo per source conversion. The borrowed root keeps every input node
  /// alive until this map is dropped; keys are immutable allocation identities,
  /// never cached expression digests. No memo escapes this invocation.
  pub(super) fn source(e: &Expr) -> Arc<Self> {
    fn visit(
      e: &Expr,
      memo: &mut FxHashMap<*const ExprData, Arc<OccurrenceShape>>,
    ) -> Arc<OccurrenceShape> {
      let identity = Arc::as_ptr(&e.0);
      if let Some(key) = memo.get(&identity) {
        return Arc::clone(key);
      }
      let key = Arc::new(match e.as_data() {
        ExprData::Bvar(i, _) => OccurrenceShape::Bvar(i.clone()),
        ExprData::Fvar(n, _) => OccurrenceShape::Fvar(n.clone()),
        ExprData::Mvar(n, _) => OccurrenceShape::Mvar(n.clone()),
        ExprData::Sort(u, _) => OccurrenceShape::Sort(u.clone()),
        ExprData::Const(n, us, _) => {
          OccurrenceShape::Const(OccurrenceRef::Named(n.clone()), us.clone())
        },
        ExprData::App(f, a, _) => {
          OccurrenceShape::App(visit(f, memo), visit(a, memo))
        },
        ExprData::Lam(n, t, b, bi, _) => OccurrenceShape::Lam(
          n.clone(),
          visit(t, memo),
          visit(b, memo),
          bi.clone(),
        ),
        ExprData::ForallE(n, t, b, bi, _) => OccurrenceShape::ForallE(
          n.clone(),
          visit(t, memo),
          visit(b, memo),
          bi.clone(),
        ),
        ExprData::LetE(n, t, v, b, nd, _) => OccurrenceShape::LetE(
          n.clone(),
          visit(t, memo),
          visit(v, memo),
          visit(b, memo),
          *nd,
        ),
        ExprData::Lit(ix_common::env::Literal::NatVal(n), _) => {
          OccurrenceShape::NatLit(n.clone())
        },
        ExprData::Lit(ix_common::env::Literal::StrVal(s), _) => {
          OccurrenceShape::StrLit(s.clone())
        },
        ExprData::Mdata(md, e, _) => {
          OccurrenceShape::Mdata(md.clone(), visit(e, memo))
        },
        ExprData::Proj(n, i, e, _) => OccurrenceShape::Proj(
          OccurrenceRef::Named(n.clone()),
          i.clone(),
          visit(e, memo),
        ),
      });
      memo.insert(identity, Arc::clone(&key));
      key
    }
    visit(e, &mut FxHashMap::default())
  }
}

/// Completed structural-comparison results for this one comparison. Both
/// roots and every descendant remain alive throughout the call. Pointer
/// identity is a sufficient reflexive case; different identities still get
/// the full structural comparison, with no digest-based equality decision.
#[derive(Default)]
struct EqualityMemo {
  shapes: FxHashMap<(*const OccurrenceShape, *const OccurrenceShape), bool>,
  levels: FxHashMap<(*const LevelData, *const LevelData), bool>,
}

impl EqualityMemo {
  fn level(&mut self, a: &Level, b: &Level) -> bool {
    let identity = (Arc::as_ptr(&a.0), Arc::as_ptr(&b.0));
    if identity.0 == identity.1 {
      return true;
    }
    if let Some(equal) = self.levels.get(&identity) {
      return *equal;
    }
    let equal = match (a.as_data(), b.as_data()) {
      (LevelData::Zero(_), LevelData::Zero(_)) => true,
      (LevelData::Succ(a, _), LevelData::Succ(b, _)) => self.level(a, b),
      (LevelData::Max(a, b, _), LevelData::Max(c, d, _))
      | (LevelData::Imax(a, b, _), LevelData::Imax(c, d, _)) => {
        self.level(a, c) && self.level(b, d)
      },
      (LevelData::Param(a, _), LevelData::Param(b, _))
      | (LevelData::Mvar(a, _), LevelData::Mvar(b, _)) => name_eq(a, b),
      _ => false,
    };
    self.levels.insert(identity, equal);
    equal
  }

  fn shape(&mut self, a: &OccurrenceShape, b: &OccurrenceShape) -> bool {
    let identity = (a as *const OccurrenceShape, b as *const OccurrenceShape);
    if identity.0 == identity.1 {
      return true;
    }
    if let Some(equal) = self.shapes.get(&identity) {
      return *equal;
    }
    let equal = match (a, b) {
      (OccurrenceShape::Bvar(a), OccurrenceShape::Bvar(b))
      | (OccurrenceShape::NatLit(a), OccurrenceShape::NatLit(b)) => a == b,
      (OccurrenceShape::Fvar(a), OccurrenceShape::Fvar(b))
      | (OccurrenceShape::Mvar(a), OccurrenceShape::Mvar(b)) => name_eq(a, b),
      (OccurrenceShape::Sort(a), OccurrenceShape::Sort(b)) => self.level(a, b),
      (OccurrenceShape::Const(an, au), OccurrenceShape::Const(bn, bu)) => {
        an == bn
          && au.len() == bu.len()
          && au.iter().zip(bu).all(|(a, b)| self.level(a, b))
      },
      (OccurrenceShape::App(af, aa), OccurrenceShape::App(bf, ba)) => {
        self.shape(af, bf) && self.shape(aa, ba)
      },
      (
        OccurrenceShape::Lam(an, at, ab, ai),
        OccurrenceShape::Lam(bn, bt, bb, bi),
      )
      | (
        OccurrenceShape::ForallE(an, at, ab, ai),
        OccurrenceShape::ForallE(bn, bt, bb, bi),
      ) => {
        name_eq(an, bn) && ai == bi && self.shape(at, bt) && self.shape(ab, bb)
      },
      (
        OccurrenceShape::LetE(an, at, av, ab, ad),
        OccurrenceShape::LetE(bn, bt, bv, bb, bd),
      ) => {
        name_eq(an, bn)
          && ad == bd
          && self.shape(at, bt)
          && self.shape(av, bv)
          && self.shape(ab, bb)
      },
      (OccurrenceShape::StrLit(a), OccurrenceShape::StrLit(b)) => a == b,
      (OccurrenceShape::Mdata(am, ae), OccurrenceShape::Mdata(bm, be)) => {
        slices_eq(am, bm, |(an, av), (bn, bv)| {
          name_eq(an, bn) && data_eq(av, bv)
        }) && self.shape(ae, be)
      },
      (
        OccurrenceShape::Proj(an, ai, ae),
        OccurrenceShape::Proj(bn, bi, be),
      ) => an == bn && ai == bi && self.shape(ae, be),
      _ => false,
    };
    self.shapes.insert(identity, equal);
    equal
  }
}

impl PartialEq for OccurrenceShape {
  fn eq(&self, other: &Self) -> bool {
    EqualityMemo::default().shape(self, other)
  }
}
impl Eq for OccurrenceShape {}

/// The hint has no equality role. In particular, two spellings normalized
/// to one key may have unrelated hints; structural fallback finds the first.
#[derive(Clone)]
pub(super) struct OccurrenceInput {
  pub(super) key: Arc<OccurrenceShape>,
  pub(super) bucket: Hash,
}
impl OccurrenceInput {
  pub(super) fn source(e: &Expr) -> Self {
    Self { key: OccurrenceShape::source(e), bucket: *e.get_hash() }
  }
}

/// Entries define first discovery. A bucket is only a cached candidate;
/// both a mismatching candidate and a missing bucket use structural lookup.
#[derive(Default)]
pub(super) struct OccurrenceTable {
  entries: Vec<(Arc<OccurrenceShape>, Name)>,
  cache: FxHashMap<Hash, usize>,
}
impl OccurrenceTable {
  pub(super) fn get(&self, input: &OccurrenceInput) -> Option<&Name> {
    if let Some(&index) = self.cache.get(&input.bucket)
      && let Some((stored, value)) = self.entries.get(index)
      && stored == &input.key
    {
      return Some(value);
    }
    self
      .entries
      .iter()
      .find_map(|(stored, value)| (stored == &input.key).then_some(value))
  }
  pub(super) fn insert(&mut self, input: OccurrenceInput, value: Name) {
    if self.get(&input).is_none() {
      self.cache.insert(input.bucket, self.entries.len());
      self.entries.push((input.key, value));
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::Arc;

  #[test]
  fn collisions_are_confirmed_and_rehashed_structure_still_hits() {
    let digest = blake3::hash(b"one deliberately shared cache bucket");
    let first = OccurrenceInput::source(&Expr(Arc::new(ExprData::Bvar(
      0u64.into(),
      digest,
    ))));
    let other = OccurrenceInput::source(&Expr(Arc::new(ExprData::Bvar(
      1u64.into(),
      digest,
    ))));
    let rehashed = OccurrenceInput::source(&Expr::bvar(0u64.into()));
    let a = Name::str(Name::anon(), "A".into());
    let b = Name::str(Name::anon(), "B".into());
    let mut table = OccurrenceTable::default();
    table.insert(first.clone(), a.clone());
    assert!(table.get(&other).is_none());
    table.insert(other.clone(), b.clone());
    assert_eq!(table.get(&first), Some(&a));
    assert_eq!(table.get(&other), Some(&b));
    assert_eq!(table.get(&rehashed), Some(&a));
    table.insert(rehashed, b);
    assert_eq!(table.get(&first), Some(&a));
    assert_eq!(table.entries.len(), 2);
  }

  #[test]
  fn reference_categories_stay_disjoint_with_shared_hashes() {
    let address = ix_common::address::Address::hash(b"address name collision");
    let name = Name::str(Name::anon(), format!("#{}", address.hex()));
    let a = Name::str(Name::anon(), "A".into());
    let b = Name::str(Name::anon(), "B".into());
    let bucket = blake3::hash(b"same advisory bucket");
    let ref_name = OccurrenceRef::Named(name);
    let ref_addr = OccurrenceRef::External(address);
    assert_ne!(ref_name, ref_addr);
    for (source, external) in [
      (
        OccurrenceShape::Const(ref_name.clone(), vec![]),
        OccurrenceShape::Const(ref_addr.clone(), vec![]),
      ),
      (
        OccurrenceShape::Proj(
          ref_name,
          0u64.into(),
          Arc::new(OccurrenceShape::Bvar(0u64.into())),
        ),
        OccurrenceShape::Proj(
          ref_addr,
          0u64.into(),
          Arc::new(OccurrenceShape::Bvar(0u64.into())),
        ),
      ),
    ] {
      let source = OccurrenceInput { key: Arc::new(source), bucket };
      let external = OccurrenceInput { key: Arc::new(external), bucket };
      let mut table = OccurrenceTable::default();
      table.insert(source.clone(), a.clone());
      table.insert(external.clone(), b.clone());
      assert_eq!(table.entries.len(), 2);
      assert_eq!(table.get(&source), Some(&a));
      assert_eq!(table.get(&external), Some(&b));
      let changed_bucket = OccurrenceInput {
        key: source.key,
        bucket: blake3::hash(b"another bucket"),
      };
      assert_eq!(table.get(&changed_bucket), Some(&a));
    }
  }

  fn shared_expr(depth: usize, leaf: u64, digest: Hash) -> Expr {
    let mut expr = Expr(Arc::new(ExprData::Bvar(leaf.into(), digest)));
    for _ in 0..depth {
      expr = Expr(Arc::new(ExprData::App(expr.clone(), expr, digest)));
    }
    expr
  }

  #[test]
  fn source_key_preserves_sharing_without_using_cached_hashes() {
    let depth = 18;
    let digest = blake3::hash(b"every input node has the same advisory hash");
    let expr = shared_expr(depth, 0, digest);
    let mut key = OccurrenceShape::source(&expr);
    for _ in 0..depth {
      let OccurrenceShape::App(left, right) = key.as_ref() else {
        panic!("shared application spine was changed");
      };
      assert!(Arc::ptr_eq(left, right));
      key = Arc::clone(left);
    }
    assert!(
      matches!(key.as_ref(), OccurrenceShape::Bvar(n) if *n == 0u64.into())
    );
    let leaf_neighbour = shared_expr(depth, 1, digest);
    assert!(
      OccurrenceShape::source(&expr)
        != OccurrenceShape::source(&leaf_neighbour)
    );
  }

  #[test]
  fn separate_equal_dags_use_completed_pair_memo_and_first_discovery() {
    let depth = 18;
    let left =
      OccurrenceInput::source(&shared_expr(depth, 0, blake3::hash(b"left")));
    let right =
      OccurrenceInput::source(&shared_expr(depth, 0, blake3::hash(b"right")));
    assert!(!Arc::ptr_eq(&left.key, &right.key));
    let mut memo = EqualityMemo::default();
    assert!(memo.shape(&left.key, &right.key));
    assert_eq!(memo.shapes.len(), depth + 1);

    let original = Name::str(Name::anon(), "Original".into());
    let replacement = Name::str(Name::anon(), "Replacement".into());
    let mut table = OccurrenceTable::default();
    table.insert(left, original.clone());
    assert_eq!(table.get(&right), Some(&original));
    table.insert(right, replacement);
    assert_eq!(table.entries.len(), 1);
  }

  fn unshared_expr(depth: usize, digest: Hash) -> Expr {
    if depth == 0 {
      Expr(Arc::new(ExprData::Bvar(0u64.into(), digest)))
    } else {
      Expr(Arc::new(ExprData::App(
        unshared_expr(depth - 1, digest),
        unshared_expr(depth - 1, digest),
        digest,
      )))
    }
  }

  #[test]
  fn sharing_topology_is_not_part_of_key_equality() {
    let depth = 8;
    let shared =
      OccurrenceShape::source(&shared_expr(depth, 0, blake3::hash(b"DAG")));
    let tree =
      OccurrenceShape::source(&unshared_expr(depth, blake3::hash(b"tree")));
    let mut memo = EqualityMemo::default();
    assert!(memo.shape(&shared, &tree));
    assert_eq!(memo.shapes.len(), (1usize << (depth + 1)) - 1);
  }

  #[test]
  fn source_memo_does_not_survive_its_borrowed_input_call() {
    let digest = blake3::hash(b"unchanged advisory digest");
    let mut expr = Expr(Arc::new(ExprData::Bvar(0u64.into(), digest)));
    let identity = Arc::as_ptr(&expr.0);
    let first = OccurrenceShape::source(&expr);
    assert!(first == OccurrenceShape::source(&expr));

    // Safe unique ownership permits mutation between calls, never during
    // the immutable borrow used by source(). Reusing a global pointer memo
    // here would incorrectly return the previous structural key.
    *Arc::get_mut(&mut expr.0)
      .expect("the source helper retained an input owner") =
      ExprData::Bvar(1u64.into(), digest);
    assert_eq!(identity, Arc::as_ptr(&expr.0));
    assert!(first != OccurrenceShape::source(&expr));
  }

  fn shared_level(depth: usize, name: &str, digest: Hash) -> Level {
    let mut level = Level(Arc::new(LevelData::Param(
      Name::str(Name::anon(), name.into()),
      digest,
    )));
    for _ in 0..depth {
      level = Level(Arc::new(LevelData::Max(level.clone(), level, digest)));
    }
    level
  }

  #[test]
  fn separate_level_dags_compare_structurally_with_a_changed_leaf_neighbour() {
    let depth = 18;
    let left = shared_level(depth, "u", blake3::hash(b"left levels"));
    let right = shared_level(depth, "u", blake3::hash(b"right levels"));
    let mut memo = EqualityMemo::default();
    assert!(memo.level(&left, &right));
    assert_eq!(memo.levels.len(), depth + 1);

    let changed = shared_level(depth, "v", blake3::hash(b"left levels"));
    let mut negative = EqualityMemo::default();
    assert!(!negative.level(&left, &changed));
    assert_eq!(negative.levels.len(), depth + 1);
  }

  #[test]
  fn nested_name_level_and_metadata_digests_are_not_equality() {
    let digest = blake3::hash(b"same hash");
    let name = Name::str(Name::anon(), "u".into());
    let rehashed_name =
      Name(Arc::new(NameData::Str(Name::anon(), "u".into(), digest)));
    let level = Level::param(name.clone());
    let rehashed_level =
      Level(Arc::new(LevelData::Param(rehashed_name.clone(), digest)));
    let a = Expr::cnst(name.clone(), vec![level]);
    let b = Expr::cnst(rehashed_name.clone(), vec![rehashed_level]);
    assert_eq!(OccurrenceShape::source(&a), OccurrenceShape::source(&b));
    let a = Expr(Arc::new(ExprData::Mdata(
      vec![(name.clone(), DataValue::OfName(name))],
      a,
      digest,
    )));
    let b = Expr(Arc::new(ExprData::Mdata(
      vec![(rehashed_name.clone(), DataValue::OfName(rehashed_name))],
      b,
      digest,
    )));
    assert_eq!(OccurrenceShape::source(&a), OccurrenceShape::source(&b));
    let changed =
      Expr(Arc::new(ExprData::Mdata(vec![], Expr::bvar(0u64.into()), digest)));
    assert_ne!(OccurrenceShape::source(&a), OccurrenceShape::source(&changed));
  }
}
/// Generated-name lookup with exactly the structural name equality used
/// by Lean. Derived `Name::eq` also compares cached fields and is not this
/// relation, even for a constructor-built name above a rehashed prefix.
#[derive(Clone)]
pub struct NameTable<T> {
  entries: Vec<(Name, T)>,
  cache: FxHashMap<Hash, usize>,
}

impl<T> Default for NameTable<T> {
  fn default() -> Self {
    Self { entries: Vec::new(), cache: FxHashMap::default() }
  }
}

impl<T> NameTable<T> {
  pub fn with_capacity(capacity: usize) -> Self {
    Self { entries: Vec::with_capacity(capacity), cache: FxHashMap::default() }
  }

  pub fn get(&self, name: &Name) -> Option<&T> {
    if let Some(&index) = self.cache.get(name.get_hash())
      && let Some((stored, value)) = self.entries.get(index)
      && name_eq(stored, name)
    {
      return Some(value);
    }
    self
      .entries
      .iter()
      .rev()
      .find_map(|(stored, value)| name_eq(stored, name).then_some(value))
  }

  pub fn contains(&self, name: &Name) -> bool {
    self.get(name).is_some()
  }

  pub fn contains_key(&self, name: &Name) -> bool {
    self.contains(name)
  }

  pub fn insert(&mut self, name: Name, value: T) {
    if self.get(&name).is_some() {
      self.entries.retain(|(stored, _)| !name_eq(stored, &name));
      self.cache.clear();
    }
    self.cache.insert(*name.get_hash(), self.entries.len());
    self.entries.push((name, value));
  }

  pub fn is_empty(&self) -> bool {
    self.entries.is_empty()
  }
  pub fn len(&self) -> usize {
    self.entries.len()
  }
  pub fn iter(&self) -> std::iter::Rev<std::slice::Iter<'_, (Name, T)>> {
    self.entries.iter().rev()
  }
}

impl<'a, T> IntoIterator for &'a NameTable<T> {
  type Item = &'a (Name, T);
  type IntoIter = std::iter::Rev<std::slice::Iter<'a, (Name, T)>>;
  fn into_iter(self) -> Self::IntoIter {
    self.iter()
  }
}

impl<T> FromIterator<(Name, T)> for NameTable<T> {
  fn from_iter<I: IntoIterator<Item = (Name, T)>>(iter: I) -> Self {
    let mut table = Self::default();
    for (name, value) in iter {
      table.insert(name, value);
    }
    table
  }
}

#[cfg(test)]
mod name_table_tests {
  use super::*;
  use std::sync::Arc;

  fn auxiliary_name(root: Name) -> Name {
    Name::str(Name::str(root, "_nested".into()), "List_1".into())
  }

  #[test]
  fn generated_names_ignore_prefix_digests_but_keep_all_components() {
    let root = Name::str(Name::anon(), "Root".into());
    let rehashed = Name(Arc::new(NameData::Str(
      Name::anon(),
      "Root".into(),
      blake3::hash(b"different cached prefix"),
    )));
    let a = auxiliary_name(root.clone());
    let b = auxiliary_name(rehashed);
    assert_ne!(a, b); // documents why derived Name equality is insufficient
    assert!(name_eq(&a, &b));
    let neighbour = auxiliary_name(root);
    assert_eq!(a, neighbour); // ordinary canonical generation agrees too
    let mut table = NameTable::default();
    table.insert(a.clone(), 1);
    assert_eq!(table.get(&b), Some(&1));
    let ctor = Name::str(a.clone(), "mk".into());
    let fresh = Name::str(Name::anon(), "Fresh".into());
    assert_eq!(
      fresh.append_components(&ctor.strip_prefix(&b).unwrap()),
      Name::str(fresh.clone(), "mk".into())
    );
    table.insert(b, 2);
    assert_eq!(table.get(&a), Some(&2));
    assert_eq!(table.len(), 1);
    let collision = Name(Arc::new(NameData::Str(
      Name::anon(),
      "Different".into(),
      *a.get_hash(),
    )));
    assert_eq!(table.get(&collision), None);
    table.insert(collision.clone(), 3);
    assert_eq!(table.get(&a), Some(&2));
    assert_eq!(table.get(&collision), Some(&3));
    assert_eq!(table.len(), 2);
  }
}
