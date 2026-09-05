//! DAG-aware source-name restoration after a real WHNF reduction.
//!
//! One pass owns all memoization and a fixed view of referenced addresses.
//! Collection remains preorder/left-to-right/first-wins; restoration starts
//! only after the hint table is complete. Eligibility is still App/Proj with
//! NO Bvar node anywhere, including under binders (canonicity §10.5).

use super::*;
use ix_common::env::Literal;
use ix_kernel::env::InternTable;
use ix_kernel::level::KUniv;
use ix_kernel::mode::Anon;
use std::collections::HashMap;
use std::hash::BuildHasher;
use std::sync::Arc;

fn ptr(expr: &LeanExpr) -> usize {
  std::ptr::from_ref(expr.as_data()).addr()
}

fn same_node(a: &LeanExpr, b: &LeanExpr) -> bool {
  Arc::ptr_eq(&a.0, &b.0)
}

/// Capture each referenced name once, preserving primary/aux/fallback
/// precedence. No live DashMap reads occur during collection or restoration.
/// This is a pass-local resolution view, not an atomic snapshot of all global
/// compiler state; later passes capture a fresh view after further publication.
fn capture_addresses(
  source: &LeanExpr,
  generated: &LeanExpr,
  stt: &crate::compile::CompileState,
) -> FxHashMap<Name, Address> {
  let mut addresses = FxHashMap::default();
  let mut seen = FxHashSet::default();
  let mut stack = vec![generated, source];
  while let Some(expr) = stack.pop() {
    if !seen.insert(ptr(expr)) {
      continue;
    }
    match expr.as_data() {
      ExprData::Const(name, _, _) | ExprData::Proj(name, _, _, _) => {
        addresses.entry(name.clone()).or_insert_with(|| {
          resolve_lean_name_addr(
            name,
            Some(&stt.name_to_addr),
            Some(&stt.aux_name_to_addr),
          )
        });
      },
      _ => {},
    }
    match expr.as_data() {
      ExprData::App(f, a, _) => stack.extend([a, f]),
      ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
        stack.extend([b, d]);
      },
      ExprData::LetE(_, t, v, b, _, _) => stack.extend([b, v, t]),
      ExprData::Proj(_, _, v, _) | ExprData::Mdata(_, v, _) => stack.push(v),
      _ => {},
    }
  }
  addresses
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ContentId(usize);

/// Exact name-erased structure of to_kexpr_static's result. Children and
/// normalized universes have exact interned identities; hashing only chooses
/// a bucket, and Eq confirms the entire shallow key. No lossy digest is used
/// as evidence of equality. Literal VALUES are included, not just blob hashes.
/// These ids never enter a kernel cache or serialized output.
#[derive(Debug, PartialEq, Eq, Hash)]
enum ContentKey {
  Var(u64),
  Sort(u64),
  Const(Address, Box<[u64]>),
  App(ContentId, ContentId),
  Lam(ContentId, ContentId),
  All(ContentId, ContentId),
  Let(ContentId, ContentId, ContentId, bool),
  Prj(Address, u64, ContentId),
  Nat(Nat),
  Str(String),
}

struct ContentTable<'a, S = rustc_hash::FxBuildHasher> {
  addresses: &'a FxHashMap<Name, Address>,
  fvars: &'a FxHashMap<Name, usize>,
  params: &'a [Name],
  shapes: HashMap<ContentKey, ContentId, S>,
  converted: FxHashMap<(usize, usize), ContentId>,
  levels: FxHashMap<usize, KUniv<Anon>>,
  univs: InternTable<Anon>,
}

impl<'a, S: BuildHasher + Default> ContentTable<'a, S> {
  fn new(
    addresses: &'a FxHashMap<Name, Address>,
    fvars: &'a FxHashMap<Name, usize>,
    params: &'a [Name],
  ) -> Self {
    Self {
      addresses,
      fvars,
      params,
      shapes: HashMap::default(),
      converted: FxHashMap::default(),
      levels: FxHashMap::default(),
      univs: InternTable::new(),
    }
  }

  fn intern(&mut self, key: ContentKey) -> ContentId {
    let next = ContentId(self.shapes.len());
    *self.shapes.entry(key).or_insert(next)
  }

  /// Use the SAME mk_max/mk_imax reductions as lean_level_to_kuniv, then
  /// intern normalized levels structurally. Parameter display names are
  /// irrelevant to hint equality. These private universe nodes never egress.
  fn level(&mut self, level: &Level) -> KUniv<Anon> {
    let ptr = std::ptr::from_ref(level.as_data()).addr();
    if let Some(result) = self.levels.get(&ptr) {
      return result.clone();
    }
    let result = match level.as_data() {
      LevelData::Zero(_) => KUniv::zero(),
      LevelData::Succ(a, _) => KUniv::succ(self.level(a)),
      LevelData::Max(a, b, _) => {
        let a = self.level(a);
        let b = self.level(b);
        KUniv::max(a, b)
      },
      LevelData::Imax(a, b, _) => {
        let a = self.level(a);
        let b = self.level(b);
        KUniv::imax(a, b)
      },
      LevelData::Param(name, _) => {
        let idx =
          self.params.iter().position(|n| n == name).unwrap_or_else(|| {
            panic!(
              "unknown level param `{}` in source-name hints",
              name.pretty()
            )
          });
        KUniv::param(idx as u64, ())
      },
      LevelData::Mvar(name, _) => {
        panic!(
          "unexpected level metavariable `{}` in source-name hints",
          name.pretty()
        );
      },
    };
    let result = self.univs.intern_univ(result);
    self.levels.insert(ptr, result.clone());
    result
  }

  fn content(&mut self, expr: &LeanExpr, depth: usize) -> ContentId {
    let memo_key = (ptr(expr), depth);
    if let Some(id) = self.converted.get(&memo_key) {
      return *id;
    }
    let key = match expr.as_data() {
      ExprData::Bvar(idx, _) => ContentKey::Var(nat_to_u64(idx)),
      ExprData::Fvar(name, _) => match self.fvars.get(name) {
        Some(level) => ContentKey::Var((depth - level - 1) as u64),
        None => {
          let zero = self.univs.intern_univ(KUniv::zero());
          ContentKey::Sort(*zero.addr())
        },
      },
      ExprData::Mvar(..) => {
        let zero = self.univs.intern_univ(KUniv::zero());
        ContentKey::Sort(*zero.addr())
      },
      ExprData::Sort(level, _) => ContentKey::Sort(*self.level(level).addr()),
      ExprData::Const(name, levels, _) => {
        let address = self.addresses[name].clone();
        let levels = levels.iter().map(|u| *self.level(u).addr()).collect();
        ContentKey::Const(address, levels)
      },
      ExprData::App(f, a, _) => {
        ContentKey::App(self.content(f, depth), self.content(a, depth))
      },
      ExprData::Lam(_, ty, body, _, _) => {
        ContentKey::Lam(self.content(ty, depth), self.content(body, depth + 1))
      },
      ExprData::ForallE(_, ty, body, _, _) => {
        ContentKey::All(self.content(ty, depth), self.content(body, depth + 1))
      },
      ExprData::LetE(_, ty, val, body, nd, _) => ContentKey::Let(
        self.content(ty, depth),
        self.content(val, depth),
        self.content(body, depth + 1),
        *nd,
      ),
      ExprData::Proj(name, field, val, _) => ContentKey::Prj(
        self.addresses[name].clone(),
        nat_to_u64(field),
        self.content(val, depth),
      ),
      ExprData::Lit(Literal::NatVal(n), _) => ContentKey::Nat(n.clone()),
      ExprData::Lit(Literal::StrVal(s), _) => ContentKey::Str(s.clone()),
      ExprData::Mdata(_, inner, _) => {
        let id = self.content(inner, depth);
        self.converted.insert(memo_key, id);
        return id;
      },
    };
    let id = self.intern(key);
    self.converted.insert(memo_key, id);
    id
  }
}

struct Pass<'a> {
  content: ContentTable<'a>,
  depth: usize,
  has_bvar: FxHashMap<usize, bool>,
  collected: FxHashSet<usize>,
  restored: FxHashMap<usize, LeanExpr>,
}

impl<'a> Pass<'a> {
  fn new(
    addresses: &'a FxHashMap<Name, Address>,
    fvars: &'a FxHashMap<Name, usize>,
    depth: usize,
    params: &'a [Name],
  ) -> Self {
    Self {
      content: ContentTable::new(addresses, fvars, params),
      depth,
      has_bvar: FxHashMap::default(),
      collected: FxHashSet::default(),
      restored: FxHashMap::default(),
    }
  }

  /// This is "contains ANY Bvar", not a loose/free-variable range test.
  fn has_bvar(&mut self, expr: &LeanExpr) -> bool {
    let key = ptr(expr);
    if let Some(result) = self.has_bvar.get(&key) {
      return *result;
    }
    let result = match expr.as_data() {
      ExprData::Bvar(..) => true,
      ExprData::App(f, a, _) => self.has_bvar(f) || self.has_bvar(a),
      ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
        self.has_bvar(d) || self.has_bvar(b)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        self.has_bvar(t) || self.has_bvar(v) || self.has_bvar(b)
      },
      ExprData::Proj(_, _, v, _) | ExprData::Mdata(_, v, _) => self.has_bvar(v),
      _ => false,
    };
    self.has_bvar.insert(key, result);
    result
  }

  fn candidate(&mut self, expr: &LeanExpr) -> bool {
    matches!(expr.as_data(), ExprData::App(..) | ExprData::Proj(..))
      && !self.has_bvar(expr)
  }

  fn collect(
    &mut self,
    source: &LeanExpr,
    hints: &mut FxHashMap<ContentId, LeanExpr>,
  ) {
    let key = ptr(source);
    if self.collected.contains(&key) {
      return;
    }
    if self.candidate(source) {
      let id = self.content.content(source, self.depth);
      hints.entry(id).or_insert_with(|| source.clone());
    }
    // Do not skip children merely because this node's hint slot was occupied.
    // Mark the exact input node done only after its entire subtree was offered.
    match source.as_data() {
      ExprData::App(f, a, _) => {
        self.collect(f, hints);
        self.collect(a, hints);
      },
      ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
        self.collect(d, hints);
        self.collect(b, hints);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        self.collect(t, hints);
        self.collect(v, hints);
        self.collect(b, hints);
      },
      ExprData::Proj(_, _, v, _) | ExprData::Mdata(_, v, _) => {
        self.collect(v, hints)
      },
      _ => {},
    }
    self.collected.insert(key);
  }

  fn restore(
    &mut self,
    generated: &LeanExpr,
    hints: &FxHashMap<ContentId, LeanExpr>,
  ) -> LeanExpr {
    let key = ptr(generated);
    if let Some(result) = self.restored.get(&key) {
      return result.clone();
    }
    if self.candidate(generated) {
      let id = self.content.content(generated, self.depth);
      if let Some(source) = hints.get(&id) {
        self.restored.insert(key, source.clone());
        return source.clone();
      }
    }
    let result = match generated.as_data() {
      ExprData::App(f, a, _) => {
        let cf = self.restore(f, hints);
        let ca = self.restore(a, hints);
        if same_node(f, &cf) && same_node(a, &ca) {
          generated.clone()
        } else {
          LeanExpr::app(cf, ca)
        }
      },
      ExprData::ForallE(n, d, b, bi, _) => {
        let cd = self.restore(d, hints);
        let cb = self.restore(b, hints);
        if same_node(d, &cd) && same_node(b, &cb) {
          generated.clone()
        } else {
          LeanExpr::all(n.clone(), cd, cb, bi.clone())
        }
      },
      ExprData::Lam(n, d, b, bi, _) => {
        let cd = self.restore(d, hints);
        let cb = self.restore(b, hints);
        if same_node(d, &cd) && same_node(b, &cb) {
          generated.clone()
        } else {
          LeanExpr::lam(n.clone(), cd, cb, bi.clone())
        }
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        let ct = self.restore(t, hints);
        let cv = self.restore(v, hints);
        let cb = self.restore(b, hints);
        if same_node(t, &ct) && same_node(v, &cv) && same_node(b, &cb) {
          generated.clone()
        } else {
          LeanExpr::letE(n.clone(), ct, cv, cb, *nd)
        }
      },
      ExprData::Proj(n, i, v, _) => {
        let cv = self.restore(v, hints);
        if same_node(v, &cv) {
          generated.clone()
        } else {
          LeanExpr::proj(n.clone(), i.clone(), cv)
        }
      },
      ExprData::Mdata(kvs, v, _) => {
        let cv = self.restore(v, hints);
        if same_node(v, &cv) {
          generated.clone()
        } else {
          LeanExpr::mdata(kvs.clone(), cv)
        }
      },
      _ => generated.clone(),
    };
    self.restored.insert(key, result.clone());
    result
  }
}

/// Roots stay borrowed until all pointer-keyed caches are dropped. Only
/// original source/generated descendants become memo keys, never temporaries.
/// The fixed context and finalized hint map cannot change during restoration.
pub(super) fn restore(
  generated: &LeanExpr,
  source: &LeanExpr,
  fvars: &FxHashMap<Name, usize>,
  depth: usize,
  params: &[Name],
  stt: &crate::compile::CompileState,
) -> LeanExpr {
  let addresses = capture_addresses(source, generated, stt);
  let mut pass = Pass::new(&addresses, fvars, depth, params);
  let mut hints = FxHashMap::default();
  pass.collect(source, &mut hints);
  pass.restore(generated, &hints)
}

#[cfg(test)]
#[path = "source_name_hints_tests.rs"]
mod tests;
