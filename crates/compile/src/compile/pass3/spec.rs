//! Pass 3: from Pass 1's canonical form of a Lean block to what the image
//! generator needs. A port of `Ix/Compile/Image/Spec.lean`.
//!
//! The canonical inductive of a class is named `rep._ix` (the view's
//! placeholder, `ImageView.viewNaming`), its constructors `rep._ix.c` (the
//! representative's constructor with its prefix replaced).

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{ConstantInfo, Expr, InductiveVal, Name, NameData};

use super::expr::{
  canonicalize_const_names, consts_in, mk_str, name_replace_prefix,
  replace_const_names,
};
use super::names::IX_COMPONENT;

/// Nested data of one component, as the view reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NestedCanon {
  /// Source position to canonical position (`None`: outside the component).
  pub perm: Vec<Option<usize>>,
  /// The number of canonical auxiliary classes.
  pub num_canon: usize,
}

/// One component of a block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComponentCanon {
  /// Members, in `all` order.
  pub members: Vec<Name>,
  /// Classes in canonical order, representative first.
  pub classes: Vec<Vec<Name>>,
  pub nested: Option<NestedCanon>,
}

impl ComponentCanon {
  pub fn reps(&self) -> Vec<Name> {
    self.classes.iter().filter_map(|c| c.first().cloned()).collect()
  }
}

/// The canonical form of a Lean block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockCanon {
  pub all: Vec<Name>,
  pub components: Vec<ComponentCanon>,
}

#[derive(Clone, Debug)]
pub struct CanonCtor {
  pub name: Name,
  pub typ: Expr,
}

#[derive(Clone, Debug)]
pub struct CanonType {
  pub name: Name,
  pub typ: Expr,
  pub ctors: Vec<CanonCtor>,
}

/// One canonical inductive block (a component of the Lean block).
#[derive(Clone, Debug)]
pub struct CanonDecl {
  pub comp: usize,
  pub level_params: Vec<Name>,
  pub num_params: usize,
  pub is_unsafe: bool,
  pub types: Vec<CanonType>,
}

/// What the image generator needs about one changed Lean block.
#[derive(Clone, Debug)]
pub struct ImageSpec {
  pub block: BlockCanon,
  pub ty_map: FxHashMap<Name, Name>,
  pub ctor_map: FxHashMap<Name, Name>,
  pub canon_inds: Vec<Name>,
  pub decls: Vec<CanonDecl>,
}

/// The view's placeholder of a canonical inductive: `rep._ix`.
pub fn ind_name(rep: &Name) -> Name {
  mk_str(rep, IX_COMPONENT)
}

impl ImageSpec {
  /// `tr_N`: members and constructors renamed (constant heads only).
  pub fn tr(&self, e: &Expr) -> Expr {
    let mut m = self.ty_map.clone();
    for (k, v) in &self.ctor_map {
      m.insert(k.clone(), v.clone());
    }
    canonicalize_const_names(&m, e)
  }

  pub fn tr_name(&self, n: &Name) -> Name {
    match self.ty_map.get(n) {
      Some(m) => m.clone(),
      None => self.ctor_map.get(n).cloned().unwrap_or_else(|| n.clone()),
    }
  }
}

pub fn ind_of(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  n: &Name,
) -> Result<InductiveVal, String> {
  match const_of(n) {
    Some(ConstantInfo::InductInfo(v)) => Ok(v),
    _ => Err(format!("image spec: {} is not an inductive", n.pretty())),
  }
}

/// The canonical constructor name.
fn canon_ctor_name(rep: &Name, canon: &Name, ctor: &Name) -> Name {
  let n = name_replace_prefix(ctor, rep, canon);
  if n == *ctor {
    match ctor.as_data() {
      NameData::Str(_, s, _) => mk_str(canon, s),
      _ => mk_str(canon, &ctor.pretty()),
    }
  } else {
    n
  }
}

/// Components in dependency order; ties by position.
fn component_order(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  b: &BlockCanon,
) -> Result<Vec<usize>, String> {
  let n = b.components.len();
  let mut owner: FxHashMap<Name, usize> = FxHashMap::default();
  for (i, c) in b.components.iter().enumerate() {
    for cls in &c.classes {
      for x in cls {
        owner.insert(x.clone(), i);
      }
    }
  }
  let owner_keys: FxHashSet<Name> = owner.keys().cloned().collect();
  let mut deps: Vec<Vec<usize>> = Vec::with_capacity(n);
  for c in &b.components {
    let mut ds: Vec<usize> = Vec::new();
    for rep in c.reps() {
      let iv = ind_of(const_of, &rep)?;
      for cn in &iv.ctors {
        let Some(ConstantInfo::CtorInfo(cv)) = const_of(cn) else {
          return Err(format!("image spec: no constructor {}", cn.pretty()));
        };
        // the Lean side iterates a hash set here; the result only feeds a
        // membership-tested dependency list, so the order is irrelevant
        let mut found: Vec<usize> = consts_in(&owner_keys, &cv.cnst.typ)
          .into_iter()
          .filter_map(|x| owner.get(&x).copied())
          .collect();
        found.sort_unstable();
        for j in found {
          if !ds.contains(&j) {
            ds.push(j);
          }
        }
      }
    }
    deps.push(ds);
  }
  let mut out: Vec<usize> = Vec::with_capacity(n);
  for _ in 0..n {
    match deps.iter().enumerate().find(|(i, ds)| {
      !out.contains(i) && ds.iter().all(|j| j == i || out.contains(j))
    }) {
      Some((i, _)) => out.push(i),
      None => {
        return Err(
          "image spec: the components have no dependency order".into(),
        );
      },
    }
  }
  Ok(out)
}

/// The image specification of a Lean block from its canonical form.
pub fn image_spec_of_block(
  const_of: &dyn Fn(&Name) -> Option<ConstantInfo>,
  b: &BlockCanon,
) -> Result<ImageSpec, String> {
  let order = component_order(const_of, b)?;
  let mut ty_map: FxHashMap<Name, Name> = FxHashMap::default();
  for c in &b.components {
    for cls in &c.classes {
      let Some(rep) = cls.first() else {
        return Err("image spec: empty class".into());
      };
      for x in cls {
        ty_map.insert(x.clone(), ind_name(rep));
      }
    }
  }
  let mut ctor_map: FxHashMap<Name, Name> = FxHashMap::default();
  let mut canon_inds: Vec<Name> = Vec::new();
  let mut decls: Vec<CanonDecl> = Vec::new();
  for ci in order {
    let Some(c) = b.components.get(ci) else {
      return Err(format!("image spec: component {ci} out of range"));
    };
    let mut types: Vec<CanonType> = Vec::new();
    let mut lps: Vec<Name> = Vec::new();
    let mut np = 0usize;
    let mut unsafe_ = false;
    for cls in &c.classes {
      let Some(rep) = cls.first() else {
        return Err("image spec: empty class".into());
      };
      let canon = ind_name(rep);
      canon_inds.push(canon.clone());
      let riv = ind_of(const_of, rep)?;
      lps = riv.cnst.level_params.clone();
      np = riv.num_params.to_u64().unwrap_or(0) as usize;
      unsafe_ = riv.is_unsafe;
      let canon_ctors: Vec<Name> =
        riv.ctors.iter().map(|c| canon_ctor_name(rep, &canon, c)).collect();
      for x in cls {
        let xv = ind_of(const_of, x)?;
        if xv.ctors.len() != canon_ctors.len() {
          return Err(format!(
            "image spec: {} and {} differ in constructor count",
            x.pretty(),
            rep.pretty()
          ));
        }
        for (cn, cc) in xv.ctors.iter().zip(canon_ctors.iter()) {
          ctor_map.insert(cn.clone(), cc.clone());
        }
      }
      let mut ctors: Vec<CanonCtor> = Vec::new();
      for (cn, cc) in riv.ctors.iter().zip(canon_ctors.iter()) {
        let Some(ConstantInfo::CtorInfo(cv)) = const_of(cn) else {
          return Err(format!("image spec: no constructor {}", cn.pretty()));
        };
        ctors.push(CanonCtor {
          name: cc.clone(),
          typ: replace_const_names(&ty_map, &cv.cnst.typ),
        });
      }
      types.push(CanonType { name: canon, typ: riv.cnst.typ.clone(), ctors });
    }
    decls.push(CanonDecl {
      comp: ci,
      level_params: lps,
      num_params: np,
      is_unsafe: unsafe_,
      types,
    });
  }
  Ok(ImageSpec { block: b.clone(), ty_map, ctor_map, canon_inds, decls })
}
