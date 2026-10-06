//! Pass 3a: the view of a changed block and the expansions of its image-kind
//! auxiliaries (Def 3.3-3.5). A port of `Ix/Compile/Pass/ImageView.lean`.
//!
//! Pass 1's canonical form of the block is read from the compiler's own
//! records instead of being recomputed (the Lean side recomputes it with
//! `Ix.Compile.Canon`, which agrees with the compiler's sort by the
//! `canon-pass1` gate): the classes of a compiled component are the classes
//! its block was compiled with, and its nested permutation is the block's
//! auxiliary layout, both recorded by hook 1 (`driver::edit_changed_block`).
//! A component that is not compiled yet gets one class per member and no
//! nested data, as on the Lean side.

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{
  ConstantInfo, ConstructorVal, Expr, InductiveVal, Name, RecursorVal,
};

use super::build::image_of;
use super::expr::{canonicalize_const_names, mk_str, nat};
use super::spec::{
  BlockCanon, ComponentCanon, ImageSpec, NestedCanon, image_spec_of_block,
};

/// The expansion of an image-kind auxiliary: `img(a)`.
#[derive(Clone, Debug)]
pub struct Expansion {
  pub level_params: Vec<Name>,
  /// A lambda over Lean's telescope.
  pub value: Expr,
  /// The number of leading lambdas.
  pub arity: usize,
  /// The value is Lean's own (Def 3.5) and is rewritten before use.
  pub needs_rewrite: bool,
}

/// The number of leading lambdas.
pub fn lam_arity(e: &Expr) -> usize {
  let mut n = 0;
  let mut cur = e.clone();
  while let ix_common::env::ExprData::Lam(_, _, b, _, _) = cur.as_data() {
    n += 1;
    let b = b.clone();
    cur = b;
  }
  n
}

/// What the view reads of the compiler.
pub struct ViewInput<'a> {
  pub const_of: &'a dyn Fn(&Name) -> Option<ConstantInfo>,
  /// The member is compiled (has an address).
  pub compiled: &'a dyn Fn(&Name) -> bool,
  /// The recorded classes and nested permutation of the compiled component
  /// containing a member.
  pub component_of: &'a dyn Fn(&Name) -> Option<ComponentRecord>,
  pub canon_rec: &'a dyn Fn(&Name) -> Option<RecursorVal>,
}

/// What hook 1 records of a compiled component of a changed block.
#[derive(Clone, Debug)]
pub struct ComponentRecord {
  pub classes: Vec<Vec<Name>>,
  pub nested: Option<NestedCanon>,
}

/// The view of one changed Lean block.
pub struct BlockView {
  pub all: Vec<Name>,
  pub spec: ImageSpec,
  /// The canonical inductives, constructors and recursors under view names.
  pub canon_consts: FxHashMap<Name, ConstantInfo>,
  /// View name to `E` name.
  pub back: FxHashMap<Name, Name>,
}

impl BlockView {
  pub fn const_of(
    &self,
    inp: &ViewInput<'_>,
    n: &Name,
  ) -> Option<ConstantInfo> {
    match self.canon_consts.get(n) {
      Some(c) => Some(c.clone()),
      None => (inp.const_of)(n),
    }
  }
}

/// The components of a block: members and constructors under the reference
/// graph, each component's members in `all` order, components by their
/// first member's position (`Canon.blockComponents`).
fn block_components(inp: &ViewInput<'_>, all: &[Name]) -> Vec<Vec<Name>> {
  let mut nodes: Vec<Name> = Vec::new();
  for n in all {
    nodes.push(n.clone());
    if let Some(ConstantInfo::InductInfo(v)) = (inp.const_of)(n) {
      nodes.extend(v.ctors.iter().cloned());
    }
  }
  let node_set: FxHashSet<Name> = nodes.iter().cloned().collect();
  let mut refs: crate::graph::RefMap = FxHashMap::default();
  for n in &nodes {
    let out: FxHashSet<Name> = match (inp.const_of)(n) {
      Some(c) => crate::graph::get_constant_info_references(&c)
        .into_iter()
        .filter(|r| node_set.contains(r))
        .collect(),
      None => FxHashSet::default(),
    };
    refs.insert(n.clone(), out);
  }
  let condensed = crate::condense::compute_sccs(&refs);
  let all_set: FxHashSet<Name> = all.iter().cloned().collect();
  let mut comps: Vec<Vec<Name>> = condensed
    .blocks
    .values()
    .filter_map(|c| {
      let ms: Vec<Name> = all
        .iter()
        .filter(|n| c.contains(*n) && all_set.contains(*n))
        .cloned()
        .collect();
      if ms.is_empty() { None } else { Some(ms) }
    })
    .collect();
  let pos = |c: &Vec<Name>| {
    c.first().and_then(|f| all.iter().position(|x| x == f)).unwrap_or(0)
  };
  comps.sort_by_key(pos);
  comps
}

/// Pass 1's canonical form of `all`, for the compiled components
/// (`ImageView.canonBlockCompiled`).
fn canon_block_compiled(
  inp: &ViewInput<'_>,
  all: &[Name],
) -> Result<BlockCanon, String> {
  let mut components = Vec::new();
  for members in block_components(inp, all) {
    if members.iter().all(|m| (inp.compiled)(m)) {
      let rec = members.iter().find_map(|m| (inp.component_of)(m)).ok_or_else(
        || {
          format!(
            "Pass 3 view: no record of the compiled component of {}",
            members[0].pretty()
          )
        },
      )?;
      // the recorded classes are the component's block classes; keep the
      // members of this component (the block of a component is the
      // component)
      let mset: FxHashSet<&Name> = members.iter().collect();
      let classes: Vec<Vec<Name>> = rec
        .classes
        .iter()
        .map(|c| {
          c.iter().filter(|n| mset.contains(n)).cloned().collect::<Vec<_>>()
        })
        .filter(|c: &Vec<Name>| !c.is_empty())
        .collect();
      components.push(ComponentCanon { members, classes, nested: rec.nested });
    } else {
      let classes = members.iter().map(|m| vec![m.clone()]).collect();
      components.push(ComponentCanon { members, classes, nested: None });
    }
  }
  Ok(BlockCanon { all: all.to_vec(), components })
}

/// The view of `all` (`ImageView.buildView`).
pub fn build_view(
  inp: &ViewInput<'_>,
  all: &[Name],
) -> Result<BlockView, String> {
  let canon = canon_block_compiled(inp, all)?;
  let spec = image_spec_of_block(inp.const_of, &canon)?;
  let all0 = all.first().ok_or("Pass 3 view: empty block")?.clone();
  let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  let mut back: FxHashMap<Name, Name> = FxHashMap::default();
  let mut comp_all: FxHashMap<usize, Vec<Name>> = FxHashMap::default();
  for d in &spec.decls {
    comp_all.insert(d.comp, d.types.iter().map(|t| t.name.clone()).collect());
  }
  for d in &spec.decls {
    let comp = canon.components.get(d.comp).ok_or_else(|| {
      format!(
        "Pass 3 view: component {} is absent from canonical block",
        d.comp
      )
    })?;
    let canon_all = comp_all.get(&d.comp).cloned().ok_or_else(|| {
      format!("Pass 3 view: component {} has no canonical member list", d.comp)
    })?;
    let num_nested = comp.nested.as_ref().map_or(0, |n| n.num_canon);
    for (k, ty) in d.types.iter().enumerate() {
      let rep =
        comp.classes.get(k).and_then(|c| c.first()).cloned().ok_or_else(
          || format!("Pass 3 view: class {k} of component {}", d.comp),
        )?;
      let Some(ConstantInfo::InductInfo(iv)) = (inp.const_of)(&rep) else {
        return Err(format!(
          "Pass 3 view: {} is not an inductive",
          rep.pretty()
        ));
      };
      back.insert(ty.name.clone(), rep.clone());
      let mut v: InductiveVal = iv.clone();
      v.cnst.name = ty.name.clone();
      v.cnst.typ = ty.typ.clone();
      v.all = canon_all.clone();
      v.ctors = ty.ctors.iter().map(|c| c.name.clone()).collect();
      v.num_nested = nat(num_nested);
      consts.insert(ty.name.clone(), ConstantInfo::InductInfo(v));
      for (j, cc) in ty.ctors.iter().enumerate() {
        let lc = iv.ctors.get(j).cloned().ok_or_else(|| {
          format!("Pass 3 view: constructor {j} of {}", rep.pretty())
        })?;
        let Some(ConstantInfo::CtorInfo(cv)) = (inp.const_of)(&lc) else {
          return Err(format!(
            "Pass 3 view: {} is not a constructor",
            lc.pretty()
          ));
        };
        back.insert(cc.name.clone(), lc.clone());
        let mut c2: ConstructorVal = cv.clone();
        c2.cnst.name = cc.name.clone();
        c2.cnst.typ = cc.typ.clone();
        c2.induct = ty.name.clone();
        consts.insert(cc.name.clone(), ConstantInfo::CtorInfo(c2));
      }
      let view_rec = mk_str(&ty.name, "rec");
      if let Some(rv) = (inp.canon_rec)(&mk_str(&rep, "rec")) {
        let mut r2 = rv.clone();
        r2.cnst.name = view_rec.clone();
        r2.cnst.typ = spec.tr(&rv.cnst.typ);
        r2.all = canon_all.clone();
        consts.insert(view_rec, ConstantInfo::RecInfo(r2));
      }
    }
    if let Some(n) = &comp.nested {
      let Some(rep0) = canon_all.first() else { continue };
      let mut done: FxHashSet<usize> = FxHashSet::default();
      for (j, p) in n.perm.iter().enumerate() {
        let Some(i) = p else { continue };
        if !done.insert(*i) {
          continue;
        }
        if let Some(rv) =
          (inp.canon_rec)(&mk_str(&all0, &format!("rec_{}", j + 1)))
        {
          let view_rec = mk_str(rep0, &format!("rec_{}", i + 1));
          let mut r2 = rv.clone();
          r2.cnst.name = view_rec.clone();
          r2.cnst.typ = spec.tr(&rv.cnst.typ);
          r2.all = canon_all.clone();
          consts.insert(view_rec, ConstantInfo::RecInfo(r2));
        }
      }
    }
  }
  Ok(BlockView { all: all.to_vec(), spec, canon_consts: consts, back })
}

impl BlockView {
  /// The expansion of an image-kind auxiliary `a` of the block, and the type
  /// of its image constant (`BlockView.expansion`).
  pub fn expansion(
    &self,
    inp: &ViewInput<'_>,
    a: &Name,
  ) -> Result<(Expansion, Expr), String> {
    match (inp.const_of)(a) {
      Some(ConstantInfo::RecInfo(_)) => {
        let lookup = |n: &Name| self.const_of(inp, n);
        let img = image_of(&lookup, &self.spec, a)?;
        let value = canonicalize_const_names(&self.back, &img.value);
        let typ = canonicalize_const_names(&self.back, &img.typ);
        Ok((
          Expansion {
            level_params: img.level_params,
            value,
            arity: img.arity,
            needs_rewrite: false,
          },
          typ,
        ))
      },
      Some(ConstantInfo::DefnInfo(d)) => Ok((
        Expansion {
          level_params: d.cnst.level_params.clone(),
          arity: lam_arity(&d.value),
          value: d.value.clone(),
          needs_rewrite: true,
        },
        d.cnst.typ.clone(),
      )),
      Some(ConstantInfo::ThmInfo(d)) => Ok((
        Expansion {
          level_params: d.cnst.level_params.clone(),
          arity: lam_arity(&d.value),
          value: d.value.clone(),
          needs_rewrite: true,
        },
        d.cnst.typ.clone(),
      )),
      _ => Err(format!(
        "Pass 3: {} has no image (not a recursor or definition)",
        a.pretty()
      )),
    }
  }
}
