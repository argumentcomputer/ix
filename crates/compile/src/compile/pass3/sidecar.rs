//! Pass 3: the side-car of a changed block (D14). A port of
//! `Ix/Compile/Pass/SideCar.lean`: every Ix auxiliary the aux tail registered
//! under a Lean name moves to its display name `x._ix.S`, with its metadata
//! renamed into the `_ix` view (the constant's own name, `all`, `ctx`,
//! constructor names and every reference in its arena); synthetic `Muts`
//! entries keep their keys with their member lists renamed. Metadata only:
//! no constant's bytes change.

use rustc_hash::FxHashMap;

use ix_common::address::Address;
use ix_common::env::Name;
use ixon::env::Named;
use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta, ExprMetaData};

fn name_addr(n: &Name) -> Address {
  Address::from_blake3_hash(*n.get_hash())
}

/// Rename name-hash addresses in one arena node (binder names stay).
fn rename_node(
  m: &FxHashMap<Address, Address>,
  n: &ExprMetaData,
) -> ExprMetaData {
  let r = |a: &Address| m.get(a).cloned().unwrap_or_else(|| a.clone());
  match n {
    ExprMetaData::Ref { name } => ExprMetaData::Ref { name: r(name) },
    ExprMetaData::Prj { struct_name, child } => {
      ExprMetaData::Prj { struct_name: r(struct_name), child: *child }
    },
    ExprMetaData::CallSite { name, entries, canon_meta, orig_head } => {
      ExprMetaData::CallSite {
        name: r(name),
        entries: entries.clone(),
        canon_meta: canon_meta.clone(),
        orig_head: *orig_head,
      }
    },
    ExprMetaData::EtaCallSite {
      n_synth,
      name,
      entries,
      canon_meta,
      wrapper_meta,
    } => ExprMetaData::EtaCallSite {
      n_synth: *n_synth,
      name: r(name),
      entries: entries.clone(),
      canon_meta: canon_meta.clone(),
      wrapper_meta: *wrapper_meta,
    },
    other => other.clone(),
  }
}

/// Rename name-hash addresses throughout a constant's metadata.
pub fn rename_meta(
  m: &FxHashMap<Address, Address>,
  cm: &ConstantMeta,
) -> ConstantMeta {
  if m.is_empty() {
    return cm.clone();
  }
  let r = |a: &Address| m.get(a).cloned().unwrap_or_else(|| a.clone());
  let rv = |v: &[Address]| v.iter().map(r).collect::<Vec<_>>();
  let arena = |a: &ExprMeta| ExprMeta {
    nodes: a.nodes.iter().map(|n| rename_node(m, n)).collect(),
  };
  let info = match &cm.info {
    ConstantMetaInfo::Empty => ConstantMetaInfo::Empty,
    ConstantMetaInfo::Def {
      name,
      lvls,
      all,
      ctx,
      arena: ar,
      type_root,
      value_root,
    } => ConstantMetaInfo::Def {
      name: r(name),
      lvls: lvls.clone(),
      all: rv(all),
      ctx: rv(ctx),
      arena: arena(ar),
      type_root: *type_root,
      value_root: *value_root,
    },
    ConstantMetaInfo::Axio { name, lvls, arena: ar, type_root } => {
      ConstantMetaInfo::Axio {
        name: r(name),
        lvls: lvls.clone(),
        arena: arena(ar),
        type_root: *type_root,
      }
    },
    ConstantMetaInfo::Quot { name, lvls, arena: ar, type_root } => {
      ConstantMetaInfo::Quot {
        name: r(name),
        lvls: lvls.clone(),
        arena: arena(ar),
        type_root: *type_root,
      }
    },
    ConstantMetaInfo::Indc {
      name,
      lvls,
      ctors,
      all,
      ctx,
      arena: ar,
      type_root,
    } => ConstantMetaInfo::Indc {
      name: r(name),
      lvls: lvls.clone(),
      ctors: rv(ctors),
      all: rv(all),
      ctx: rv(ctx),
      arena: arena(ar),
      type_root: *type_root,
    },
    ConstantMetaInfo::Ctor { name, lvls, induct, arena: ar, type_root } => {
      ConstantMetaInfo::Ctor {
        name: r(name),
        lvls: lvls.clone(),
        induct: r(induct),
        arena: arena(ar),
        type_root: *type_root,
      }
    },
    ConstantMetaInfo::Rec {
      name,
      lvls,
      rules,
      all,
      ctx,
      arena: ar,
      type_root,
      rule_roots,
    } => ConstantMetaInfo::Rec {
      name: r(name),
      lvls: lvls.clone(),
      rules: rv(rules),
      all: rv(all),
      ctx: rv(ctx),
      arena: arena(ar),
      type_root: *type_root,
      rule_roots: rule_roots.clone(),
    },
    ConstantMetaInfo::Muts { all, aux_layout } => ConstantMetaInfo::Muts {
      all: all.iter().map(|c| rv(c)).collect(),
      aux_layout: aux_layout.clone(),
    },
  };
  let mut out = cm.clone();
  out.info = info;
  out
}

/// Rename a `Named` entry's metadata and its `original`'s, keeping its
/// address and hints.
pub fn rename_named(m: &FxHashMap<Address, Address>, n: &Named) -> Named {
  let mut out = Named::new(n.addr.clone(), rename_meta(m, &n.meta()));
  out.set_hints(n.hints());
  if let Some((a, om)) = n.original() {
    out.set_original(a, rename_meta(m, &om));
  }
  out
}

/// The name-hash renaming of a display map (`SideCarEdit.apply`'s `full`).
pub fn hash_map_of(display: &[(Name, Name)]) -> FxHashMap<Address, Address> {
  display.iter().map(|(k, v)| (name_addr(k), name_addr(v))).collect()
}
