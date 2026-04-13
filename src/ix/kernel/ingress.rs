//! Ingress: convert Ixon environment to zero kernel types.
//!
//! Converts Ixon `Constant`/`ConstantInfo`/`Expr`/`Univ` (alpha-invariant,
//! content-addressed) to `KExpr`/`KUniv`/`KConst` (kernel types with positional
//! universe params and optional metadata). Uses iterative stack-based traversal
//! to avoid stack overflow on deeply nested expressions.

use std::cell::Cell;
use std::sync::Arc;

use rayon::iter::{IntoParallelIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, Name};
use crate::ix::ixon::constant::{
  Constant, ConstantInfo as IxonCI, MutConst as IxonMutConst,
};
use crate::ix::ixon::env::Env as IxonEnv;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::metadata::{
  ConstantMeta, ConstantMetaInfo, ExprMeta, ExprMetaData, resolve_kvmap,
};
use crate::ix::ixon::univ::Univ as IxonUniv;
use lean_ffi::nat::Nat;

use super::constant::{KConst, RecRule};
use super::env::{InternTable, KEnv};
use super::expr::{KExpr, MData};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;

// ============================================================================
// Lookup tables
// ============================================================================

/// Read-only context for converting a single Ixon constant's expressions.
struct Ctx<'a, M: KernelMode> {
  sharing: &'a [Arc<IxonExpr>],
  refs: &'a [Address],
  univs: &'a [Arc<IxonUniv>],
  /// ZIds of mutual block members (for resolving `Expr::Rec`).
  mut_ctx: Vec<KId<M>>,
  arena: &'a ExprMeta,
  names: &'a FxHashMap<Address, Name>,
  lvls: Vec<Name>,
  /// Canonical intern table (shared across all ingress calls).
  intern: &'a InternTable<M>,
  /// Counter for generating synthetic unique names when metadata is missing.
  synth_counter: Cell<u64>,
}

/// Expression conversion cache, keyed on (expr pointer, arena_idx).
type ExprCache<M> = FxHashMap<(usize, u64), KExpr<M>>;

fn resolve_name(addr: &Address, names: &FxHashMap<Address, Name>) -> Name {
  names.get(addr).cloned().unwrap_or_else(Name::anon)
}

impl<M: KernelMode> Ctx<'_, M> {
  /// Generate a unique synthetic name like `_s0`, `_s1`, etc.
  fn synth_name(&self) -> Name {
    let n = self.synth_counter.get();
    self.synth_counter.set(n + 1);
    Name::str(Name::anon(), format!("_s{n}"))
  }
}

fn resolve_level_params(
  lvl_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
) -> Vec<Name> {
  lvl_addrs.iter().map(|a| resolve_name(a, names)).collect()
}

/// Resolve a ConstantMeta `all` field to `Vec<KId<M>>`.
fn resolve_all<M: KernelMode>(
  all_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<KId<M>> {
  all_addrs
    .iter()
    .map(|name_addr| {
      let name = resolve_name(name_addr, names);
      let addr = name_to_addr
        .get(&name)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(*name.get_hash()));
      KId::new(addr, M::meta_field(name))
    })
    .collect()
}

fn get_ctx_addrs(meta: &ConstantMeta) -> &[Address] {
  match &meta.info {
    ConstantMetaInfo::Def { ctx, .. }
    | ConstantMetaInfo::Indc { ctx, .. }
    | ConstantMetaInfo::Rec { ctx, .. } => ctx,
    _ => &[],
  }
}

fn build_mut_ctx<M: KernelMode>(
  meta: &ConstantMeta,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Vec<KId<M>> {
  resolve_all(get_ctx_addrs(meta), names, name_to_addr)
}

// ============================================================================
// Universe ingress (iterative)
// ============================================================================

enum UnivFrame {
  Process(Arc<IxonUniv>),
  Succ,
  MaxLeft(Arc<IxonUniv>),
  Max,
  IMaxLeft(Arc<IxonUniv>),
  IMax,
}

fn ingress_univ<M: KernelMode>(
  root: &Arc<IxonUniv>,
  ctx: &Ctx<'_, M>,
  intern: &InternTable<M>,
) -> KUniv<M> {
  let mut stack: Vec<UnivFrame> = vec![UnivFrame::Process(root.clone())];
  let mut values: Vec<KUniv<M>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      UnivFrame::Process(u) => match u.as_ref() {
        IxonUniv::Zero => values.push(intern.intern_univ(KUniv::zero())),
        IxonUniv::Succ(inner) => {
          stack.push(UnivFrame::Succ);
          stack.push(UnivFrame::Process(inner.clone()));
        },
        IxonUniv::Max(a, b) => {
          stack.push(UnivFrame::Max);
          stack.push(UnivFrame::Process(b.clone()));
          stack.push(UnivFrame::MaxLeft(a.clone()));
        },
        IxonUniv::IMax(a, b) => {
          stack.push(UnivFrame::IMax);
          stack.push(UnivFrame::Process(b.clone()));
          stack.push(UnivFrame::IMaxLeft(a.clone()));
        },
        IxonUniv::Var(idx) => {
          let pos =
            usize::try_from(*idx).expect("univ var index exceeds usize");
          let name = ctx.lvls.get(pos).cloned().unwrap_or_else(Name::anon);
          values
            .push(intern.intern_univ(KUniv::param(*idx, M::meta_field(name))));
        },
      },
      UnivFrame::Succ => {
        let inner = values.pop().unwrap();
        values.push(intern.intern_univ(KUniv::succ(inner)));
      },
      UnivFrame::MaxLeft(a) | UnivFrame::IMaxLeft(a) => {
        stack.push(UnivFrame::Process(a));
      },
      UnivFrame::Max => {
        let b = values.pop().unwrap();
        let a = values.pop().unwrap();
        values.push(intern.intern_univ(KUniv::max(a, b)));
      },
      UnivFrame::IMax => {
        let b = values.pop().unwrap();
        let a = values.pop().unwrap();
        values.push(intern.intern_univ(KUniv::imax(a, b)));
      },
    }
  }

  intern.intern_univ(values.pop().unwrap())
}

fn ingress_univ_args<M: KernelMode>(
  univ_idxs: &[u64],
  ctx: &Ctx<'_, M>,
  intern: &InternTable<M>,
) -> Box<[KUniv<M>]> {
  univ_idxs
    .iter()
    .filter_map(|&idx| ctx.univs.get(usize::try_from(idx).ok()?))
    .map(|u| ingress_univ(u, ctx, intern))
    .collect()
}

// ============================================================================
// Expression ingress (iterative)
// ============================================================================

enum ExprFrame<M: KernelMode> {
  Process {
    expr: Arc<IxonExpr>,
    arena_idx: u64,
  },
  AppArg {
    arg: Arc<IxonExpr>,
    arg_arena: u64,
  },
  AppDone {
    mdata: M::MField<Vec<MData>>,
  },
  LamBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  LamDone {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    mdata: M::MField<Vec<MData>>,
  },
  AllBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  AllDone {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    mdata: M::MField<Vec<MData>>,
  },
  LetVal {
    val: Arc<IxonExpr>,
    val_arena: u64,
    body: Arc<IxonExpr>,
    body_arena: u64,
    binder_name: Name,
  },
  LetBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  LetDone {
    name: M::MField<Name>,
    nd: bool,
    mdata: M::MField<Vec<MData>>,
  },
  PrjDone {
    type_id: KId<M>,
    field_idx: u64,
    mdata: M::MField<Vec<MData>>,
  },
  Cache {
    key: (usize, u64),
  },
  /// Push a binder name before processing a body (for BVar name resolution).
  BinderPush {
    name: Name,
  },
  /// Pop a binder name after processing a body.
  BinderPop,
}

/// Default empty arena for constants without metadata.
static DEFAULT_ARENA: ExprMeta = ExprMeta { nodes: Vec::new() };

fn ingress_expr<M: KernelMode>(
  root_expr: &Arc<IxonExpr>,
  root_arena: u64,
  ctx: &Ctx<'_, M>,
  ixon_env: &IxonEnv,
  cache: &mut ExprCache<M>,
) -> Result<KExpr<M>, String> {
  let mut stack: Vec<ExprFrame<M>> =
    vec![ExprFrame::Process { expr: root_expr.clone(), arena_idx: root_arena }];
  let mut values: Vec<KExpr<M>> = Vec::new();
  // Binder name context for resolving BVar names via de Bruijn index.
  // Pushed when entering a binder body, popped when leaving.
  let mut binder_names: Vec<Name> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      ExprFrame::Process { expr, arena_idx } => {
        // Walk mdata chain in arena
        let mut current_idx = arena_idx;
        let mut mdata_layers: Vec<MData> = Vec::new();
        while let Some(ExprMetaData::Mdata { mdata, child }) =
          ctx.arena.nodes.get(
            usize::try_from(current_idx).map_err(|_e| {
              format!("arena index {current_idx} exceeds usize")
            })?,
          )
        {
          for kvm in mdata {
            mdata_layers.push(resolve_kvmap(kvm, ixon_env));
          }
          current_idx = *child;
        }

        //loop {
        //  match ctx.arena.nodes.get(current_idx as usize) {
        //    Some(ExprMetaData::Mdata { mdata, child }) => {
        //      for kvm in mdata {
        //        mdata_layers.push(resolve_kvmap(kvm, ixon_env));
        //      }
        //      current_idx = *child;
        //    },
        //    _ => break,
        //  }
        //}

        // Expand Share transparently
        if let IxonExpr::Share(share_idx) = expr.as_ref() {
          if let Some(shared) = ctx.sharing.get(
            usize::try_from(*share_idx)
              .map_err(|_e| format!("Share index {share_idx} exceeds usize"))?,
          ) {
            stack.push(ExprFrame::Process { expr: shared.clone(), arena_idx });
            continue;
          } else {
            return Err(format!("invalid Share index {share_idx}"));
          }
        }

        // BVar early return (no caching needed for leaves)
        if let IxonExpr::Var(idx) = expr.as_ref() {
          // Resolve name from the binder context using de Bruijn index.
          let idx_usize = usize::try_from(*idx)
            .map_err(|_e| format!("BVar index {idx} exceeds usize"))?;
          let name = binder_names
            .len()
            .checked_sub(1 + idx_usize)
            .and_then(|i| binder_names.get(i))
            .cloned()
            .unwrap_or_else(Name::anon);
          if mdata_layers.is_empty() {
            values.push(
              ctx.intern.intern_expr(KExpr::var(*idx, M::meta_field(name))),
            );
          } else {
            values.push(ctx.intern.intern_expr(KExpr::var_mdata(
              *idx,
              M::meta_field(name),
              M::meta_field(mdata_layers),
            )));
          }
          continue;
        }

        // Check cache
        let cache_key = (Arc::as_ptr(&expr) as usize, arena_idx);
        if let Some(cached) = cache.get(&cache_key) {
          values.push(cached.clone());
          continue;
        }

        let node =
          ctx
            .arena
            .nodes
            .get(usize::try_from(current_idx).map_err(|_e| {
              format!("arena index {current_idx} exceeds usize")
            })?)
            .unwrap_or(&ExprMetaData::Leaf);

        stack.push(ExprFrame::Cache { key: cache_key });
        let mdata = M::meta_field(mdata_layers);

        match expr.as_ref() {
          IxonExpr::Sort(idx) => {
            let u =
              ctx
                .univs
                .get(usize::try_from(*idx).map_err(|_e| {
                  format!("Sort univ index {idx} exceeds usize")
                })?)
                .ok_or_else(|| format!("invalid Sort univ index {idx}"))?;
            let zu = ingress_univ(u, ctx, ctx.intern);
            values.push(ctx.intern.intern_expr(KExpr::sort_mdata(zu, mdata)));
          },

          IxonExpr::Var(_) | IxonExpr::Share(_) => unreachable!(),

          IxonExpr::Ref(ref_idx, univ_idxs) => {
            let addr = ctx
              .refs
              .get(
                usize::try_from(*ref_idx)
                  .map_err(|_e| format!("Ref index {ref_idx} exceeds usize"))?,
              )
              .ok_or_else(|| format!("invalid Ref index {ref_idx}"))?
              .clone();
            let name = match node {
              ExprMetaData::Ref { name: name_addr } => {
                resolve_name(name_addr, ctx.names)
              },
              _ => {
                return Err(format!(
                  "Ref at index {ref_idx} (addr {}) has no metadata name (node={node:?})",
                  &addr.hex()[..8]
                ));
              },
            };
            let univs = ingress_univ_args(univ_idxs, ctx, ctx.intern);
            values.push(ctx.intern.intern_expr(KExpr::cnst_mdata(
              KId::new(addr, M::meta_field(name)),
              univs,
              mdata,
            )));
          },

          IxonExpr::Rec(rec_idx, univ_idxs) => {
            let mid = ctx
              .mut_ctx
              .get(
                usize::try_from(*rec_idx)
                  .map_err(|_e| format!("Rec index {rec_idx} exceeds usize"))?,
              )
              .ok_or_else(|| format!("invalid Rec index {rec_idx}"))?
              .clone();
            let univs = ingress_univ_args(univ_idxs, ctx, ctx.intern);
            values.push(
              ctx.intern.intern_expr(KExpr::cnst_mdata(mid, univs, mdata)),
            );
          },

          IxonExpr::App(f, a) => {
            let (f_arena, a_arena) = match node {
              ExprMetaData::App { children } => (children[0], children[1]),
              _ => (current_idx, current_idx),
            };
            stack.push(ExprFrame::AppDone { mdata });
            stack
              .push(ExprFrame::AppArg { arg: a.clone(), arg_arena: a_arena });
            stack
              .push(ExprFrame::Process { expr: f.clone(), arena_idx: f_arena });
          },

          IxonExpr::Lam(ty, body) => {
            let (name, bi, ty_arena, body_arena) = match node {
              ExprMetaData::Binder { name: addr, info, children } => (
                resolve_name(addr, ctx.names),
                info.clone(),
                children[0],
                children[1],
              ),
              _ => (
                ctx.synth_name(),
                BinderInfo::Default,
                current_idx,
                current_idx,
              ),
            };
            stack.push(ExprFrame::LamDone {
              name: M::meta_field(name.clone()),
              bi: M::meta_field(bi),
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::LamBody { body: body.clone(), body_arena });
            stack.push(ExprFrame::BinderPush { name });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::All(ty, body) => {
            let (name, bi, ty_arena, body_arena) = match node {
              ExprMetaData::Binder { name: addr, info, children } => (
                resolve_name(addr, ctx.names),
                info.clone(),
                children[0],
                children[1],
              ),
              _ => (
                ctx.synth_name(),
                BinderInfo::Default,
                current_idx,
                current_idx,
              ),
            };
            stack.push(ExprFrame::AllDone {
              name: M::meta_field(name.clone()),
              bi: M::meta_field(bi),
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::AllBody { body: body.clone(), body_arena });
            stack.push(ExprFrame::BinderPush { name });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::Let(nd, ty, val, body) => {
            let (name, ty_arena, val_arena, body_arena) = match node {
              ExprMetaData::LetBinder { name: addr, children } => (
                resolve_name(addr, ctx.names),
                children[0],
                children[1],
                children[2],
              ),
              _ => (ctx.synth_name(), current_idx, current_idx, current_idx),
            };
            stack.push(ExprFrame::LetDone {
              name: M::meta_field(name.clone()),
              nd: *nd,
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::LetVal {
              val: val.clone(),
              val_arena,
              body: body.clone(),
              body_arena,
              binder_name: name,
            });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::Prj(type_ref_idx, field_idx, s) => {
            let type_addr = ctx
              .refs
              .get(usize::try_from(*type_ref_idx).map_err(|_e| {
                format!("Prj type ref index {type_ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| {
                format!("invalid Prj type ref index {type_ref_idx}")
              })?
              .clone();
            let (struct_name, child_arena) = match node {
              ExprMetaData::Prj { struct_name: addr, child } => {
                (resolve_name(addr, ctx.names), *child)
              },
              _ => {
                return Err(format!(
                  "Prj at ref index {type_ref_idx} (addr {}) has no metadata name (node={node:?})",
                  &type_addr.hex()[..8]
                ));
              },
            };
            stack.push(ExprFrame::PrjDone {
              type_id: KId::new(type_addr, M::meta_field(struct_name)),
              field_idx: *field_idx,
              mdata,
            });
            stack.push(ExprFrame::Process {
              expr: s.clone(),
              arena_idx: child_arena,
            });
          },

          IxonExpr::Str(ref_idx) => {
            let addr = ctx
              .refs
              .get(usize::try_from(*ref_idx).map_err(|_e| {
                format!("Str ref index {ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| format!("invalid Str ref index {ref_idx}"))?;
            let s = ixon_env
              .get_blob(addr)
              .and_then(|b| String::from_utf8(b).ok())
              .unwrap_or_default();
            values.push(ctx.intern.intern_expr(KExpr::str_mdata(
              s,
              addr.clone(),
              mdata,
            )));
          },

          IxonExpr::Nat(ref_idx) => {
            let addr = ctx
              .refs
              .get(usize::try_from(*ref_idx).map_err(|_e| {
                format!("Nat ref index {ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| format!("invalid Nat ref index {ref_idx}"))?;
            let n = ixon_env
              .get_blob(addr)
              .map_or_else(|| Nat::from(0u64), |b| Nat::from_le_bytes(&b));
            values.push(ctx.intern.intern_expr(KExpr::nat_mdata(
              n,
              addr.clone(),
              mdata,
            )));
          },
        }
      },

      // Continuation frames
      ExprFrame::AppArg { arg, arg_arena } => {
        stack.push(ExprFrame::Process { expr: arg, arena_idx: arg_arena });
      },
      ExprFrame::AppDone { mdata } => {
        let a = values.pop().unwrap();
        let f = values.pop().unwrap();
        values.push(ctx.intern.intern_expr(KExpr::app_mdata(f, a, mdata)));
      },
      ExprFrame::LamBody { body, body_arena } => {
        // The binder name was already pushed by BinderPush before this frame
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
      },
      ExprFrame::LamDone { name, bi, mdata } => {
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        values.push(
          ctx.intern.intern_expr(KExpr::lam_mdata(name, bi, ty, body, mdata)),
        );
      },
      ExprFrame::AllBody { body, body_arena }
      | ExprFrame::LetBody { body, body_arena } => {
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
      },
      ExprFrame::AllDone { name, bi, mdata } => {
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        values.push(
          ctx.intern.intern_expr(KExpr::all_mdata(name, bi, ty, body, mdata)),
        );
      },
      ExprFrame::LetVal { val, val_arena, body, body_arena, binder_name } => {
        stack.push(ExprFrame::LetBody { body, body_arena });
        stack.push(ExprFrame::BinderPush { name: binder_name });
        stack.push(ExprFrame::Process { expr: val, arena_idx: val_arena });
      },
      ExprFrame::LetDone { name, nd, mdata } => {
        let body = values.pop().unwrap();
        let val = values.pop().unwrap();
        let ty = values.pop().unwrap();
        values.push(
          ctx
            .intern
            .intern_expr(KExpr::let_mdata(name, ty, val, body, nd, mdata)),
        );
      },
      ExprFrame::BinderPush { name } => {
        binder_names.push(name);
      },
      ExprFrame::BinderPop => {
        binder_names.pop();
      },
      ExprFrame::PrjDone { type_id, field_idx, mdata } => {
        let s = values.pop().unwrap();
        values.push(
          ctx
            .intern
            .intern_expr(KExpr::prj_mdata(type_id, field_idx, s, mdata)),
        );
      },
      ExprFrame::Cache { key } => {
        let result = values.last().unwrap().clone();
        cache.insert(key, result);
      },
    }
  }

  values.pop().ok_or_else(|| "ingress_expr: empty value stack".to_string())
}

// ============================================================================
// Constant ingress
// ============================================================================

#[allow(clippy::too_many_arguments)]
fn ingress_defn<M: KernelMode>(
  def: &crate::ix::ixon::constant::Definition,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &InternTable<M>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let mut cache: ExprCache<M> = FxHashMap::default();
  let (level_params, arena, type_root, value_root, hints, safety, all_addrs) =
    match &meta.info {
      ConstantMetaInfo::Def {
        lvls,
        arena,
        type_root,
        value_root,
        hints,
        all,
        ..
      } => (
        resolve_level_params(lvls, names),
        arena,
        *type_root,
        *value_root,
        *hints,
        def.safety,
        all.clone(),
      ),
      _ => (
        vec![],
        &DEFAULT_ARENA,
        0,
        0,
        crate::ix::env::ReducibilityHints::Regular(0),
        def.safety,
        vec![],
      ),
    };

  let ctx = Ctx {
    sharing,
    refs,
    univs,
    mut_ctx: build_mut_ctx(meta, names, name_to_addr),
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(&def.typ, type_root, &ctx, ixon_env, &mut cache)?;
  let value = ingress_expr(&def.value, value_root, &ctx, ixon_env, &mut cache)?;
  let lean_all = resolve_all(&all_addrs, names, name_to_addr);

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Def { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  Ok(vec![(
    self_id,
    KConst::Defn {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params),
      kind: def.kind,
      safety,
      hints,
      lvls: def.lvls,
      ty: typ,
      val: value,
      lean_all: M::meta_field(lean_all),
      block,
    },
  )])
}

#[allow(clippy::too_many_arguments)]
fn ingress_recursor<M: KernelMode>(
  rec: &crate::ix::ixon::constant::Recursor,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &InternTable<M>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let mut cache: ExprCache<M> = FxHashMap::default();
  let (level_params, arena, type_root, rule_roots, all_addrs) = match &meta.info
  {
    ConstantMetaInfo::Rec {
      lvls, arena, type_root, rule_roots, all, ..
    } => (
      resolve_level_params(lvls, names),
      arena,
      *type_root,
      rule_roots.clone(),
      all.clone(),
    ),
    _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![]),
  };

  let ctx = Ctx {
    sharing,
    refs,
    univs,
    mut_ctx: build_mut_ctx(meta, names, name_to_addr),
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(&rec.typ, type_root, &ctx, ixon_env, &mut cache)?;
  let rules: Result<Vec<RecRule<M>>, String> = rec
    .rules
    .iter()
    .enumerate()
    .map(|(i, rule)| {
      let rhs_root = rule_roots.get(i).copied().unwrap_or(0);
      let rhs = ingress_expr(&rule.rhs, rhs_root, &ctx, ixon_env, &mut cache)?;
      Ok(RecRule { fields: rule.fields, rhs })
    })
    .collect();
  let lean_all = resolve_all(&all_addrs, names, name_to_addr);

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Rec { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  Ok(vec![(
    self_id,
    KConst::Recr {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params),
      k: rec.k,
      is_unsafe: rec.is_unsafe,
      lvls: rec.lvls,
      params: rec.params,
      indices: rec.indices,
      motives: rec.motives,
      minors: rec.minors,
      block,
      member_idx: 0, // filled in by caller for muts blocks
      ty: typ,
      rules: rules?,
      lean_all: M::meta_field(lean_all),
    },
  )])
}

#[allow(clippy::too_many_arguments)]
fn ingress_standalone<M: KernelMode>(
  const_name: &Name,
  addr: &Address,
  constant: &Constant,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &InternTable<M>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let self_id: KId<M> =
    KId::new(addr.clone(), M::meta_field(const_name.clone()));

  match &constant.info {
    IxonCI::Defn(def) => ingress_defn(
      def,
      self_id.clone(),
      meta,
      ixon_env,
      names,
      name_to_addr,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id,
      intern,
    ),

    IxonCI::Axio(ax) => {
      let mut cache: ExprCache<M> = FxHashMap::default();
      let (level_params, arena, type_root) = match &meta.info {
        ConstantMetaInfo::Axio { lvls, arena, type_root, .. } => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        _ => (vec![], &DEFAULT_ARENA, 0),
      };
      let ctx = Ctx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        mut_ctx: vec![],
        arena,
        names,
        lvls: level_params.clone(),
        intern,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(&ax.typ, type_root, &ctx, ixon_env, &mut cache)?;
      let name = resolve_name(
        match &meta.info {
          ConstantMetaInfo::Axio { name, .. } => name,
          _ => addr,
        },
        names,
      );
      Ok(vec![(
        self_id,
        KConst::Axio {
          name: M::meta_field(name),
          level_params: M::meta_field(level_params),
          is_unsafe: ax.is_unsafe,
          lvls: ax.lvls,
          ty: typ,
        },
      )])
    },

    IxonCI::Quot(q) => {
      let mut cache: ExprCache<M> = FxHashMap::default();
      let (level_params, arena, type_root) = match &meta.info {
        ConstantMetaInfo::Quot { lvls, arena, type_root, .. } => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        _ => (vec![], &DEFAULT_ARENA, 0),
      };
      let ctx = Ctx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        mut_ctx: vec![],
        arena,
        names,
        lvls: level_params.clone(),
        intern,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(&q.typ, type_root, &ctx, ixon_env, &mut cache)?;
      let name = resolve_name(
        match &meta.info {
          ConstantMetaInfo::Quot { name, .. } => name,
          _ => addr,
        },
        names,
      );
      Ok(vec![(
        self_id,
        KConst::Quot {
          name: M::meta_field(name),
          level_params: M::meta_field(level_params),
          kind: q.kind,
          lvls: q.lvls,
          ty: typ,
        },
      )])
    },

    IxonCI::Recr(rec) => ingress_recursor(
      rec,
      self_id.clone(),
      meta,
      ixon_env,
      names,
      name_to_addr,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id,
      intern,
    ),

    // Projections and Muts are handled in ingress_muts_block
    IxonCI::IPrj(_)
    | IxonCI::CPrj(_)
    | IxonCI::RPrj(_)
    | IxonCI::DPrj(_)
    | IxonCI::Muts(_) => Ok(vec![]),
  }
}

// ============================================================================
// Muts block ingress
// ============================================================================

#[allow(clippy::too_many_arguments)]
fn ingress_muts_inductive<M: KernelMode>(
  ind: &crate::ix::ixon::constant::Inductive,
  self_id: &KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  block_constant: &Constant,
  block_id: KId<M>,
  member_idx: u64,
  intern: &InternTable<M>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let (level_params, arena, type_root, all_addrs, ctor_addrs) = match &meta.info
  {
    ConstantMetaInfo::Indc { lvls, arena, type_root, all, ctors, .. } => (
      resolve_level_params(lvls, names),
      arena,
      *type_root,
      all.clone(),
      ctors.clone(),
    ),
    _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![]),
  };

  let mut cache: ExprCache<M> = FxHashMap::default();
  let mut_ctx = build_mut_ctx(meta, names, name_to_addr);
  let ctx = Ctx {
    sharing: &block_constant.sharing,
    refs: &block_constant.refs,
    univs: &block_constant.univs,
    mut_ctx,
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(&ind.typ, type_root, &ctx, ixon_env, &mut cache)?;
  let lean_all = resolve_all(&all_addrs, names, name_to_addr);
  let ctor_ids: Vec<KId<M>> = ctor_addrs
    .iter()
    .map(|a| {
      let n = resolve_name(a, names);
      let ca = name_to_addr
        .get(&n)
        .cloned()
        .unwrap_or_else(|| Address::from_blake3_hash(*n.get_hash()));
      KId::new(ca, M::meta_field(n))
    })
    .collect();

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Indc { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  let mut results = vec![(
    self_id.clone(),
    KConst::Indc {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params.clone()),
      lvls: ind.lvls,
      params: ind.params,
      indices: ind.indices,
      is_rec: ind.recr,
      is_refl: ind.refl,
      is_unsafe: ind.is_unsafe,
      nested: ind.nested,
      block: block_id,
      member_idx,
      ty: typ,
      ctors: ctor_ids.clone(),
      lean_all: M::meta_field(lean_all),
    },
  )];

  // Emit constructors
  for (cidx, ctor) in ind.ctors.iter().enumerate() {
    cache.clear();
    let ctor_id = match ctor_ids.get(cidx).cloned() {
      Some(id) => id,
      None => {
        return Err(format!("missing ctor_id for constructor index {cidx}"));
      },
    };

    let ctor_name =
      resolve_name(ctor_addrs.get(cidx).unwrap_or(&self_id.addr), names);
    let ctor_named = ixon_env.lookup_name(&ctor_name);
    let ctor_meta = ctor_named.as_ref().map(|n| &n.meta);

    let (ctor_lvl_params, ctor_arena, ctor_type_root) =
      match ctor_meta.map(|m| &m.info) {
        Some(ConstantMetaInfo::Ctor { lvls, arena, type_root, .. }) => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        _ => (level_params.clone(), &DEFAULT_ARENA, 0),
      };

    let ctor_ctx = Ctx {
      sharing: &block_constant.sharing,
      refs: &block_constant.refs,
      univs: &block_constant.univs,
      mut_ctx: ctx.mut_ctx.clone(),
      arena: ctor_arena,
      names,
      lvls: ctor_lvl_params.clone(),
      intern,
      synth_counter: Cell::new(0),
    };

    let ctor_typ =
      ingress_expr(&ctor.typ, ctor_type_root, &ctor_ctx, ixon_env, &mut cache)?;

    results.push((
      ctor_id,
      KConst::Ctor {
        name: M::meta_field(ctor_name),
        level_params: M::meta_field(ctor_lvl_params),
        is_unsafe: ctor.is_unsafe,
        lvls: ctor.lvls,
        induct: self_id.clone(),
        cidx: ctor.cidx,
        params: ctor.params,
        fields: ctor.fields,
        ty: ctor_typ,
      },
    ));
  }

  Ok(results)
}

#[allow(clippy::too_many_arguments)]
fn ingress_muts_block<M: KernelMode>(
  entry_name: &Name,
  entry_addr: &Address,
  all: &[Vec<Address>],
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &InternTable<M>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let block_id: KId<M> =
    KId::new(entry_addr.clone(), M::meta_field(entry_name.clone()));

  let block_constant = ixon_env.get_const(entry_addr).ok_or_else(|| {
    format!("missing Muts block constant {}", entry_addr.hex())
  })?;
  let members = match &block_constant.info {
    IxonCI::Muts(m) => m,
    _ => return Err(format!("constant at {} is not Muts", entry_addr.hex())),
  };

  let mut results: Vec<(KId<M>, KConst<M>)> = Vec::new();

  for (i, member) in members.iter().enumerate() {
    let primary_name_addr = all
      .get(i)
      .and_then(|cls| cls.first())
      .ok_or_else(|| format!("Muts block member {i} has no name in all"))?;
    let member_name = resolve_name(primary_name_addr, names);

    let member_named = ixon_env.lookup_name(&member_name).ok_or_else(|| {
      format!("Muts member '{member_name}' not found in named entries")
    })?;
    let member_addr = &member_named.addr;
    let member_meta = &member_named.meta;

    let self_id: KId<M> =
      KId::new(member_addr.clone(), M::meta_field(member_name.clone()));

    match member {
      IxonMutConst::Indc(ind) => {
        results.extend(ingress_muts_inductive(
          ind,
          &self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant,
          block_id.clone(),
          i as u64,
          intern,
        )?);
      },
      IxonMutConst::Recr(rec) => {
        results.extend(ingress_recursor(
          rec,
          self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          intern,
        )?);
      },
      IxonMutConst::Defn(def) => {
        results.extend(ingress_defn(
          def,
          self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          intern,
        )?);
      },
    }
  }

  Ok(results)
}

// ============================================================================
// Lightweight LeanExpr → KExpr ingress (compile-side)
// ============================================================================

use super::mode::Anon;
use crate::ix::env::{
  Expr as LeanExpr, ExprData as LeanExprData, Level, LevelData,
};

/// Convert a Lean Level to KUniv<Anon>, mapping named params to positional indices.
pub fn lean_level_to_kuniv(lvl: &Level, param_names: &[Name]) -> KUniv<Anon> {
  match lvl.as_data() {
    LevelData::Succ(l, _) => KUniv::succ(lean_level_to_kuniv(l, param_names)),
    LevelData::Max(a, b, _) => KUniv::max(
      lean_level_to_kuniv(a, param_names),
      lean_level_to_kuniv(b, param_names),
    ),
    LevelData::Imax(a, b, _) => KUniv::imax(
      lean_level_to_kuniv(a, param_names),
      lean_level_to_kuniv(b, param_names),
    ),
    LevelData::Param(name, _) => {
      let idx = param_names.iter().position(|n| n == name).unwrap_or(0) as u64;
      KUniv::param(idx, ())
    },
    LevelData::Zero(_) | LevelData::Mvar(_, _) => KUniv::zero(),
  }
}

/// Resolve a Lean Name to an Address, using real Ixon address if available.
///
/// Checks `name_to_ixon_addr` first (real compiled address), falls back to
/// `Address::from_blake3_hash(*name.get_hash())` for constants not yet compiled.
pub fn resolve_lean_name_addr(
  name: &Name,
  name_to_ixon_addr: Option<&dashmap::DashMap<Name, Address>>,
  aux_n2a: Option<&dashmap::DashMap<Name, Address>>,
) -> Address {
  if let Some(map) = name_to_ixon_addr
    && let Some(entry) = map.get(name)
  {
    return entry.value().clone();
  }
  if let Some(map) = aux_n2a
    && let Some(entry) = map.get(name)
  {
    return entry.value().clone();
  }
  Address::from_blake3_hash(*name.get_hash())
}

/// Convert a LeanExpr to KExpr<Anon>.
///
/// `param_names` provides the positional mapping for universe level params.
/// `name_to_ixon_addr` maps Lean names to real Ixon addresses for already-compiled
/// constants. Falls back to name hash for constants not yet compiled.
pub fn lean_expr_to_zexpr(
  expr: &LeanExpr,
  param_names: &[Name],
  intern: &InternTable<Anon>,
  name_to_ixon_addr: Option<&dashmap::DashMap<Name, Address>>,
  aux_n2a: Option<&dashmap::DashMap<Name, Address>>,
) -> KExpr<Anon> {
  let e = lean_expr_to_zexpr_raw(
    expr,
    param_names,
    intern,
    name_to_ixon_addr,
    aux_n2a,
  );
  intern.intern_expr(e)
}

fn lean_expr_to_zexpr_raw(
  expr: &LeanExpr,
  pn: &[Name],
  intern: &InternTable<Anon>,
  n2a: Option<&dashmap::DashMap<Name, Address>>,
  aux_n2a: Option<&dashmap::DashMap<Name, Address>>,
) -> KExpr<Anon> {
  match expr.as_data() {
    LeanExprData::Bvar(idx, _) => KExpr::var(idx.to_u64().unwrap_or(0), ()),
    LeanExprData::Sort(lvl, _) => KExpr::sort(lean_level_to_kuniv(lvl, pn)),
    LeanExprData::Const(name, us, _) => {
      let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
      let zid = KId::new(addr, ());
      let zus: Box<[KUniv<Anon>]> =
        us.iter().map(|u| lean_level_to_kuniv(u, pn)).collect();
      KExpr::cnst(zid, zus)
    },
    LeanExprData::App(f, a, _) => {
      let zf = lean_expr_to_zexpr(f, pn, intern, n2a, aux_n2a);
      let za = lean_expr_to_zexpr(a, pn, intern, n2a, aux_n2a);
      KExpr::app(zf, za)
    },
    LeanExprData::ForallE(_, dom, body, _, _) => {
      let zd = lean_expr_to_zexpr(dom, pn, intern, n2a, aux_n2a);
      let zb = lean_expr_to_zexpr(body, pn, intern, n2a, aux_n2a);
      KExpr::all((), (), zd, zb)
    },
    LeanExprData::Lam(_, dom, body, _, _) => {
      let zd = lean_expr_to_zexpr(dom, pn, intern, n2a, aux_n2a);
      let zb = lean_expr_to_zexpr(body, pn, intern, n2a, aux_n2a);
      KExpr::lam((), (), zd, zb)
    },
    LeanExprData::LetE(_, ty, val, body, nd, _) => {
      let zt = lean_expr_to_zexpr(ty, pn, intern, n2a, aux_n2a);
      let zv = lean_expr_to_zexpr(val, pn, intern, n2a, aux_n2a);
      let zb = lean_expr_to_zexpr(body, pn, intern, n2a, aux_n2a);
      KExpr::let_((), zt, zv, zb, *nd)
    },
    LeanExprData::Proj(name, idx, e, _) => {
      let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
      let zid = KId::new(addr, ());
      let ze = lean_expr_to_zexpr(e, pn, intern, n2a, aux_n2a);
      KExpr::prj(zid, idx.to_u64().unwrap_or(0), ze)
    },
    LeanExprData::Lit(lit, _) => {
      use crate::ix::env::Literal;
      match lit {
        Literal::NatVal(n) => {
          let addr = Address::hash(&n.to_u64().unwrap_or(0).to_le_bytes());
          KExpr::nat(n.clone(), addr)
        },
        Literal::StrVal(s) => {
          let addr = Address::hash(s.as_bytes());
          KExpr::str(s.clone(), addr)
        },
      }
    },
    // FVar, MVar, Mdata — shouldn't appear in elaborated kernel terms
    _ => KExpr::sort(KUniv::zero()),
  }
}

/// Name → Address for KId construction from Lean Names.
pub fn lean_name_to_addr(name: &Name) -> Address {
  Address::from_blake3_hash(*name.get_hash())
}

/// Incrementally ingress a set of just-compiled constants into a KEnv.
///
/// Called after each block compiles in the topological compilation loop.
/// `names` are the Lean names of constants in the block. For each name,
/// we look up its Ixon address and constant, convert to KConst, and insert.
/// Build lookup tables from the ixon env for use with `ingress_compiled_names`.
/// Call once at compile start, then pass to each incremental ingress call.
pub fn build_ingress_lookups(
  ixon_env: &IxonEnv,
) -> (FxHashMap<Address, Name>, FxHashMap<Name, Address>) {
  let mut name_map: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in ixon_env.names.iter() {
    name_map.insert(entry.key().clone(), entry.value().clone());
  }
  let mut addr_map: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in ixon_env.named.iter() {
    addr_map.insert(entry.key().clone(), entry.value().addr.clone());
  }
  (name_map, addr_map)
}

pub fn ingress_compiled_names(
  names: &[Name],
  ixon_env: &IxonEnv,
  zenv: &KEnv<Anon>,
  intern: &InternTable<Anon>,
  name_map: &FxHashMap<Address, Name>,
  addr_map: &FxHashMap<Name, Address>,
) {
  for name in names {
    let named = match ixon_env.named.get(name) {
      Some(entry) => entry.value().clone(),
      None => continue,
    };
    let constant = match ixon_env.get_const(&named.addr) {
      Some(c) => c,
      None => continue,
    };

    // Check if this is a Muts entry (mutual block) — handle differently
    if matches!(&named.meta.info, ConstantMetaInfo::Muts { .. }) {
      if let ConstantMetaInfo::Muts { all } = &named.meta.info
        && let Ok(entries) = ingress_muts_block(
          name,
          &named.addr,
          all,
          ixon_env,
          name_map,
          addr_map,
          intern,
        )
      {
        let block_id = entries.first().and_then(|(_, zc)| match zc {
          KConst::Defn { block, .. }
          | KConst::Recr { block, .. }
          | KConst::Indc { block, .. } => Some(block.clone()),
          _ => None,
        });
        let member_ids: Vec<KId<Anon>> =
          entries.iter().map(|(id, _)| id.clone()).collect();
        if let Some(bid) = block_id {
          zenv.blocks.insert(bid, member_ids);
        }
        for (id, zc) in entries {
          zenv.insert(id, zc);
        }
      }
      continue;
    }

    // Standalone constant (or member of a mutual block handled via Muts)
    // Skip projection wrappers — they're handled by the Muts path
    match &constant.info {
      IxonCI::IPrj(_) | IxonCI::CPrj(_) | IxonCI::RPrj(_) | IxonCI::DPrj(_) => {
        continue;
      },
      _ => {},
    }

    if let Ok(entries) = ingress_standalone(
      name,
      &named.addr,
      &constant,
      &named.meta,
      ixon_env,
      name_map,
      addr_map,
      intern,
    ) {
      for (id, zc) in entries {
        zenv.insert(id, zc);
      }
    }
  }
}

// ============================================================================
// Top-level entry point
// ============================================================================

/// Convert an Ixon environment to a zero kernel environment.
pub fn ixon_to_zenv<M: KernelMode>(
  ixon_env: &IxonEnv,
) -> Result<(KEnv<M>, InternTable<M>), String> {
  let intern = InternTable::new();

  // Build lookup tables
  let mut names: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in ixon_env.names.iter() {
    names.insert(entry.key().clone(), entry.value().clone());
  }

  let mut name_to_addr: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in ixon_env.named.iter() {
    name_to_addr.insert(entry.key().clone(), entry.value().addr.clone());
  }

  // Partition named entries into standalone vs Muts
  let mut standalone: Vec<(Name, crate::ix::ixon::env::Named)> = Vec::new();
  let mut muts: Vec<(Name, crate::ix::ixon::env::Named)> = Vec::new();

  for entry in ixon_env.named.iter() {
    let const_name = entry.key().clone();
    let named = entry.value().clone();
    match &named.meta.info {
      ConstantMetaInfo::Muts { .. } => {
        muts.push((const_name, named));
      },
      ConstantMetaInfo::Indc { .. }
      | ConstantMetaInfo::Ctor { .. }
      | ConstantMetaInfo::Rec { .. } => {
        if let Some(c) = ixon_env.get_const(&named.addr) {
          match &c.info {
            IxonCI::IPrj(_)
            | IxonCI::CPrj(_)
            | IxonCI::RPrj(_)
            | IxonCI::DPrj(_) => {},
            _ => standalone.push((const_name, named)),
          }
        }
      },
      ConstantMetaInfo::Def { .. } => {
        if let Some(c) = ixon_env.get_const(&named.addr) {
          match &c.info {
            IxonCI::DPrj(_) => {},
            _ => standalone.push((const_name, named)),
          }
        }
      },
      _ => standalone.push((const_name, named)),
    }
  }

  // Pass 1: Parallel standalone constants
  let standalone_results: Result<Vec<Vec<(KId<M>, KConst<M>)>>, String> =
    standalone
      .into_par_iter()
      .map(|(const_name, named)| {
        let constant = match ixon_env.get_const(&named.addr) {
          Some(c) => c,
          None => return Ok(vec![]),
        };
        ingress_standalone(
          &const_name,
          &named.addr,
          &constant,
          &named.meta,
          ixon_env,
          &names,
          &name_to_addr,
          &intern,
        )
        .map_err(|e| format!("{const_name}: {e}"))
      })
      .collect();

  // Pass 2: Parallel Muts blocks
  let muts_results: Result<Vec<Vec<(KId<M>, KConst<M>)>>, String> = muts
    .into_par_iter()
    .map(|(entry_name, named)| {
      let all = match &named.meta.info {
        ConstantMetaInfo::Muts { all } => all,
        _ => return Ok(vec![]),
      };
      ingress_muts_block(
        &entry_name,
        &named.addr,
        all,
        ixon_env,
        &names,
        &name_to_addr,
        &intern,
      )
      .map_err(|e| format!("{entry_name}: {e}"))
    })
    .collect();

  // Assemble environment
  let zenv: KEnv<M> = KEnv::new();

  for entries in standalone_results? {
    for (id, zc) in entries {
      zenv.blocks.entry(id.clone()).or_default().push(id.clone());
      zenv.insert(id, zc);
    }
  }

  for entries in muts_results? {
    let block_id = entries.first().and_then(|(_, zc)| match zc {
      KConst::Defn { block, .. }
      | KConst::Recr { block, .. }
      | KConst::Indc { block, .. } => Some(block.clone()),
      _ => None,
    });
    let member_ids: Vec<KId<M>> =
      entries.iter().map(|(id, _)| id.clone()).collect();
    if let Some(bid) = block_id {
      zenv.blocks.insert(bid, member_ids);
    }
    for (id, zc) in entries {
      zenv.insert(id, zc);
    }
  }

  Ok((zenv, intern))
}
