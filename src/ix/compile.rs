use indexmap::IndexSet;
use itertools::Itertools;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use std::{
  cmp::Ordering,
  collections::HashMap,
  hash::{Hash, Hasher},
  sync::{Arc, Mutex},
};

use crate::{
  cons_list::ConsList,
  ix::address::{Address, MetaAddress},
  ix::env::{
    AxiomVal, ConstantInfo, ConstantVal, ConstructorVal,
    DataValue as LeanDataValue, DefinitionSafety, DefinitionVal, Env, Expr,
    ExprData, InductiveVal, Level, LevelData, Literal, Name, NameData,
    OpaqueVal, QuotVal, RecursorRule, RecursorVal, ReducibilityHints,
    SourceInfo as LeanSourceInfo, Substring as LeanSubstring,
    Syntax as LeanSyntax, SyntaxPreresolved, TheoremVal,
  },
  ix::graph::{NameSet, RefMap},
  ix::ixon::{
    self, Axiom, BuiltIn, Constructor, DataValue, DefKind, Definition,
    Inductive, Ixon, Metadata, Metadatum, Preresolved, Quotient, Recursor,
    Serialize, SourceInfo, Substring, Syntax,
  },
  ix::mutual::{Def, Ind, MutConst, MutCtx, Rec},
  ix::store::{Store, StoreError},
  ix::strong_ordering::SOrder,
  lean::nat::Nat,
};

#[derive(Default)]
#[allow(clippy::type_complexity)]
pub struct CompileState {
  pub const_cache: FxHashMap<Name, MetaAddress>,
  pub expr_cache: FxHashMap<Expr, MetaAddress>,
  pub univ_cache: FxHashMap<Level, MetaAddress>,
  pub name_cache: FxHashMap<Name, Address>,
  pub const_cmp: FxHashMap<(Name, Name), Ordering>,
}

#[derive(Debug)]
pub enum CompileError {
  StoreError(StoreError),
  Todo,
}

pub type CompileResult =
  Result<Arc<FxHashMap<Name, MetaAddress>>, CompileError>;

pub type Consts = Arc<FxHashMap<Name, MetaAddress>>;

pub fn store_ixon(ixon: &Ixon) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  ixon.put(&mut bytes);
  Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn store_string(str: &str) -> Result<Address, CompileError> {
  Store::write(str.as_bytes()).map_err(CompileError::StoreError)
}

pub fn store_nat(nat: &Nat) -> Result<Address, CompileError> {
  Store::write(&nat.to_le_bytes()).map_err(CompileError::StoreError)
}

pub fn store_serialize<A: Serialize>(a: &A) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  a.put(&mut bytes);
  Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn store_meta(x: Metadata) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  x.put(&mut bytes);
  Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn compile_name(
  name: Name,
  stt: &mut CompileState,
) -> Result<Address, CompileError> {
  if let Some(cached) = stt.name_cache.get(&name) {
    Ok(cached.clone())
  } else {
    let addr = match name.as_data() {
      NameData::Anonymous => store_ixon(&Ixon::NAnon)?,
      NameData::Str(n, s, _) => {
        let n2 = compile_name(n.clone(), stt)?;
        let s2 = store_string(s)?;
        store_ixon(&Ixon::NStr(n2, s2))?
      },
      NameData::Num(n, i, _) => {
        let n_ = compile_name(n.clone(), stt)?;
        let s_ = store_nat(i)?;
        store_ixon(&Ixon::NNum(n_, s_))?
      },
    };
    stt.name_cache.insert(name, addr.clone());
    Ok(addr)
  }
}

pub fn compile_level(
  level: &Level,
  univs: ConsList<Name>,
  stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
  if let Some(cached) = stt.univ_cache.get(level) {
    Ok(cached.clone())
  } else {
    let (data_ixon, meta_ixon) = match level.as_data() {
      LevelData::Zero => (Ixon::UZero, Ixon::Meta(Metadata::default())),
      LevelData::Succ(x) => {
        let MetaAddress { data, meta } = compile_level(x, univs, stt)?;
        let nodes = vec![Metadatum::Link(meta)];
        (Ixon::USucc(data), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Max(x, y) => {
        let MetaAddress { data: data_x, meta: meta_x } =
          compile_level(x, univs.clone(), stt)?;
        let MetaAddress { data: data_y, meta: meta_y } =
          compile_level(y, univs, stt)?;
        let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
        (Ixon::UMax(data_x, data_y), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Imax(x, y) => {
        let MetaAddress { data: data_x, meta: meta_x } =
          compile_level(x, univs.clone(), stt)?;
        let MetaAddress { data: data_y, meta: meta_y } =
          compile_level(y, univs, stt)?;
        let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
        (Ixon::UIMax(data_x, data_y), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Param(n) => match univs.index_of(n) {
        Some(i) => {
          let data = Ixon::UVar(Nat::from_le_bytes(&i.to_le_bytes()));
          let n_addr = compile_name(n.clone(), stt)?;
          let nodes = vec![Metadatum::Link(n_addr)];
          (data, Ixon::Meta(Metadata { nodes }))
        },
        None => return Err(CompileError::Todo),
      },
      LevelData::Mvar(_) => return Err(CompileError::Todo),
    };
    let data = store_ixon(&data_ixon)?;
    let meta = store_ixon(&meta_ixon)?;
    let address = MetaAddress { data, meta };
    stt.univ_cache.insert(level.clone(), address.clone());
    Ok(address)
  }
}

pub fn compare_level(
  x_ctx: ConsList<Name>,
  y_ctx: ConsList<Name>,
  x: &Level,
  y: &Level,
) -> Result<SOrder, CompileError> {
  match (x.as_data(), y.as_data()) {
    (LevelData::Mvar(_), _) => Err(CompileError::Todo),
    (_, LevelData::Mvar(_)) => Err(CompileError::Todo),
    (LevelData::Zero, LevelData::Zero) => Ok(SOrder::eq(true)),
    (LevelData::Zero, _) => Ok(SOrder::lt(true)),
    (_, LevelData::Zero) => Ok(SOrder::gt(true)),
    (LevelData::Succ(x), LevelData::Succ(y)) => {
      compare_level(x_ctx.clone(), y_ctx.clone(), x, y)
    },
    (LevelData::Succ(_), _) => Ok(SOrder::lt(true)),
    (_, LevelData::Succ(_)) => Ok(SOrder::gt(true)),
    (LevelData::Max(xl, xr), LevelData::Max(yl, yr)) => SOrder::try_cmp(
      compare_level(x_ctx.clone(), y_ctx.clone(), xl, yl)?,
      || compare_level(x_ctx, y_ctx, xr, yr),
    ),
    (LevelData::Max(_, _), _) => Ok(SOrder::lt(true)),
    (_, LevelData::Max(_, _)) => Ok(SOrder::gt(true)),
    (LevelData::Imax(xl, xr), LevelData::Imax(yl, yr)) => SOrder::try_cmp(
      compare_level(x_ctx.clone(), y_ctx.clone(), xl, yl)?,
      || compare_level(x_ctx, y_ctx, xr, yr),
    ),
    (LevelData::Imax(_, _), _) => Ok(SOrder::lt(true)),
    (_, LevelData::Imax(_, _)) => Ok(SOrder::gt(true)),
    (LevelData::Param(x), LevelData::Param(y)) => {
      match (x_ctx.index_of(x), y_ctx.index_of(y)) {
        (Some(xi), Some(yi)) => {
          Ok(SOrder { strong: true, ordering: xi.cmp(&yi) })
        },
        (None, _) => Err(CompileError::Todo),
        (_, None) => Err(CompileError::Todo),
      }
    },
  }
}

pub fn compile_substring(
  substring: &LeanSubstring,
) -> Result<Substring, CompileError> {
  let LeanSubstring { str, start_pos, stop_pos } = substring;
  let str = store_string(str)?;
  Ok(Substring {
    str,
    start_pos: start_pos.clone(),
    stop_pos: stop_pos.clone(),
  })
}

pub fn compile_preresolved(
  preresolved: &SyntaxPreresolved,
  stt: &mut CompileState,
) -> Result<Preresolved, CompileError> {
  match preresolved {
    SyntaxPreresolved::Namespace(ns) => {
      Ok(Preresolved::Namespace(compile_name(ns.clone(), stt)?))
    },
    SyntaxPreresolved::Decl(n, fs) => {
      let fs = fs.iter().map(|s| store_string(s)).try_collect()?;
      Ok(Preresolved::Decl(compile_name(n.clone(), stt)?, fs))
    },
  }
}

pub fn compile_source_info(
  info: &LeanSourceInfo,
) -> Result<SourceInfo, CompileError> {
  match info {
    LeanSourceInfo::Original(l, p, t, e) => {
      let l = compile_substring(l)?;
      let t = compile_substring(t)?;
      Ok(SourceInfo::Original(l, p.clone(), t, e.clone()))
    },
    LeanSourceInfo::Synthetic(p, e, c) => {
      Ok(SourceInfo::Synthetic(p.clone(), e.clone(), *c))
    },
    LeanSourceInfo::None => Ok(SourceInfo::None),
  }
}

pub fn compile_syntax(
  syn: &LeanSyntax,
  stt: &mut CompileState,
) -> Result<Syntax, CompileError> {
  match syn {
    LeanSyntax::Missing => Ok(Syntax::Missing),
    LeanSyntax::Node(info, kind, args) => {
      let info = compile_source_info(info)?;
      let kind = compile_name(kind.clone(), stt)?;
      let args = args
        .iter()
        .map(|s| store_serialize(&compile_syntax(s, stt)?))
        .try_collect()?;
      Ok(Syntax::Node(info, kind, args))
    },
    LeanSyntax::Atom(info, val) => {
      let info = compile_source_info(info)?;
      let val = store_string(val)?;
      Ok(Syntax::Atom(info, val))
    },
    LeanSyntax::Ident(info, raw_val, val, preresolved) => {
      let info = compile_source_info(info)?;
      let raw_val = compile_substring(raw_val)?;
      let val = compile_name(val.clone(), stt)?;
      let preresolved = preresolved
        .iter()
        .map(|pre| compile_preresolved(pre, stt))
        .try_collect()?;
      Ok(Syntax::Ident(info, raw_val, val, preresolved))
    },
  }
}

pub fn compile_data_value(
  data_value: &LeanDataValue,
  stt: &mut CompileState,
) -> Result<DataValue, CompileError> {
  match data_value {
    LeanDataValue::OfString(s) => Ok(DataValue::OfString(store_string(s)?)),
    LeanDataValue::OfBool(b) => Ok(DataValue::OfBool(*b)),
    LeanDataValue::OfName(n) => {
      Ok(DataValue::OfName(compile_name(n.clone(), stt)?))
    },
    LeanDataValue::OfNat(i) => Ok(DataValue::OfNat(store_nat(i)?)),
    LeanDataValue::OfInt(i) => Ok(DataValue::OfInt(store_serialize(i)?)),
    LeanDataValue::OfSyntax(s) => {
      Ok(DataValue::OfSyntax(store_serialize(&compile_syntax(s, stt)?)?))
    },
  }
}

pub fn compile_kv_maps(
  maps: &ConsList<Vec<(Name, LeanDataValue)>>,
  stt: &mut CompileState,
) -> Result<Address, CompileError> {
  let nodes = maps
    .iter()
    .map(|kv_map| {
      let mut kv = Vec::with_capacity(kv_map.len());
      for (name, data_value) in kv_map {
        let n = compile_name(name.clone(), stt)?;
        let d = compile_data_value(data_value, stt)?;
        kv.push((n, d));
      }
      Ok(Metadatum::KVMap(kv))
    })
    .try_collect()?;
  store_ixon(&Ixon::Meta(Metadata { nodes }))
}
pub fn compile_ref(
  comms: Consts,
  consts: Consts,
  name: Name,
) -> Result<MetaAddress, CompileError> {
  if let Some(builtin) = BuiltIn::from_name(&name) {
    Ok(MetaAddress {
      data: store_ixon(&Ixon::Prim(builtin))?,
      meta: store_ixon(&Ixon::Meta(Metadata { nodes: vec![] }))?,
    })
  } else if let Some(addr) = comms.as_ref().get(&name) {
    Ok(addr.clone())
  } else if let Some(addr) = consts.as_ref().get(&name) {
    Ok(addr.clone())
  } else {
    Err(CompileError::Todo)
  }
}

pub fn compile_expr_inner(
  kvs: &ConsList<Vec<(Name, LeanDataValue)>>,
  expr: &Expr,
  univ_ctx: ConsList<Name>,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Ixon, Ixon), CompileError> {
  match expr.as_data() {
    ExprData::Mdata(kv, x, _) => compile_expr_inner(
      &kvs.cons(kv.clone()),
      x,
      univ_ctx,
      mut_ctx,
      comms,
      consts,
      stt,
    ),
    ExprData::Bvar(idx, _) => {
      let data = Ixon::EVar(idx.clone());
      let md = compile_kv_maps(kvs, stt)?;
      let nodes = vec![Metadatum::Link(md)];
      let meta = Ixon::Meta(Metadata { nodes });
      Ok((data, meta))
    },
    ExprData::Sort(univ, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let MetaAddress { data: udata, meta: umeta } =
        compile_level(univ, univ_ctx, stt)?;
      let data = Ixon::ESort(udata);
      let nodes = vec![Metadatum::Link(md), Metadatum::Link(umeta)];
      let meta = Ixon::Meta(Metadata { nodes });
      Ok((data, meta))
    },
    ExprData::Const(name, lvls, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let n = compile_name(name.clone(), stt)?;
      let mut us_data = Vec::with_capacity(lvls.len());
      let mut us_meta = Vec::with_capacity(lvls.len());
      for u in lvls {
        let MetaAddress { data, meta } =
          compile_level(u, univ_ctx.clone(), stt)?;
        us_data.push(data);
        us_meta.push(meta);
      }
      match mut_ctx.as_ref().get(name) {
        Some(idx) => {
          let data = Ixon::ERec(idx.clone(), us_data);
          let meta = Ixon::Meta(Metadata {
            nodes: vec![
              Metadatum::Link(md),
              Metadatum::Link(n),
              Metadatum::Links(us_meta),
            ],
          });
          Ok((data, meta))
        },
        None => {
          let addr = compile_ref(comms, consts, name.clone())?;
          let data = Ixon::ERef(addr.data.clone(), us_data);
          let meta = Ixon::Meta(Metadata {
            nodes: vec![
              Metadatum::Link(md),
              Metadatum::Link(n),
              Metadatum::Link(addr.meta.clone()),
              Metadatum::Links(us_meta),
            ],
          });
          Ok((data, meta))
        },
      }
    },
    ExprData::App(f, a, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let f = compile_expr(
        f,
        univ_ctx.clone(),
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        stt,
      )?;
      let a = compile_expr(a, univ_ctx, mut_ctx, comms, consts, stt)?;
      let data = Ixon::EApp(f.data, a.data);
      let meta = Ixon::Meta(Metadata {
        nodes: vec![
          Metadatum::Link(md),
          Metadatum::Link(f.meta),
          Metadatum::Link(a.meta),
        ],
      });
      Ok((data, meta))
    },
    ExprData::Lam(n, t, b, i, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let n = compile_name(n.clone(), stt)?;
      let t = compile_expr(
        t,
        univ_ctx.clone(),
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        stt,
      )?;
      let b = compile_expr(b, univ_ctx, mut_ctx, comms, consts, stt)?;
      let data = Ixon::ELam(t.data, b.data);
      let meta = Ixon::Meta(Metadata {
        nodes: vec![
          Metadatum::Link(md),
          Metadatum::Link(n),
          Metadatum::Info(i.clone()),
          Metadatum::Link(t.meta),
          Metadatum::Link(b.meta),
        ],
      });
      Ok((data, meta))
    },
    ExprData::ForallE(n, t, b, i, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let n = compile_name(n.clone(), stt)?;
      let t = compile_expr(
        t,
        univ_ctx.clone(),
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        stt,
      )?;
      let b = compile_expr(b, univ_ctx, mut_ctx, comms, consts, stt)?;
      let data = Ixon::EAll(t.data, b.data);
      let meta = Ixon::Meta(Metadata {
        nodes: vec![
          Metadatum::Link(md),
          Metadatum::Link(n),
          Metadatum::Info(i.clone()),
          Metadatum::Link(t.meta),
          Metadatum::Link(b.meta),
        ],
      });
      Ok((data, meta))
    },
    ExprData::LetE(n, t, v, b, nd, _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let n = compile_name(n.clone(), stt)?;
      let t = compile_expr(
        t,
        univ_ctx.clone(),
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        stt,
      )?;
      let v = compile_expr(
        v,
        univ_ctx.clone(),
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        stt,
      )?;
      let b = compile_expr(b, univ_ctx, mut_ctx, comms, consts, stt)?;
      let data = Ixon::ELet(*nd, t.data, v.data, b.data);
      let meta = Ixon::Meta(Metadata {
        nodes: vec![
          Metadatum::Link(md),
          Metadatum::Link(n),
          Metadatum::Link(t.meta),
          Metadatum::Link(v.meta),
          Metadatum::Link(b.meta),
        ],
      });
      Ok((data, meta))
    },
    ExprData::Lit(Literal::NatVal(n), _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let data = Ixon::ENat(store_nat(n)?);
      let meta = Ixon::Meta(Metadata { nodes: vec![Metadatum::Link(md)] });
      Ok((data, meta))
    },
    ExprData::Lit(Literal::StrVal(s), _) => {
      let md = compile_kv_maps(kvs, stt)?;
      let data = Ixon::EStr(store_string(s)?);
      let meta = Ixon::Meta(Metadata { nodes: vec![Metadatum::Link(md)] });
      Ok((data, meta))
    },
    ExprData::Proj(tn, i, s, _) => {
      let md = compile_kv_maps(kvs, stt)?;

      let n = compile_name(tn.clone(), stt)?;
      let t = match consts.as_ref().get(tn) {
        Some(addr) => addr.clone(),
        None => return Err(CompileError::Todo),
      };
      let s =
        compile_expr(s, univ_ctx, mut_ctx, comms.clone(), consts.clone(), stt)?;
      let data = Ixon::EPrj(t.data, i.clone(), s.data);
      let meta = Ixon::Meta(Metadata {
        nodes: vec![
          Metadatum::Link(md),
          Metadatum::Link(n),
          Metadatum::Link(t.meta),
          Metadatum::Link(s.meta),
        ],
      });
      Ok((data, meta))
    },
    ExprData::Fvar(..) | ExprData::Mvar(..) => Err(CompileError::Todo),
  }
}

fn compile_expr(
  expr: &Expr,
  univ_ctx: ConsList<Name>,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
  if let Some(cached) = stt.expr_cache.get(expr) {
    Ok(cached.clone())
  } else {
    let (data_ixon, meta_ixon) = compile_expr_inner(
      &ConsList::Nil,
      expr,
      univ_ctx,
      mut_ctx,
      comms,
      consts,
      stt,
    )?;
    let data = store_ixon(&data_ixon)?;
    let meta = store_ixon(&meta_ixon)?;
    let meta_address = MetaAddress { data, meta };
    stt.expr_cache.insert(expr.clone(), meta_address.clone());
    Ok(meta_address)
  }
}

pub fn compare_expr(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x_lvls: ConsList<Name>,
  y_lvls: ConsList<Name>,
  x: &Expr,
  y: &Expr,
) -> Result<SOrder, CompileError> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) => Err(CompileError::Todo),
    (_, ExprData::Mvar(..)) => Err(CompileError::Todo),
    (ExprData::Fvar(..), _) => Err(CompileError::Todo),
    (_, ExprData::Fvar(..)) => Err(CompileError::Todo),
    (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
      compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, x, y)
    },
    (ExprData::Mdata(_, x, _), _) => {
      compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, x, y)
    },
    (_, ExprData::Mdata(_, y, _)) => {
      compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, x, y)
    },
    (ExprData::Bvar(x, _), ExprData::Bvar(y, _)) => {
      Ok(SOrder { strong: true, ordering: x.cmp(y) })
    },
    (ExprData::Bvar(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::Bvar(..)) => Ok(SOrder::gt(true)),
    (ExprData::Sort(x, _), ExprData::Sort(y, _)) => {
      compare_level(x_lvls, y_lvls, x, y)
    },
    (ExprData::Sort(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::Sort(..)) => Ok(SOrder::gt(true)),
    (ExprData::Const(x, xls, _), ExprData::Const(y, yls, _)) => {
      let us = SOrder::try_zip(
        |a, b| compare_level(x_lvls.clone(), y_lvls.clone(), a, b),
        xls,
        yls,
      )?;
      if us.ordering != Ordering::Equal {
        Ok(us)
      } else if x == y {
        Ok(SOrder::eq(true))
      } else {
        match (mut_ctx.as_ref().get(x), mut_ctx.as_ref().get(y)) {
          (Some(nx), Some(ny)) => {
            Ok(SOrder { strong: false, ordering: nx.cmp(ny) })
          },
          (Some(..), _) => Ok(SOrder::lt(true)),
          (None, Some(..)) => Ok(SOrder::gt(true)),
          (None, None) => {
            let xa = compile_ref(comms.clone(), consts.clone(), x.clone())?;
            let ya = compile_ref(comms.clone(), consts.clone(), y.clone())?;
            Ok(SOrder { strong: true, ordering: xa.data.cmp(&ya.data) })
          },
        }
      }
    },

    (ExprData::Const(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::Const(..)) => Ok(SOrder::gt(true)),
    (ExprData::App(xl, xr, _), ExprData::App(yl, yr, _)) => SOrder::try_cmp(
      compare_expr(
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        x_lvls.clone(),
        y_lvls.clone(),
        xl,
        yl,
      )?,
      || compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, xr, yr),
    ),
    (ExprData::App(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::App(..)) => Ok(SOrder::gt(true)),
    (ExprData::Lam(_, xt, xb, _, _), ExprData::Lam(_, yt, yb, _, _)) => {
      SOrder::try_cmp(
        compare_expr(
          mut_ctx.clone(),
          comms.clone(),
          consts.clone(),
          x_lvls.clone(),
          y_lvls.clone(),
          xt,
          yt,
        )?,
        || compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, xb, yb),
      )
    },
    (ExprData::Lam(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::Lam(..)) => Ok(SOrder::gt(true)),
    (
      ExprData::ForallE(_, xt, xb, _, _),
      ExprData::ForallE(_, yt, yb, _, _),
    ) => SOrder::try_cmp(
      compare_expr(
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        x_lvls.clone(),
        y_lvls.clone(),
        xt,
        yt,
      )?,
      || compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, xb, yb),
    ),
    (ExprData::ForallE(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::ForallE(..)) => Ok(SOrder::gt(true)),
    (
      ExprData::LetE(_, xt, xv, xb, _, _),
      ExprData::LetE(_, yt, yv, yb, _, _),
    ) => SOrder::try_zip(
      |a, b| {
        compare_expr(
          mut_ctx.clone(),
          comms.clone(),
          consts.clone(),
          x_lvls.clone(),
          y_lvls.clone(),
          a,
          b,
        )
      },
      &[xt, xv, xb],
      &[yt, yv, yb],
    ),
    (ExprData::LetE(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::LetE(..)) => Ok(SOrder::gt(true)),
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => {
      Ok(SOrder { strong: true, ordering: x.cmp(y) })
    },
    (ExprData::Lit(..), _) => Ok(SOrder::lt(true)),
    (_, ExprData::Lit(..)) => Ok(SOrder::gt(true)),
    (ExprData::Proj(tnx, ix, tx, _), ExprData::Proj(tny, iy, ty, _)) => {
      let tn = match (mut_ctx.as_ref().get(tnx), mut_ctx.as_ref().get(tny)) {
        (Some(nx), Some(ny)) => {
          Ok(SOrder { strong: false, ordering: nx.cmp(ny) })
        },
        (Some(..), _) => Ok(SOrder::lt(true)),
        (None, Some(..)) => Ok(SOrder::gt(true)),
        (None, None) => {
          let xa = compile_ref(comms.clone(), consts.clone(), tnx.clone())?;
          let ya = compile_ref(comms.clone(), consts.clone(), tny.clone())?;
          Ok(SOrder { strong: true, ordering: xa.data.cmp(&ya.data) })
        },
      }?;
      SOrder::try_cmp(tn, || {
        SOrder::try_cmp(SOrder { strong: true, ordering: ix.cmp(iy) }, || {
          compare_expr(mut_ctx, comms, consts, x_lvls, y_lvls, tx, ty)
        })
      })
    },
  }
}
pub fn compile_defn(
  def: Def,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Definition, Metadata), CompileError> {
  let univ_ctx = ConsList::from_iterator(def.level_params.iter().cloned());
  let n = compile_name(def.name.clone(), stt)?;
  let ls = def
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &def.typ,
    univ_ctx.clone(),
    mut_ctx.clone(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let v = compile_expr(
    &def.value,
    univ_ctx.clone(),
    mut_ctx.clone(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let all =
    def.all.iter().map(|n| compile_name(n.clone(), stt)).try_collect()?;
  let data = Definition {
    kind: def.kind,
    safety: def.safety,
    lvls: Nat(def.level_params.len().into()),
    typ: t.data,
    value: v.data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Hints(def.hints),
      Metadatum::Link(t.meta),
      Metadatum::Link(v.meta),
      Metadatum::Links(all),
    ],
  };
  Ok((data, meta))
}

pub fn compile_rule(
  rule: &RecursorRule,
  univ_ctx: ConsList<Name>,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(ixon::RecursorRule, Address, Address), CompileError> {
  let n = compile_name(rule.ctor.clone(), stt)?;
  let rhs = compile_expr(&rule.rhs, univ_ctx, mut_ctx, comms, consts, stt)?;
  let data =
    ixon::RecursorRule { fields: rule.n_fields.clone(), rhs: rhs.data };
  Ok((data, n, rhs.meta))
}

pub fn compile_recr(
  recr: Rec,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Recursor, Metadata), CompileError> {
  let univ_ctx =
    ConsList::from_iterator(recr.cnst.level_params.iter().cloned());
  let n = compile_name(recr.cnst.name.clone(), stt)?;
  let ls: Vec<Address> = recr
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &recr.cnst.typ,
    univ_ctx.clone(),
    mut_ctx.clone(),
    consts.clone(),
    comms.clone(),
    stt,
  )?;
  let mut rule_data = Vec::with_capacity(recr.rules.len());
  let mut rule_meta = Vec::with_capacity(recr.rules.len());
  for rule in recr.rules {
    let (rr, rn, rm) = compile_rule(
      &rule,
      univ_ctx.clone(),
      mut_ctx.clone(),
      comms.clone(),
      consts.clone(),
      stt,
    )?;
    rule_data.push(rr);
    rule_meta.push((rn, rm));
  }
  let all =
    recr.all.iter().map(|n| compile_name(n.clone(), stt)).try_collect()?;
  let data = Recursor {
    k: recr.k,
    is_unsafe: recr.is_unsafe,
    lvls: Nat(recr.cnst.level_params.len().into()),
    params: recr.num_params.clone(),
    indices: recr.num_indices.clone(),
    motives: recr.num_motives.clone(),
    minors: recr.num_minors.clone(),
    typ: t.data,
    rules: rule_data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(t.meta),
      Metadatum::Map(rule_meta),
      Metadatum::Links(all),
    ],
  };
  Ok((data, meta))
}

fn compile_ctor(
  ctor: &ConstructorVal,
  induct: Address,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Constructor, Metadata), CompileError> {
  let n = compile_name(ctor.cnst.name.clone(), stt)?;
  let univ_ctx =
    ConsList::from_iterator(ctor.cnst.level_params.iter().cloned());
  let ls = ctor
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &ctor.cnst.typ,
    univ_ctx.clone(),
    mut_ctx.clone(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let data = Constructor {
    is_unsafe: ctor.is_unsafe,
    lvls: Nat(ctor.cnst.level_params.len().into()),
    cidx: ctor.cidx.clone(),
    params: ctor.num_params.clone(),
    fields: ctor.num_fields.clone(),
    typ: t.data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(t.meta),
      Metadatum::Link(induct),
    ],
  };
  Ok((data, meta))
}

pub fn compile_indc(
  ind: &Ind,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Inductive, FxHashMap<Address, Address>), CompileError> {
  let n = compile_name(ind.ind.cnst.name.clone(), stt)?;
  let univ_ctx =
    ConsList::from_iterator(ind.ind.cnst.level_params.iter().cloned());
  let ls = ind
    .ind
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &ind.ind.cnst.typ,
    univ_ctx.clone(),
    mut_ctx.clone(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let mut ctor_data = Vec::with_capacity(ind.ctors.len());
  let mut ctor_meta = Vec::with_capacity(ind.ctors.len());
  let mut meta_map = FxHashMap::default();
  for ctor in ind.ctors.iter() {
    let (cd, cm) = compile_ctor(
      ctor,
      n.clone(),
      mut_ctx.clone(),
      comms.clone(),
      consts.clone(),
      stt,
    )?;
    ctor_data.push(cd);
    let cn = compile_name(ctor.cnst.name.clone(), stt)?;
    let cm = store_meta(cm)?;
    ctor_meta.push(cm.clone());
    meta_map.insert(cn, cm);
  }
  let all =
    ind.ind.all.iter().map(|n| compile_name(n.clone(), stt)).try_collect()?;
  let data = Inductive {
    recr: ind.ind.is_rec,
    refl: ind.ind.is_reflexive,
    is_unsafe: ind.ind.is_unsafe,
    lvls: Nat(ind.ind.cnst.level_params.len().into()),
    params: ind.ind.num_params.clone(),
    indices: ind.ind.num_indices.clone(),
    nested: ind.ind.num_nested.clone(),
    typ: t.data,
    ctors: ctor_data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n.clone()),
      Metadatum::Links(ls),
      Metadatum::Link(t.meta),
      Metadatum::Links(ctor_meta),
      Metadatum::Links(all),
    ],
  };
  let m = store_meta(meta)?;
  meta_map.insert(n, m);
  Ok((data, meta_map))
}

pub fn compare_defn(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x: &Def,
  y: &Def,
) -> Result<SOrder, CompileError> {
  SOrder::try_cmp(
    SOrder { strong: true, ordering: x.kind.cmp(&y.kind) },
    || {
      SOrder::try_cmp(
        SOrder {
          strong: true,
          ordering: x.level_params.len().cmp(&y.level_params.len()),
        },
        || {
          SOrder::try_cmp(
            compare_expr(
              mut_ctx.clone(),
              comms.clone(),
              consts.clone(),
              ConsList::from_iterator(x.level_params.iter().cloned()),
              ConsList::from_iterator(y.level_params.iter().cloned()),
              &x.typ,
              &y.typ,
            )?,
            || {
              compare_expr(
                mut_ctx.clone(),
                comms.clone(),
                consts.clone(),
                ConsList::from_iterator(x.level_params.iter().cloned()),
                ConsList::from_iterator(y.level_params.iter().cloned()),
                &x.value,
                &y.value,
              )
            },
          )
        },
      )
    },
  )
}

pub fn compare_ctor_inner(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x: &ConstructorVal,
  y: &ConstructorVal,
) -> Result<SOrder, CompileError> {
  SOrder::try_cmp(
    SOrder {
      strong: true,
      ordering: x.cnst.level_params.len().cmp(&y.cnst.level_params.len()),
    },
    || {
      SOrder::try_cmp(
        SOrder { strong: true, ordering: x.cidx.cmp(&y.cidx) },
        || {
          SOrder::try_cmp(
            SOrder { strong: true, ordering: x.num_params.cmp(&y.num_params) },
            || {
              SOrder::try_cmp(
                SOrder {
                  strong: true,
                  ordering: x.num_fields.cmp(&y.num_fields),
                },
                || {
                  compare_expr(
                    mut_ctx.clone(),
                    comms.clone(),
                    consts.clone(),
                    ConsList::from_iterator(
                      x.cnst.level_params.iter().cloned(),
                    ),
                    ConsList::from_iterator(
                      y.cnst.level_params.iter().cloned(),
                    ),
                    &x.cnst.typ,
                    &y.cnst.typ,
                  )
                },
              )
            },
          )
        },
      )
    },
  )
}

pub fn compare_ctor(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
  x: &ConstructorVal,
  y: &ConstructorVal,
) -> Result<SOrder, CompileError> {
  let key = if x.cnst.name <= y.cnst.name {
    (x.cnst.name.clone(), y.cnst.name.clone())
  } else {
    (y.cnst.name.clone(), x.cnst.name.clone())
  };
  if let Some(o) = stt.const_cmp.get(&key) {
    Ok(SOrder { strong: true, ordering: *o })
  } else {
    let so = compare_ctor_inner(mut_ctx, comms, consts, x, y)?;
    if so.strong {
      stt.const_cmp.insert(key, so.ordering);
    }
    Ok(so)
  }
}

pub fn compare_indc(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
  x: &Ind,
  y: &Ind,
) -> Result<SOrder, CompileError> {
  SOrder::try_cmp(
    SOrder {
      strong: true,
      ordering: x
        .ind
        .cnst
        .level_params
        .len()
        .cmp(&y.ind.cnst.level_params.len()),
    },
    || {
      SOrder::try_cmp(
        SOrder {
          strong: true,
          ordering: x.ind.num_params.cmp(&y.ind.num_params),
        },
        || {
          SOrder::try_cmp(
            SOrder {
              strong: true,
              ordering: x.ind.num_indices.cmp(&y.ind.num_indices),
            },
            || {
              SOrder::try_cmp(
                SOrder {
                  strong: true,
                  ordering: x.ind.ctors.len().cmp(&y.ind.ctors.len()),
                },
                || {
                  SOrder::try_cmp(
                    compare_expr(
                      mut_ctx.clone(),
                      comms.clone(),
                      consts.clone(),
                      ConsList::from_iterator(
                        x.ind.cnst.level_params.iter().cloned(),
                      ),
                      ConsList::from_iterator(
                        y.ind.cnst.level_params.iter().cloned(),
                      ),
                      &x.ind.cnst.typ,
                      &y.ind.cnst.typ,
                    )?,
                    || {
                      SOrder::try_zip(
                        |a, b| {
                          compare_ctor(
                            mut_ctx.clone(),
                            comms.clone(),
                            consts.clone(),
                            stt,
                            a,
                            b,
                          )
                        },
                        &x.ctors,
                        &y.ctors,
                      )
                    },
                  )
                },
              )
            },
          )
        },
      )
    },
  )
}

pub fn compare_recr_rule(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x_lvls: ConsList<Name>,
  y_lvls: ConsList<Name>,
  x: &RecursorRule,
  y: &RecursorRule,
) -> Result<SOrder, CompileError> {
  SOrder::try_cmp(
    SOrder { strong: true, ordering: x.n_fields.cmp(&y.n_fields) },
    || {
      compare_expr(
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        x_lvls,
        y_lvls,
        &x.rhs,
        &y.rhs,
      )
    },
  )
}

pub fn compare_recr(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x: &Rec,
  y: &Rec,
) -> Result<SOrder, CompileError> {
  SOrder::try_cmp(
    SOrder {
      strong: true,
      ordering: x.cnst.level_params.len().cmp(&y.cnst.level_params.len()),
    },
    || {
      SOrder::try_cmp(
        SOrder { strong: true, ordering: x.num_params.cmp(&y.num_params) },
        || {
          SOrder::try_cmp(
            SOrder {
              strong: true,
              ordering: x.num_indices.cmp(&y.num_indices),
            },
            || {
              SOrder::try_cmp(
                SOrder {
                  strong: true,
                  ordering: x.num_motives.cmp(&y.num_motives),
                },
                || {
                  SOrder::try_cmp(
                    SOrder {
                      strong: true,
                      ordering: x.num_minors.cmp(&y.num_minors),
                    },
                    || {
                      SOrder::try_cmp(
                        SOrder { strong: true, ordering: x.k.cmp(&y.k) },
                        || {
                          SOrder::try_cmp(
                            compare_expr(
                              mut_ctx.clone(),
                              comms.clone(),
                              consts.clone(),
                              ConsList::from_iterator(
                                x.cnst.level_params.iter().cloned(),
                              ),
                              ConsList::from_iterator(
                                y.cnst.level_params.iter().cloned(),
                              ),
                              &x.cnst.typ,
                              &y.cnst.typ,
                            )?,
                            || {
                              SOrder::try_zip(
                                |a, b| {
                                  compare_recr_rule(
                                    mut_ctx.clone(),
                                    comms.clone(),
                                    consts.clone(),
                                    ConsList::from_iterator(
                                      x.cnst.level_params.iter().cloned(),
                                    ),
                                    ConsList::from_iterator(
                                      y.cnst.level_params.iter().cloned(),
                                    ),
                                    a,
                                    b,
                                  )
                                },
                                &x.rules,
                                &y.rules,
                              )
                            },
                          )
                        },
                      )
                    },
                  )
                },
              )
            },
          )
        },
      )
    },
  )
}

pub fn compare_const(
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
  x: &MutConst,
  y: &MutConst,
) -> Result<Ordering, CompileError> {
  let key = if x.name() <= y.name() {
    (x.name(), y.name())
  } else {
    (y.name(), x.name())
  };
  if let Some(so) = stt.const_cmp.get(&key) {
    Ok(*so)
  } else {
    let so: SOrder = match (x, y) {
      (MutConst::Defn(x), MutConst::Defn(y)) => {
        compare_defn(mut_ctx.clone(), comms.clone(), consts.clone(), x, y)?
      },
      (MutConst::Defn(_), _) => SOrder::lt(true),
      (MutConst::Indc(x), MutConst::Indc(y)) => {
        compare_indc(mut_ctx.clone(), comms.clone(), consts.clone(), stt, x, y)?
      },
      (MutConst::Indc(_), _) => SOrder::lt(true),
      (MutConst::Recr(x), MutConst::Recr(y)) => {
        compare_recr(mut_ctx.clone(), comms.clone(), consts.clone(), x, y)?
      },
      (MutConst::Recr(_), _) => SOrder::lt(true),
    };
    if so.strong {
      stt.const_cmp.insert(key, so.ordering);
    }
    Ok(so.ordering)
  }
}

pub fn eq_const(
  mut_ctx: &MutCtx,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
  x: &MutConst,
  y: &MutConst,
) -> Result<bool, CompileError> {
  let ordering =
    compare_const(mut_ctx.clone(), comms.clone(), consts.clone(), stt, x, y)?;
  Ok(ordering == Ordering::Equal)
}

pub fn group_by<T, F>(
  items: Vec<T>,
  mut eq: F,
) -> Result<Vec<Vec<T>>, CompileError>
where
  F: FnMut(&T, &T) -> Result<bool, CompileError>,
{
  let mut groups = Vec::new();
  let mut current = Vec::new();
  for item in items {
    if let Some(last) = current.last() {
      if eq(last, &item)? {
        current.push(item);
      } else {
        groups.push(std::mem::replace(&mut current, vec![item]));
      }
    } else {
      current.push(item);
    }
  }
  if !current.is_empty() {
    groups.push(current);
  }
  Ok(groups)
}

pub fn sort_by_compare(
  items: &[MutConst],
  ctx: &MutCtx,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<MutConst>, CompileError> {
  if items.len() <= 1 {
    return Ok(items.to_vec());
  }
  let mid = items.len() / 2;
  let (left, right) = items.split_at(mid);
  let left = sort_by_compare(left, ctx, comms, consts, stt)?;
  let right = sort_by_compare(right, ctx, comms, consts, stt)?;
  merge(left, right, ctx, comms, consts, stt)
}

pub fn merge(
  left: Vec<MutConst>,
  right: Vec<MutConst>,
  ctx: &MutCtx,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<MutConst>, CompileError> {
  let mut result = Vec::with_capacity(left.len() + right.len());
  let mut left_iter = left.into_iter();
  let mut right_iter = right.into_iter();
  let mut left_item = left_iter.next();
  let mut right_item = right_iter.next();

  while let (Some(l), Some(r)) = (&left_item, &right_item) {
    let cmp =
      compare_const(ctx.clone(), comms.clone(), consts.clone(), stt, l, r)?;
    if cmp == Ordering::Greater {
      result.push(right_item.take().unwrap());
      right_item = right_iter.next();
    } else {
      result.push(left_item.take().unwrap());
      left_item = left_iter.next();
    }
  }

  if let Some(l) = left_item {
    result.push(l);
    result.extend(left_iter);
  }
  if let Some(r) = right_item {
    result.push(r);
    result.extend(right_iter);
  }

  Ok(result)
}

pub fn sort_consts(
  mut cs: Vec<MutConst>,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<Vec<MutConst>>, CompileError> {
  cs.sort_by_key(|x| x.name());
  let mut classes = vec![cs];
  loop {
    let ctx = MutConst::ctx(&classes);
    let mut new_classes: Vec<Vec<MutConst>> = vec![];
    for class in classes.iter() {
      match class.len() {
        0 => {
          return Err(CompileError::Todo);
        },
        1 => {
          new_classes.push(class.clone());
        },
        _ => {
          let sorted =
            sort_by_compare(class.as_ref(), &ctx, comms, consts, stt)?;
          let groups =
            group_by(sorted, |a, b| eq_const(&ctx, comms, consts, stt, a, b))?;
          new_classes.extend(groups);
        },
      }
    }
    for class in &mut new_classes {
      class.sort_by_key(|x| x.name())
    }
    if classes == new_classes {
      return Ok(new_classes);
    }
    classes = new_classes;
  }
}

///// The size of the SCC chunks in which parallel compilation will occur.
///// This constant regulates the maximum recursion depth that can happen
///// in the worst-case scenario when there's a linear dependency between SCCs.
//const PAR_CHUNK_SIZE: usize = 1024;
//
//pub fn compile(
//  sccs: &RefMap,
//  out_refs: &RefMap,
//  const_map: &ConstMap,
//) -> Result<FxHashMap<Arc<Name>, MetaAddress>, CompileError> {
//  // The compilation process involves:
//  // 1. Finding root SCCs (those with no external dependencies)
//  // 2. Building a dependency DAG and sequencing it
//  // 3. Compiling SCCs in parallel chunks from leaves to roots
//  // 4. Collecting and validating the resulting data
//
//  // Internal macro for safe access to SCC and dependency data.
//  macro_rules! get {
//    (SCC, $name:expr) => {
//      sccs.get($name).expect("Missing SCC")
//    };
//    (DEPS, $name:expr) => {
//      out_refs.get($name).expect("Missing dependencies")
//    };
//  }
//
//  // Find root SCCs - those that no other SCC depends on.
//  let mut roots: FxHashSet<_> = sccs.values().map(NameSetWrap).collect();
//  for (name, deps) in out_refs {
//    for dep in deps {
//      let dep_scc = get!(SCC, dep);
//      // Don't remove SCCs due to circular dependencies within the same SCC.
//      if !dep_scc.contains(name) {
//        roots.remove(&NameSetWrap(dep_scc));
//      }
//    }
//  }
//
//  // Build a sequenced DAG of SCCs with roots on the left and transitive
//  // dependencies to the right, reached via DFS.
//  let mut dag = IndexSet::with_capacity_and_hasher(sccs.len(), FxBuildHasher);
//  for scc_wrap in roots {
//    if dag.contains(&scc_wrap) {
//      continue;
//    }
//    dag.insert(scc_wrap.clone());
//
//    // Initiate the stack with the immediate children of the current SCC.
//    let mut scc_stack = vec![];
//    for name in scc_wrap.0 {
//      for dep in get!(DEPS, name) {
//        let dep_scc = get!(SCC, dep);
//        if !dag.contains(&NameSetWrap(dep_scc)) {
//          scc_stack.push(dep_scc);
//        }
//      }
//    }
//
//    // Pop the last SCC from the stack, add it to the sequenced DAG and push
//    // its unvisited children to the stack.
//    while let Some(popped_scc) = scc_stack.pop() {
//      dag.insert(NameSetWrap(popped_scc));
//      for name in popped_scc {
//        for dep in get!(DEPS, name) {
//          let dep_scc = get!(SCC, dep);
//          if !dag.contains(&NameSetWrap(dep_scc)) {
//            scc_stack.push(dep_scc);
//          }
//        }
//      }
//    }
//  }
//
//  // Reverse the DAG so we process from leaves to roots.
//  // This order enables efficient compilation with caching while avoiding the
//  // recursion depth limit.
//  let dag_rev: Vec<_> = dag.into_iter().rev().collect();
//
//  // Pre-populate hash storage with mutexes for thread-safe updates.
//  let mut hashes =
//    HashMap::with_capacity_and_hasher(dag_rev.len(), FxBuildHasher);
//  for scc in &dag_rev {
//    hashes.insert(scc, Mutex::new(None));
//  }
//
//  // Compile SCCs in parallel chunks.
//  dag_rev.chunks(PAR_CHUNK_SIZE).for_each(|sccs_chunk| {
//    sccs_chunk.par_iter().for_each(|scc_wrap| {
//      let _ = compile_scc(scc_wrap, sccs, const_map, &hashes);
//    });
//  });
//
//  // Collect results and validate disjoint SCCs.
//  let mut map = FxHashMap::default();
//  for mutex in hashes.values() {
//    let mutex_lock = mutex.lock().unwrap();
//    let compile_result = mutex_lock.as_ref().expect("Missing computed hash");
//    match compile_result {
//      Err(err) => return Err(err.clone()),
//      Ok(scc_hashes) => {
//        for (name, hash) in scc_hashes.as_ref() {
//          // SCCs are disjoint so there should be no duplicates.
//          assert!(map.insert(name.clone(), hash.clone()).is_none());
//        }
//      },
//    }
//  }
//
//  // Verify that we computed hashes for all nodes in the dependency graph.
//  assert_eq!(map.len(), out_refs.len());
//  Ok(map)
//}
//
///// Wrapper for [`NameSet`] to provide concrete [`Hash`] and [`Eq`] implementations.
//#[derive(PartialEq, Eq, Clone)]
//struct NameSetWrap<'a>(&'a NameSet);
//
//impl Hash for NameSetWrap<'_> {
//  fn hash<H: Hasher>(&self, state: &mut H) {
//    for name in self.0 {
//      name.get_hash().hash(state);
//    }
//  }
//}
//
///// Thread-safe storage for computed hashes of SCCs.
/////
///// This is a specialized hashmap where each value is protected by a mutex,
///// allowing concurrent access to different SCCs without contention.
//type HashedEntries<'a> =
//  FxHashMap<&'a NameSetWrap<'a>, Mutex<Option<CompileResult>>>;
//
//type CompileResult =
//  Result<Arc<FxHashMap<Arc<Name>, MetaAddress>>, CompileError>;
//
//#[derive(Clone)]
//pub struct CompileError;
//
//fn compile_scc(
//  scc_wrap: &NameSetWrap<'_>,
//  sccs: &RefMap,
//  const_map: &ConstMap,
//  hashes: &HashedEntries<'_>,
//) -> CompileResult {
//  let mutex = hashes.get(scc_wrap).expect("Missing SCC");
//  let scc = scc_wrap.0;
//
//  // Lock the entire SCC.
//  let mut mutex_lock = mutex.lock().unwrap();
//
//  // Return cached result if already computed.
//  if let Some(scc_hashes) = mutex_lock.as_ref() {
//    return scc_hashes.clone();
//  }
//
//  let mut stt = CompileState::default();
//  let mut hashes_map =
//    HashMap::with_capacity_and_hasher(scc.len(), FxBuildHasher);
//  let mut delayed_ctors = Vec::new();
//  for constant_name in scc {
//    let const_info = const_map.get(constant_name).expect("Missing constant");
//    match const_info {
//      ConstantInfo::DefnInfo(val) => {
//        let base_def = BaseDef::mk_defn(val);
//        let mut_const = LeanMutConst::Def(base_def);
//        let (data_ixon, meta_ixon) =
//          compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::ThmInfo(val) => {
//        let base_def = BaseDef::mk_theo(val);
//        let mut_const = LeanMutConst::Def(base_def);
//        let (data_ixon, meta_ixon) =
//          compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::OpaqueInfo(val) => {
//        let base_def = BaseDef::mk_opaq(val);
//        let mut_const = LeanMutConst::Def(base_def);
//        let (data_ixon, meta_ixon) =
//          compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::InductInfo(val) => {
//        let base_ind = BaseInd::mk(val, const_map)?;
//        let mut_const = LeanMutConst::Ind(base_ind);
//        let (data_ixon, meta_ixon) =
//          compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::RecInfo(val) => {
//        let mut_const = LeanMutConst::Rec(val);
//        let (data_ixon, meta_ixon) =
//          compile_mutual(mut_const, scc, sccs, const_map, hashes, &mut stt)?;
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::CtorInfo(val) => {
//        delayed_ctors.push(val.constant_val.name.clone())
//      },
//      ConstantInfo::AxiomInfo(val) => {
//        let AxiomVal { constant_val, is_unsafe } = val;
//        let ConstantVal { name, level_params, typ } = constant_val;
//        let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
//        let n = compile_name(name.clone(), &mut stt);
//        let ls = level_params
//          .iter()
//          .map(|n| compile_name(n.clone(), &mut stt))
//          .collect();
//        let MetaAddress { data: data_t, meta: meta_t } = compile_expr(
//          typ,
//          univ_ctx,
//          ConsList::Nil,
//          sccs,
//          const_map,
//          hashes,
//          &mut stt,
//        )?;
//        let axiom = Axiom {
//          is_unsafe: *is_unsafe,
//          lvls: Nat::from_le_bytes(&level_params.len().to_le_bytes()),
//          typ: data_t,
//        };
//        let nodes = vec![
//          Metadatum::Link(n),
//          Metadatum::Links(ls),
//          Metadatum::Link(meta_t),
//        ];
//        let data_ixon = Ixon::Axio(axiom);
//        let meta_ixon = Ixon::Meta(Metadata { nodes });
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//      ConstantInfo::QuotInfo(val) => {
//        let QuotVal { constant_val, kind } = val;
//        let ConstantVal { name, level_params, typ } = constant_val;
//        let univ_ctx = ConsList::from_iterator(level_params.iter().cloned());
//        let n = compile_name(name.clone(), &mut stt);
//        let ls = level_params
//          .iter()
//          .map(|n| compile_name(n.clone(), &mut stt))
//          .collect();
//        let MetaAddress { data: data_t, meta: meta_t } = compile_expr(
//          typ,
//          univ_ctx,
//          ConsList::Nil,
//          sccs,
//          const_map,
//          hashes,
//          &mut stt,
//        )?;
//        let quot = Quotient {
//          kind: *kind,
//          lvls: Nat::from_le_bytes(&level_params.len().to_le_bytes()),
//          typ: data_t,
//        };
//        let nodes = vec![
//          Metadatum::Link(n),
//          Metadatum::Links(ls),
//          Metadatum::Link(meta_t),
//        ];
//        let data_ixon = Ixon::Quot(quot);
//        let meta_ixon = Ixon::Meta(Metadata { nodes });
//        let data = store_ixon(&data_ixon);
//        let meta = store_ixon(&meta_ixon);
//        let addr = MetaAddress { data, meta };
//        hashes_map.insert(constant_name.clone(), addr);
//      },
//    }
//  }
//
//  for delayed_ctor in delayed_ctors {
//    let addr = stt.ctors.remove(&delayed_ctor).expect("Missing compiled ctor");
//    hashes_map.insert(delayed_ctor, addr);
//  }
//
//  let hashes_arc = Arc::new(hashes_map);
//  let compile_result = Ok(hashes_arc);
//
//  // Cache and return the result
//  *mutex_lock = Some(compile_result.clone());
//  compile_result
//}
//
//fn compile_mutual<'a>(
//  mutual: LeanMutConst<'a>,
//  all: &NameSet,
//  sccs: &RefMap,
//  const_map: &ConstMap,
//  hashes: &HashedEntries<'_>,
//  stt: &mut CompileState,
//) -> Result<(Ixon, Ixon), CompileError> {
//  if all.len() == 1
//    && matches!(&mutual, LeanMutConst::Def(_) | LeanMutConst::Rec(_))
//  {
//    match mutual {
//      LeanMutConst::Def(base_def) => {
//        let mut_ctx = ConsList::Nil.cons((base_def.name.clone(), Nat::ZERO));
//        let (data, meta) =
//          compile_base_def(base_def, mut_ctx, sccs, const_map, hashes, stt)?;
//        Ok((Ixon::Defn(data), Ixon::Meta(meta)))
//      },
//      LeanMutConst::Rec(rec) => {
//        let mut_ctx =
//          ConsList::Nil.cons((rec.constant_val.name.clone(), Nat::ZERO));
//        let (data, meta) =
//          compile_rec(rec, &mut_ctx, sccs, const_map, hashes, stt)?;
//        Ok((Ixon::Recr(data), Ixon::Meta(meta)))
//      },
//      _ => unreachable!(),
//    }
//  } else {
//    let mut consts = Vec::new();
//    for name in all {
//      let Some(const_info) = const_map.get(name) else {
//        return Err(CompileError);
//      };
//      let mut_const = match const_info {
//        ConstantInfo::InductInfo(val) => {
//          let base_ind = BaseInd::mk(val, const_map)?;
//          LeanMutConst::Ind(base_ind)
//        },
//        ConstantInfo::DefnInfo(val) => {
//          let base_def = BaseDef::mk_defn(val);
//          LeanMutConst::Def(base_def)
//        },
//        ConstantInfo::OpaqueInfo(val) => {
//          let base_def = BaseDef::mk_opaq(val);
//          LeanMutConst::Def(base_def)
//        },
//        ConstantInfo::ThmInfo(val) => {
//          let base_def = BaseDef::mk_theo(val);
//          LeanMutConst::Def(base_def)
//        },
//        ConstantInfo::RecInfo(val) => LeanMutConst::Rec(val),
//        _ => continue,
//      };
//      consts.push(mut_const);
//    }
//    let consts_sorted = sort_consts(&consts);
//    let mut_meta = consts_sorted
//      .iter()
//      .map(|m| m.iter().map(|c| compile_name(c.name(), stt)).collect())
//      .collect();
//
//    let mut_ctx: ConsList<(Arc<Name>, Nat)> = ConsList::Nil; // TODO
//
//    let ctx = mut_ctx
//      .iter()
//      .map(|(n, i)| (compile_name(n.clone(), stt), store_nat(i)))
//      .collect();
//
//    let (data, metas) = compile_mut_consts(consts_sorted, mut_ctx)?;
//
//    let metas_vec = metas.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
//    let nodes = vec![
//      Metadatum::Muts(mut_meta),
//      Metadatum::Map(ctx),
//      Metadatum::Map(metas_vec),
//    ];
//
//    #[expect(unused_variables)]
//    let block_addr = MetaAddress {
//      data: store_ixon(&data),
//      meta: store_serialize(&Metadata { nodes }),
//    };
//
//    todo!()
//  }
//}
//
//fn compile_mut_consts(
//  _mut_consts: Vec<Vec<LeanMutConst<'_>>>,
//  _mut_ctx: ConsList<(Arc<Name>, Nat)>,
//) -> Result<(Ixon, FxHashMap<Address, Address>), CompileError> {
//  todo!()
//}
//
//fn sort_consts<'a>(_consts: &[LeanMutConst<'_>]) -> Vec<Vec<LeanMutConst<'a>>> {
//  todo!()
//}
//
//
//
//
//
//
