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
    self, Axiom, BuiltIn, Constructor, ConstructorProj, DataValue, DefKind,
    Definition, DefinitionProj, Inductive, InductiveProj, Ixon, Metadata,
    Metadatum, Preresolved, Quotient, Recursor, RecursorProj, Serialize,
    SourceInfo, Substring, Syntax,
  },
  ix::mutual::{Def, Ind, MutConst, MutCtx, Rec},
  ix::store::{Store, StoreError},
  ix::strong_ordering::SOrd,
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
  pub blocks: FxHashSet<MetaAddress>,
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
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (LevelData::Mvar(_), _) => Err(CompileError::Todo),
    (_, LevelData::Mvar(_)) => Err(CompileError::Todo),
    (LevelData::Zero, LevelData::Zero) => Ok(SOrd::eq(true)),
    (LevelData::Zero, _) => Ok(SOrd::lt(true)),
    (_, LevelData::Zero) => Ok(SOrd::gt(true)),
    (LevelData::Succ(x), LevelData::Succ(y)) => {
      compare_level(x_ctx.clone(), y_ctx.clone(), x, y)
    },
    (LevelData::Succ(_), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Succ(_)) => Ok(SOrd::gt(true)),
    (LevelData::Max(xl, xr), LevelData::Max(yl, yr)) => SOrd::try_compare(
      compare_level(x_ctx.clone(), y_ctx.clone(), xl, yl)?,
      || compare_level(x_ctx, y_ctx, xr, yr),
    ),
    (LevelData::Max(_, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Max(_, _)) => Ok(SOrd::gt(true)),
    (LevelData::Imax(xl, xr), LevelData::Imax(yl, yr)) => SOrd::try_compare(
      compare_level(x_ctx.clone(), y_ctx.clone(), xl, yl)?,
      || compare_level(x_ctx, y_ctx, xr, yr),
    ),
    (LevelData::Imax(_, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Imax(_, _)) => Ok(SOrd::gt(true)),
    (LevelData::Param(x), LevelData::Param(y)) => {
      match (x_ctx.index_of(x), y_ctx.index_of(y)) {
        (Some(xi), Some(yi)) => {
          Ok(SOrd { strong: true, ordering: xi.cmp(&yi) })
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
  name: &Name,
  comms: Consts,
  consts: Consts,
) -> Result<MetaAddress, CompileError> {
  if let Some(builtin) = BuiltIn::from_name(name) {
    Ok(MetaAddress {
      data: store_ixon(&Ixon::Prim(builtin))?,
      meta: store_ixon(&Ixon::Meta(Metadata { nodes: vec![] }))?,
    })
  } else if let Some(addr) = comms.as_ref().get(name) {
    Ok(addr.clone())
  } else if let Some(addr) = consts.as_ref().get(name) {
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
          let addr = compile_ref(name, comms, consts)?;
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
  x: &Expr,
  y: &Expr,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x_lvls: ConsList<Name>,
  y_lvls: ConsList<Name>,
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) => Err(CompileError::Todo),
    (_, ExprData::Mvar(..)) => Err(CompileError::Todo),
    (ExprData::Fvar(..), _) => Err(CompileError::Todo),
    (_, ExprData::Fvar(..)) => Err(CompileError::Todo),
    (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
      compare_expr(x, y, mut_ctx, comms, consts, x_lvls, y_lvls)
    },
    (ExprData::Mdata(_, x, _), _) => {
      compare_expr(x, y, mut_ctx, comms, consts, x_lvls, y_lvls)
    },
    (_, ExprData::Mdata(_, y, _)) => {
      compare_expr(x, y, mut_ctx, comms, consts, x_lvls, y_lvls)
    },
    (ExprData::Bvar(x, _), ExprData::Bvar(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Bvar(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Bvar(..)) => Ok(SOrd::gt(true)),
    (ExprData::Sort(x, _), ExprData::Sort(y, _)) => {
      compare_level(x_lvls, y_lvls, x, y)
    },
    (ExprData::Sort(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Sort(..)) => Ok(SOrd::gt(true)),
    (ExprData::Const(x, xls, _), ExprData::Const(y, yls, _)) => {
      let us = SOrd::try_zip(
        |a, b| compare_level(x_lvls.clone(), y_lvls.clone(), a, b),
        xls,
        yls,
      )?;
      if us.ordering != Ordering::Equal {
        Ok(us)
      } else if x == y {
        Ok(SOrd::eq(true))
      } else {
        match (mut_ctx.as_ref().get(x), mut_ctx.as_ref().get(y)) {
          (Some(nx), Some(ny)) => Ok(SOrd::cmp(nx, ny)),
          (Some(..), _) => Ok(SOrd::lt(true)),
          (None, Some(..)) => Ok(SOrd::gt(true)),
          (None, None) => {
            let xa = compile_ref(x, comms.clone(), consts.clone())?;
            let ya = compile_ref(y, comms.clone(), consts.clone())?;
            Ok(SOrd::cmp(&xa.data, &ya.data))
          },
        }
      }
    },

    (ExprData::Const(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Const(..)) => Ok(SOrd::gt(true)),
    (ExprData::App(xl, xr, _), ExprData::App(yl, yr, _)) => SOrd::try_compare(
      compare_expr(
        xl,
        yl,
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        x_lvls.clone(),
        y_lvls.clone(),
      )?,
      || compare_expr(xr, yr, mut_ctx, comms, consts, x_lvls, y_lvls),
    ),
    (ExprData::App(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::App(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lam(_, xt, xb, _, _), ExprData::Lam(_, yt, yb, _, _)) => {
      SOrd::try_compare(
        compare_expr(
          xt,
          yt,
          mut_ctx.clone(),
          comms.clone(),
          consts.clone(),
          x_lvls.clone(),
          y_lvls.clone(),
        )?,
        || compare_expr(xb, yb, mut_ctx, comms, consts, x_lvls, y_lvls),
      )
    },
    (ExprData::Lam(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lam(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::ForallE(_, xt, xb, _, _),
      ExprData::ForallE(_, yt, yb, _, _),
    ) => SOrd::try_compare(
      compare_expr(
        xt,
        yt,
        mut_ctx.clone(),
        comms.clone(),
        consts.clone(),
        x_lvls.clone(),
        y_lvls.clone(),
      )?,
      || compare_expr(xb, yb, mut_ctx, comms, consts, x_lvls, y_lvls),
    ),
    (ExprData::ForallE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::ForallE(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::LetE(_, xt, xv, xb, _, _),
      ExprData::LetE(_, yt, yv, yb, _, _),
    ) => SOrd::try_zip(
      |a, b| {
        compare_expr(
          a,
          b,
          mut_ctx.clone(),
          comms.clone(),
          consts.clone(),
          x_lvls.clone(),
          y_lvls.clone(),
        )
      },
      &[xt, xv, xb],
      &[yt, yv, yb],
    ),
    (ExprData::LetE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::LetE(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Lit(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lit(..)) => Ok(SOrd::gt(true)),
    (ExprData::Proj(tnx, ix, tx, _), ExprData::Proj(tny, iy, ty, _)) => {
      let tn = match (mut_ctx.as_ref().get(tnx), mut_ctx.as_ref().get(tny)) {
        (Some(nx), Some(ny)) => Ok(SOrd::cmp(nx, ny)),
        (Some(..), _) => Ok(SOrd::lt(true)),
        (None, Some(..)) => Ok(SOrd::gt(true)),
        (None, None) => {
          let xa = compile_ref(tnx, comms.clone(), consts.clone())?;
          let ya = compile_ref(tny, comms.clone(), consts.clone())?;
          Ok(SOrd::cmp(&xa.data, &ya.data))
        },
      }?;
      SOrd::try_compare(tn, || {
        SOrd::try_compare(SOrd::cmp(ix, iy), || {
          compare_expr(tx, ty, mut_ctx, comms, consts, x_lvls, y_lvls)
        })
      })
    },
  }
}
pub fn compile_defn(
  def: &Def,
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
  recr: &Rec,
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
  for rule in recr.rules.iter() {
    let (rr, rn, rm) = compile_rule(
      rule,
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

pub fn mk_indc(ind: &InductiveVal, env: Arc<Env>) -> Result<Ind, CompileError> {
  let mut ctors = Vec::with_capacity(ind.ctors.len());
  for ctor_name in &ind.ctors {
    if let Some(ConstantInfo::CtorInfo(c)) = env.as_ref().get(ctor_name) {
      ctors.push(c.clone());
    } else {
      return Err(CompileError::Todo);
    };
  }
  Ok(Ind { ind: ind.clone(), ctors })
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

pub fn compile_quot(
  val: &QuotVal,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Quotient, Metadata), CompileError> {
  let n = compile_name(val.cnst.name.clone(), stt)?;
  let univ_ctx = ConsList::from_iterator(val.cnst.level_params.iter().cloned());
  let ls = val
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &val.cnst.typ,
    univ_ctx.clone(),
    MutCtx::default(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let data = Quotient {
    kind: val.kind,
    lvls: Nat(val.cnst.level_params.len().into()),
    typ: t.data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(t.meta),
    ],
  };
  Ok((data, meta))
}

pub fn compile_axio(
  val: &AxiomVal,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<(Axiom, Metadata), CompileError> {
  let n = compile_name(val.cnst.name.clone(), stt)?;
  let univ_ctx = ConsList::from_iterator(val.cnst.level_params.iter().cloned());
  let ls = val
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n.clone(), stt))
    .try_collect()?;
  let t = compile_expr(
    &val.cnst.typ,
    univ_ctx.clone(),
    MutCtx::default(),
    comms.clone(),
    consts.clone(),
    stt,
  )?;
  let data = Axiom {
    is_unsafe: val.is_unsafe,
    lvls: Nat(val.cnst.level_params.len().into()),
    typ: t.data,
  };
  let meta = Metadata {
    nodes: vec![
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(t.meta),
    ],
  };
  Ok((data, meta))
}

pub fn compare_defn(
  x: &Def,
  y: &Def,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd { strong: true, ordering: x.kind.cmp(&y.kind) },
    || {
      SOrd::try_compare(
        SOrd::cmp(&x.level_params.len(), &y.level_params.len()),
        || {
          SOrd::try_compare(
            compare_expr(
              &x.typ,
              &y.typ,
              mut_ctx.clone(),
              comms.clone(),
              consts.clone(),
              ConsList::from_iterator(x.level_params.iter().cloned()),
              ConsList::from_iterator(y.level_params.iter().cloned()),
            )?,
            || {
              compare_expr(
                &x.value,
                &y.value,
                mut_ctx.clone(),
                comms.clone(),
                consts.clone(),
                ConsList::from_iterator(x.level_params.iter().cloned()),
                ConsList::from_iterator(y.level_params.iter().cloned()),
              )
            },
          )
        },
      )
    },
  )
}

pub fn compare_ctor_inner(
  x: &ConstructorVal,
  y: &ConstructorVal,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.cnst.level_params.len(), &y.cnst.level_params.len()),
    || {
      SOrd::try_compare(SOrd::cmp(&x.cidx, &y.cidx), || {
        SOrd::try_compare(SOrd::cmp(&x.num_params, &y.num_params), || {
          SOrd::try_compare(SOrd::cmp(&x.num_fields, &y.num_fields), || {
            compare_expr(
              &x.cnst.typ,
              &y.cnst.typ,
              mut_ctx.clone(),
              comms.clone(),
              consts.clone(),
              ConsList::from_iterator(x.cnst.level_params.iter().cloned()),
              ConsList::from_iterator(y.cnst.level_params.iter().cloned()),
            )
          })
        })
      })
    },
  )
}

pub fn compare_ctor(
  x: &ConstructorVal,
  y: &ConstructorVal,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<SOrd, CompileError> {
  let key = if x.cnst.name <= y.cnst.name {
    (x.cnst.name.clone(), y.cnst.name.clone())
  } else {
    (y.cnst.name.clone(), x.cnst.name.clone())
  };
  if let Some(o) = stt.const_cmp.get(&key) {
    Ok(SOrd { strong: true, ordering: *o })
  } else {
    let so = compare_ctor_inner(x, y, mut_ctx, comms, consts)?;
    if so.strong {
      stt.const_cmp.insert(key, so.ordering);
    }
    Ok(so)
  }
}

pub fn compare_indc(
  x: &Ind,
  y: &Ind,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  stt: &mut CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd {
      strong: true,
      ordering: x
        .ind
        .cnst
        .level_params
        .len()
        .cmp(&y.ind.cnst.level_params.len()),
    },
    || {
      SOrd::try_compare(SOrd::cmp(&x.ind.num_params, &y.ind.num_params), || {
        SOrd::try_compare(
          SOrd::cmp(&x.ind.num_indices, &y.ind.num_indices),
          || {
            SOrd::try_compare(
              SOrd::cmp(&x.ind.ctors.len(), &y.ind.ctors.len()),
              || {
                SOrd::try_compare(
                  compare_expr(
                    &x.ind.cnst.typ,
                    &y.ind.cnst.typ,
                    mut_ctx.clone(),
                    comms.clone(),
                    consts.clone(),
                    ConsList::from_iterator(
                      x.ind.cnst.level_params.iter().cloned(),
                    ),
                    ConsList::from_iterator(
                      y.ind.cnst.level_params.iter().cloned(),
                    ),
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| {
                        compare_ctor(
                          a,
                          b,
                          mut_ctx.clone(),
                          comms.clone(),
                          consts.clone(),
                          stt,
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
      })
    },
  )
}

pub fn compare_recr_rule(
  x: &RecursorRule,
  y: &RecursorRule,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
  x_lvls: ConsList<Name>,
  y_lvls: ConsList<Name>,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(SOrd::cmp(&x.n_fields, &y.n_fields), || {
    compare_expr(
      &x.rhs,
      &y.rhs,
      mut_ctx.clone(),
      comms.clone(),
      consts.clone(),
      x_lvls,
      y_lvls,
    )
  })
}

pub fn compare_recr(
  x: &Rec,
  y: &Rec,
  mut_ctx: MutCtx,
  comms: Consts,
  consts: Consts,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.cnst.level_params.len(), &y.cnst.level_params.len()),
    || {
      SOrd::try_compare(SOrd::cmp(&x.num_params, &y.num_params), || {
        SOrd::try_compare(SOrd::cmp(&x.num_indices, &y.num_indices), || {
          SOrd::try_compare(SOrd::cmp(&x.num_motives, &y.num_motives), || {
            SOrd::try_compare(SOrd::cmp(&x.num_minors, &y.num_minors), || {
              SOrd::try_compare(SOrd::cmp(&x.k, &y.k), || {
                SOrd::try_compare(
                  compare_expr(
                    &x.cnst.typ,
                    &y.cnst.typ,
                    mut_ctx.clone(),
                    comms.clone(),
                    consts.clone(),
                    ConsList::from_iterator(
                      x.cnst.level_params.iter().cloned(),
                    ),
                    ConsList::from_iterator(
                      y.cnst.level_params.iter().cloned(),
                    ),
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| {
                        compare_recr_rule(
                          a,
                          b,
                          mut_ctx.clone(),
                          comms.clone(),
                          consts.clone(),
                          ConsList::from_iterator(
                            x.cnst.level_params.iter().cloned(),
                          ),
                          ConsList::from_iterator(
                            y.cnst.level_params.iter().cloned(),
                          ),
                        )
                      },
                      &x.rules,
                      &y.rules,
                    )
                  },
                )
              })
            })
          })
        })
      })
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
    let so: SOrd = match (x, y) {
      (MutConst::Defn(x), MutConst::Defn(y)) => {
        compare_defn(x, y, mut_ctx.clone(), comms.clone(), consts.clone())?
      },
      (MutConst::Defn(_), _) => SOrd::lt(true),
      (MutConst::Indc(x), MutConst::Indc(y)) => {
        compare_indc(x, y, mut_ctx.clone(), comms.clone(), consts.clone(), stt)?
      },
      (MutConst::Indc(_), _) => SOrd::lt(true),
      (MutConst::Recr(x), MutConst::Recr(y)) => {
        compare_recr(x, y, mut_ctx.clone(), comms.clone(), consts.clone())?
      },
      (MutConst::Recr(_), _) => SOrd::lt(true),
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
  items: Vec<&T>,
  mut eq: F,
) -> Result<Vec<Vec<&T>>, CompileError>
where
  F: FnMut(&T, &T) -> Result<bool, CompileError>,
{
  let mut groups = Vec::new();
  let mut current: Vec<&T> = Vec::new();
  for item in items {
    if let Some(last) = current.last() {
      if eq(last, item)? {
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

pub fn merge<'a>(
  left: Vec<&'a MutConst>,
  right: Vec<&'a MutConst>,
  ctx: &MutCtx,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
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

pub fn sort_by_compare<'a>(
  items: &[&'a MutConst],
  ctx: &MutCtx,
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
  if items.len() <= 1 {
    return Ok(items.to_vec());
  }
  let mid = items.len() / 2;
  let (left, right) = items.split_at(mid);
  let left = sort_by_compare(left, ctx, comms, consts, stt)?;
  let right = sort_by_compare(right, ctx, comms, consts, stt)?;
  merge(left, right, ctx, comms, consts, stt)
}

pub fn sort_consts<'a>(
  cs: &[&'a MutConst],
  comms: &Consts,
  consts: &Consts,
  stt: &mut CompileState,
) -> Result<Vec<Vec<&'a MutConst>>, CompileError> {
  let mut classes = vec![cs.to_owned()];
  loop {
    let ctx = MutConst::ctx(&classes);
    let mut new_classes: Vec<Vec<&MutConst>> = vec![];
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

fn compile_mut_consts(
  classes: Vec<Vec<&MutConst>>,
  comms: Consts,
  consts: Consts,
  mut_ctx: MutCtx,
  stt: &mut CompileState,
) -> Result<(Ixon, FxHashMap<Address, Address>), CompileError> {
  let mut data = vec![];
  let mut meta = FxHashMap::default();
  for class in classes {
    let mut class_data = vec![];
    for cnst in class {
      match cnst {
        MutConst::Indc(x) => {
          let (i, m) = compile_indc(
            x,
            mut_ctx.clone(),
            comms.clone(),
            consts.clone(),
            stt,
          )?;
          class_data.push(ixon::MutConst::Indc(i));
          meta.extend(m);
        },
        MutConst::Defn(x) => {
          let (d, m) = compile_defn(
            x,
            mut_ctx.clone(),
            comms.clone(),
            consts.clone(),
            stt,
          )?;
          class_data.push(ixon::MutConst::Defn(d));
          meta.insert(compile_name(x.name.clone(), stt)?, store_meta(m)?);
        },
        MutConst::Recr(x) => {
          let (r, m) = compile_recr(
            x,
            mut_ctx.clone(),
            comms.clone(),
            consts.clone(),
            stt,
          )?;
          class_data.push(ixon::MutConst::Recr(r));
          meta.insert(compile_name(x.cnst.name.clone(), stt)?, store_meta(m)?);
        },
      }
      if class_data.is_empty()
        || !class_data.iter().all(|x| x == &class_data[0])
      {
        return Err(CompileError::Todo);
      } else {
        data.push(class_data[0].clone())
      }
    }
  }
  Ok((Ixon::Muts(data), meta))
}

pub fn compile_mutual(
  mutual: &MutConst,
  all: &NameSet,
  comms: Consts,
  consts: Consts,
  env: Arc<Env>,
  stt: &mut CompileState,
) -> Result<(Ixon, Ixon), CompileError> {
  if all.len() == 1 && matches!(&mutual, MutConst::Defn(_) | MutConst::Recr(_))
  {
    match mutual {
      MutConst::Defn(defn) => {
        let mut_ctx = MutConst::single_ctx(defn.name.clone());
        let (data, meta) = compile_defn(defn, mut_ctx, comms, consts, stt)?;
        Ok((Ixon::Defn(data), Ixon::Meta(meta)))
      },
      MutConst::Recr(recr) => {
        let mut_ctx = MutConst::single_ctx(recr.cnst.name.clone());
        let (data, meta) = compile_recr(recr, mut_ctx, comms, consts, stt)?;
        Ok((Ixon::Recr(data), Ixon::Meta(meta)))
      },
      _ => unreachable!(),
    }
  } else {
    let mut cs = Vec::new();
    for name in all {
      let Some(const_info) = env.get(name) else {
        return Err(CompileError::Todo);
      };
      let mut_const = match const_info {
        ConstantInfo::InductInfo(val) => {
          MutConst::Indc(mk_indc(val, env.clone())?)
        },
        ConstantInfo::DefnInfo(val) => MutConst::Defn(Def::mk_defn(val)),
        ConstantInfo::OpaqueInfo(val) => MutConst::Defn(Def::mk_opaq(val)),
        ConstantInfo::ThmInfo(val) => MutConst::Defn(Def::mk_theo(val)),
        ConstantInfo::RecInfo(val) => MutConst::Recr(val.clone()),
        _ => continue,
      };
      cs.push(mut_const);
    }
    let mut_consts = sort_consts(
      &cs.iter().collect::<Vec<&MutConst>>(),
      &comms.clone(),
      &consts.clone(),
      stt,
    )?;
    let mut_meta: Vec<Vec<Address>> = mut_consts
      .iter()
      .map(|m| m.iter().map(|c| compile_name(c.name(), stt)).try_collect())
      .try_collect()?;
    let mut_ctx = MutConst::ctx(&mut_consts);
    let (data, metas) =
      compile_mut_consts(mut_consts, comms, consts, mut_ctx.clone(), stt)?;
    let ctx = mut_ctx
      .iter()
      .map(|(n, i)| Ok((compile_name(n.clone(), stt)?, store_nat(i)?)))
      .try_collect()?;
    let block = MetaAddress {
      data: store_ixon(&data)?,
      meta: store_meta(Metadata {
        nodes: vec![
          Metadatum::Muts(mut_meta),
          Metadatum::Map(ctx),
          Metadatum::Map(metas.clone().into_iter().collect()),
        ],
      })?,
    };
    stt.blocks.insert(block.clone());
    let mut ret: Option<(Ixon, Ixon)> = None;
    for c in cs {
      let idx = mut_ctx.as_ref().get(&c.name()).ok_or(CompileError::Todo)?;
      let n = compile_name(c.name(), stt)?;
      let meta = match metas.get(&n) {
        Some(m) => Ok(Metadata {
          nodes: vec![
            Metadatum::Link(block.meta.clone()),
            Metadatum::Link(m.clone()),
          ],
        }),
        None => Err(CompileError::Todo),
      }?;
      let data = match c {
        MutConst::Defn(..) => Ixon::DPrj(DefinitionProj {
          idx: idx.clone(),
          block: block.data.clone(),
        }),
        MutConst::Indc(..) => Ixon::IPrj(InductiveProj {
          idx: idx.clone(),
          block: block.data.clone(),
        }),
        MutConst::Recr(..) => Ixon::RPrj(RecursorProj {
          idx: idx.clone(),
          block: block.data.clone(),
        }),
      };
      let addr = MetaAddress {
        data: store_ixon(&data)?,
        meta: store_meta(meta.clone())?,
      };
      stt.const_cache.insert(c.name(), addr.clone());
      if c.name() == mutual.name() {
        ret = Some((data, Ixon::Meta(meta)));
      }
      for ctor in c.ctors() {
        let cdata = Ixon::CPrj(ConstructorProj {
          idx: idx.clone(),
          cidx: ctor.cidx.clone(),
          block: block.data.clone(),
        });
        let cn = compile_name(ctor.cnst.name.clone(), stt)?;
        let cmeta = match metas.get(&cn) {
          Some(m) => Ok(Metadata {
            nodes: vec![
              Metadatum::Link(block.meta.clone()),
              Metadatum::Link(m.clone()),
            ],
          }),
          None => Err(CompileError::Todo),
        }?;
        let caddr = MetaAddress {
          data: store_ixon(&cdata)?,
          meta: store_meta(cmeta.clone())?,
        };
        stt.const_cache.insert(ctor.cnst.name, caddr);
      }
    }
    ret.ok_or(CompileError::Todo)
  }
}

pub fn compile_const_info(
  cnst: &ConstantInfo,
  all: &NameSet,
  comms: Consts,
  consts: Consts,
  env: Arc<Env>,
  stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
  match cnst {
    ConstantInfo::DefnInfo(val) => {
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_defn(val)),
        all,
        comms,
        consts,
        env,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d)?, meta: store_ixon(&m)? })
    },
    ConstantInfo::OpaqueInfo(val) => {
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_opaq(val)),
        all,
        comms,
        consts,
        env,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d)?, meta: store_ixon(&m)? })
    },
    ConstantInfo::ThmInfo(val) => {
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_theo(val)),
        all,
        comms,
        consts,
        env,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d)?, meta: store_ixon(&m)? })
    },
    ConstantInfo::CtorInfo(val) => {
      if let Some(ConstantInfo::InductInfo(ind)) = env.as_ref().get(&val.induct)
      {
        let _ = compile_mutual(
          &MutConst::Indc(mk_indc(ind, env.clone())?),
          all,
          comms,
          consts,
          env,
          stt,
        )?;
        stt.const_cache.get(&val.cnst.name).ok_or(CompileError::Todo).cloned()
      } else {
        Err(CompileError::Todo)
      }
    },
    ConstantInfo::InductInfo(val) => {
      let (d, m) = compile_mutual(
        &MutConst::Indc(mk_indc(val, env.clone())?),
        all,
        comms,
        consts,
        env,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d)?, meta: store_ixon(&m)? })
    },
    ConstantInfo::RecInfo(val) => {
      let (d, m) = compile_mutual(
        &MutConst::Recr(val.clone()),
        all,
        comms,
        consts,
        env,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d)?, meta: store_ixon(&m)? })
    },
    ConstantInfo::QuotInfo(val) => {
      let (quot, meta) = compile_quot(val, comms, consts, stt)?;
      Ok(MetaAddress {
        data: store_ixon(&Ixon::Quot(quot))?,
        meta: store_ixon(&Ixon::Meta(meta))?,
      })
    },
    ConstantInfo::AxiomInfo(val) => {
      let (axio, meta) = compile_axio(val, comms, consts, stt)?;
      Ok(MetaAddress {
        data: store_ixon(&Ixon::Axio(axio))?,
        meta: store_ixon(&Ixon::Meta(meta))?,
      })
    },
  }
}
//
pub fn compile_const(
  name: &Name,
  graph: &RefMap,
  comms: Consts,
  consts: Consts,
  env: Arc<Env>,
  stt: &mut CompileState,
) -> Result<MetaAddress, CompileError> {
  if let Some(cached) = stt.const_cache.get(name) {
    Ok(cached.clone())
  } else {
    let cnst = env.as_ref().get(name).ok_or(CompileError::Todo)?;
    let all = graph.get(name).ok_or(CompileError::Todo)?;
    compile_const_info(cnst, all, comms, consts, env.clone(), stt)
  }
}
