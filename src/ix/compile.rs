use dashmap::{DashMap, DashSet};
use itertools::Itertools;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;
use std::{cmp::Ordering, sync::Arc};

use crate::{
  ix::address::{Address, MetaAddress},
  ix::condense::compute_sccs,
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstructorVal,
    DataValue as LeanDataValue, Env, Expr, ExprData, InductiveVal, Level,
    LevelData, Literal, Name, NameData, QuotVal, RecursorRule,
    SourceInfo as LeanSourceInfo, Substring as LeanSubstring,
    Syntax as LeanSyntax, SyntaxPreresolved,
  },
  ix::graph::{NameSet, build_ref_graph},
  ix::ground::ground_consts,
  ix::ixon::{
    self, Axiom, BuiltIn, Constructor, ConstructorProj, DataValue, Definition,
    DefinitionProj, Inductive, InductiveProj, Ixon, Metadata, Metadatum,
    Preresolved, Quotient, Recursor, RecursorProj, Serialize, SourceInfo,
    Substring, Syntax,
  },
  ix::mutual::{Def, Ind, MutConst, MutCtx, Rec},
  ix::strong_ordering::SOrd,
  lean::nat::Nat,
};

#[derive(Default)]
#[allow(clippy::type_complexity)]
pub struct CompileState {
  pub consts: DashMap<Name, MetaAddress>,
  pub names: DashMap<Name, Address>,
  pub blocks: DashSet<MetaAddress>,
  pub store: DashMap<Address, Vec<u8>>,
}

#[derive(Default)]
pub struct BlockCache {
  pub exprs: FxHashMap<Expr, MetaAddress>,
  pub univs: FxHashMap<Level, MetaAddress>,
  pub cmps: FxHashMap<(Name, Name), Ordering>,
}

#[derive(Debug)]
pub struct CompileStateStats {
  pub consts: usize,
  pub names: usize,
  pub blocks: usize,
  pub store: usize,
}

impl CompileState {
  pub fn stats(&self) -> CompileStateStats {
    CompileStateStats {
      consts: self.consts.len(),
      names: self.names.len(),
      blocks: self.blocks.len(),
      store: self.store.len(),
    }
  }
}

#[derive(Debug)]
pub enum CompileError {
  //StoreError(StoreError),
  UngroundedEnv,
  CondenseError,
  LevelParam(Name, Vec<Name>),
  LevelMVar(Name),
  Ref(Name),
  ExprFVar,
  ExprMVar,
  CompileExpr,
  MkIndc,
  SortConsts,
  CompileMutConsts(Vec<ixon::MutConst>),
  CompileMutual,
  CompileMutual2,
  CompileMutual3,
  CompileMutual4,
  CompileMutual5,
  CompileConstInfo,
  CompileConstInfo2,
  CompileConst,
}

//pub type CompileResult =
//  Result<Arc<FxHashMap<Name, MetaAddress>>, CompileError>;

//pub type Consts = Arc<FxHashMap<Name, MetaAddress>>;

pub fn store_ixon(
  ixon: &Ixon,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  ixon.put(&mut bytes);
  let addr = Address::hash(&bytes);
  stt.store.insert(addr.clone(), bytes);
  Ok(addr)
  //Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn store_string(
  str: &str,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let bytes = str.as_bytes();
  let addr = Address::hash(bytes);
  stt.store.insert(addr.clone(), bytes.to_vec());
  Ok(addr)
  //Store::write(str.as_bytes()).map_err(CompileError::StoreError)
}

pub fn store_nat(
  nat: &Nat,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let bytes = nat.to_le_bytes();
  let addr = Address::hash(&bytes);
  stt.store.insert(addr.clone(), bytes);
  Ok(addr)
  //Store::write(&nat.to_le_bytes()).map_err(CompileError::StoreError)
}

pub fn store_serialize<A: Serialize>(
  a: &A,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  a.put(&mut bytes);
  let addr = Address::hash(&bytes);
  stt.store.insert(addr.clone(), bytes);
  Ok(addr)
  //Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn store_meta(
  x: &Metadata,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let mut bytes = Vec::new();
  x.put(&mut bytes);
  let addr = Address::hash(&bytes);
  stt.store.insert(addr.clone(), bytes);
  Ok(addr)
  //Store::write(&bytes).map_err(CompileError::StoreError)
}

pub fn compile_name(
  name: &Name,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  if let Some(cached) = stt.names.get(name) {
    Ok(cached.clone())
  } else {
    let addr = match name.as_data() {
      NameData::Anonymous => store_ixon(&Ixon::NAnon, stt)?,
      NameData::Str(n, s, _) => {
        let n2 = compile_name(n, stt)?;
        let s2 = store_string(s, stt)?;
        store_ixon(&Ixon::NStr(n2, s2), stt)?
      },
      NameData::Num(n, i, _) => {
        let n_ = compile_name(n, stt)?;
        let s_ = store_nat(i, stt)?;
        store_ixon(&Ixon::NNum(n_, s_), stt)?
      },
    };
    stt.names.insert(name.clone(), addr.clone());
    Ok(addr)
  }
}

pub fn compile_level(
  level: &Level,
  univs: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<MetaAddress, CompileError> {
  if let Some(cached) = cache.univs.get(level) {
    Ok(cached.clone())
  } else {
    let (data_ixon, meta_ixon) = match level.as_data() {
      LevelData::Zero => (Ixon::UZero, Ixon::Meta(Metadata::default())),
      LevelData::Succ(x) => {
        let MetaAddress { data, meta } = compile_level(x, univs, cache, stt)?;
        let nodes = vec![Metadatum::Link(meta)];
        (Ixon::USucc(data), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Max(x, y) => {
        let MetaAddress { data: data_x, meta: meta_x } =
          compile_level(x, univs, cache, stt)?;
        let MetaAddress { data: data_y, meta: meta_y } =
          compile_level(y, univs, cache, stt)?;
        let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
        (Ixon::UMax(data_x, data_y), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Imax(x, y) => {
        let MetaAddress { data: data_x, meta: meta_x } =
          compile_level(x, univs, cache, stt)?;
        let MetaAddress { data: data_y, meta: meta_y } =
          compile_level(y, univs, cache, stt)?;
        let nodes = vec![Metadatum::Link(meta_x), Metadatum::Link(meta_y)];
        (Ixon::UIMax(data_x, data_y), Ixon::Meta(Metadata { nodes }))
      },
      LevelData::Param(n) => match univs.iter().position(|x| x == n) {
        Some(i) => {
          let data = Ixon::UVar(Nat::from_le_bytes(&i.to_le_bytes()));
          let n_addr = compile_name(n, stt)?;
          let nodes = vec![Metadatum::Link(n_addr)];
          (data, Ixon::Meta(Metadata { nodes }))
        },
        None => {
          return Err(CompileError::LevelParam(n.clone(), univs.to_vec()));
        },
      },
      LevelData::Mvar(x) => {
        return Err(CompileError::LevelMVar(x.clone()));
      },
    };
    let data = store_ixon(&data_ixon, stt)?;
    let meta = store_ixon(&meta_ixon, stt)?;
    let address = MetaAddress { data, meta };
    cache.univs.insert(level.clone(), address.clone());
    Ok(address)
  }
}

pub fn compare_level(
  x: &Level,
  y: &Level,
  x_ctx: &[Name],
  y_ctx: &[Name],
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (LevelData::Mvar(e), _) | (_, LevelData::Mvar(e)) => {
      Err(CompileError::LevelMVar(e.clone()))
    },
    (LevelData::Zero, LevelData::Zero) => Ok(SOrd::eq(true)),
    (LevelData::Zero, _) => Ok(SOrd::lt(true)),
    (_, LevelData::Zero) => Ok(SOrd::gt(true)),
    (LevelData::Succ(x), LevelData::Succ(y)) => {
      compare_level(x, y, x_ctx, y_ctx)
    },
    (LevelData::Succ(_), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Succ(_)) => Ok(SOrd::gt(true)),
    (LevelData::Max(xl, xr), LevelData::Max(yl, yr)) => {
      SOrd::try_compare(compare_level(xl, yl, x_ctx, y_ctx)?, || {
        compare_level(xr, yr, x_ctx, y_ctx)
      })
    },
    (LevelData::Max(_, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Max(_, _)) => Ok(SOrd::gt(true)),
    (LevelData::Imax(xl, xr), LevelData::Imax(yl, yr)) => {
      SOrd::try_compare(compare_level(xl, yl, x_ctx, y_ctx)?, || {
        compare_level(xr, yr, x_ctx, y_ctx)
      })
    },
    (LevelData::Imax(_, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Imax(_, _)) => Ok(SOrd::gt(true)),
    (LevelData::Param(x), LevelData::Param(y)) => {
      match (
        x_ctx.iter().position(|n| x == n),
        y_ctx.iter().position(|n| y == n),
      ) {
        (Some(xi), Some(yi)) => Ok(SOrd::cmp(&xi, &yi)),
        (None, _) => Err(CompileError::LevelParam(x.clone(), x_ctx.to_vec())),
        (_, None) => Err(CompileError::LevelParam(y.clone(), y_ctx.to_vec())),
      }
    },
  }
}

pub fn compile_substring(
  substring: &LeanSubstring,
  stt: &CompileState,
) -> Result<Substring, CompileError> {
  let LeanSubstring { str, start_pos, stop_pos } = substring;
  let str = store_string(str, stt)?;
  Ok(Substring {
    str,
    start_pos: start_pos.clone(),
    stop_pos: stop_pos.clone(),
  })
}

pub fn compile_preresolved(
  preresolved: &SyntaxPreresolved,
  stt: &CompileState,
) -> Result<Preresolved, CompileError> {
  match preresolved {
    SyntaxPreresolved::Namespace(ns) => {
      Ok(Preresolved::Namespace(compile_name(ns, stt)?))
    },
    SyntaxPreresolved::Decl(n, fs) => {
      let fs = fs.iter().map(|s| store_string(s, stt)).try_collect()?;
      Ok(Preresolved::Decl(compile_name(n, stt)?, fs))
    },
  }
}

pub fn compile_source_info(
  info: &LeanSourceInfo,
  stt: &CompileState,
) -> Result<SourceInfo, CompileError> {
  match info {
    LeanSourceInfo::Original(l, p, t, e) => {
      let l = compile_substring(l, stt)?;
      let t = compile_substring(t, stt)?;
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
  stt: &CompileState,
) -> Result<Syntax, CompileError> {
  match syn {
    LeanSyntax::Missing => Ok(Syntax::Missing),
    LeanSyntax::Node(info, kind, args) => {
      let info = compile_source_info(info, stt)?;
      let kind = compile_name(kind, stt)?;
      let args = args
        .iter()
        .map(|s| store_serialize(&compile_syntax(s, stt)?, stt))
        .try_collect()?;
      Ok(Syntax::Node(info, kind, args))
    },
    LeanSyntax::Atom(info, val) => {
      let info = compile_source_info(info, stt)?;
      let val = store_string(val, stt)?;
      Ok(Syntax::Atom(info, val))
    },
    LeanSyntax::Ident(info, raw_val, val, preresolved) => {
      let info = compile_source_info(info, stt)?;
      let raw_val = compile_substring(raw_val, stt)?;
      let val = compile_name(val, stt)?;
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
  stt: &CompileState,
) -> Result<DataValue, CompileError> {
  match data_value {
    LeanDataValue::OfString(s) => {
      Ok(DataValue::OfString(store_string(s, stt)?))
    },
    LeanDataValue::OfBool(b) => Ok(DataValue::OfBool(*b)),
    LeanDataValue::OfName(n) => Ok(DataValue::OfName(compile_name(n, stt)?)),
    LeanDataValue::OfNat(i) => Ok(DataValue::OfNat(store_nat(i, stt)?)),
    LeanDataValue::OfInt(i) => Ok(DataValue::OfInt(store_serialize(i, stt)?)),
    LeanDataValue::OfSyntax(s) => {
      Ok(DataValue::OfSyntax(store_serialize(&compile_syntax(s, stt)?, stt)?))
    },
  }
}

pub fn compile_kv_map(
  kv: &Vec<(Name, LeanDataValue)>,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  let mut list = Vec::with_capacity(kv.len());
  for (name, data_value) in kv {
    let n = compile_name(name, stt)?;
    let d = compile_data_value(data_value, stt)?;
    list.push((n, d));
  }
  store_ixon(&Ixon::meta(vec![Metadatum::KVMap(list)]), stt)
}
pub fn compile_ref(
  name: &Name,
  stt: &CompileState,
) -> Result<MetaAddress, CompileError> {
  if let Some(builtin) = BuiltIn::from_name(name) {
    Ok(MetaAddress {
      data: store_ixon(&Ixon::Prim(builtin), stt)?,
      meta: store_ixon(&Ixon::Meta(Metadata { nodes: vec![] }), stt)?,
    })
  } else if let Some(addr) = stt.consts.get(name) {
    Ok(addr.clone())
  } else {
    Err(CompileError::Ref(name.clone()))
  }
}

pub fn compile_expr(
  expr: &Expr,
  univ_ctx: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<MetaAddress, CompileError> {
  enum Frame<'a> {
    Compile(&'a Expr),
    Mdata(Address),
    App,
    Lam(Address, BinderInfo),
    All(Address, BinderInfo),
    Let(Address, bool),
    Proj(Address, MetaAddress, Nat),
    Cache(Expr),
  }
  if let Some(cached) = cache.exprs.get(expr) {
    return Ok(cached.clone());
  }
  let mut stack: Vec<Frame<'_>> = vec![Frame::Compile(expr)];
  let mut result: Vec<MetaAddress> = vec![];

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Compile(expr) => {
        if let Some(cached) = cache.exprs.get(expr) {
          result.push(cached.clone());
          continue;
        }
        stack.push(Frame::Cache(expr.clone()));
        match expr.as_data() {
          ExprData::Mdata(kv, inner, _) => {
            let md = compile_kv_map(kv, stt)?;
            stack.push(Frame::Mdata(md));
            stack.push(Frame::Compile(inner));
          },
          ExprData::Bvar(idx, _) => {
            let data = store_ixon(&Ixon::EVar(idx.clone()), stt)?;
            let meta = store_ixon(&Ixon::meta(vec![]), stt)?;
            result.push(MetaAddress { meta, data })
          },
          ExprData::Sort(univ, _) => {
            let u = compile_level(univ, univ_ctx, cache, stt)?;
            let data = store_ixon(&Ixon::ESort(u.data), stt)?;
            let meta =
              store_ixon(&Ixon::meta(vec![Metadatum::Link(u.meta)]), stt)?;
            result.push(MetaAddress { meta, data })
          },
          ExprData::Const(name, lvls, _) => {
            let n = compile_name(name, stt)?;
            let mut lds = Vec::with_capacity(lvls.len());
            let mut lms = Vec::with_capacity(lvls.len());
            for l in lvls {
              let u = compile_level(l, univ_ctx, cache, stt)?;
              lds.push(u.data);
              lms.push(u.meta);
            }
            match mut_ctx.get(name) {
              Some(idx) => {
                let data = store_ixon(&Ixon::ERec(idx.clone(), lds), stt)?;
                let meta = store_ixon(
                  &Ixon::meta(vec![Metadatum::Link(n), Metadatum::Links(lms)]),
                  stt,
                )?;
                result.push(MetaAddress { data, meta })
              },
              None => {
                let addr = compile_ref(name, stt)?;
                let data =
                  store_ixon(&Ixon::ERef(addr.data.clone(), lds), stt)?;
                let meta = store_ixon(
                  &Ixon::meta(vec![
                    Metadatum::Link(n),
                    Metadatum::Link(addr.meta.clone()),
                    Metadatum::Links(lms),
                  ]),
                  stt,
                )?;
                result.push(MetaAddress { data, meta })
              },
            };
          },
          ExprData::App(f, a, _) => {
            stack.push(Frame::App);
            stack.push(Frame::Compile(a));
            stack.push(Frame::Compile(f));
          },
          ExprData::Lam(name, t, b, info, _) => {
            let n = compile_name(name, stt)?;
            stack.push(Frame::Lam(n, info.clone()));
            stack.push(Frame::Compile(b));
            stack.push(Frame::Compile(t));
          },
          ExprData::ForallE(name, t, b, info, _) => {
            let n = compile_name(name, stt)?;
            stack.push(Frame::All(n, info.clone()));
            stack.push(Frame::Compile(b));
            stack.push(Frame::Compile(t));
          },
          ExprData::LetE(name, t, v, b, nd, _) => {
            let n = compile_name(name, stt)?;
            stack.push(Frame::Let(n, *nd));
            stack.push(Frame::Compile(b));
            stack.push(Frame::Compile(v));
            stack.push(Frame::Compile(t));
          },
          ExprData::Lit(Literal::NatVal(n), _) => {
            let data = store_ixon(&Ixon::ENat(store_nat(n, stt)?), stt)?;
            let meta = store_ixon(&Ixon::meta(vec![]), stt)?;
            result.push(MetaAddress { data, meta })
          },
          ExprData::Lit(Literal::StrVal(n), _) => {
            let data = store_ixon(&Ixon::EStr(store_string(n, stt)?), stt)?;
            let meta = store_ixon(&Ixon::meta(vec![]), stt)?;
            result.push(MetaAddress { data, meta })
          },
          ExprData::Proj(tn, i, s, _) => {
            let n = compile_name(tn, stt)?;
            let t = compile_ref(tn, stt)?;
            stack.push(Frame::Proj(n, t, i.clone()));
            stack.push(Frame::Compile(s));
          },
          ExprData::Fvar(..) => return Err(CompileError::ExprFVar),
          ExprData::Mvar(..) => return Err(CompileError::ExprMVar),
        }
      },
      Frame::Mdata(md) => {
        let inner = result.pop().unwrap();
        let meta = store_ixon(
          &Ixon::meta(vec![Metadatum::Link(md), Metadatum::Link(inner.meta)]),
          stt,
        )?;
        result.push(MetaAddress { data: inner.data, meta });
      },
      Frame::App => {
        let a = result.pop().expect("Frame::App missing a result");
        let f = result.pop().expect("Frame::App missing f result");
        let data = store_ixon(&Ixon::EApp(f.data, a.data), stt)?;
        let meta = store_ixon(
          &Ixon::meta(vec![Metadatum::Link(f.meta), Metadatum::Link(a.meta)]),
          stt,
        )?;
        result.push(MetaAddress { data, meta })
      },
      Frame::Lam(n, i) => {
        let b = result.pop().expect("Frame::Lam missing b result");
        let t = result.pop().expect("Frame::Lam missing t result");
        let data = store_ixon(&Ixon::ELam(t.data, b.data), stt)?;
        let meta = store_ixon(
          &Ixon::meta(vec![
            Metadatum::Link(n),
            Metadatum::Info(i),
            Metadatum::Link(t.meta),
            Metadatum::Link(b.meta),
          ]),
          stt,
        )?;
        result.push(MetaAddress { data, meta })
      },
      Frame::All(n, i) => {
        let b = result.pop().expect("Frame::All missing b result");
        let t = result.pop().expect("Frame::All missing t result");
        let data = store_ixon(&Ixon::EAll(t.data, b.data), stt)?;
        let meta = store_ixon(
          &Ixon::meta(vec![
            Metadatum::Link(n),
            Metadatum::Info(i),
            Metadatum::Link(t.meta),
            Metadatum::Link(b.meta),
          ]),
          stt,
        )?;
        result.push(MetaAddress { data, meta })
      },
      Frame::Let(n, nd) => {
        let b = result.pop().expect("Frame::Let missing b result");
        let v = result.pop().expect("Frame::Let missing v result");
        let t = result.pop().expect("Frame::Let missing t result");
        let data = store_ixon(&Ixon::ELet(nd, t.data, v.data, b.data), stt)?;
        let meta = store_ixon(
          &Ixon::meta(vec![
            Metadatum::Link(n),
            Metadatum::Link(t.meta),
            Metadatum::Link(v.meta),
            Metadatum::Link(b.meta),
          ]),
          stt,
        )?;
        result.push(MetaAddress { data, meta })
      },
      Frame::Proj(n, t, i) => {
        let s = result.pop().expect("Frame::Proj missing s result");
        let data = store_ixon(&Ixon::EPrj(t.data, i.clone(), s.data), stt)?;
        let meta = store_ixon(
          &Ixon::meta(vec![
            Metadatum::Link(n),
            Metadatum::Link(t.meta),
            Metadatum::Link(s.meta),
          ]),
          stt,
        )?;
        result.push(MetaAddress { data, meta })
      },
      Frame::Cache(expr) => {
        if let Some(result) = result.last() {
          cache.exprs.insert(expr, result.clone());
        }
      },
    }
  }
  result.pop().ok_or(CompileError::CompileExpr)
}

pub fn compare_expr(
  x: &Expr,
  y: &Expr,
  mut_ctx: &MutCtx,
  x_lvls: &[Name],
  y_lvls: &[Name],
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err(CompileError::ExprMVar)
    },
    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err(CompileError::ExprFVar)
    },
    (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
      compare_expr(x, y, mut_ctx, x_lvls, y_lvls, stt)
    },
    (ExprData::Mdata(_, x, _), _) => {
      compare_expr(x, y, mut_ctx, x_lvls, y_lvls, stt)
    },
    (_, ExprData::Mdata(_, y, _)) => {
      compare_expr(x, y, mut_ctx, x_lvls, y_lvls, stt)
    },
    (ExprData::Bvar(x, _), ExprData::Bvar(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Bvar(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Bvar(..)) => Ok(SOrd::gt(true)),
    (ExprData::Sort(x, _), ExprData::Sort(y, _)) => {
      compare_level(x, y, x_lvls, y_lvls)
    },
    (ExprData::Sort(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Sort(..)) => Ok(SOrd::gt(true)),
    (ExprData::Const(x, xls, _), ExprData::Const(y, yls, _)) => {
      let us =
        SOrd::try_zip(|a, b| compare_level(a, b, x_lvls, y_lvls), xls, yls)?;
      if us.ordering != Ordering::Equal {
        Ok(us)
      } else if x == y {
        Ok(SOrd::eq(true))
      } else {
        match (mut_ctx.get(x), mut_ctx.get(y)) {
          (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
          (Some(..), _) => Ok(SOrd::lt(true)),
          (None, Some(..)) => Ok(SOrd::gt(true)),
          (None, None) => {
            let xa = compile_ref(x, stt)?;
            let ya = compile_ref(y, stt)?;
            Ok(SOrd::cmp(&xa.data, &ya.data))
          },
        }
      }
    },

    (ExprData::Const(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Const(..)) => Ok(SOrd::gt(true)),
    (ExprData::App(xl, xr, _), ExprData::App(yl, yr, _)) => SOrd::try_compare(
      compare_expr(xl, yl, mut_ctx, x_lvls, y_lvls, stt)?,
      || compare_expr(xr, yr, mut_ctx, x_lvls, y_lvls, stt),
    ),
    (ExprData::App(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::App(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lam(_, xt, xb, _, _), ExprData::Lam(_, yt, yb, _, _)) => {
      SOrd::try_compare(
        compare_expr(xt, yt, mut_ctx, x_lvls, y_lvls, stt)?,
        || compare_expr(xb, yb, mut_ctx, x_lvls, y_lvls, stt),
      )
    },
    (ExprData::Lam(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lam(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::ForallE(_, xt, xb, _, _),
      ExprData::ForallE(_, yt, yb, _, _),
    ) => SOrd::try_compare(
      compare_expr(xt, yt, mut_ctx, x_lvls, y_lvls, stt)?,
      || compare_expr(xb, yb, mut_ctx, x_lvls, y_lvls, stt),
    ),
    (ExprData::ForallE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::ForallE(..)) => Ok(SOrd::gt(true)),
    (
      ExprData::LetE(_, xt, xv, xb, _, _),
      ExprData::LetE(_, yt, yv, yb, _, _),
    ) => SOrd::try_zip(
      |a, b| compare_expr(a, b, mut_ctx, x_lvls, y_lvls, stt),
      &[xt, xv, xb],
      &[yt, yv, yb],
    ),
    (ExprData::LetE(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::LetE(..)) => Ok(SOrd::gt(true)),
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => Ok(SOrd::cmp(x, y)),
    (ExprData::Lit(..), _) => Ok(SOrd::lt(true)),
    (_, ExprData::Lit(..)) => Ok(SOrd::gt(true)),
    (ExprData::Proj(tnx, ix, tx, _), ExprData::Proj(tny, iy, ty, _)) => {
      let tn = match (mut_ctx.get(tnx), mut_ctx.get(tny)) {
        (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
        (Some(..), _) => Ok(SOrd::lt(true)),
        (None, Some(..)) => Ok(SOrd::gt(true)),
        (None, None) => {
          let xa = compile_ref(tnx, stt)?;
          let ya = compile_ref(tny, stt)?;
          Ok(SOrd::cmp(&xa.data, &ya.data))
        },
      }?;
      SOrd::try_compare(tn, || {
        SOrd::try_compare(SOrd::cmp(ix, iy), || {
          compare_expr(tx, ty, mut_ctx, x_lvls, y_lvls, stt)
        })
      })
    },
  }
}
pub fn compile_defn(
  def: &Def,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Definition, Metadata), CompileError> {
  let univ_ctx = &def.level_params;
  let n = compile_name(&def.name, stt)?;
  let ls =
    def.level_params.iter().map(|n| compile_name(n, stt)).try_collect()?;
  let t = compile_expr(&def.typ, univ_ctx, mut_ctx, cache, stt)?;
  let v = compile_expr(&def.value, univ_ctx, mut_ctx, cache, stt)?;
  let all = def.all.iter().map(|n| compile_name(n, stt)).try_collect()?;
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
  univ_ctx: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(ixon::RecursorRule, Address, Address), CompileError> {
  let n = compile_name(&rule.ctor, stt)?;
  let rhs = compile_expr(&rule.rhs, univ_ctx, mut_ctx, cache, stt)?;
  let data =
    ixon::RecursorRule { fields: rule.n_fields.clone(), rhs: rhs.data };
  Ok((data, n, rhs.meta))
}

pub fn compile_recr(
  recr: &Rec,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Recursor, Metadata), CompileError> {
  let univ_ctx = &recr.cnst.level_params;
  let n = compile_name(&recr.cnst.name, stt)?;
  let ls: Vec<Address> = recr
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n, stt))
    .try_collect()?;
  let t = compile_expr(&recr.cnst.typ, univ_ctx, mut_ctx, cache, stt)?;
  let mut rule_data = Vec::with_capacity(recr.rules.len());
  let mut rule_meta = Vec::with_capacity(recr.rules.len());
  for rule in recr.rules.iter() {
    let (rr, rn, rm) = compile_rule(rule, univ_ctx, mut_ctx, cache, stt)?;
    rule_data.push(rr);
    rule_meta.push((rn, rm));
  }
  let all = recr.all.iter().map(|n| compile_name(n, stt)).try_collect()?;
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
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Constructor, Metadata), CompileError> {
  let n = compile_name(&ctor.cnst.name, stt)?;
  let univ_ctx = &ctor.cnst.level_params;
  let ls = ctor
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n, stt))
    .try_collect()?;
  let t = compile_expr(&ctor.cnst.typ, univ_ctx, mut_ctx, cache, stt)?;
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

pub fn mk_indc(
  ind: &InductiveVal,
  env: &Arc<Env>,
) -> Result<Ind, CompileError> {
  let mut ctors = Vec::with_capacity(ind.ctors.len());
  for ctor_name in &ind.ctors {
    if let Some(ConstantInfo::CtorInfo(c)) = env.as_ref().get(ctor_name) {
      ctors.push(c.clone());
    } else {
      return Err(CompileError::MkIndc);
    };
  }
  Ok(Ind { ind: ind.clone(), ctors })
}

pub fn compile_indc(
  ind: &Ind,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Inductive, FxHashMap<Address, Address>), CompileError> {
  let n = compile_name(&ind.ind.cnst.name, stt)?;
  let univ_ctx = &ind.ind.cnst.level_params;
  let ls = ind
    .ind
    .cnst
    .level_params
    .iter()
    .map(|n| compile_name(n, stt))
    .try_collect()?;
  let t = compile_expr(&ind.ind.cnst.typ, univ_ctx, mut_ctx, cache, stt)?;
  let mut ctor_data = Vec::with_capacity(ind.ctors.len());
  let mut ctor_meta = Vec::with_capacity(ind.ctors.len());
  let mut meta_map = FxHashMap::default();
  for ctor in ind.ctors.iter() {
    let (cd, cm) = compile_ctor(ctor, n.clone(), mut_ctx, cache, stt)?;
    ctor_data.push(cd);
    let cn = compile_name(&ctor.cnst.name, stt)?;
    let cm = store_meta(&cm, stt)?;
    ctor_meta.push(cm.clone());
    meta_map.insert(cn, cm);
  }
  let all = ind.ind.all.iter().map(|n| compile_name(n, stt)).try_collect()?;
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
  let m = store_meta(&meta, stt)?;
  meta_map.insert(n, m);
  Ok((data, meta_map))
}

pub fn compile_quot(
  val: &QuotVal,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Quotient, Metadata), CompileError> {
  let n = compile_name(&val.cnst.name, stt)?;
  let univ_ctx = &val.cnst.level_params;
  let ls =
    val.cnst.level_params.iter().map(|n| compile_name(n, stt)).try_collect()?;
  let t =
    compile_expr(&val.cnst.typ, univ_ctx, &MutCtx::default(), cache, stt)?;
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
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Axiom, Metadata), CompileError> {
  let n = compile_name(&val.cnst.name, stt)?;
  let univ_ctx = &val.cnst.level_params;
  let ls =
    val.cnst.level_params.iter().map(|n| compile_name(n, stt)).try_collect()?;
  let t =
    compile_expr(&val.cnst.typ, univ_ctx, &MutCtx::default(), cache, stt)?;
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
  mut_ctx: &MutCtx,
  stt: &CompileState,
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
              mut_ctx,
              &x.level_params,
              &y.level_params,
              stt,
            )?,
            || {
              compare_expr(
                &x.value,
                &y.value,
                mut_ctx,
                &x.level_params,
                &y.level_params,
                stt,
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
  mut_ctx: &MutCtx,
  stt: &CompileState,
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
              mut_ctx,
              &x.cnst.level_params,
              &y.cnst.level_params,
              stt,
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
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  let key = if x.cnst.name <= y.cnst.name {
    (x.cnst.name.clone(), y.cnst.name.clone())
  } else {
    (y.cnst.name.clone(), x.cnst.name.clone())
  };
  if let Some(o) = cache.cmps.get(&key) {
    Ok(SOrd { strong: true, ordering: *o })
  } else {
    let so = compare_ctor_inner(x, y, mut_ctx, stt)?;
    if so.strong {
      cache.cmps.insert(key, so.ordering);
    }
    Ok(so)
  }
}

pub fn compare_indc(
  x: &Ind,
  y: &Ind,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(
    SOrd::cmp(&x.ind.cnst.level_params.len(), &y.ind.cnst.level_params.len()),
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
                    mut_ctx,
                    &x.ind.cnst.level_params,
                    &y.ind.cnst.level_params,
                    stt,
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| compare_ctor(a, b, mut_ctx, cache, stt),
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
  mut_ctx: &MutCtx,
  x_lvls: &[Name],
  y_lvls: &[Name],
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  SOrd::try_compare(SOrd::cmp(&x.n_fields, &y.n_fields), || {
    compare_expr(&x.rhs, &y.rhs, mut_ctx, x_lvls, y_lvls, stt)
  })
}

pub fn compare_recr(
  x: &Rec,
  y: &Rec,
  mut_ctx: &MutCtx,
  stt: &CompileState,
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
                    mut_ctx,
                    &x.cnst.level_params,
                    &y.cnst.level_params,
                    stt,
                  )?,
                  || {
                    SOrd::try_zip(
                      |a, b| {
                        compare_recr_rule(
                          a,
                          b,
                          mut_ctx,
                          &x.cnst.level_params,
                          &y.cnst.level_params,
                          stt,
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
  x: &MutConst,
  y: &MutConst,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Ordering, CompileError> {
  let key = if x.name() <= y.name() {
    (x.name(), y.name())
  } else {
    (y.name(), x.name())
  };
  if let Some(so) = cache.cmps.get(&key) {
    Ok(*so)
  } else {
    let so: SOrd = match (x, y) {
      (MutConst::Defn(x), MutConst::Defn(y)) => {
        compare_defn(x, y, mut_ctx, stt)?
      },
      (MutConst::Indc(x), MutConst::Indc(y)) => {
        compare_indc(x, y, mut_ctx, cache, stt)?
      },
      (MutConst::Recr(x), MutConst::Recr(y)) => {
        compare_recr(x, y, mut_ctx, stt)?
      },
      (MutConst::Defn(_) | MutConst::Indc(_) | MutConst::Recr(_), _) => {
        SOrd::lt(true)
      },
    };
    if so.strong {
      cache.cmps.insert(key, so.ordering);
    }
    Ok(so.ordering)
  }
}

pub fn eq_const(
  x: &MutConst,
  y: &MutConst,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<bool, CompileError> {
  let ordering = compare_const(x, y, mut_ctx, cache, stt)?;
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
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
  let mut result = Vec::with_capacity(left.len() + right.len());
  let mut left_iter = left.into_iter();
  let mut right_iter = right.into_iter();
  let mut left_item = left_iter.next();
  let mut right_item = right_iter.next();

  while let (Some(l), Some(r)) = (&left_item, &right_item) {
    let cmp = compare_const(l, r, ctx, cache, stt)?;
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
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<&'a MutConst>, CompileError> {
  if items.len() <= 1 {
    return Ok(items.to_vec());
  }
  let mid = items.len() / 2;
  let (left, right) = items.split_at(mid);
  let left = sort_by_compare(left, ctx, cache, stt)?;
  let right = sort_by_compare(right, ctx, cache, stt)?;
  merge(left, right, ctx, cache, stt)
}

pub fn sort_consts<'a>(
  cs: &[&'a MutConst],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<Vec<&'a MutConst>>, CompileError> {
  //println!("sort_consts");
  let mut classes = vec![cs.to_owned()];
  loop {
    //println!("sort_consts loop");
    let ctx = MutConst::ctx(&classes);
    let mut new_classes: Vec<Vec<&MutConst>> = vec![];
    for class in classes.iter() {
      match class.len() {
        0 => {
          return Err(CompileError::SortConsts);
        },
        1 => {
          new_classes.push(class.clone());
        },
        _ => {
          let sorted = sort_by_compare(class.as_ref(), &ctx, cache, stt)?;
          let groups =
            group_by(sorted, |a, b| eq_const(a, b, &ctx, cache, stt))?;
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
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Ixon, FxHashMap<Address, Address>), CompileError> {
  //println!("compile_mut_consts");
  let mut data = vec![];
  let mut meta = FxHashMap::default();
  for class in classes {
    let mut class_data = vec![];
    for cnst in class {
      match cnst {
        MutConst::Indc(x) => {
          let (i, m) = compile_indc(x, mut_ctx, cache, stt)?;
          class_data.push(ixon::MutConst::Indc(i));
          meta.extend(m);
        },
        MutConst::Defn(x) => {
          let (d, m) = compile_defn(x, mut_ctx, cache, stt)?;
          class_data.push(ixon::MutConst::Defn(d));
          meta.insert(compile_name(&x.name, stt)?, store_meta(&m, stt)?);
        },
        MutConst::Recr(x) => {
          let (r, m) = compile_recr(x, mut_ctx, cache, stt)?;
          class_data.push(ixon::MutConst::Recr(r));
          meta.insert(compile_name(&x.cnst.name, stt)?, store_meta(&m, stt)?);
        },
      }
    }
    if class_data.is_empty() || !class_data.iter().all(|x| x == &class_data[0])
    {
      return Err(CompileError::CompileMutConsts(class_data.clone()));
    } else {
      data.push(class_data[0].clone())
    }
  }
  Ok((Ixon::Muts(data), meta))
}

pub fn compile_mutual(
  mutual: &MutConst,
  all: &NameSet,
  env: &Arc<Env>,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Ixon, Ixon), CompileError> {
  //println!("compile_mutual");
  if all.len() == 1 && matches!(&mutual, MutConst::Defn(_) | MutConst::Recr(_))
  {
    match mutual {
      MutConst::Defn(defn) => {
        //println!("compile_mutual defn");
        let mut_ctx = MutConst::single_ctx(defn.name.clone());
        let (data, meta) = compile_defn(defn, &mut_ctx, cache, stt)?;
        Ok((Ixon::Defn(data), Ixon::Meta(meta)))
      },
      MutConst::Recr(recr) => {
        //println!("compile_mutual recr");
        let mut_ctx = MutConst::single_ctx(recr.cnst.name.clone());
        let (data, meta) = compile_recr(recr, &mut_ctx, cache, stt)?;
        Ok((Ixon::Recr(data), Ixon::Meta(meta)))
      },
      _ => {
        //println!("compile_mutual unreachable");
        unreachable!()
      },
    }
  } else {
    //println!("compile_mutual else");
    let mut cs = Vec::new();
    for name in all {
      let Some(const_info) = env.get(name) else {
        return Err(CompileError::CompileMutual);
      };
      let mut_const = match const_info {
        ConstantInfo::InductInfo(val) => {
          //println!("compile_mutual InductInfo");
          MutConst::Indc(mk_indc(val, env)?)
        },
        ConstantInfo::DefnInfo(val) => {
          //println!("compile_mutual DefnInfo");
          MutConst::Defn(Def::mk_defn(val))
        },
        ConstantInfo::OpaqueInfo(val) => {
          //println!("compile_mutual OpaqueInfo");
          MutConst::Defn(Def::mk_opaq(val))
        },
        ConstantInfo::ThmInfo(val) => {
          //println!("compile_mutual ThmInfo");
          MutConst::Defn(Def::mk_theo(val))
        },
        ConstantInfo::RecInfo(val) => {
          //println!("compile_mutual RecInfo");
          MutConst::Recr(val.clone())
        },
        _ => {
          //println!("compile_mutual continue");
          continue;
        },
      };
      cs.push(mut_const);
    }
    let mut_consts =
      sort_consts(&cs.iter().collect::<Vec<&MutConst>>(), cache, stt)?;
    let mut_meta: Vec<Vec<Address>> = mut_consts
      .iter()
      .map(|m| m.iter().map(|c| compile_name(&c.name(), stt)).try_collect())
      .try_collect()?;
    let mut_ctx = MutConst::ctx(&mut_consts);
    let (data, metas) = compile_mut_consts(mut_consts, &mut_ctx, cache, stt)?;
    let ctx = mut_ctx
      .iter()
      .map(|(n, i)| Ok((compile_name(n, stt)?, store_nat(i, stt)?)))
      .try_collect()?;
    let block = MetaAddress {
      data: store_ixon(&data, stt)?,
      meta: store_meta(
        &Metadata {
          nodes: vec![
            Metadatum::Muts(mut_meta),
            Metadatum::Map(ctx),
            Metadatum::Map(metas.clone().into_iter().collect()),
          ],
        },
        stt,
      )?,
    };
    stt.blocks.insert(block.clone());
    let mut ret: Option<(Ixon, Ixon)> = None;
    for c in cs {
      let idx = mut_ctx.get(&c.name()).ok_or(CompileError::CompileMutual2)?;
      let n = compile_name(&c.name(), stt)?;
      let meta = match metas.get(&n) {
        Some(m) => Ok(Metadata {
          nodes: vec![
            Metadatum::Link(block.meta.clone()),
            Metadatum::Link(m.clone()),
          ],
        }),
        None => Err(CompileError::CompileMutual3),
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
        data: store_ixon(&data, stt)?,
        meta: store_meta(&meta, stt)?,
      };
      stt.consts.insert(c.name(), addr.clone());
      if c.name() == mutual.name() {
        ret = Some((data, Ixon::Meta(meta)));
      }
      for ctor in c.ctors() {
        let cdata = Ixon::CPrj(ConstructorProj {
          idx: idx.clone(),
          cidx: ctor.cidx.clone(),
          block: block.data.clone(),
        });
        let cn = compile_name(&ctor.cnst.name, stt)?;
        let cmeta = match metas.get(&cn) {
          Some(m) => Ok(Metadata {
            nodes: vec![
              Metadatum::Link(block.meta.clone()),
              Metadatum::Link(m.clone()),
            ],
          }),
          None => Err(CompileError::CompileMutual4),
        }?;
        let caddr = MetaAddress {
          data: store_ixon(&cdata, stt)?,
          meta: store_meta(&cmeta, stt)?,
        };
        stt.consts.insert(ctor.cnst.name, caddr);
      }
    }
    ret.ok_or(CompileError::CompileMutual5)
  }
}

pub fn compile_const_info(
  cnst: &ConstantInfo,
  all: &NameSet,
  env: &Arc<Env>,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<MetaAddress, CompileError> {
  match cnst {
    ConstantInfo::DefnInfo(val) => {
      //println!("compile_const_info def");
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_defn(val)),
        all,
        env,
        cache,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d, stt)?, meta: store_ixon(&m, stt)? })
    },
    ConstantInfo::OpaqueInfo(val) => {
      //println!("compile_const_info opaq");
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_opaq(val)),
        all,
        env,
        cache,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d, stt)?, meta: store_ixon(&m, stt)? })
    },
    ConstantInfo::ThmInfo(val) => {
      //println!("compile_const_info theo");
      let (d, m) = compile_mutual(
        &MutConst::Defn(Def::mk_theo(val)),
        all,
        env,
        cache,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d, stt)?, meta: store_ixon(&m, stt)? })
    },
    ConstantInfo::CtorInfo(val) => {
      //println!("compile_const_info ctor");
      if let Some(ConstantInfo::InductInfo(ind)) = env.as_ref().get(&val.induct)
      {
        let _ = compile_mutual(
          &MutConst::Indc(mk_indc(ind, env)?),
          all,
          env,
          cache,
          stt,
        )?;
        let addr = stt
          .consts
          .get(&val.cnst.name)
          .ok_or(CompileError::CompileConstInfo)?;
        Ok(addr.clone())
      } else {
        Err(CompileError::CompileConstInfo2)
      }
    },
    ConstantInfo::InductInfo(val) => {
      //println!("compile_const_info ind");
      let (d, m) = compile_mutual(
        &MutConst::Indc(mk_indc(val, env)?),
        all,
        env,
        cache,
        stt,
      )?;
      Ok(MetaAddress { data: store_ixon(&d, stt)?, meta: store_ixon(&m, stt)? })
    },
    ConstantInfo::RecInfo(val) => {
      //println!("compile_const_info rec");
      let (d, m) =
        compile_mutual(&MutConst::Recr(val.clone()), all, env, cache, stt)?;
      Ok(MetaAddress { data: store_ixon(&d, stt)?, meta: store_ixon(&m, stt)? })
    },
    ConstantInfo::QuotInfo(val) => {
      //println!("compile_const_info quot");
      let (quot, meta) = compile_quot(val, cache, stt)?;
      Ok(MetaAddress {
        data: store_ixon(&Ixon::Quot(quot), stt)?,
        meta: store_ixon(&Ixon::Meta(meta), stt)?,
      })
    },
    ConstantInfo::AxiomInfo(val) => {
      //println!("compile_const_info axio");
      let (axio, meta) = compile_axio(val, cache, stt)?;
      Ok(MetaAddress {
        data: store_ixon(&Ixon::Axio(axio), stt)?,
        meta: store_ixon(&Ixon::Meta(meta), stt)?,
      })
    },
  }
}
//
pub fn compile_const(
  name: &Name,
  all: &NameSet,
  env: &Arc<Env>,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<MetaAddress, CompileError> {
  //println!("compile_const {:?}", name.pretty());
  if let Some(cached) = stt.consts.get(name) {
    Ok(cached.clone())
  } else {
    let cnst = env.as_ref().get(name).ok_or(CompileError::CompileConst)?;
    let addr = compile_const_info(cnst, all, env, cache, stt)?;
    stt.consts.insert(name.clone(), addr.clone());
    Ok(addr)
  }
}

pub fn compile_env(env: &Arc<Env>) -> Result<CompileState, CompileError> {
  let start_ref_graph = std::time::SystemTime::now();
  let graph = build_ref_graph(env.as_ref());
  println!(
    "Ref-graph: {:.2}s",
    start_ref_graph.elapsed().unwrap().as_secs_f32()
  );
  let start_ground = std::time::SystemTime::now();
  let ungrounded = ground_consts(env.as_ref(), &graph.in_refs);
  if !ungrounded.is_empty() {
    for (n, e) in ungrounded {
      println!("Ungrounded {:?}: {:?}", n, e);
    }
    return Err(CompileError::UngroundedEnv);
  }
  println!("Ground: {:.2}s", start_ground.elapsed().unwrap().as_secs_f32());
  let start_sccs = std::time::SystemTime::now();
  let blocks = compute_sccs(&graph.out_refs);
  println!("SCCs: {:.2}s", start_sccs.elapsed().unwrap().as_secs_f32());
  let start_compile = std::time::SystemTime::now();
  let stt = CompileState::default();

  let remaining: DashMap<Name, (NameSet, NameSet)> = DashMap::default();

  blocks.blocks.par_iter().try_for_each(|(lo, all)| {
    let deps = blocks.block_refs.get(lo).ok_or(CompileError::CondenseError)?;
    remaining.insert(lo.clone(), (all.clone(), deps.clone()));
    Ok::<(), CompileError>(())
  })?;

  //let num_blocks = remaining.len();
  //let mut i = 0;

  while !remaining.is_empty() {
    //i += 1;
    //let len = remaining.len();
    //let pct = 100f64 - ((len as f64 / num_blocks as f64) * 100f64);
    //println!("Wave {i}, {pct}%: {len}/{num_blocks}");
    //println!("Stats {:?}", stt.stats());
    let ready: DashMap<Name, NameSet> = DashMap::default();
    remaining.par_iter().for_each(|entry| {
      let lo = entry.key();
      let (all, deps) = entry.value();
      if deps.iter().all(|x| stt.consts.contains_key(x)) {
        ready.insert(lo.clone(), all.clone());
      }
    });
    //println!("Wave {i} ready {}", ready.len());

    ready.par_iter().try_for_each(|entry| {
      let mut cache = BlockCache::default();
      compile_const(entry.key(), entry.value(), env, &mut cache, &stt)?;
      remaining.remove(entry.key());
      Ok::<(), CompileError>(())
    })?;
  }
  println!("Compile: {:.2}s", start_compile.elapsed().unwrap().as_secs_f32());
  Ok(stt)
}
