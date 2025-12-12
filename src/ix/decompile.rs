use crate::{
  ix::address::{Address, MetaAddress},
  ix::compile::CompileState,
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo, ConstantVal, ConstructorVal,
    DataValue as LeanDataValue, DefinitionSafety, DefinitionVal, Env, Expr,
    InductiveVal, Int, Level, Literal, Name, OpaqueVal, QuotVal, RecursorRule,
    RecursorVal, SourceInfo as LeanSourceInfo, Substring as LeanSubstring,
    Syntax as LeanSyntax, SyntaxPreresolved, TheoremVal,
  },
  ix::ixon::{
    self, Constructor, DataValue, DefKind, Definition, Inductive, Ixon,
    Metadata, Metadatum, MutConst, Preresolved, Recursor, Serialize,
    SourceInfo, Substring, Syntax,
  },
  ix::mutual::MutCtx,
  lean::nat::Nat,
};
use blake3::Hash;
use dashmap::DashMap;
use itertools::Itertools;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;
use std::str::Utf8Error;

#[derive(Debug)]
pub enum DecompileError {
  UnknownStoreAddress,
  Deserialize(String),
  Utf8(Utf8Error),
  BadBlock(Box<(Ixon, Ixon)>),
  BadName(Box<Ixon>),
  BadLevel(Box<Ixon>),
  BadExprERec(Name, Box<Nat>),
  ConstName(Name, Name),
  BadDef(Box<(Definition, Metadata)>),
  BadInd(Box<(Inductive, Metadata)>),
  BadRec(Box<(Recursor, Metadata)>),
  BadCtor(Box<(Constructor, Metadata)>),
  MismatchedLevels(Name, Nat, Vec<Address>),
  MismatchedCtors(Name, Vec<Constructor>, Vec<Address>),
  MalformedProjection(Name, Address),
  ConstAddrNotDecompiled(Name, Box<MetaAddress>),
  ConstAddrMismatch(Name, Box<MetaAddress>, Name),
  ConstNameNotCompiled(Name, Box<MetaAddress>),
  ConstNameMismatch(Name, Box<(MetaAddress, MetaAddress)>),
  ConstMissingInOriginal(Name),
  ConstHashMismatch(Name, Box<(Hash, Hash)>),
  EnvSizeMismatch { original: usize, decompiled: usize },
  Todo,
}

#[derive(Default, Debug)]
pub struct DecompileState {
  pub names: DashMap<Address, Name>,
  pub consts: DashMap<MetaAddress, Name>,
  pub block_ctx: DashMap<MetaAddress, MutCtx>,
  pub env: DashMap<Name, ConstantInfo>,
}

#[derive(Debug)]
pub struct DecompileStateStats {
  pub names: usize,
  pub consts: usize,
  pub block_ctx: usize,
  pub env: usize,
}

impl DecompileState {
  pub fn stats(&self) -> DecompileStateStats {
    DecompileStateStats {
      names: self.names.len(),
      consts: self.consts.len(),
      block_ctx: self.block_ctx.len(),
      env: self.env.len(),
    }
  }
}

#[derive(Default, Debug)]
pub struct BlockCache {
  pub ctx: MutCtx,
  pub exprs: FxHashMap<MetaAddress, Expr>,
  pub univs: FxHashMap<Address, Level>,
}

pub fn read_ixon(
  addr: &Address,
  stt: &CompileState,
) -> Result<Ixon, DecompileError> {
  let bytes = stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
  Ixon::get(&mut bytes.as_slice()).map_err(DecompileError::Deserialize)
}

pub fn read_nat(
  addr: &Address,
  stt: &CompileState,
) -> Result<Nat, DecompileError> {
  let bytes = stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
  Ok(Nat::from_le_bytes(&bytes))
}

pub fn read_string(
  addr: &Address,
  stt: &CompileState,
) -> Result<String, DecompileError> {
  let bytes = stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
  let str = str::from_utf8(&bytes).map_err(DecompileError::Utf8)?;
  Ok(str.to_owned())
}

pub fn read_meta(
  addr: &Address,
  stt: &CompileState,
) -> Result<Metadata, DecompileError> {
  let bytes = stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
  Metadata::get(&mut bytes.as_slice()).map_err(DecompileError::Deserialize)
}

pub fn decompile_name(
  addr: &Address,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<Name, DecompileError> {
  match dstt.names.get(addr) {
    Some(name) => Ok(name.clone()),
    None => {
      let name = match read_ixon(addr, stt)? {
        Ixon::NAnon => Name::anon(),
        Ixon::NStr(n, s) => {
          Name::str(decompile_name(&n, stt, dstt)?, read_string(&s, stt)?)
        },
        Ixon::NNum(n, s) => {
          Name::num(decompile_name(&n, stt, dstt)?, read_nat(&s, stt)?)
        },
        e => return Err(DecompileError::BadName(Box::new(e))),
      };
      dstt.names.insert(addr.clone(), name.clone());
      Ok(name)
    },
  }
}

pub fn decompile_level(
  addr: &Address,
  lvls: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Level, DecompileError> {
  if let Some(cached) = cache.univs.get(addr) {
    return Ok(cached.clone());
  }
  let level = match read_ixon(addr, stt)? {
    Ixon::UZero => Ok(Level::zero()),
    Ixon::USucc(x) => {
      let inner = decompile_level(&x, lvls, cache, stt)?;
      Ok(Level::succ(inner))
    },
    Ixon::UMax(x, y) => {
      let lx = decompile_level(&x, lvls, cache, stt)?;
      let ly = decompile_level(&y, lvls, cache, stt)?;
      Ok(Level::max(lx, ly))
    },
    Ixon::UIMax(x, y) => {
      let lx = decompile_level(&x, lvls, cache, stt)?;
      let ly = decompile_level(&y, lvls, cache, stt)?;
      Ok(Level::imax(lx, ly))
    },
    Ixon::UVar(idx) => {
      let idx_usize: usize =
        idx.0.try_into().map_err(|_e| DecompileError::Todo)?;
      let name = lvls.get(idx_usize).ok_or(DecompileError::Todo)?.clone();
      Ok(Level::param(name))
    },
    e => Err(DecompileError::BadLevel(Box::new(e))),
  }?;
  cache.univs.insert(addr.clone(), level.clone());
  Ok(level)
}

fn decompile_levels(
  addrs: &[Address],
  lvls: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Vec<Level>, DecompileError> {
  addrs.iter().map(|a| decompile_level(a, lvls, cache, stt)).collect()
}

fn decompile_substring(
  ss: &Substring,
  stt: &CompileState,
) -> Result<LeanSubstring, DecompileError> {
  Ok(LeanSubstring {
    str: read_string(&ss.str, stt)?,
    start_pos: ss.start_pos.clone(),
    stop_pos: ss.stop_pos.clone(),
  })
}

fn decompile_source_info(
  info: &SourceInfo,
  stt: &CompileState,
) -> Result<LeanSourceInfo, DecompileError> {
  match info {
    SourceInfo::Original(l, p, t, e) => Ok(LeanSourceInfo::Original(
      decompile_substring(l, stt)?,
      p.clone(),
      decompile_substring(t, stt)?,
      e.clone(),
    )),
    SourceInfo::Synthetic(p, e, c) => {
      Ok(LeanSourceInfo::Synthetic(p.clone(), e.clone(), *c))
    },
    SourceInfo::None => Ok(LeanSourceInfo::None),
  }
}

fn decompile_preresolved(
  pre: &Preresolved,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<SyntaxPreresolved, DecompileError> {
  match pre {
    Preresolved::Namespace(ns) => {
      Ok(SyntaxPreresolved::Namespace(decompile_name(ns, stt, dstt)?))
    },
    Preresolved::Decl(n, fields) => {
      let name = decompile_name(n, stt, dstt)?;
      let fields: Result<Vec<String>, _> =
        fields.iter().map(|f| read_string(f, stt)).collect();
      Ok(SyntaxPreresolved::Decl(name, fields?))
    },
  }
}

fn decompile_syntax(
  addr: &Address,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanSyntax, DecompileError> {
  let bytes = stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
  let syn =
    Syntax::get(&mut bytes.as_slice()).map_err(DecompileError::Deserialize)?;

  match syn {
    Syntax::Missing => Ok(LeanSyntax::Missing),
    Syntax::Node(info, kind, args) => {
      let info = decompile_source_info(&info, stt)?;
      let kind = decompile_name(&kind, stt, dstt)?;
      let args: Result<Vec<_>, _> =
        args.iter().map(|a| decompile_syntax(a, stt, dstt)).collect();
      Ok(LeanSyntax::Node(info, kind, args?))
    },
    Syntax::Atom(info, val) => {
      let info = decompile_source_info(&info, stt)?;
      Ok(LeanSyntax::Atom(info, read_string(&val, stt)?))
    },
    Syntax::Ident(info, raw_val, val, preresolved) => {
      let info = decompile_source_info(&info, stt)?;
      let raw_val = decompile_substring(&raw_val, stt)?;
      let val = decompile_name(&val, stt, dstt)?;
      let pres: Result<Vec<_>, _> = preresolved
        .iter()
        .map(|p| decompile_preresolved(p, stt, dstt))
        .collect();
      Ok(LeanSyntax::Ident(info, raw_val, val, pres?))
    },
  }
}

fn decompile_data_value(
  dv: &DataValue,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<LeanDataValue, DecompileError> {
  match dv {
    DataValue::OfString(addr) => {
      Ok(LeanDataValue::OfString(read_string(addr, stt)?))
    },
    DataValue::OfBool(b) => Ok(LeanDataValue::OfBool(*b)),
    DataValue::OfName(addr) => {
      Ok(LeanDataValue::OfName(decompile_name(addr, stt, dstt)?))
    },
    DataValue::OfNat(addr) => Ok(LeanDataValue::OfNat(read_nat(addr, stt)?)),
    DataValue::OfInt(addr) => {
      let bytes =
        stt.store.get(addr).ok_or(DecompileError::UnknownStoreAddress)?;
      let int =
        Int::get(&mut bytes.as_slice()).map_err(DecompileError::Deserialize)?;
      Ok(LeanDataValue::OfInt(int))
    },
    DataValue::OfSyntax(addr) => {
      Ok(LeanDataValue::OfSyntax(Box::new(decompile_syntax(addr, stt, dstt)?)))
    },
  }
}
fn decompile_kv_map(
  kvs: &[(Address, DataValue)],
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<Vec<(Name, LeanDataValue)>, DecompileError> {
  let mut kv = vec![];
  for (n, v) in kvs {
    let name = decompile_name(n, stt, dstt)?;
    let val = decompile_data_value(v, stt, dstt)?;
    kv.push((name, val))
  }
  Ok(kv)
}

pub fn decompile_expr(
  addr: MetaAddress,
  lvls: &[Name],
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<Expr, DecompileError> {
  enum Frame {
    Decompile(MetaAddress),
    Mdata(Vec<(Name, LeanDataValue)>),
    App,
    Lam(Name, BinderInfo),
    All(Name, BinderInfo),
    Let(Name, bool),
    Proj(Name, Nat),
    Cache(MetaAddress),
  }
  if let Some(expr) = cache.exprs.get(&addr) {
    return Ok(expr.clone());
  }

  let mut stack = vec![Frame::Decompile(addr)];
  let mut res = vec![];

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Decompile(addr) => {
        if let Some(expr) = cache.exprs.get(&addr) {
          res.push(expr.clone());
          continue;
        }
        let meta_ixon = read_ixon(&addr.meta, stt)?;
        if let Ixon::Meta(m) = &meta_ixon
          && let [Metadatum::KVMap(kv), Metadatum::Link(inner_meta)] =
            m.nodes.as_slice()
        {
          let kv = decompile_kv_map(kv, stt, dstt)?;
          stack.push(Frame::Cache(addr.clone()));
          stack.push(Frame::Mdata(kv));
          stack.push(Frame::Decompile(MetaAddress {
            data: addr.data.clone(),
            meta: inner_meta.clone(),
          }));
          continue;
        }
        let data_ixon = read_ixon(&addr.data, stt)?;
        match (&data_ixon, &meta_ixon) {
          (Ixon::EVar(idx), Ixon::Meta(m)) if m.nodes.is_empty() => {
            let expr = Expr::bvar(idx.clone());
            cache.exprs.insert(addr, expr.clone());
            res.push(expr);
          },
          (Ixon::ESort(u_data), Ixon::Meta(m)) if m.nodes.is_empty() => {
            let level = decompile_level(u_data, lvls, cache, stt)?;
            let expr = Expr::sort(level);
            cache.exprs.insert(addr, expr.clone());
            res.push(expr);
          },
          (Ixon::ERef(_, lvl_datas), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [Metadatum::Link(name_addr), Metadatum::Link(_)] => {
                let name = decompile_name(name_addr, stt, dstt)?;
                let levels = decompile_levels(lvl_datas, lvls, cache, stt)?;
                let expr = Expr::cnst(name, levels);
                cache.exprs.insert(addr, expr.clone());
                res.push(expr);
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::ERec(idx, lvl_datas), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [Metadatum::Link(name_addr)] => {
                let name = decompile_name(name_addr, stt, dstt)?;
                let levels = decompile_levels(lvl_datas, lvls, cache, stt)?;
                match cache.ctx.get(&name) {
                  Some(i) if i == idx => {},
                  _ => {
                    return Err(DecompileError::BadExprERec(
                      name,
                      Box::new(idx.clone()),
                    ));
                  },
                }
                let expr = Expr::cnst(name, levels);
                cache.exprs.insert(addr, expr.clone());
                res.push(expr);
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::ENat(nat_addr), Ixon::Meta(m)) if m.nodes.is_empty() => {
            let n = read_nat(nat_addr, stt)?;
            let expr = Expr::lit(Literal::NatVal(n));
            cache.exprs.insert(addr, expr.clone());
            res.push(expr);
          },
          (Ixon::EStr(str_addr), Ixon::Meta(m)) if m.nodes.is_empty() => {
            let s = read_string(str_addr, stt)?;
            let expr = Expr::lit(Literal::StrVal(s));
            cache.exprs.insert(addr, expr.clone());
            res.push(expr);
          },
          (Ixon::EApp(f_data, a_data), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [Metadatum::Link(f_meta), Metadatum::Link(a_meta)] => {
                stack.push(Frame::Cache(addr.clone()));
                stack.push(Frame::App);
                stack.push(Frame::Decompile(MetaAddress {
                  data: a_data.clone(),
                  meta: a_meta.clone(),
                }));
                stack.push(Frame::Decompile(MetaAddress {
                  data: f_data.clone(),
                  meta: f_meta.clone(),
                }));
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::ELam(t_data, b_data), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [
                Metadatum::Link(n_addr),
                Metadatum::Info(bi),
                Metadatum::Link(t_meta),
                Metadatum::Link(b_meta),
              ] => {
                let name = decompile_name(n_addr, stt, dstt)?;
                stack.push(Frame::Cache(addr.clone()));
                stack.push(Frame::Lam(name, bi.clone()));
                stack.push(Frame::Decompile(MetaAddress {
                  data: b_data.clone(),
                  meta: b_meta.clone(),
                }));
                stack.push(Frame::Decompile(MetaAddress {
                  data: t_data.clone(),
                  meta: t_meta.clone(),
                }));
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::EAll(t_data, b_data), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [
                Metadatum::Link(n_addr),
                Metadatum::Info(bi),
                Metadatum::Link(t_meta),
                Metadatum::Link(b_meta),
              ] => {
                let name = decompile_name(n_addr, stt, dstt)?;
                stack.push(Frame::Cache(addr.clone()));
                stack.push(Frame::All(name, bi.clone()));
                stack.push(Frame::Decompile(MetaAddress {
                  data: b_data.clone(),
                  meta: b_meta.clone(),
                }));
                stack.push(Frame::Decompile(MetaAddress {
                  data: t_data.clone(),
                  meta: t_meta.clone(),
                }));
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::ELet(nd, t_data, v_data, b_data), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [
                Metadatum::Link(n_addr),
                Metadatum::Link(t_meta),
                Metadatum::Link(v_meta),
                Metadatum::Link(b_meta),
              ] => {
                let name = decompile_name(n_addr, stt, dstt)?;
                stack.push(Frame::Cache(addr.clone()));
                stack.push(Frame::Let(name, *nd));
                stack.push(Frame::Decompile(MetaAddress {
                  data: b_data.clone(),
                  meta: b_meta.clone(),
                }));
                stack.push(Frame::Decompile(MetaAddress {
                  data: v_data.clone(),
                  meta: v_meta.clone(),
                }));
                stack.push(Frame::Decompile(MetaAddress {
                  data: t_data.clone(),
                  meta: t_meta.clone(),
                }));
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          (Ixon::EPrj(_, idx, s_data), Ixon::Meta(m)) => {
            match m.nodes.as_slice() {
              [
                Metadatum::Link(n_addr),
                Metadatum::Link(_),
                Metadatum::Link(s_meta),
              ] => {
                let name = decompile_name(n_addr, stt, dstt)?;
                stack.push(Frame::Cache(addr.clone()));
                stack.push(Frame::Proj(name, idx.clone()));
                stack.push(Frame::Decompile(MetaAddress {
                  data: s_data.clone(),
                  meta: s_meta.clone(),
                }));
              },
              _ => return Err(DecompileError::Todo),
            }
          },
          _ => return Err(DecompileError::Todo),
        }
      },
      Frame::Mdata(kv) => {
        let inner = res.pop().expect("Mdata missing inner");
        let expr = Expr::mdata(kv, inner);
        res.push(expr);
      },
      Frame::App => {
        let a = res.pop().expect("App missing a");
        let f = res.pop().expect("App missing f");
        let expr = Expr::app(f, a);
        res.push(expr);
      },
      Frame::Lam(name, bi) => {
        let body = res.pop().expect("Lam missing body");
        let typ = res.pop().expect("Lam missing typ");
        let expr = Expr::lam(name, typ, body, bi);
        res.push(expr);
      },
      Frame::All(name, bi) => {
        let body = res.pop().expect("All missing body");
        let typ = res.pop().expect("All missing typ");
        let expr = Expr::all(name, typ, body, bi);
        res.push(expr);
      },
      Frame::Let(name, nd) => {
        let body = res.pop().expect("Let missing body");
        let val = res.pop().expect("Let missing val");
        let typ = res.pop().expect("Let missing typ");
        let expr = Expr::letE(name, typ, val, body, nd);
        res.push(expr);
      },
      Frame::Proj(name, idx) => {
        let s = res.pop().expect("Proj missing s");
        let expr = Expr::proj(name, idx, s);
        res.push(expr);
      },
      Frame::Cache(maddr) => {
        if let Some(expr) = res.last() {
          cache.exprs.insert(maddr, expr.clone());
        }
      },
    }
  }
  res.pop().ok_or(DecompileError::Todo)
}

pub fn decompile_const_val(
  name: &Address,
  num_lvls: &Nat,
  lvl_names: &[Address],
  typ: MetaAddress,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstantVal, DecompileError> {
  let name = decompile_name(name, stt, dstt)?;
  if Nat(lvl_names.len().into()) != *num_lvls {
    return Err(DecompileError::MismatchedLevels(
      name.clone(),
      num_lvls.clone(),
      lvl_names.to_vec(),
    ));
  }
  let level_params: Vec<Name> =
    lvl_names.iter().map(|x| decompile_name(x, stt, dstt)).try_collect()?;
  let typ = decompile_expr(typ, &level_params, cache, stt, dstt)?;
  Ok(ConstantVal { name, level_params, typ })
}

pub fn decompile_ctor(
  ctor: &Constructor,
  meta: &Address,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstructorVal, DecompileError> {
  let meta = read_meta(meta, stt)?;
  match meta.nodes.as_slice() {
    [
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(tm),
      Metadatum::Link(i),
    ] => {
      let cnst = decompile_const_val(
        n,
        &ctor.lvls,
        ls,
        MetaAddress { data: ctor.typ.clone(), meta: tm.clone() },
        cache,
        stt,
        dstt,
      )?;
      let induct = decompile_name(i, stt, dstt)?;
      Ok(ConstructorVal {
        cnst,
        induct,
        cidx: ctor.cidx.clone(),
        num_params: ctor.params.clone(),
        num_fields: ctor.fields.clone(),
        is_unsafe: ctor.is_unsafe,
      })
    },
    _ => Err(DecompileError::BadCtor(Box::new((ctor.clone(), meta.clone())))),
  }
}

pub fn decompile_recr_rule(
  lvls: &[Name],
  rule: &ixon::RecursorRule,
  n: &Address,
  m: &Address,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<RecursorRule, DecompileError> {
  let ctor = decompile_name(n, stt, dstt)?;
  let rhs = decompile_expr(
    MetaAddress { data: rule.rhs.clone(), meta: m.clone() },
    lvls,
    cache,
    stt,
    dstt,
  )?;
  Ok(RecursorRule { ctor, n_fields: rule.fields.clone(), rhs })
}

pub fn decompile_defn(
  cnst_name: &Name,
  def: &Definition,
  meta: &Metadata,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstantInfo, DecompileError> {
  match meta.nodes.as_slice() {
    [
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Hints(hints),
      Metadatum::Link(tm),
      Metadatum::Link(vm),
      Metadatum::Links(all),
    ] => {
      let cnst = decompile_const_val(
        n,
        &def.lvls,
        ls,
        MetaAddress { data: def.typ.clone(), meta: tm.clone() },
        cache,
        stt,
        dstt,
      )?;
      if cnst.name != *cnst_name {
        return Err(DecompileError::ConstName(
          cnst.name.clone(),
          cnst_name.clone(),
        ));
      }
      let value = decompile_expr(
        MetaAddress { data: def.value.clone(), meta: vm.clone() },
        &cnst.level_params,
        cache,
        stt,
        dstt,
      )?;
      let all =
        all.iter().map(|x| decompile_name(x, stt, dstt)).try_collect()?;
      match def.kind {
        DefKind::Definition => Ok(ConstantInfo::DefnInfo(DefinitionVal {
          cnst,
          value,
          hints: *hints,
          safety: def.safety,
          all,
        })),
        DefKind::Theorem => {
          Ok(ConstantInfo::ThmInfo(TheoremVal { cnst, value, all }))
        },
        DefKind::Opaque => Ok(ConstantInfo::OpaqueInfo(OpaqueVal {
          cnst,
          value,
          is_unsafe: def.safety == DefinitionSafety::Unsafe,
          all,
        })),
      }
    },
    _ => Err(DecompileError::BadDef(Box::new((def.clone(), meta.clone())))),
  }
}

pub fn decompile_recr(
  cnst_name: &Name,
  recr: &Recursor,
  meta: &Metadata,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstantInfo, DecompileError> {
  match meta.nodes.as_slice() {
    [
      Metadatum::Link(n),
      Metadatum::Links(ls),
      Metadatum::Link(tm),
      Metadatum::Map(rs),
      Metadatum::Links(all),
    ] => {
      let cnst = decompile_const_val(
        n,
        &recr.lvls,
        ls,
        MetaAddress { data: recr.typ.clone(), meta: tm.clone() },
        cache,
        stt,
        dstt,
      )?;
      if cnst.name != *cnst_name {
        return Err(DecompileError::ConstName(
          cnst.name.clone(),
          cnst_name.clone(),
        ));
      }
      let all =
        all.iter().map(|x| decompile_name(x, stt, dstt)).try_collect()?;
      let rules: Vec<RecursorRule> = recr
        .rules
        .iter()
        .zip(rs)
        .map(|(rd, (n, rm))| {
          decompile_recr_rule(&cnst.level_params, rd, n, rm, cache, stt, dstt)
        })
        .try_collect()?;
      Ok(ConstantInfo::RecInfo(RecursorVal {
        cnst,
        all,
        num_params: recr.params.clone(),
        num_indices: recr.indices.clone(),
        num_motives: recr.motives.clone(),
        num_minors: recr.minors.clone(),
        rules,
        k: recr.k,
        is_unsafe: recr.is_unsafe,
      }))
    },
    _ => Err(DecompileError::BadRec(Box::new((recr.clone(), meta.clone())))),
  }
}

pub fn decompile_mut_const(
  cnst_name: &Name,
  cnst: &MutConst,
  meta: &Metadata,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<ConstantInfo, DecompileError> {
  match cnst {
    MutConst::Defn(d) => decompile_defn(cnst_name, d, meta, cache, stt, dstt),
    MutConst::Indc(i) => match meta.nodes.as_slice() {
      [
        Metadatum::Link(n),
        Metadatum::Links(ls),
        Metadatum::Link(tm),
        Metadatum::Links(cs),
        Metadatum::Links(all),
      ] => {
        let cnst = decompile_const_val(
          n,
          &i.lvls,
          ls,
          MetaAddress { data: i.typ.clone(), meta: tm.clone() },
          cache,
          stt,
          dstt,
        )?;
        if cnst.name != *cnst_name {
          return Err(DecompileError::ConstName(
            cnst.name.clone(),
            cnst_name.clone(),
          ));
        }
        let all =
          all.iter().map(|x| decompile_name(x, stt, dstt)).try_collect()?;
        if i.ctors.len() != cs.len() {
          return Err(DecompileError::MismatchedCtors(
            cnst.name.clone(),
            i.ctors.clone(),
            cs.clone(),
          ));
        }
        let ctors: Vec<ConstructorVal> = i
          .ctors
          .iter()
          .zip(cs)
          .map(|(c, m)| decompile_ctor(c, m, cache, stt, dstt))
          .try_collect()?;
        let ctor_names: Vec<Name> =
          ctors.iter().map(|c| c.cnst.name.clone()).collect();
        for (cn, c) in ctor_names.iter().zip(ctors) {
          dstt.env.insert(cn.clone(), ConstantInfo::CtorInfo(c));
        }
        Ok(ConstantInfo::InductInfo(InductiveVal {
          cnst,
          num_params: i.params.clone(),
          num_indices: i.indices.clone(),
          all,
          ctors: ctor_names,
          num_nested: i.nested.clone(),
          is_rec: i.recr,
          is_reflexive: i.refl,
          is_unsafe: i.is_unsafe,
        }))
      },
      _ => Err(DecompileError::BadInd(Box::new((i.clone(), meta.clone())))),
    },
    MutConst::Recr(r) => decompile_recr(cnst_name, r, meta, cache, stt, dstt),
  }
}

pub fn decompile_block(
  addr: &MetaAddress,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  match (read_ixon(&addr.data, stt)?, read_ixon(&addr.meta, stt)?) {
    (ref d @ Ixon::Muts(ref muts), ref m @ Ixon::Meta(ref meta)) => {
      match meta.nodes.as_slice() {
        [
          Metadatum::Muts(muts_names),
          Metadatum::Map(muts_ctx),
          Metadatum::Map(muts_metas),
        ] => {
          if muts.len() != muts_names.len() {
            Err(DecompileError::BadBlock(Box::new((d.clone(), m.clone()))))
          } else {
            let mut meta_map = FxHashMap::default();
            for (name, meta) in muts_metas {
              let name = decompile_name(name, stt, dstt)?;
              let meta = read_meta(meta, stt)?;
              meta_map.insert(name, meta);
            }
            let mut ctx = MutCtx::default();
            for (name, idx) in muts_ctx {
              let name = decompile_name(name, stt, dstt)?;
              let idx = read_nat(idx, stt)?;
              ctx.insert(name, idx);
            }
            dstt.block_ctx.insert(addr.clone(), ctx.clone());
            cache.ctx = ctx;
            for (cnst, names) in muts.iter().zip(muts_names) {
              for n in names {
                let name = decompile_name(n, stt, dstt)?;
                let meta = meta_map.get(&name).ok_or(DecompileError::Todo)?;
                let info =
                  decompile_mut_const(&name, cnst, meta, cache, stt, dstt)?;
                dstt.env.insert(name, info);
              }
            }
            Ok(())
          }
        },
        _ => Err(DecompileError::BadBlock(Box::new((d.clone(), m.clone())))),
      }
    },
    (d, m) => Err(DecompileError::BadBlock(Box::new((d, m)))),
  }
}

pub fn decompile_const(
  cnst_name: &Name,
  addr: &MetaAddress,
  cache: &mut BlockCache,
  stt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  match (read_ixon(&addr.data, stt)?, read_ixon(&addr.meta, stt)?) {
    (Ixon::Defn(x), Ixon::Meta(m)) => {
      cache.ctx =
        vec![(cnst_name.clone(), Nat(0u64.into()))].into_iter().collect();
      let info = decompile_defn(cnst_name, &x, &m, cache, stt, dstt)?;
      dstt.env.insert(cnst_name.clone(), info);
      dstt.consts.insert(addr.clone(), cnst_name.clone());
      Ok(())
    },
    (Ixon::Recr(x), Ixon::Meta(m)) => {
      cache.ctx =
        vec![(cnst_name.clone(), Nat(0u64.into()))].into_iter().collect();
      let info = decompile_recr(cnst_name, &x, &m, cache, stt, dstt)?;
      dstt.env.insert(cnst_name.clone(), info);
      dstt.consts.insert(addr.clone(), cnst_name.clone());
      Ok(())
    },
    (Ixon::Axio(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(n), Metadatum::Links(ls), Metadatum::Link(tm)] => {
        let cnst = decompile_const_val(
          n,
          &x.lvls,
          ls,
          MetaAddress { data: x.typ, meta: tm.clone() },
          cache,
          stt,
          dstt,
        )?;
        let info =
          ConstantInfo::AxiomInfo(AxiomVal { cnst, is_unsafe: x.is_unsafe });
        dstt.env.insert(cnst_name.clone(), info);
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    (Ixon::Quot(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(n), Metadatum::Links(ls), Metadatum::Link(tm)] => {
        let cnst = decompile_const_val(
          n,
          &x.lvls,
          ls,
          MetaAddress { data: x.typ, meta: tm.clone() },
          cache,
          stt,
          dstt,
        )?;
        let info = ConstantInfo::QuotInfo(QuotVal { cnst, kind: x.kind });
        dstt.env.insert(cnst_name.clone(), info);
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    (Ixon::DPrj(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(bm), Metadatum::Link(_)] => {
        let block = MetaAddress { data: x.block, meta: bm.clone() };
        let ctx = dstt.block_ctx.get(&block).ok_or(DecompileError::Todo)?;
        ctx.get(cnst_name).ok_or(DecompileError::Todo)?;
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    (Ixon::RPrj(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(bm), Metadatum::Link(_)] => {
        let block = MetaAddress { data: x.block, meta: bm.clone() };
        let ctx = dstt.block_ctx.get(&block).ok_or(DecompileError::Todo)?;
        ctx.get(cnst_name).ok_or(DecompileError::Todo)?;
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    (Ixon::CPrj(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(bm), Metadatum::Link(_)] => {
        let block = MetaAddress { data: x.block, meta: bm.clone() };
        let ctx = dstt.block_ctx.get(&block).ok_or(DecompileError::Todo)?;
        ctx.get(cnst_name).ok_or(DecompileError::Todo)?;
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    (Ixon::IPrj(x), Ixon::Meta(m)) => match m.nodes.as_slice() {
      [Metadatum::Link(bm), Metadatum::Link(_)] => {
        let block = MetaAddress { data: x.block, meta: bm.clone() };
        let ctx = dstt.block_ctx.get(&block).ok_or(DecompileError::Todo)?;
        ctx.get(cnst_name).ok_or(DecompileError::Todo)?;
        dstt.consts.insert(addr.clone(), cnst_name.clone());
        Ok(())
      },
      _ => Err(DecompileError::Todo),
    },
    _ => todo!(),
  }
}

pub fn decompile_env(
  stt: &CompileState,
) -> Result<DecompileState, DecompileError> {
  let dstt = DecompileState::default();
  stt.blocks.par_iter().try_for_each(|addr| {
    decompile_block(&addr, &mut BlockCache::default(), stt, &dstt)
  })?;
  stt.consts.par_iter().try_for_each(|entry| {
    decompile_const(
      entry.key(),
      entry.value(),
      &mut BlockCache::default(),
      stt,
      &dstt,
    )
  })?;
  Ok(dstt)
}

pub fn check_decompile(
  env: &Env,
  cstt: &CompileState,
  dstt: &DecompileState,
) -> Result<(), DecompileError> {
  cstt.consts.par_iter().try_for_each(|entry| {
    let (name, addr) = (entry.key(), entry.value());
    match dstt.consts.get(addr) {
      Some(n2) if name == n2.value() => Ok(()),
      Some(n2) => Err(DecompileError::ConstAddrMismatch(
        name.clone(),
        Box::new(addr.clone()),
        n2.value().clone(),
      )),
      None => Err(DecompileError::ConstAddrNotDecompiled(
        name.clone(),
        Box::new(addr.clone()),
      )),
    }
  })?;

  dstt.consts.par_iter().try_for_each(|entry| {
    let (addr, name) = (entry.key(), entry.value());
    match cstt.consts.get(name) {
      Some(a2) if addr == a2.value() => Ok(()),
      Some(a2) => Err(DecompileError::ConstNameMismatch(
        name.clone(),
        Box::new((addr.clone(), a2.value().clone())),
      )),
      None => Err(DecompileError::ConstNameNotCompiled(
        name.clone(),
        Box::new(addr.clone()),
      )),
    }
  })?;

  if env.len() != dstt.env.len() {
    return Err(DecompileError::EnvSizeMismatch {
      original: env.len(),
      decompiled: dstt.env.len(),
    });
  }

  dstt.env.par_iter().try_for_each(|entry| {
    let (name, info) = (entry.key(), entry.value());
    match env.get(name) {
      Some(info2) if info.get_hash() == info2.get_hash() => Ok(()),
      Some(info2) => Err(DecompileError::ConstHashMismatch(
        name.clone(),
        Box::new((info2.get_hash(), info.get_hash())),
      )),
      None => Err(DecompileError::ConstMissingInOriginal(name.clone())),
    }
  })?;

  Ok(())
}
