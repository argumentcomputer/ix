//! Compilation from Lean environment to Ixon format.
//!
//! This module compiles Lean constants to alpha-invariant Ixon representations
//! with sharing analysis for deduplication within constants

#![allow(clippy::cast_possible_truncation)]
#![allow(clippy::cast_precision_loss)]

use dashmap::{DashMap, DashSet};
use rustc_hash::FxHashMap;
use std::{
  cmp::Ordering,
  sync::{
    Arc,
    atomic::{AtomicUsize, Ordering as AtomicOrdering},
  },
  thread,
};

use crate::{
  ix::address::Address,
  ix::condense::compute_sccs,
  ix::env::{
    AxiomVal, BinderInfo, ConstantInfo as LeanConstantInfo, ConstructorVal,
    DataValue as LeanDataValue, Env as LeanEnv, Expr as LeanExpr, ExprData,
    InductiveVal, Level, LevelData, Literal, Name, NameData, QuotVal,
    RecursorRule as LeanRecursorRule, SourceInfo as LeanSourceInfo,
    Substring as LeanSubstring, Syntax as LeanSyntax, SyntaxPreresolved,
  },
  ix::graph::{NameSet, build_ref_graph},
  ix::ground::ground_consts,
  ix::ixon::{
    CompileError,
    constant::{
      Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
      Definition, DefinitionProj, Inductive, InductiveProj,
      MutConst as IxonMutConst, Quotient, Recursor, RecursorProj, RecursorRule,
    },
    env::{Env as IxonEnv, Named},
    expr::Expr,
    metadata::{ConstantMeta, CtorMeta, DataValue, ExprMeta, ExprMetas, KVMap},
    sharing::{analyze_block, build_sharing_vec, decide_sharing},
    univ::Univ,
  },
  ix::mutual::{Def, Ind, MutConst, MutCtx, Rec, ctx_to_all},
  ix::strong_ordering::SOrd,
  lean::nat::Nat,
};

/// Compile state for building the Ixon environment.
#[derive(Default)]
pub struct CompileState {
  /// Ixon environment being built
  pub env: IxonEnv,
  /// Map from Lean constant name to Ixon address
  pub name_to_addr: DashMap<Name, Address>,
  /// Addresses of mutual blocks
  pub blocks: DashSet<Address>,
}

/// Per-block compilation cache.
#[derive(Default)]
pub struct BlockCache {
  /// Cache for compiled expressions
  pub exprs: FxHashMap<*const LeanExpr, Arc<Expr>>,
  /// Cache for compiled universes (Level -> Univ conversion)
  pub univ_cache: FxHashMap<Level, Arc<Univ>>,
  /// Cache for expression comparisons
  pub cmps: FxHashMap<(Name, Name), Ordering>,
  /// Pre-order traversal index for current expression tree
  pub expr_index: u64,
  /// Expression metadata collected during compilation (keyed by pre-order index)
  pub expr_metas: ExprMetas,
  /// Stack for collecting mdata wrappers
  pub mdata_stack: Vec<KVMap>,
  /// Reference table: unique addresses of constants referenced by Expr::Ref
  pub refs: indexmap::IndexSet<Address>,
  /// Universe table: unique universes referenced by expressions
  pub univs: indexmap::IndexSet<Arc<Univ>>,
}

#[derive(Debug)]
pub struct CompileStateStats {
  pub consts: usize,
  pub names: usize,
  pub blobs: usize,
  pub blocks: usize,
}

impl CompileState {
  pub fn stats(&self) -> CompileStateStats {
    CompileStateStats {
      consts: self.env.const_count(),
      names: self.env.name_count(),
      blobs: self.env.blob_count(),
      blocks: self.blocks.len(),
    }
  }
}

// ===========================================================================
// Helper functions
// ===========================================================================

/// Convert a Nat to u64, returning an error if the value is too large.
fn nat_to_u64(n: &Nat, context: &'static str) -> Result<u64, CompileError> {
  n.to_u64().ok_or(CompileError::UnsupportedExpr { desc: context })
}

// ===========================================================================
// Name compilation
// ===========================================================================

/// Store a string as a blob and return its address.
pub fn store_string(s: &str, stt: &CompileState) -> Address {
  stt.env.store_blob(s.as_bytes().to_vec())
}

/// Store a Nat as a blob and return its address.
pub fn store_nat(n: &Nat, stt: &CompileState) -> Address {
  stt.env.store_blob(n.to_le_bytes())
}

/// Compile a Lean Name to an address (stored in env.names).
/// Uses the Name's internal hash as the address.
/// String components are stored in blobs.
pub fn compile_name(name: &Name, stt: &CompileState) -> Address {
  // Use the Name's internal hash as the address
  let addr = Address::from_blake3_hash(name.get_hash());

  // Check if already stored
  if stt.env.names.contains_key(&addr) {
    return addr;
  }

  // Recurse on parent first (ensures parent is stored)
  match name.as_data() {
    NameData::Anonymous(_) => {},
    NameData::Str(parent, s, _) => {
      compile_name(parent, stt);
      store_string(s, stt); // string data in blobs
    },
    NameData::Num(parent, _, _) => {
      compile_name(parent, stt);
      // Nat is inline in Name, no blob needed
    },
  }

  // Store Name struct directly in env.names
  stt.env.names.insert(addr.clone(), name.clone());
  addr
}

// ===========================================================================
// Universe compilation
// ===========================================================================

/// Compile a Lean Level to an Ixon Univ.
pub fn compile_univ(
  level: &Level,
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<Arc<Univ>, CompileError> {
  if let Some(cached) = cache.univ_cache.get(level) {
    return Ok(cached.clone());
  }

  let univ = match level.as_data() {
    LevelData::Zero(_) => Univ::zero(),
    LevelData::Succ(inner, _) => {
      let inner_univ = compile_univ(inner, univ_params, cache)?;
      Univ::succ(inner_univ)
    },
    LevelData::Max(a, b, _) => {
      let a_univ = compile_univ(a, univ_params, cache)?;
      let b_univ = compile_univ(b, univ_params, cache)?;
      Univ::max(a_univ, b_univ)
    },
    LevelData::Imax(a, b, _) => {
      let a_univ = compile_univ(a, univ_params, cache)?;
      let b_univ = compile_univ(b, univ_params, cache)?;
      Univ::imax(a_univ, b_univ)
    },
    LevelData::Param(name, _) => {
      let idx = univ_params
        .iter()
        .position(|n| n == name)
        .ok_or_else(|| CompileError::MissingConstant { name: name.pretty() })?;
      Univ::var(idx as u64)
    },
    LevelData::Mvar(_name, _) => {
      return Err(CompileError::UnsupportedExpr { desc: "level metavariable" });
    },
  };

  cache.univ_cache.insert(level.clone(), univ.clone());
  Ok(univ)
}

/// Compile a universe and add it to the univs table, returning its index.
fn compile_univ_idx(
  level: &Level,
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<u64, CompileError> {
  let univ = compile_univ(level, univ_params, cache)?;
  let (idx, _) = cache.univs.insert_full(univ);
  Ok(idx as u64)
}

/// Compile a list of universes and add them to the univs table, returning indices.
fn compile_univ_indices(
  levels: &[Level],
  univ_params: &[Name],
  cache: &mut BlockCache,
) -> Result<Vec<u64>, CompileError> {
  levels.iter().map(|l| compile_univ_idx(l, univ_params, cache)).collect()
}

// ===========================================================================
// Expression compilation
// ===========================================================================

/// Compile a Lean expression to an Ixon expression.
/// Also collects metadata (names, binder info) into cache.expr_metas using pre-order indices.
pub fn compile_expr(
  expr: &LeanExpr,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Arc<Expr>, CompileError> {
  // Stack-based iterative compilation to avoid stack overflow
  enum Frame<'a> {
    Compile(&'a LeanExpr),
    BuildApp,
    BuildLam(u64, Address, BinderInfo), // index, name_addr, info
    BuildAll(u64, Address, BinderInfo), // index, name_addr, info
    BuildLet(u64, Address, bool),       // index, name_addr, non_dep
    BuildProj(u64, u64, u64, Address), // index, type_ref_idx, field_idx, struct_name_addr
    BuildMdata,
    Cache(&'a LeanExpr),
    PopMdata,
  }

  let expr_ptr = expr as *const LeanExpr;
  if let Some(cached) = cache.exprs.get(&expr_ptr) {
    return Ok(cached.clone());
  }

  let mut stack: Vec<Frame<'_>> = vec![Frame::Compile(expr)];
  let mut results: Vec<Arc<Expr>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      Frame::Compile(e) => {
        let ptr = e as *const LeanExpr;
        if let Some(cached) = cache.exprs.get(&ptr) {
          results.push(cached.clone());
          continue;
        }

        // Assign pre-order index for this node
        let node_index = cache.expr_index;
        cache.expr_index += 1;

        stack.push(Frame::Cache(e));

        match e.as_data() {
          ExprData::Bvar(idx, _) => {
            let idx_u64 = nat_to_u64(idx, "bvar index too large")?;
            results.push(Expr::var(idx_u64));
          },

          ExprData::Sort(level, _) => {
            let univ_idx = compile_univ_idx(level, univ_params, cache)?;
            results.push(Expr::sort(univ_idx));
          },

          ExprData::Const(name, levels, _) => {
            let univ_indices =
              compile_univ_indices(levels, univ_params, cache)?;
            let name_addr = compile_name(name, stt);

            // Check if this is a mutual reference
            if let Some(idx) = mut_ctx.get(name) {
              let idx_u64 = nat_to_u64(idx, "mutual index too large")?;
              results.push(Expr::rec(idx_u64, univ_indices));
              // Store ref metadata for reconstruction
              let mdata = std::mem::take(&mut cache.mdata_stack);
              cache
                .expr_metas
                .insert(node_index, ExprMeta::Ref { name: name_addr, mdata });
            } else {
              // External reference - need to look up the address
              let const_addr = stt
                .name_to_addr
                .get(name)
                .ok_or_else(|| CompileError::MissingConstant {
                  name: name.pretty(),
                })?
                .clone();
              // Add to refs table and get index
              let (ref_idx, _) = cache.refs.insert_full(const_addr);
              results.push(Expr::reference(ref_idx as u64, univ_indices));
              // Store ref metadata
              let mdata = std::mem::take(&mut cache.mdata_stack);
              if !mdata.is_empty() {
                cache
                  .expr_metas
                  .insert(node_index, ExprMeta::Ref { name: name_addr, mdata });
              }
            }
          },

          ExprData::App(f, a, _) => {
            stack.push(Frame::BuildApp);
            stack.push(Frame::Compile(a));
            stack.push(Frame::Compile(f));
          },

          ExprData::Lam(name, ty, body, info, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildLam(node_index, name_addr, info.clone()));
            stack.push(Frame::Compile(body));
            stack.push(Frame::Compile(ty));
          },

          ExprData::ForallE(name, ty, body, info, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildAll(node_index, name_addr, info.clone()));
            stack.push(Frame::Compile(body));
            stack.push(Frame::Compile(ty));
          },

          ExprData::LetE(name, ty, val, body, non_dep, _) => {
            let name_addr = compile_name(name, stt);
            stack.push(Frame::BuildLet(node_index, name_addr, *non_dep));
            stack.push(Frame::Compile(body));
            stack.push(Frame::Compile(val));
            stack.push(Frame::Compile(ty));
          },

          ExprData::Lit(Literal::NatVal(n), _) => {
            let addr = store_nat(n, stt);
            let (ref_idx, _) = cache.refs.insert_full(addr);
            results.push(Expr::nat(ref_idx as u64));
          },

          ExprData::Lit(Literal::StrVal(s), _) => {
            let addr = store_string(s, stt);
            let (ref_idx, _) = cache.refs.insert_full(addr);
            results.push(Expr::str(ref_idx as u64));
          },

          ExprData::Proj(type_name, idx, struct_val, _) => {
            let idx_u64 = nat_to_u64(idx, "proj index too large")?;

            // Get the type's address
            let type_addr = stt
              .name_to_addr
              .get(type_name)
              .ok_or_else(|| CompileError::MissingConstant {
                name: type_name.pretty(),
              })?
              .clone();

            // Add to refs table and get index
            let (ref_idx, _) = cache.refs.insert_full(type_addr);

            let name_addr = compile_name(type_name, stt);

            // Build projection with ref index directly
            stack.push(Frame::BuildProj(
              node_index,
              ref_idx as u64,
              idx_u64,
              name_addr,
            ));
            stack.push(Frame::Compile(struct_val));
          },

          ExprData::Mdata(kv, inner, _) => {
            // Compile KV map and push to mdata stack
            let mut pairs = Vec::new();
            for (k, v) in kv {
              let k_addr = compile_name(k, stt);
              let v_data = compile_data_value(v, stt);
              pairs.push((k_addr, v_data));
            }
            cache.mdata_stack.push(pairs);

            stack.push(Frame::PopMdata);
            stack.push(Frame::BuildMdata);
            stack.push(Frame::Compile(inner));
          },

          ExprData::Fvar(..) => {
            return Err(CompileError::UnsupportedExpr {
              desc: "free variable",
            });
          },

          ExprData::Mvar(..) => {
            return Err(CompileError::UnsupportedExpr { desc: "metavariable" });
          },
        }
      },

      Frame::BuildApp => {
        let arg = results.pop().expect("BuildApp missing arg");
        let fun = results.pop().expect("BuildApp missing fun");
        results.push(Expr::app(fun, arg));
      },

      Frame::BuildLam(index, name_addr, info) => {
        let body = results.pop().expect("BuildLam missing body");
        let ty = results.pop().expect("BuildLam missing ty");
        results.push(Expr::lam(ty, body));
        // Store binder metadata
        let mdata = std::mem::take(&mut cache.mdata_stack);
        cache
          .expr_metas
          .insert(index, ExprMeta::Binder { name: name_addr, info, mdata });
      },

      Frame::BuildAll(index, name_addr, info) => {
        let body = results.pop().expect("BuildAll missing body");
        let ty = results.pop().expect("BuildAll missing ty");
        results.push(Expr::all(ty, body));
        // Store binder metadata
        let mdata = std::mem::take(&mut cache.mdata_stack);
        cache
          .expr_metas
          .insert(index, ExprMeta::Binder { name: name_addr, info, mdata });
      },

      Frame::BuildLet(index, name_addr, non_dep) => {
        let body = results.pop().expect("BuildLet missing body");
        let val = results.pop().expect("BuildLet missing val");
        let ty = results.pop().expect("BuildLet missing ty");
        results.push(Expr::let_(non_dep, ty, val, body));
        // Store let binder metadata
        let mdata = std::mem::take(&mut cache.mdata_stack);
        cache
          .expr_metas
          .insert(index, ExprMeta::LetBinder { name: name_addr, mdata });
      },

      Frame::BuildProj(index, type_ref_idx, field_idx, struct_name_addr) => {
        let struct_val = results.pop().expect("BuildProj missing struct_val");
        results.push(Expr::prj(type_ref_idx, field_idx, struct_val));
        // Store projection metadata
        let mdata = std::mem::take(&mut cache.mdata_stack);
        cache.expr_metas.insert(
          index,
          ExprMeta::Prj { struct_name: struct_name_addr, mdata },
        );
      },

      Frame::BuildMdata => {
        // Mdata doesn't change the expression structure in Ixon
        // The metadata is stored in mdata_stack and attached to inner expr
      },

      Frame::PopMdata => {
        // Pop mdata after inner is processed (mdata was already consumed)
        // This happens if mdata was not consumed by a metadata-bearing node
        if !cache.mdata_stack.is_empty() {
          // mdata wasn't consumed - need to record it as standalone Mdata
          // This can happen for nodes like App, Bvar, Sort, Lit that don't have ExprMeta
          // For now we just discard it - the mdata system needs more work
        }
      },

      Frame::Cache(e) => {
        let ptr = e as *const LeanExpr;
        if let Some(result) = results.last() {
          cache.exprs.insert(ptr, result.clone());
        }
      },
    }
  }

  results.pop().ok_or(CompileError::UnsupportedExpr { desc: "empty result" })
}

/// Compile a Lean DataValue to Ixon DataValue.
fn compile_data_value(dv: &LeanDataValue, stt: &CompileState) -> DataValue {
  match dv {
    LeanDataValue::OfString(s) => DataValue::OfString(store_string(s, stt)),
    LeanDataValue::OfBool(b) => DataValue::OfBool(*b),
    LeanDataValue::OfName(n) => DataValue::OfName(compile_name(n, stt)),
    LeanDataValue::OfNat(n) => DataValue::OfNat(store_nat(n, stt)),
    LeanDataValue::OfInt(i) => {
      // Serialize Int and store as blob
      let mut bytes = Vec::new();
      match i {
        crate::ix::env::Int::OfNat(n) => {
          bytes.push(0);
          bytes.extend_from_slice(&n.to_le_bytes());
        },
        crate::ix::env::Int::NegSucc(n) => {
          bytes.push(1);
          bytes.extend_from_slice(&n.to_le_bytes());
        },
      }
      DataValue::OfInt(stt.env.store_blob(bytes))
    },
    LeanDataValue::OfSyntax(syn) => {
      // Serialize syntax and store as blob
      let bytes = serialize_syntax(syn, stt);
      DataValue::OfSyntax(stt.env.store_blob(bytes))
    },
  }
}

/// Serialize a Lean Syntax to bytes.
fn serialize_syntax(syn: &LeanSyntax, stt: &CompileState) -> Vec<u8> {
  let mut bytes = Vec::new();
  serialize_syntax_inner(syn, stt, &mut bytes);
  bytes
}

fn serialize_syntax_inner(
  syn: &LeanSyntax,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match syn {
    LeanSyntax::Missing => bytes.push(0),
    LeanSyntax::Node(info, kind, args) => {
      bytes.push(1);
      serialize_source_info(info, stt, bytes);
      bytes.extend_from_slice(compile_name(kind, stt).as_bytes());
      bytes.extend_from_slice(&(args.len() as u64).to_le_bytes());
      for arg in args {
        serialize_syntax_inner(arg, stt, bytes);
      }
    },
    LeanSyntax::Atom(info, val) => {
      bytes.push(2);
      serialize_source_info(info, stt, bytes);
      bytes.extend_from_slice(store_string(val, stt).as_bytes());
    },
    LeanSyntax::Ident(info, raw_val, val, preresolved) => {
      bytes.push(3);
      serialize_source_info(info, stt, bytes);
      serialize_substring(raw_val, stt, bytes);
      bytes.extend_from_slice(compile_name(val, stt).as_bytes());
      bytes.extend_from_slice(&(preresolved.len() as u64).to_le_bytes());
      for pr in preresolved {
        serialize_preresolved(pr, stt, bytes);
      }
    },
  }
}

fn serialize_source_info(
  info: &LeanSourceInfo,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match info {
    LeanSourceInfo::Original(leading, leading_pos, trailing, trailing_pos) => {
      bytes.push(0);
      serialize_substring(leading, stt, bytes);
      bytes.extend_from_slice(&leading_pos.to_le_bytes());
      serialize_substring(trailing, stt, bytes);
      bytes.extend_from_slice(&trailing_pos.to_le_bytes());
    },
    LeanSourceInfo::Synthetic(start, end, canonical) => {
      bytes.push(1);
      bytes.extend_from_slice(&start.to_le_bytes());
      bytes.extend_from_slice(&end.to_le_bytes());
      bytes.push(if *canonical { 1 } else { 0 });
    },
    LeanSourceInfo::None => bytes.push(2),
  }
}

fn serialize_substring(
  ss: &LeanSubstring,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  bytes.extend_from_slice(store_string(&ss.str, stt).as_bytes());
  bytes.extend_from_slice(&ss.start_pos.to_le_bytes());
  bytes.extend_from_slice(&ss.stop_pos.to_le_bytes());
}

fn serialize_preresolved(
  pr: &SyntaxPreresolved,
  stt: &CompileState,
  bytes: &mut Vec<u8>,
) {
  match pr {
    SyntaxPreresolved::Namespace(n) => {
      bytes.push(0);
      bytes.extend_from_slice(compile_name(n, stt).as_bytes());
    },
    SyntaxPreresolved::Decl(n, fields) => {
      bytes.push(1);
      bytes.extend_from_slice(compile_name(n, stt).as_bytes());
      bytes.extend_from_slice(&(fields.len() as u64).to_le_bytes());
      for f in fields {
        bytes.extend_from_slice(store_string(f, stt).as_bytes());
      }
    },
  }
}

// ===========================================================================
// Sharing analysis helper
// ===========================================================================

/// Apply sharing analysis to a set of expressions.
/// Returns the rewritten expressions and the sharing vector.
fn apply_sharing(exprs: Vec<Arc<Expr>>) -> (Vec<Arc<Expr>>, Vec<Arc<Expr>>) {
  let (info_map, ptr_to_hash) = analyze_block(&exprs);

  // Early exit if no sharing opportunities (< 2 repeated subterms)
  let has_candidates = info_map.values().any(|info| info.usage_count >= 2);
  if !has_candidates {
    return (exprs, Vec::new());
  }

  let shared_hashes = decide_sharing(&info_map);

  // Early exit if nothing to share
  if shared_hashes.is_empty() {
    return (exprs, Vec::new());
  }

  build_sharing_vec(&exprs, &shared_hashes, &ptr_to_hash, &info_map)
}

/// Apply sharing to a Definition and return a Constant.
#[allow(clippy::needless_pass_by_value)]
fn apply_sharing_to_definition(
  def: Definition,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Constant {
  let (rewritten, sharing) =
    apply_sharing(vec![def.typ.clone(), def.value.clone()]);
  let def = Definition {
    kind: def.kind,
    safety: def.safety,
    lvls: def.lvls,
    typ: rewritten[0].clone(),
    value: rewritten[1].clone(),
  };
  Constant::with_tables(ConstantInfo::Defn(def), sharing, refs, univs)
}

/// Apply sharing to an Axiom and return a Constant.
#[allow(clippy::needless_pass_by_value)]
fn apply_sharing_to_axiom(
  ax: Axiom,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Constant {
  let (rewritten, sharing) = apply_sharing(vec![ax.typ.clone()]);
  let ax =
    Axiom { is_unsafe: ax.is_unsafe, lvls: ax.lvls, typ: rewritten[0].clone() };
  Constant::with_tables(ConstantInfo::Axio(ax), sharing, refs, univs)
}

/// Apply sharing to a Quotient and return a Constant.
#[allow(clippy::needless_pass_by_value)]
fn apply_sharing_to_quotient(
  quot: Quotient,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Constant {
  let (rewritten, sharing) = apply_sharing(vec![quot.typ.clone()]);
  let quot =
    Quotient { kind: quot.kind, lvls: quot.lvls, typ: rewritten[0].clone() };
  Constant::with_tables(ConstantInfo::Quot(quot), sharing, refs, univs)
}

/// Apply sharing to a Recursor and return a Constant.
fn apply_sharing_to_recursor(
  rec: Recursor,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Constant {
  // Collect all expressions: typ + all rule rhs
  let mut exprs = vec![rec.typ.clone()];
  for rule in &rec.rules {
    exprs.push(rule.rhs.clone());
  }

  let (rewritten, sharing) = apply_sharing(exprs);
  let typ = rewritten[0].clone();
  let rules: Vec<RecursorRule> = rec
    .rules
    .into_iter()
    .zip(rewritten.into_iter().skip(1))
    .map(|(r, rhs)| RecursorRule { fields: r.fields, rhs })
    .collect();

  let rec = Recursor {
    k: rec.k,
    is_unsafe: rec.is_unsafe,
    lvls: rec.lvls,
    params: rec.params,
    indices: rec.indices,
    motives: rec.motives,
    minors: rec.minors,
    typ,
    rules,
  };
  Constant::with_tables(ConstantInfo::Recr(rec), sharing, refs, univs)
}

/// Apply sharing to a mutual block and return a Constant.
fn apply_sharing_to_mutual_block(
  mut_consts: Vec<IxonMutConst>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> Constant {
  // Collect all expressions from all constants in the block
  let mut all_exprs: Vec<Arc<Expr>> = Vec::new();
  let mut layout: Vec<(MutConstKind, Vec<usize>)> = Vec::new();

  for mc in &mut_consts {
    let (kind, indices) = match mc {
      IxonMutConst::Defn(def) => {
        let start = all_exprs.len();
        all_exprs.push(def.typ.clone());
        all_exprs.push(def.value.clone());
        (MutConstKind::Defn, vec![start, start + 1])
      },
      IxonMutConst::Indc(ind) => {
        let start = all_exprs.len();
        all_exprs.push(ind.typ.clone());
        let mut indices = vec![start];
        for ctor in &ind.ctors {
          indices.push(all_exprs.len());
          all_exprs.push(ctor.typ.clone());
        }
        (MutConstKind::Indc, indices)
      },
      IxonMutConst::Recr(rec) => {
        let start = all_exprs.len();
        all_exprs.push(rec.typ.clone());
        let mut indices = vec![start];
        for rule in &rec.rules {
          indices.push(all_exprs.len());
          all_exprs.push(rule.rhs.clone());
        }
        (MutConstKind::Recr, indices)
      },
    };
    layout.push((kind, indices));
  }

  // Apply sharing analysis to all expressions at once
  let (rewritten, sharing) = apply_sharing(all_exprs);

  // Rebuild the constants with rewritten expressions
  let mut new_consts = Vec::with_capacity(mut_consts.len());
  for (i, mc) in mut_consts.into_iter().enumerate() {
    let (kind, indices) = &layout[i];
    let new_mc = match (kind, mc) {
      (MutConstKind::Defn, IxonMutConst::Defn(def)) => {
        IxonMutConst::Defn(Definition {
          kind: def.kind,
          safety: def.safety,
          lvls: def.lvls,
          typ: rewritten[indices[0]].clone(),
          value: rewritten[indices[1]].clone(),
        })
      },
      (MutConstKind::Indc, IxonMutConst::Indc(ind)) => {
        let new_ctors: Vec<Constructor> = ind
          .ctors
          .into_iter()
          .enumerate()
          .map(|(ci, ctor)| Constructor {
            is_unsafe: ctor.is_unsafe,
            lvls: ctor.lvls,
            cidx: ctor.cidx,
            params: ctor.params,
            fields: ctor.fields,
            typ: rewritten[indices[ci + 1]].clone(),
          })
          .collect();
        IxonMutConst::Indc(Inductive {
          recr: ind.recr,
          refl: ind.refl,
          is_unsafe: ind.is_unsafe,
          lvls: ind.lvls,
          params: ind.params,
          indices: ind.indices,
          nested: ind.nested,
          typ: rewritten[indices[0]].clone(),
          ctors: new_ctors,
        })
      },
      (MutConstKind::Recr, IxonMutConst::Recr(rec)) => {
        let new_rules: Vec<RecursorRule> = rec
          .rules
          .into_iter()
          .enumerate()
          .map(|(ri, rule)| RecursorRule {
            fields: rule.fields,
            rhs: rewritten[indices[ri + 1]].clone(),
          })
          .collect();
        IxonMutConst::Recr(Recursor {
          k: rec.k,
          is_unsafe: rec.is_unsafe,
          lvls: rec.lvls,
          params: rec.params,
          indices: rec.indices,
          motives: rec.motives,
          minors: rec.minors,
          typ: rewritten[indices[0]].clone(),
          rules: new_rules,
        })
      },
      _ => unreachable!("layout mismatch"),
    };
    new_consts.push(new_mc);
  }

  Constant::with_tables(ConstantInfo::Muts(new_consts), sharing, refs, univs)
}

/// Helper enum for tracking mutual constant layout during sharing.
#[derive(Clone, Copy)]
enum MutConstKind {
  Defn,
  Indc,
  Recr,
}

// ===========================================================================
// Constant compilation
// ===========================================================================

/// Reset expression metadata tracking for a new expression tree.
fn reset_expr_meta(cache: &mut BlockCache) {
  cache.expr_index = 0;
  cache.expr_metas.clear();
  cache.mdata_stack.clear();
}

/// Take the current expression metadata and reset for next expression.
fn take_expr_metas(cache: &mut BlockCache) -> ExprMetas {
  cache.expr_index = 0;
  cache.mdata_stack.clear();
  std::mem::take(&mut cache.expr_metas)
}

/// Compile a Definition.
fn compile_definition(
  def: &Def,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Definition, ConstantMeta), CompileError> {
  let univ_params = &def.level_params;

  // Compile type expression and collect metadata
  reset_expr_meta(cache);
  let typ = compile_expr(&def.typ, univ_params, mut_ctx, cache, stt)?;
  let type_meta = take_expr_metas(cache);

  // Compile value expression and collect metadata
  let value = compile_expr(&def.value, univ_params, mut_ctx, cache, stt)?;
  let value_meta = take_expr_metas(cache);

  let name_addr = compile_name(&def.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();
  // Store both:
  // - all: original Lean `all` field (for roundtrip fidelity)
  // - ctx: mut_ctx used during compilation (for Rec expr decompilation)
  let all_addrs: Vec<Address> =
    def.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> =
    ctx_to_all(mut_ctx).iter().map(|n| compile_name(n, stt)).collect();

  let data = Definition {
    kind: match def.kind {
      crate::ix::ixon_old::DefKind::Definition => DefKind::Definition,
      crate::ix::ixon_old::DefKind::Opaque => DefKind::Opaque,
      crate::ix::ixon_old::DefKind::Theorem => DefKind::Theorem,
    },
    safety: def.safety,
    lvls: def.level_params.len() as u64,
    typ,
    value,
  };

  let meta = ConstantMeta::Def {
    name: name_addr,
    lvls: lvl_addrs,
    hints: def.hints,
    all: all_addrs,
    ctx: ctx_addrs,
    type_meta,
    value_meta,
  };

  Ok((data, meta))
}

/// Compile a RecursorRule.
fn compile_recursor_rule(
  rule: &LeanRecursorRule,
  univ_params: &[Name],
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(RecursorRule, Address), CompileError> {
  let rhs = compile_expr(&rule.rhs, univ_params, mut_ctx, cache, stt)?;
  let ctor_addr = compile_name(&rule.ctor, stt);
  let fields = nat_to_u64(&rule.n_fields, "n_fields too large")?;

  Ok((RecursorRule { fields, rhs }, ctor_addr))
}

/// Compile a Recursor.
fn compile_recursor(
  rec: &Rec,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Recursor, ConstantMeta), CompileError> {
  let univ_params = &rec.cnst.level_params;

  // Compile type expression
  reset_expr_meta(cache);
  let typ = compile_expr(&rec.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_meta = take_expr_metas(cache);

  let mut rules = Vec::with_capacity(rec.rules.len());
  let mut rule_addrs = Vec::new();
  for rule in &rec.rules {
    let (r, ctor_addr) =
      compile_recursor_rule(rule, univ_params, mut_ctx, cache, stt)?;
    rule_addrs.push(ctor_addr);
    rules.push(r);
  }

  let name_addr = compile_name(&rec.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Recursor {
    k: rec.k,
    is_unsafe: rec.is_unsafe,
    lvls: univ_params.len() as u64,
    params: nat_to_u64(&rec.num_params, "num_params too large")?,
    indices: nat_to_u64(&rec.num_indices, "num_indices too large")?,
    motives: nat_to_u64(&rec.num_motives, "num_motives too large")?,
    minors: nat_to_u64(&rec.num_minors, "num_minors too large")?,
    typ,
    rules,
  };

  // Store both:
  // - all: original Lean `all` field (for roundtrip fidelity)
  // - ctx: mut_ctx used during compilation (for Rec expr decompilation)
  let all_addrs: Vec<Address> =
    rec.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> =
    ctx_to_all(mut_ctx).iter().map(|n| compile_name(n, stt)).collect();

  let meta = ConstantMeta::Rec {
    name: name_addr,
    lvls: lvl_addrs,
    rules: rule_addrs,
    all: all_addrs,
    ctx: ctx_addrs,
    type_meta,
  };

  Ok((data, meta))
}

/// Compile a Constructor.
fn compile_constructor(
  ctor: &ConstructorVal,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Constructor, ConstantMeta), CompileError> {
  let univ_params = &ctor.cnst.level_params;

  reset_expr_meta(cache);
  let typ = compile_expr(&ctor.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_meta = take_expr_metas(cache);

  let name_addr = compile_name(&ctor.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();
  let induct_addr = compile_name(&ctor.induct, stt);

  let data = Constructor {
    is_unsafe: ctor.is_unsafe,
    lvls: univ_params.len() as u64,
    cidx: nat_to_u64(&ctor.cidx, "cidx too large")?,
    params: nat_to_u64(&ctor.num_params, "ctor num_params too large")?,
    fields: nat_to_u64(&ctor.num_fields, "num_fields too large")?,
    typ,
  };

  let meta = ConstantMeta::Ctor {
    name: name_addr,
    lvls: lvl_addrs,
    induct: induct_addr,
    type_meta,
  };

  Ok((data, meta))
}

/// Compile an Inductive.
fn compile_inductive(
  ind: &Ind,
  mut_ctx: &MutCtx,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Inductive, ConstantMeta), CompileError> {
  let univ_params = &ind.ind.cnst.level_params;

  reset_expr_meta(cache);
  let typ = compile_expr(&ind.ind.cnst.typ, univ_params, mut_ctx, cache, stt)?;
  let type_meta = take_expr_metas(cache);

  let mut ctors = Vec::with_capacity(ind.ctors.len());
  let mut ctor_metas = Vec::new();
  let mut ctor_name_addrs = Vec::new();
  for ctor in &ind.ctors {
    let (c, m) = compile_constructor(ctor, mut_ctx, cache, stt)?;
    let ctor_name_addr = compile_name(&ctor.cnst.name, stt);
    ctor_name_addrs.push(ctor_name_addr.clone());
    // Extract CtorMeta from ConstantMeta::Ctor
    if let ConstantMeta::Ctor { name, lvls, type_meta, .. } = m {
      ctor_metas.push(CtorMeta { name, lvls, type_meta });
    }
    ctors.push(c);
  }

  let name_addr = compile_name(&ind.ind.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Inductive {
    recr: ind.ind.is_rec,
    refl: ind.ind.is_reflexive,
    is_unsafe: ind.ind.is_unsafe,
    lvls: univ_params.len() as u64,
    params: nat_to_u64(&ind.ind.num_params, "inductive num_params too large")?,
    indices: nat_to_u64(
      &ind.ind.num_indices,
      "inductive num_indices too large",
    )?,
    nested: nat_to_u64(&ind.ind.num_nested, "num_nested too large")?,
    typ,
    ctors,
  };

  // Store both:
  // - all: original Lean `all` field (for roundtrip fidelity)
  // - ctx: mut_ctx used during compilation (for Rec expr decompilation)
  let all_addrs: Vec<Address> =
    ind.ind.all.iter().map(|n| compile_name(n, stt)).collect();
  let ctx_addrs: Vec<Address> =
    ctx_to_all(mut_ctx).iter().map(|n| compile_name(n, stt)).collect();

  let meta = ConstantMeta::Indc {
    name: name_addr,
    lvls: lvl_addrs,
    ctors: ctor_name_addrs,
    ctor_metas,
    all: all_addrs,
    ctx: ctx_addrs,
    type_meta,
  };

  Ok((data, meta))
}

/// Compile an Axiom.
fn compile_axiom(
  val: &AxiomVal,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Axiom, ConstantMeta), CompileError> {
  let univ_params = &val.cnst.level_params;

  reset_expr_meta(cache);
  let typ =
    compile_expr(&val.cnst.typ, univ_params, &MutCtx::default(), cache, stt)?;
  let type_meta = take_expr_metas(cache);

  let name_addr = compile_name(&val.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data =
    Axiom { is_unsafe: val.is_unsafe, lvls: univ_params.len() as u64, typ };

  let meta = ConstantMeta::Axio { name: name_addr, lvls: lvl_addrs, type_meta };

  Ok((data, meta))
}

/// Compile a Quotient.
fn compile_quotient(
  val: &QuotVal,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<(Quotient, ConstantMeta), CompileError> {
  let univ_params = &val.cnst.level_params;

  reset_expr_meta(cache);
  let typ =
    compile_expr(&val.cnst.typ, univ_params, &MutCtx::default(), cache, stt)?;
  let type_meta = take_expr_metas(cache);

  let name_addr = compile_name(&val.cnst.name, stt);
  let lvl_addrs: Vec<Address> =
    univ_params.iter().map(|n| compile_name(n, stt)).collect();

  let data = Quotient { kind: val.kind, lvls: univ_params.len() as u64, typ };

  let meta = ConstantMeta::Quot { name: name_addr, lvls: lvl_addrs, type_meta };

  Ok((data, meta))
}

// ===========================================================================
// Mutual block compilation
// ===========================================================================

/// Compile a mutual block with block-level sharing.
/// Returns the Constant and its content-addressed hash.
fn compile_mutual_block(
  mut_consts: Vec<IxonMutConst>,
  refs: Vec<Address>,
  univs: Vec<Arc<Univ>>,
) -> (Constant, Address) {
  // Apply sharing analysis across all expressions in the mutual block
  let constant = apply_sharing_to_mutual_block(mut_consts, refs, univs);

  // Compute content address
  let mut bytes = Vec::new();
  constant.put(&mut bytes);
  let addr = Address::hash(&bytes);

  (constant, addr)
}

/// Create Inductive from InductiveVal and Env.
pub fn mk_indc(
  ind: &InductiveVal,
  env: &Arc<LeanEnv>,
) -> Result<Ind, CompileError> {
  let mut ctors = Vec::with_capacity(ind.ctors.len());
  for ctor_name in &ind.ctors {
    if let Some(LeanConstantInfo::CtorInfo(c)) = env.as_ref().get(ctor_name) {
      ctors.push(c.clone());
    } else {
      return Err(CompileError::MissingConstant { name: ctor_name.pretty() });
    }
  }
  Ok(Ind { ind: ind.clone(), ctors })
}

// ===========================================================================
// Comparison functions for sorting
// ===========================================================================

pub fn compare_level(
  x: &Level,
  y: &Level,
  x_ctx: &[Name],
  y_ctx: &[Name],
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (LevelData::Mvar(..), _) | (_, LevelData::Mvar(..)) => {
      Err(CompileError::UnsupportedExpr {
        desc: "level metavariable in comparison",
      })
    },
    (LevelData::Zero(_), LevelData::Zero(_)) => Ok(SOrd::eq(true)),
    (LevelData::Zero(_), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Zero(_)) => Ok(SOrd::gt(true)),
    (LevelData::Succ(x, _), LevelData::Succ(y, _)) => {
      compare_level(x, y, x_ctx, y_ctx)
    },
    (LevelData::Succ(_, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Succ(_, _)) => Ok(SOrd::gt(true)),
    (LevelData::Max(xl, xr, _), LevelData::Max(yl, yr, _)) => {
      SOrd::try_compare(compare_level(xl, yl, x_ctx, y_ctx)?, || {
        compare_level(xr, yr, x_ctx, y_ctx)
      })
    },
    (LevelData::Max(_, _, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Max(_, _, _)) => Ok(SOrd::gt(true)),
    (LevelData::Imax(xl, xr, _), LevelData::Imax(yl, yr, _)) => {
      SOrd::try_compare(compare_level(xl, yl, x_ctx, y_ctx)?, || {
        compare_level(xr, yr, x_ctx, y_ctx)
      })
    },
    (LevelData::Imax(_, _, _), _) => Ok(SOrd::lt(true)),
    (_, LevelData::Imax(_, _, _)) => Ok(SOrd::gt(true)),
    (LevelData::Param(x, _), LevelData::Param(y, _)) => {
      match (
        x_ctx.iter().position(|n| x == n),
        y_ctx.iter().position(|n| y == n),
      ) {
        (Some(xi), Some(yi)) => Ok(SOrd::cmp(&xi, &yi)),
        (None, _) => Err(CompileError::MissingConstant { name: x.pretty() }),
        (_, None) => Err(CompileError::MissingConstant { name: y.pretty() }),
      }
    },
  }
}

pub fn compare_expr(
  x: &LeanExpr,
  y: &LeanExpr,
  mut_ctx: &MutCtx,
  x_lvls: &[Name],
  y_lvls: &[Name],
  stt: &CompileState,
) -> Result<SOrd, CompileError> {
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err(CompileError::UnsupportedExpr { desc: "metavariable in comparison" })
    },
    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err(CompileError::UnsupportedExpr { desc: "fvar in comparison" })
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
            // Compare by address
            let xa = stt.name_to_addr.get(x);
            let ya = stt.name_to_addr.get(y);
            match (xa, ya) {
              (Some(xa), Some(ya)) => Ok(SOrd::cmp(xa.value(), ya.value())),
              _ => {
                Ok(SOrd::cmp(x.get_hash().as_bytes(), y.get_hash().as_bytes()))
              },
            }
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
      let tn: Result<SOrd, CompileError> =
        match (mut_ctx.get(tnx), mut_ctx.get(tny)) {
          (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
          (Some(..), _) => Ok(SOrd::lt(true)),
          (None, Some(..)) => Ok(SOrd::gt(true)),
          (None, None) => {
            let xa = stt.name_to_addr.get(tnx);
            let ya = stt.name_to_addr.get(tny);
            match (xa, ya) {
              (Some(xa), Some(ya)) => Ok(SOrd::cmp(xa.value(), ya.value())),
              _ => Ok(SOrd::cmp(
                tnx.get_hash().as_bytes(),
                tny.get_hash().as_bytes(),
              )),
            }
          },
        };
      let tn = tn?;
      SOrd::try_compare(tn, || {
        SOrd::try_compare(SOrd::cmp(ix, iy), || {
          compare_expr(tx, ty, mut_ctx, x_lvls, y_lvls, stt)
        })
      })
    },
  }
}

// ===========================================================================
// Sorting functions
// ===========================================================================

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
  x: &LeanRecursorRule,
  y: &LeanRecursorRule,
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
  let mut classes = vec![cs.to_owned()];
  loop {
    let ctx = MutConst::ctx(&classes);
    let mut new_classes: Vec<Vec<&MutConst>> = vec![];
    for class in classes.iter() {
      match class.len() {
        0 => {
          return Err(CompileError::InvalidMutualBlock {
            reason: "empty class",
          });
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

// ===========================================================================
// Main compilation entry points
// ===========================================================================

/// Compile a single constant.
pub fn compile_const(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  if let Some(cached) = stt.name_to_addr.get(name) {
    return Ok(cached.clone());
  }

  let cnst = lean_env
    .get(name)
    .ok_or_else(|| CompileError::MissingConstant { name: name.pretty() })?;

  // Handle each constant type
  let addr = match cnst {
    LeanConstantInfo::DefnInfo(val) => {
      if all.len() == 1 {
        // Single definition - no mutual block
        let def = Def::mk_defn(val);
        let mut_ctx = MutConst::single_ctx(def.name.clone());
        let (data, meta) = compile_definition(&def, &mut_ctx, cache, stt)?;
        let refs: Vec<Address> = cache.refs.iter().cloned().collect();
        let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
        let constant = apply_sharing_to_definition(data, refs, univs);
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let addr = Address::hash(&bytes);
        stt.env.store_const(addr.clone(), constant);
        stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
        addr
      } else {
        // Part of a mutual block - handled separately
        compile_mutual(name, all, lean_env, cache, stt)?
      }
    },

    LeanConstantInfo::ThmInfo(val) => {
      if all.len() == 1 {
        let def = Def::mk_theo(val);
        let mut_ctx = MutConst::single_ctx(def.name.clone());
        let (data, meta) = compile_definition(&def, &mut_ctx, cache, stt)?;
        let refs: Vec<Address> = cache.refs.iter().cloned().collect();
        let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
        let constant = apply_sharing_to_definition(data, refs, univs);
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let addr = Address::hash(&bytes);
        stt.env.store_const(addr.clone(), constant);
        stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
        addr
      } else {
        compile_mutual(name, all, lean_env, cache, stt)?
      }
    },

    LeanConstantInfo::OpaqueInfo(val) => {
      if all.len() == 1 {
        let def = Def::mk_opaq(val);
        let mut_ctx = MutConst::single_ctx(def.name.clone());
        let (data, meta) = compile_definition(&def, &mut_ctx, cache, stt)?;
        let refs: Vec<Address> = cache.refs.iter().cloned().collect();
        let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
        let constant = apply_sharing_to_definition(data, refs, univs);
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let addr = Address::hash(&bytes);
        stt.env.store_const(addr.clone(), constant);
        stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
        addr
      } else {
        compile_mutual(name, all, lean_env, cache, stt)?
      }
    },

    LeanConstantInfo::AxiomInfo(val) => {
      let (data, meta) = compile_axiom(val, cache, stt)?;
      let refs: Vec<Address> = cache.refs.iter().cloned().collect();
      let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
      let constant = apply_sharing_to_axiom(data, refs, univs);
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let addr = Address::hash(&bytes);
      stt.env.store_const(addr.clone(), constant);
      stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
      addr
    },

    LeanConstantInfo::QuotInfo(val) => {
      let (data, meta) = compile_quotient(val, cache, stt)?;
      let refs: Vec<Address> = cache.refs.iter().cloned().collect();
      let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
      let constant = apply_sharing_to_quotient(data, refs, univs);
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let addr = Address::hash(&bytes);
      stt.env.store_const(addr.clone(), constant);
      stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
      addr
    },

    LeanConstantInfo::InductInfo(_) => {
      compile_mutual(name, all, lean_env, cache, stt)?
    },

    LeanConstantInfo::RecInfo(val) => {
      if all.len() == 1 {
        let mut_ctx = MutConst::single_ctx(val.cnst.name.clone());
        let (data, meta) = compile_recursor(val, &mut_ctx, cache, stt)?;
        let refs: Vec<Address> = cache.refs.iter().cloned().collect();
        let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
        let constant = apply_sharing_to_recursor(data, refs, univs);
        let mut bytes = Vec::new();
        constant.put(&mut bytes);
        let addr = Address::hash(&bytes);
        stt.env.store_const(addr.clone(), constant);
        stt.env.register_name(name.clone(), Named::new(addr.clone(), meta));
        addr
      } else {
        compile_mutual(name, all, lean_env, cache, stt)?
      }
    },

    LeanConstantInfo::CtorInfo(val) => {
      // Constructors are compiled as part of their inductive
      if let Some(LeanConstantInfo::InductInfo(_)) = lean_env.get(&val.induct) {
        let _ = compile_mutual(&val.induct, all, lean_env, cache, stt)?;
        stt
          .name_to_addr
          .get(name)
          .ok_or_else(|| CompileError::MissingConstant { name: name.pretty() })?
          .clone()
      } else {
        return Err(CompileError::MissingConstant {
          name: val.induct.pretty(),
        });
      }
    },
  };

  stt.name_to_addr.insert(name.clone(), addr.clone());
  Ok(addr)
}

/// Compile a mutual block.
fn compile_mutual(
  name: &Name,
  all: &NameSet,
  lean_env: &Arc<LeanEnv>,
  cache: &mut BlockCache,
  stt: &CompileState,
) -> Result<Address, CompileError> {
  // Collect all constants in the mutual block
  let mut cs = Vec::new();
  for n in all {
    let Some(const_info) = lean_env.get(n) else {
      return Err(CompileError::MissingConstant { name: n.pretty() });
    };
    let mut_const = match const_info {
      LeanConstantInfo::InductInfo(val) => {
        MutConst::Indc(mk_indc(val, lean_env)?)
      },
      LeanConstantInfo::DefnInfo(val) => MutConst::Defn(Def::mk_defn(val)),
      LeanConstantInfo::OpaqueInfo(val) => MutConst::Defn(Def::mk_opaq(val)),
      LeanConstantInfo::ThmInfo(val) => MutConst::Defn(Def::mk_theo(val)),
      LeanConstantInfo::RecInfo(val) => MutConst::Recr(val.clone()),
      _ => continue,
    };
    cs.push(mut_const);
  }

  // Sort constants
  let sorted_classes = sort_consts(&cs.iter().collect::<Vec<_>>(), cache, stt)?;
  let mut_ctx = MutConst::ctx(&sorted_classes);

  // Compile each constant
  let mut ixon_mutuals = Vec::new();
  let mut all_metas: FxHashMap<Name, ConstantMeta> = FxHashMap::default();

  for class in &sorted_classes {
    for cnst in class {
      match cnst {
        MutConst::Defn(def) => {
          let (data, meta) = compile_definition(def, &mut_ctx, cache, stt)?;
          ixon_mutuals.push(IxonMutConst::Defn(data));
          all_metas.insert(def.name.clone(), meta);
        },
        MutConst::Indc(ind) => {
          let (data, meta) = compile_inductive(ind, &mut_ctx, cache, stt)?;
          ixon_mutuals.push(IxonMutConst::Indc(data));
          all_metas.insert(ind.ind.cnst.name.clone(), meta);
          // Constructor metas are now embedded in the Indc meta
        },
        MutConst::Recr(rec) => {
          let (data, meta) = compile_recursor(rec, &mut_ctx, cache, stt)?;
          ixon_mutuals.push(IxonMutConst::Recr(data));
          all_metas.insert(rec.cnst.name.clone(), meta);
        },
      }
    }
  }

  // Create mutual block with sharing
  let refs: Vec<Address> = cache.refs.iter().cloned().collect();
  let univs: Vec<Arc<Univ>> = cache.univs.iter().cloned().collect();
  let (block_constant, block_addr) =
    compile_mutual_block(ixon_mutuals, refs, univs);
  stt.env.store_const(block_addr.clone(), block_constant);
  stt.blocks.insert(block_addr.clone());

  // Create projections for each constant
  let mut idx = 0u64;
  for class in &sorted_classes {
    for cnst in class {
      let n = cnst.name();
      let meta = all_metas.get(&n).cloned().unwrap_or_default();

      let proj = match cnst {
        MutConst::Defn(_) => {
          Constant::new(ConstantInfo::DPrj(DefinitionProj {
            idx,
            block: block_addr.clone(),
          }))
        },
        MutConst::Indc(ind) => {
          // Register inductive projection
          let indc_proj = Constant::new(ConstantInfo::IPrj(InductiveProj {
            idx,
            block: block_addr.clone(),
          }));
          let mut proj_bytes = Vec::new();
          indc_proj.put(&mut proj_bytes);
          let proj_addr = Address::hash(&proj_bytes);
          stt.env.store_const(proj_addr.clone(), indc_proj);
          stt.env.register_name(
            n.clone(),
            Named::new(proj_addr.clone(), meta.clone()),
          );
          stt.name_to_addr.insert(n.clone(), proj_addr.clone());

          // Register constructor projections
          for (cidx, ctor) in ind.ctors.iter().enumerate() {
            let ctor_meta =
              all_metas.get(&ctor.cnst.name).cloned().unwrap_or_default();
            let ctor_proj =
              Constant::new(ConstantInfo::CPrj(ConstructorProj {
                idx,
                cidx: cidx as u64,
                block: block_addr.clone(),
              }));
            let mut ctor_bytes = Vec::new();
            ctor_proj.put(&mut ctor_bytes);
            let ctor_addr = Address::hash(&ctor_bytes);
            stt.env.store_const(ctor_addr.clone(), ctor_proj);
            stt.env.register_name(
              ctor.cnst.name.clone(),
              Named::new(ctor_addr.clone(), ctor_meta),
            );
            stt.name_to_addr.insert(ctor.cnst.name.clone(), ctor_addr);
          }

          continue;
        },
        MutConst::Recr(_) => Constant::new(ConstantInfo::RPrj(RecursorProj {
          idx,
          block: block_addr.clone(),
        })),
      };

      let mut proj_bytes = Vec::new();
      proj.put(&mut proj_bytes);
      let proj_addr = Address::hash(&proj_bytes);
      stt.env.store_const(proj_addr.clone(), proj);
      stt.env.register_name(n.clone(), Named::new(proj_addr.clone(), meta));
      stt.name_to_addr.insert(n.clone(), proj_addr);
    }
    idx += 1;
  }

  // Return the address for the requested name
  stt
    .name_to_addr
    .get(name)
    .ok_or_else(|| CompileError::MissingConstant { name: name.pretty() })
    .map(|r| r.clone())
}

/// Compile an entire Lean environment to Ixon format.
/// Work-stealing compilation using crossbeam channels.
///
/// Instead of processing blocks in waves (which underutilizes cores when wave sizes vary),
/// we use a work queue. When a block completes, it immediately unlocks dependent blocks.
pub fn compile_env(
  lean_env: &Arc<LeanEnv>,
) -> Result<CompileState, CompileError> {
  let start_ref_graph = std::time::SystemTime::now();
  let graph = build_ref_graph(lean_env.as_ref());
  println!(
    "Ref-graph: {:.2}s",
    start_ref_graph.elapsed().unwrap().as_secs_f32()
  );

  let start_ground = std::time::SystemTime::now();
  let ungrounded = ground_consts(lean_env.as_ref(), &graph.in_refs);
  if !ungrounded.is_empty() {
    for (n, e) in ungrounded {
      println!("Ungrounded {:?}: {:?}", n, e);
    }
    return Err(CompileError::InvalidMutualBlock {
      reason: "ungrounded environment",
    });
  }
  println!("Ground: {:.2}s", start_ground.elapsed().unwrap().as_secs_f32());

  let start_sccs = std::time::SystemTime::now();
  let condensed = compute_sccs(&graph.out_refs);
  println!("SCCs: {:.2}s", start_sccs.elapsed().unwrap().as_secs_f32());

  let start_compile = std::time::SystemTime::now();
  let stt = CompileState::default();

  // Build work-stealing data structures
  let total_blocks = condensed.blocks.len();

  // For each block: (all names in block, remaining dep count)
  let block_info: DashMap<Name, (NameSet, AtomicUsize)> = DashMap::default();

  // Reverse deps: name → set of block leaders that depend on this name
  let reverse_deps: DashMap<Name, Vec<Name>> = DashMap::default();

  // Initialize block info and reverse deps
  for (lo, all) in &condensed.blocks {
    let deps =
      condensed.block_refs.get(lo).ok_or(CompileError::InvalidMutualBlock {
        reason: "missing block refs",
      })?;

    block_info.insert(lo.clone(), (all.clone(), AtomicUsize::new(deps.len())));

    // Register reverse dependencies
    for dep_name in deps {
      reverse_deps.entry(dep_name.clone()).or_default().push(lo.clone());
    }
  }

  // Shared ready queue: blocks that are ready to compile
  // Use a Mutex<Vec> for simplicity - workers push newly-ready blocks here
  let ready_queue: std::sync::Mutex<Vec<(Name, NameSet)>> =
    std::sync::Mutex::new(Vec::new());

  // Initialize with blocks that have no dependencies
  {
    let mut queue = ready_queue.lock().unwrap();
    for entry in block_info.iter() {
      let lo = entry.key();
      let (all, dep_count) = entry.value();
      if dep_count.load(AtomicOrdering::SeqCst) == 0 {
        queue.push((lo.clone(), all.clone()));
      }
    }
  }

  // Track completed count for termination
  let completed = AtomicUsize::new(0);

  // Error storage for propagating errors from workers
  let error: std::sync::Mutex<Option<CompileError>> =
    std::sync::Mutex::new(None);

  // Use scoped threads to borrow from parent scope
  let num_threads =
    thread::available_parallelism().map(|n| n.get()).unwrap_or(4);

  // Progress tracking
  let last_progress = AtomicUsize::new(0);
  let last_progress_ref = &last_progress;

  println!("Compiling {} blocks with {} threads...", total_blocks, num_threads);

  // Take references to shared data outside the loop
  let error_ref = &error;
  let stt_ref = &stt;
  let reverse_deps_ref = &reverse_deps;
  let block_info_ref = &block_info;
  let completed_ref = &completed;
  let ready_queue_ref = &ready_queue;

  thread::scope(|s| {
    // Spawn worker threads
    for _ in 0..num_threads {
      s.spawn(move || {
        loop {
          // Try to get work from the ready queue
          let work = {
            let mut queue = ready_queue_ref.lock().unwrap();
            queue.pop()
          };

          match work {
            Some((lo, all)) => {
              // Check if we should stop due to error
              if error_ref.lock().unwrap().is_some() {
                return;
              }

              // Track time for slow block detection
              let block_start = std::time::Instant::now();

              // Compile this block
              let mut cache = BlockCache::default();
              if let Err(e) =
                compile_const(&lo, &all, lean_env, &mut cache, stt_ref)
              {
                let mut err_guard = error_ref.lock().unwrap();
                if err_guard.is_none() {
                  *err_guard = Some(e);
                }
                return;
              }

              // Check for slow blocks
              let elapsed = block_start.elapsed();
              if elapsed.as_secs_f32() > 1.0 {
                eprintln!(
                  "Slow block {:?} ({} consts): {:.2}s",
                  lo.pretty(),
                  all.len(),
                  elapsed.as_secs_f32()
                );
              }

              // Collect newly-ready blocks
              let mut newly_ready = Vec::new();

              // For each name in this block, decrement dep counts for dependents
              for name in &all {
                if let Some(dependents) = reverse_deps_ref.get(name) {
                  for dependent_lo in dependents.value() {
                    if let Some(entry) = block_info_ref.get(dependent_lo) {
                      let (dep_all, dep_count) = entry.value();
                      let prev = dep_count.fetch_sub(1, AtomicOrdering::SeqCst);
                      if prev == 1 {
                        // This block is now ready
                        newly_ready
                          .push((dependent_lo.clone(), dep_all.clone()));
                      }
                    }
                  }
                }
              }

              // Add newly-ready blocks to the queue
              if !newly_ready.is_empty() {
                let mut queue = ready_queue_ref.lock().unwrap();
                queue.extend(newly_ready);
              }

              completed_ref.fetch_add(1, AtomicOrdering::SeqCst);

              // Print progress every 10000 blocks or at 10%, 20%, etc.
              // (disabled for cleaner output - uncomment for debugging)
              // let done = completed_ref.load(AtomicOrdering::Relaxed);
              // let last = last_progress_ref.load(AtomicOrdering::Relaxed);
              // let pct = done * 100 / total_blocks;
              // let last_pct = last * 100 / total_blocks;
              // if pct > last_pct || done - last >= 10000 {
              //   if last_progress_ref.compare_exchange(
              //     last, done, AtomicOrdering::SeqCst, AtomicOrdering::Relaxed
              //   ).is_ok() {
              //     let elapsed = start_compile.elapsed().unwrap().as_secs_f32();
              //     eprintln!("Progress: {}/{} blocks ({}%) in {:.1}s",
              //       done, total_blocks, pct, elapsed);
              //   }
              // }
              let _ = last_progress_ref; // suppress unused warning
            },
            None => {
              // No work available - check if we're done
              if completed_ref.load(AtomicOrdering::SeqCst) == total_blocks {
                return;
              }
              // Check for errors
              if error_ref.lock().unwrap().is_some() {
                return;
              }
              // Brief sleep to avoid busy-waiting
              thread::sleep(std::time::Duration::from_micros(100));
            },
          }
        }
      });
    }
  });

  // Check for errors
  if let Some(e) = error.into_inner().unwrap() {
    return Err(e);
  }

  // Verify completion
  let final_completed = completed.load(AtomicOrdering::SeqCst);
  if final_completed != total_blocks {
    // Find what's still blocked
    let mut blocked_count = 0;
    for entry in block_info.iter() {
      let (_, dep_count) = entry.value();
      if dep_count.load(AtomicOrdering::SeqCst) > 0 {
        blocked_count += 1;
        if blocked_count <= 5 {
          eprintln!(
            "Still blocked: {:?} with {} deps remaining",
            entry.key().pretty(),
            dep_count.load(AtomicOrdering::SeqCst)
          );
        }
      }
    }
    return Err(CompileError::InvalidMutualBlock {
      reason: "circular dependency or missing constant",
    });
  }

  println!("Compile: {:.2}s", start_compile.elapsed().unwrap().as_secs_f32());
  Ok(stt)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{BinderInfo, Expr as LeanExpr, Level};

  #[test]
  fn test_compile_univ_zero() {
    let level = Level::zero();
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    assert!(matches!(univ.as_ref(), Univ::Zero));
  }

  #[test]
  fn test_compile_univ_succ() {
    let level = Level::succ(Level::zero());
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    match univ.as_ref() {
      Univ::Succ(inner) => assert!(matches!(inner.as_ref(), Univ::Zero)),
      _ => panic!("expected Succ"),
    }
  }

  #[test]
  fn test_compile_univ_param() {
    let name = Name::str(Name::anon(), "u".to_string());
    let level = Level::param(name.clone());
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[name], &mut cache).unwrap();
    assert!(matches!(univ.as_ref(), Univ::Var(0)));
  }

  #[test]
  fn test_compile_univ_max() {
    let level = Level::max(Level::zero(), Level::succ(Level::zero()));
    let mut cache = BlockCache::default();
    let univ = compile_univ(&level, &[], &mut cache).unwrap();
    match univ.as_ref() {
      Univ::Max(a, b) => {
        assert!(matches!(a.as_ref(), Univ::Zero));
        match b.as_ref() {
          Univ::Succ(inner) => assert!(matches!(inner.as_ref(), Univ::Zero)),
          _ => panic!("expected Succ"),
        }
      },
      _ => panic!("expected Max"),
    }
  }

  #[test]
  fn test_store_string() {
    let stt = CompileState::default();
    let addr1 = store_string("hello", &stt);
    let addr2 = store_string("hello", &stt);
    // Same content should give same address
    assert_eq!(addr1, addr2);
    // Check we can retrieve it
    let bytes = stt.env.get_blob(&addr1).unwrap();
    assert_eq!(bytes, b"hello");
  }

  #[test]
  fn test_store_nat() {
    let stt = CompileState::default();
    let n = Nat::from(42u64);
    let addr = store_nat(&n, &stt);
    let bytes = stt.env.get_blob(&addr).unwrap();
    let n2 = Nat::from_le_bytes(&bytes);
    assert_eq!(n, n2);
  }

  #[test]
  fn test_compile_name_anon() {
    let stt = CompileState::default();
    let name = Name::anon();
    let addr = compile_name(&name, &stt);
    // Name is stored in env.names, not blobs
    let stored_name = stt.env.names.get(&addr).unwrap();
    assert_eq!(*stored_name, name);
  }

  #[test]
  fn test_compile_name_str() {
    let stt = CompileState::default();
    let name = Name::str(Name::anon(), "foo".to_string());
    let addr = compile_name(&name, &stt);
    // Name is stored in env.names
    let stored_name = stt.env.names.get(&addr).unwrap();
    assert_eq!(*stored_name, name);
    // String component should be in blobs
    let foo_bytes = "foo".as_bytes();
    let foo_addr = Address::hash(foo_bytes);
    assert!(stt.env.blobs.contains_key(&foo_addr));
  }

  #[test]
  fn test_compile_expr_bvar() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::bvar(Nat::from(3u64));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    assert!(matches!(result.as_ref(), Expr::Var(3)));
  }

  #[test]
  fn test_compile_expr_sort() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::sort(Level::zero());
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Sort(idx) => {
        assert_eq!(*idx, 0);
        assert!(matches!(
          cache.univs.get_index(0).unwrap().as_ref(),
          Univ::Zero
        ));
      },
      _ => panic!("expected Sort"),
    }
  }

  #[test]
  fn test_compile_expr_app() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let f = LeanExpr::bvar(Nat::from(0u64));
    let a = LeanExpr::bvar(Nat::from(1u64));
    let expr = LeanExpr::app(f, a);
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::App(f, a) => {
        assert!(matches!(f.as_ref(), Expr::Var(0)));
        assert!(matches!(a.as_ref(), Expr::Var(1)));
      },
      _ => panic!("expected App"),
    }
  }

  #[test]
  fn test_compile_expr_lam() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let ty = LeanExpr::sort(Level::zero());
    let body = LeanExpr::bvar(Nat::from(0u64));
    let expr = LeanExpr::lam(Name::anon(), ty, body, BinderInfo::Default);
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Lam(ty, body) => {
        match ty.as_ref() {
          Expr::Sort(idx) => {
            assert_eq!(*idx, 0);
            assert!(matches!(
              cache.univs.get_index(0).unwrap().as_ref(),
              Univ::Zero
            ));
          },
          _ => panic!("expected Sort for ty"),
        }
        assert!(matches!(body.as_ref(), Expr::Var(0)));
      },
      _ => panic!("expected Lam"),
    }
  }

  #[test]
  fn test_compile_expr_nat_lit() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::lit(Literal::NatVal(Nat::from(42u64)));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Nat(ref_idx) => {
        let addr = cache.refs.get_index(*ref_idx as usize).unwrap();
        let bytes = stt.env.get_blob(addr).unwrap();
        let n = Nat::from_le_bytes(&bytes);
        assert_eq!(n, Nat::from(42u64));
      },
      _ => panic!("expected Nat"),
    }
  }

  #[test]
  fn test_compile_expr_str_lit() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let expr = LeanExpr::lit(Literal::StrVal("hello".to_string()));
    let result =
      compile_expr(&expr, &[], &MutCtx::default(), &mut cache, &stt).unwrap();
    match result.as_ref() {
      Expr::Str(ref_idx) => {
        let addr = cache.refs.get_index(*ref_idx as usize).unwrap();
        let bytes = stt.env.get_blob(addr).unwrap();
        assert_eq!(String::from_utf8(bytes).unwrap(), "hello");
      },
      _ => panic!("expected Str"),
    }
  }

  #[test]
  fn test_compile_axiom() {
    use crate::ix::env::{AxiomVal, ConstantVal};

    // Create a simple axiom: axiom myAxiom : Type
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    let result = compile_const(&name, &all, &lean_env, &mut cache, &stt);
    assert!(result.is_ok(), "compile_const failed: {:?}", result.err());

    let addr = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name));
    assert!(stt.env.get_const(&addr).is_some());
  }

  #[test]
  fn test_compile_simple_def() {
    use crate::ix::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    // Create a simple definition: def myDef : Nat := 42
    let name = Name::str(Name::anon(), "myDef".to_string());
    let nat_name = Name::str(Name::anon(), "Nat".to_string());
    let typ = LeanExpr::cnst(nat_name.clone(), vec![]);
    let value = LeanExpr::lit(Literal::NatVal(Nat::from(42u64)));
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let def = DefinitionVal {
      cnst,
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    // Note: We also need Nat in the env for the reference to work,
    // but for this test we just check the compile doesn't crash
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    // This will fail because nat_name isn't in name_to_addr, but let's see the error
    let result = compile_const(&name, &all, &lean_env, &mut cache, &stt);
    // We expect this to fail with MissingConstant for Nat
    match result {
      Err(CompileError::MissingConstant { name: missing }) => {
        assert!(
          missing.contains("Nat"),
          "Expected missing Nat, got: {}",
          missing
        );
      },
      Err(e) => panic!("Unexpected error: {:?}", e),
      Ok(_) => panic!("Expected error for missing Nat reference"),
    }
  }

  #[test]
  fn test_compile_self_referential_def() {
    use crate::ix::env::{
      ConstantInfo as LeanConstantInfo, ConstantVal, DefinitionSafety,
      DefinitionVal, Env as LeanEnv, ReducibilityHints,
    };
    use crate::ix::ixon::constant::ConstantInfo;

    // Create a self-referential definition (like a recursive function placeholder)
    // def myDef : Type := myDef  (this is silly but tests the mutual handling)
    let name = Name::str(Name::anon(), "myDef".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let value = LeanExpr::cnst(name.clone(), vec![]); // self-reference
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let def = DefinitionVal {
      cnst,
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let mut all = NameSet::default();
    all.insert(name.clone());

    // This should work because it's a single self-referential def
    let result = compile_const(&name, &all, &lean_env, &mut cache, &stt);
    assert!(result.is_ok(), "compile_const failed: {:?}", result.err());

    let addr = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name));

    // Check the constant was stored
    let cnst = stt.env.get_const(&addr);
    assert!(cnst.is_some());
    match cnst.unwrap() {
      Constant { info: ConstantInfo::Defn(d), .. } => {
        // Value should be a Rec(0) since it's self-referential in a single-element block
        match d.value.as_ref() {
          Expr::Rec(0, _) => {}, // Expected
          other => panic!("Expected Rec(0), got {:?}", other),
        }
      },
      other => panic!("Expected Defn, got {:?}", other),
    }
  }

  #[test]
  fn test_compile_env_single_axiom() {
    use crate::ix::env::{AxiomVal, ConstantVal};

    // Create a minimal environment with just one axiom
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&name), "name not in name_to_addr");
    assert_eq!(stt.env.const_count(), 1, "expected 1 constant");
  }

  #[test]
  fn test_compile_env_two_independent_axioms() {
    use crate::ix::env::{AxiomVal, ConstantVal};

    let name1 = Name::str(Name::anon(), "axiom1".to_string());
    let name2 = Name::str(Name::anon(), "axiom2".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero()));

    let axiom1 = AxiomVal {
      cnst: ConstantVal {
        name: name1.clone(),
        level_params: vec![],
        typ: typ.clone(),
      },
      is_unsafe: false,
    };
    let axiom2 = AxiomVal {
      cnst: ConstantVal { name: name2.clone(), level_params: vec![], typ },
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name1.clone(), LeanConstantInfo::AxiomInfo(axiom1));
    lean_env.insert(name2.clone(), LeanConstantInfo::AxiomInfo(axiom2));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    // Both names should be registered
    assert!(stt.name_to_addr.contains_key(&name1), "name1 not in name_to_addr");
    assert!(stt.name_to_addr.contains_key(&name2), "name2 not in name_to_addr");
    // Both names point to the same constant (alpha-equivalent axioms)
    let addr1 = stt.name_to_addr.get(&name1).unwrap().clone();
    let addr2 = stt.name_to_addr.get(&name2).unwrap().clone();
    assert_eq!(
      addr1, addr2,
      "alpha-equivalent axioms should have same address"
    );
    // Only 1 unique constant in the store (alpha-equivalent axioms deduplicated)
    assert_eq!(stt.env.const_count(), 1);
  }

  #[test]
  fn test_compile_env_def_referencing_axiom() {
    use crate::ix::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    let axiom_name = Name::str(Name::anon(), "myType".to_string());
    let def_name = Name::str(Name::anon(), "myDef".to_string());

    // axiom myType : Type
    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::succ(Level::zero())),
      },
      is_unsafe: false,
    };

    // def myDef : myType := myType (referencing the axiom in the value)
    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(axiom_name.clone(), vec![]),
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]), // reference the axiom
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    let result = compile_env(&lean_env);
    assert!(result.is_ok(), "compile_env failed: {:?}", result.err());

    let stt = result.unwrap();
    assert!(stt.name_to_addr.contains_key(&axiom_name));
    assert!(stt.name_to_addr.contains_key(&def_name));
    assert_eq!(stt.env.const_count(), 2);
  }

  // =========================================================================
  // Sharing tests
  // =========================================================================

  #[test]
  fn test_mutual_block_roundtrip() {
    use crate::ix::env::DefinitionSafety;
    use crate::ix::ixon::constant::{DefKind, Definition};

    // Create a mutual block and verify it roundtrips through serialization
    let sort0 = Expr::sort(0);
    let ty = Expr::all(sort0.clone(), Expr::var(0));

    let def1 = IxonMutConst::Defn(Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: ty.clone(),
      value: Expr::var(0),
    });

    let def2 = IxonMutConst::Defn(Definition {
      kind: DefKind::Theorem,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: ty,
      value: Expr::var(1),
    });

    let (constant, addr) =
      compile_mutual_block(vec![def1, def2], vec![], vec![]);

    // Serialize
    let mut buf = Vec::new();
    constant.put(&mut buf);

    // Deserialize
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    // Re-serialize to check determinism
    let mut buf2 = Vec::new();
    recovered.put(&mut buf2);

    assert_eq!(buf, buf2, "Serialization should be deterministic");

    // Re-hash to check address stability
    let addr2 = Address::hash(&buf2);
    assert_eq!(addr, addr2, "Content address should be stable");
  }

  // =========================================================================
  // Constant-level sharing tests
  // =========================================================================

  #[test]
  fn test_apply_sharing_basic() {
    // Test the apply_sharing helper function with a repeated subterm
    let sort0 = Expr::sort(0);
    let var0 = Expr::var(0);
    // Create term: App(Lam(Sort0, Var0), Lam(Sort0, Var0))
    // Lam(Sort0, Var0) is repeated and should be shared
    let lam = Expr::lam(sort0.clone(), var0);
    let app = Expr::app(lam.clone(), lam);

    let (rewritten, sharing) = apply_sharing(vec![app]);

    // Should have sharing since lam is used twice
    assert!(!sharing.is_empty(), "Expected sharing for repeated subterm");
    // The sharing vector should contain the shared Lam
    assert!(sharing.iter().any(|e| matches!(e.as_ref(), Expr::Lam(_, _))));
    // The rewritten expression should have Share references
    assert!(matches!(rewritten[0].as_ref(), Expr::App(_, _)));
  }

  #[test]
  fn test_definition_with_sharing() {
    use crate::ix::ixon::constant::Definition;

    // Create a definition where typ and value share structure
    let sort0 = Expr::sort(0);
    let shared_subterm = Expr::all(sort0.clone(), Expr::var(0));
    // typ = App(shared, shared) -- shared twice
    let typ = Expr::app(shared_subterm.clone(), shared_subterm.clone());
    // value = shared
    let value = shared_subterm;

    let (rewritten, sharing) = apply_sharing(vec![typ, value]);

    // shared_subterm appears 3 times total, should definitely be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for definition with repeated subterms"
    );

    // Create constant with sharing at Constant level
    let def = Definition {
      kind: DefKind::Definition,
      safety: crate::ix::env::DefinitionSafety::Safe,
      lvls: 0,
      typ: rewritten[0].clone(),
      value: rewritten[1].clone(),
    };

    let constant = Constant::with_tables(
      ConstantInfo::Defn(def),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    assert!(matches!(recovered.info, ConstantInfo::Defn(_)));
  }

  #[test]
  fn test_axiom_with_sharing() {
    use crate::ix::ixon::constant::Axiom;

    // Axiom with repeated subterms in its type
    let sort0 = Expr::sort(0);
    let shared = Expr::all(sort0.clone(), Expr::var(0));
    // typ = All(shared, All(shared, Var(0)))
    let typ =
      Expr::all(shared.clone(), Expr::all(shared.clone(), Expr::var(0)));

    let (rewritten, sharing) = apply_sharing(vec![typ]);

    // shared appears twice, should be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for axiom with repeated subterms"
    );

    let axiom = Axiom { is_unsafe: false, lvls: 0, typ: rewritten[0].clone() };
    let constant = Constant::with_tables(
      ConstantInfo::Axio(axiom),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    assert!(matches!(recovered.info, ConstantInfo::Axio(_)));
  }

  #[test]
  fn test_recursor_with_sharing() {
    use crate::ix::ixon::constant::{Recursor, RecursorRule};

    // Recursor with shared subterms across typ and rules
    let sort0 = Expr::sort(0);
    let shared = Expr::lam(sort0.clone(), Expr::var(0));

    // typ uses shared twice
    let typ = Expr::app(shared.clone(), shared.clone());

    // rules also use shared
    let rules = vec![
      RecursorRule { fields: 0, rhs: shared.clone() },
      RecursorRule { fields: 1, rhs: shared },
    ];

    // Collect all expressions
    let mut all_exprs = vec![typ];
    for r in &rules {
      all_exprs.push(r.rhs.clone());
    }

    let (rewritten, sharing) = apply_sharing(all_exprs);

    // shared appears 4 times, should definitely be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for recursor with repeated subterms"
    );

    let rec = Recursor {
      k: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      motives: 1,
      minors: 2,
      typ: rewritten[0].clone(),
      rules: rules
        .into_iter()
        .zip(rewritten.into_iter().skip(1))
        .map(|(r, rhs)| RecursorRule { fields: r.fields, rhs })
        .collect(),
    };

    let constant = Constant::with_tables(
      ConstantInfo::Recr(rec),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    if let ConstantInfo::Recr(rec2) = &recovered.info {
      assert_eq!(2, rec2.rules.len());
    } else {
      panic!("Expected Recursor");
    }
  }

  #[test]
  fn test_inductive_with_sharing() {
    use crate::ix::ixon::constant::{Constructor, Inductive};

    // Inductive with shared subterms across type and constructors
    let sort0 = Expr::sort(0);
    let shared = Expr::all(sort0.clone(), Expr::var(0));

    let typ = Expr::app(shared.clone(), shared.clone());

    let ctors = vec![
      Constructor {
        is_unsafe: false,
        lvls: 0,
        cidx: 0,
        params: 0,
        fields: 0,
        typ: shared.clone(),
      },
      Constructor {
        is_unsafe: false,
        lvls: 0,
        cidx: 1,
        params: 0,
        fields: 1,
        typ: shared,
      },
    ];

    // Collect all expressions
    let mut all_exprs = vec![typ];
    for c in &ctors {
      all_exprs.push(c.typ.clone());
    }

    let (rewritten, sharing) = apply_sharing(all_exprs);

    // shared appears 4 times, should be shared
    assert!(
      !sharing.is_empty(),
      "Expected sharing for inductive with repeated subterms"
    );

    let ind = Inductive {
      recr: false,
      refl: false,
      is_unsafe: false,
      lvls: 0,
      params: 0,
      indices: 0,
      nested: 0,
      typ: rewritten[0].clone(),
      ctors: ctors
        .into_iter()
        .zip(rewritten.into_iter().skip(1))
        .map(|(c, typ)| Constructor {
          is_unsafe: c.is_unsafe,
          lvls: c.lvls,
          cidx: c.cidx,
          params: c.params,
          fields: c.fields,
          typ,
        })
        .collect(),
    };

    // Wrap in MutConst for serialization with sharing at Constant level
    let constant = Constant::with_tables(
      ConstantInfo::Muts(vec![IxonMutConst::Indc(ind)]),
      sharing.clone(),
      vec![],
      vec![],
    );

    let mut buf = Vec::new();
    constant.put(&mut buf);
    let recovered = Constant::get(&mut buf.as_slice()).unwrap();

    assert_eq!(sharing.len(), recovered.sharing.len());
    if let ConstantInfo::Muts(mutuals) = &recovered.info {
      if let Some(IxonMutConst::Indc(ind2)) = mutuals.first() {
        assert_eq!(2, ind2.ctors.len());
      } else {
        panic!("Expected Inductive in Muts");
      }
    } else {
      panic!("Expected Muts");
    }
  }

  #[test]
  fn test_no_sharing_when_not_repeated() {
    // When a subterm only appears once, it shouldn't be shared
    let _sort0 = Expr::sort(0);
    let var0 = Expr::var(0);
    let var1 = Expr::var(1);
    let app = Expr::app(var0, var1);

    let (rewritten, sharing) = apply_sharing(vec![app.clone()]);

    // No repeated subterms, so no sharing
    assert!(sharing.is_empty(), "Expected no sharing when nothing is repeated");
    // Rewritten should be identical to original
    assert_eq!(rewritten[0].as_ref(), app.as_ref());
  }

  // =========================================================================
  // Compile/Decompile Roundtrip Tests
  // =========================================================================

  #[test]
  fn test_roundtrip_axiom() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{AxiomVal, ConstantVal};

    // Create an axiom: axiom myAxiom : Type
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let typ = LeanExpr::sort(Level::succ(Level::zero())); // Type 0
    let cnst = ConstantVal { name: name.clone(), level_params: vec![], typ };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered =
      dstt.env.get(&name).expect("name not found in decompiled env");
    match &*recovered {
      LeanConstantInfo::AxiomInfo(ax) => {
        assert_eq!(ax.cnst.name, axiom.cnst.name);
        assert_eq!(ax.is_unsafe, axiom.is_unsafe);
        assert_eq!(ax.cnst.level_params.len(), axiom.cnst.level_params.len());
      },
      _ => panic!("Expected AxiomInfo"),
    }
  }

  #[test]
  fn test_roundtrip_axiom_with_level_params() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{AxiomVal, ConstantVal, Env as LeanEnv};

    // Create an axiom with universe params: axiom myAxiom.{u, v} : Sort (max u v)
    let name = Name::str(Name::anon(), "myAxiom".to_string());
    let u = Name::str(Name::anon(), "u".to_string());
    let v = Name::str(Name::anon(), "v".to_string());
    let typ = LeanExpr::sort(Level::max(
      Level::param(u.clone()),
      Level::param(v.clone()),
    ));
    let cnst = ConstantVal {
      name: name.clone(),
      level_params: vec![u.clone(), v.clone()],
      typ,
    };
    let axiom = AxiomVal { cnst, is_unsafe: false };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::AxiomInfo(axiom.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::AxiomInfo(ax) => {
        assert_eq!(ax.cnst.name, name);
        assert_eq!(ax.cnst.level_params.len(), 2);
        assert_eq!(ax.cnst.level_params[0], u);
        assert_eq!(ax.cnst.level_params[1], v);
      },
      _ => panic!("Expected AxiomInfo"),
    }
  }

  #[test]
  fn test_roundtrip_definition() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    // Create a definition: def id : Type -> Type := fun x => x
    let name = Name::str(Name::anon(), "id".to_string());
    let type1 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let typ = LeanExpr::all(
      Name::str(Name::anon(), "x".to_string()),
      type1.clone(),
      type1.clone(),
      crate::ix::env::BinderInfo::Default,
    );
    let value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type1,
      LeanExpr::bvar(Nat::from(0u64)),
      crate::ix::env::BinderInfo::Default,
    );
    let def = DefinitionVal {
      cnst: ConstantVal { name: name.clone(), level_params: vec![], typ },
      value,
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::DefnInfo(def.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, name);
        assert_eq!(d.hints, def.hints);
        assert_eq!(d.safety, def.safety);
        assert_eq!(d.all.len(), def.all.len());
      },
      _ => panic!("Expected DefnInfo"),
    }
  }

  #[test]
  fn test_roundtrip_def_referencing_axiom() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints,
    };

    // Create axiom A : Type and def B : A := A
    let axiom_name = Name::str(Name::anon(), "A".to_string());
    let def_name = Name::str(Name::anon(), "B".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      is_unsafe: false,
    };

    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(axiom_name.clone(), vec![]),
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check both roundtrip
    assert!(dstt.env.contains_key(&axiom_name));
    assert!(dstt.env.contains_key(&def_name));

    match &*dstt.env.get(&def_name).unwrap() {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, def_name);
      },
      _ => panic!("Expected DefnInfo"),
    }
  }

  #[test]
  fn test_roundtrip_quotient() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{ConstantVal, Env as LeanEnv, QuotKind, QuotVal};

    // Create quotient constants
    let quot_name = Name::str(Name::anon(), "Quot".to_string());
    let u = Name::str(Name::anon(), "u".to_string());

    // Quot.{u} : (α : Sort u) → (α → α → Prop) → Sort u
    let alpha = Name::str(Name::anon(), "α".to_string());
    let sort_u = LeanExpr::sort(Level::param(u.clone()));
    let prop = LeanExpr::sort(Level::zero());

    // Build: (α : Sort u) → (α → α → Prop) → Sort u
    let rel_type = LeanExpr::all(
      Name::anon(),
      LeanExpr::bvar(Nat::from(0u64)),
      LeanExpr::all(
        Name::anon(),
        LeanExpr::bvar(Nat::from(1u64)),
        prop.clone(),
        crate::ix::env::BinderInfo::Default,
      ),
      crate::ix::env::BinderInfo::Default,
    );
    let typ = LeanExpr::all(
      alpha,
      sort_u.clone(),
      LeanExpr::all(
        Name::anon(),
        rel_type,
        sort_u.clone(),
        crate::ix::env::BinderInfo::Default,
      ),
      crate::ix::env::BinderInfo::Default,
    );

    let quot = QuotVal {
      cnst: ConstantVal {
        name: quot_name.clone(),
        level_params: vec![u.clone()],
        typ,
      },
      kind: QuotKind::Type,
    };

    let mut lean_env = LeanEnv::default();
    lean_env
      .insert(quot_name.clone(), LeanConstantInfo::QuotInfo(quot.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&quot_name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::QuotInfo(q) => {
        assert_eq!(q.cnst.name, quot_name);
        assert_eq!(q.kind, QuotKind::Type);
        assert_eq!(q.cnst.level_params.len(), 1);
      },
      _ => panic!("Expected QuotInfo"),
    }
  }

  #[test]
  fn test_roundtrip_theorem() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{ConstantVal, Env as LeanEnv, TheoremVal};

    // Create a theorem: theorem trivial : True := True.intro
    let name = Name::str(Name::anon(), "trivial".to_string());
    let prop = LeanExpr::sort(Level::zero()); // Prop

    // For simplicity, just use Prop as both type and value
    let thm = TheoremVal {
      cnst: ConstantVal {
        name: name.clone(),
        level_params: vec![],
        typ: prop.clone(),
      },
      value: prop,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::ThmInfo(thm.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::ThmInfo(t) => {
        assert_eq!(t.cnst.name, name);
        assert_eq!(t.all.len(), 1);
      },
      _ => panic!("Expected ThmInfo"),
    }
  }

  #[test]
  fn test_roundtrip_opaque() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{ConstantVal, Env as LeanEnv, OpaqueVal};

    // Create an opaque: opaque secret : Nat := 42
    let name = Name::str(Name::anon(), "secret".to_string());
    let nat_type = LeanExpr::sort(Level::zero()); // Using Prop as placeholder

    let opaq = OpaqueVal {
      cnst: ConstantVal {
        name: name.clone(),
        level_params: vec![],
        typ: nat_type.clone(),
      },
      value: nat_type,
      is_unsafe: false,
      all: vec![name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(name.clone(), LeanConstantInfo::OpaqueInfo(opaq.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&name).expect("name not found");
    match &*recovered {
      LeanConstantInfo::OpaqueInfo(o) => {
        assert_eq!(o.cnst.name, name);
        assert!(!o.is_unsafe);
        assert_eq!(o.all.len(), 1);
      },
      _ => panic!("Expected OpaqueInfo"),
    }
  }

  #[test]
  fn test_roundtrip_multiple_constants() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints, TheoremVal,
    };

    // Create multiple constants of different types
    let axiom_name = Name::str(Name::anon(), "A".to_string());
    let def_name = Name::str(Name::anon(), "B".to_string());
    let thm_name = Name::str(Name::anon(), "C".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let prop = LeanExpr::sort(Level::zero());

    let axiom = AxiomVal {
      cnst: ConstantVal {
        name: axiom_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      is_unsafe: false,
    };

    let def = DefinitionVal {
      cnst: ConstantVal {
        name: def_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      value: LeanExpr::cnst(axiom_name.clone(), vec![]),
      hints: ReducibilityHints::Regular(10),
      safety: DefinitionSafety::Safe,
      all: vec![def_name.clone()],
    };

    let thm = TheoremVal {
      cnst: ConstantVal {
        name: thm_name.clone(),
        level_params: vec![],
        typ: prop.clone(),
      },
      value: prop,
      all: vec![thm_name.clone()],
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(axiom_name.clone(), LeanConstantInfo::AxiomInfo(axiom));
    lean_env.insert(def_name.clone(), LeanConstantInfo::DefnInfo(def));
    lean_env.insert(thm_name.clone(), LeanConstantInfo::ThmInfo(thm));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");
    assert_eq!(stt.env.const_count(), 3);

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check all constants roundtrip
    assert!(matches!(
      &*dstt.env.get(&axiom_name).unwrap(),
      LeanConstantInfo::AxiomInfo(_)
    ));
    assert!(matches!(
      &*dstt.env.get(&def_name).unwrap(),
      LeanConstantInfo::DefnInfo(_)
    ));
    assert!(matches!(
      &*dstt.env.get(&thm_name).unwrap(),
      LeanConstantInfo::ThmInfo(_)
    ));
  }

  #[test]
  fn test_roundtrip_inductive_simple() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create a simple inductive: inductive Unit : Type where | unit : Unit
    // No recursor to keep it simple and self-contained
    let unit_name = Name::str(Name::anon(), "Unit".to_string());
    let unit_ctor_name = Name::str(unit_name.clone(), "unit".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type

    // Unit : Type
    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: unit_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![unit_name.clone()],
      ctors: vec![unit_ctor_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Unit.unit : Unit
    let ctor = ConstructorVal {
      cnst: ConstantVal {
        name: unit_ctor_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(unit_name.clone(), vec![]),
      },
      induct: unit_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(
      unit_name.clone(),
      LeanConstantInfo::InductInfo(inductive.clone()),
    );
    lean_env
      .insert(unit_ctor_name.clone(), LeanConstantInfo::CtorInfo(ctor.clone()));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip for inductive
    let recovered_ind = dstt.env.get(&unit_name).expect("Unit not found");
    match &*recovered_ind {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, unit_name);
        assert_eq!(i.ctors.len(), 1);
        assert_eq!(i.all.len(), 1);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check roundtrip for constructor
    let recovered_ctor =
      dstt.env.get(&unit_ctor_name).expect("Unit.unit not found");
    match &*recovered_ctor {
      LeanConstantInfo::CtorInfo(c) => {
        assert_eq!(c.cnst.name, unit_ctor_name);
        assert_eq!(c.induct, unit_name);
      },
      _ => panic!("Expected CtorInfo"),
    }
  }

  #[test]
  fn test_roundtrip_inductive_with_multiple_ctors() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create Bool with two constructors (no recursor to keep self-contained)
    let bool_name = Name::str(Name::anon(), "Bool".to_string());
    let false_name = Name::str(bool_name.clone(), "false".to_string());
    let true_name = Name::str(bool_name.clone(), "true".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let bool_type = LeanExpr::cnst(bool_name.clone(), vec![]);

    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: bool_name.clone(),
        level_params: vec![],
        typ: type0,
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![bool_name.clone()],
      ctors: vec![false_name.clone(), true_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    let ctor_false = ConstructorVal {
      cnst: ConstantVal {
        name: false_name.clone(),
        level_params: vec![],
        typ: bool_type.clone(),
      },
      induct: bool_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let ctor_true = ConstructorVal {
      cnst: ConstantVal {
        name: true_name.clone(),
        level_params: vec![],
        typ: bool_type.clone(),
      },
      induct: bool_name.clone(),
      cidx: Nat::from(1u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(bool_name.clone(), LeanConstantInfo::InductInfo(inductive));
    lean_env.insert(false_name.clone(), LeanConstantInfo::CtorInfo(ctor_false));
    lean_env.insert(true_name.clone(), LeanConstantInfo::CtorInfo(ctor_true));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check roundtrip
    let recovered = dstt.env.get(&bool_name).expect("Bool not found");
    match &*recovered {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, bool_name);
        assert_eq!(i.ctors.len(), 2);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check both constructors
    assert!(dstt.env.contains_key(&false_name));
    assert!(dstt.env.contains_key(&true_name));
  }

  #[test]
  fn test_roundtrip_mutual_definitions() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      ConstantVal, DefinitionSafety, DefinitionVal, Env as LeanEnv,
      ReducibilityHints,
    };

    // Create mutual definitions that only reference each other (self-contained)
    // def f : Type → Type and def g : Type → Type
    // where f references g and g references f
    let f_name = Name::str(Name::anon(), "f".to_string());
    let g_name = Name::str(Name::anon(), "g".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let fn_type = LeanExpr::all(
      Name::anon(),
      type0.clone(),
      type0.clone(),
      crate::ix::env::BinderInfo::Default,
    );

    // f := fun x => g x
    let f_value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type0.clone(),
      LeanExpr::app(
        LeanExpr::cnst(g_name.clone(), vec![]),
        LeanExpr::bvar(Nat::from(0u64)),
      ),
      crate::ix::env::BinderInfo::Default,
    );

    // g := fun x => f x
    let g_value = LeanExpr::lam(
      Name::str(Name::anon(), "x".to_string()),
      type0.clone(),
      LeanExpr::app(
        LeanExpr::cnst(f_name.clone(), vec![]),
        LeanExpr::bvar(Nat::from(0u64)),
      ),
      crate::ix::env::BinderInfo::Default,
    );

    // Mutual block: both reference each other
    let all = vec![f_name.clone(), g_name.clone()];

    let f_def = DefinitionVal {
      cnst: ConstantVal {
        name: f_name.clone(),
        level_params: vec![],
        typ: fn_type.clone(),
      },
      value: f_value,
      hints: ReducibilityHints::Regular(1),
      safety: DefinitionSafety::Safe,
      all: all.clone(),
    };

    let g_def = DefinitionVal {
      cnst: ConstantVal {
        name: g_name.clone(),
        level_params: vec![],
        typ: fn_type,
      },
      value: g_value,
      hints: ReducibilityHints::Regular(1),
      safety: DefinitionSafety::Safe,
      all: all.clone(),
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(f_name.clone(), LeanConstantInfo::DefnInfo(f_def));
    lean_env.insert(g_name.clone(), LeanConstantInfo::DefnInfo(g_def));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Should have a mutual block
    assert!(!stt.blocks.is_empty(), "Expected at least one mutual block");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check both definitions roundtrip
    let recovered_f = dstt.env.get(&f_name).expect("f not found");
    match &*recovered_f {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, f_name);
        // The all field should contain both names
        assert_eq!(d.all.len(), 2);
      },
      _ => panic!("Expected DefnInfo for f"),
    }

    let recovered_g = dstt.env.get(&g_name).expect("g not found");
    match &*recovered_g {
      LeanConstantInfo::DefnInfo(d) => {
        assert_eq!(d.cnst.name, g_name);
        assert_eq!(d.all.len(), 2);
      },
      _ => panic!("Expected DefnInfo for g"),
    }
  }

  #[test]
  fn test_roundtrip_mutual_inductives() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{
      ConstantVal, ConstructorVal, Env as LeanEnv, InductiveVal,
    };

    // Create two mutually recursive inductives (simplified):
    // inductive Even : Type where | zero : Even | succ : Odd → Even
    // inductive Odd : Type where | succ : Even → Odd
    let even_name = Name::str(Name::anon(), "Even".to_string());
    let odd_name = Name::str(Name::anon(), "Odd".to_string());
    let even_zero = Name::str(even_name.clone(), "zero".to_string());
    let even_succ = Name::str(even_name.clone(), "succ".to_string());
    let odd_succ = Name::str(odd_name.clone(), "succ".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let even_type = LeanExpr::cnst(even_name.clone(), vec![]);
    let odd_type = LeanExpr::cnst(odd_name.clone(), vec![]);

    let all = vec![even_name.clone(), odd_name.clone()];

    let even_ind = InductiveVal {
      cnst: ConstantVal {
        name: even_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: all.clone(),
      ctors: vec![even_zero.clone(), even_succ.clone()],
      num_nested: Nat::from(0u64),
      is_rec: true, // mutually recursive
      is_unsafe: false,
      is_reflexive: false,
    };

    let odd_ind = InductiveVal {
      cnst: ConstantVal {
        name: odd_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: all.clone(),
      ctors: vec![odd_succ.clone()],
      num_nested: Nat::from(0u64),
      is_rec: true,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Even.zero : Even
    let even_zero_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: even_zero.clone(),
        level_params: vec![],
        typ: even_type.clone(),
      },
      induct: even_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    // Even.succ : Odd → Even
    let even_succ_type = LeanExpr::all(
      Name::anon(),
      odd_type.clone(),
      even_type.clone(),
      crate::ix::env::BinderInfo::Default,
    );

    let even_succ_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: even_succ.clone(),
        level_params: vec![],
        typ: even_succ_type,
      },
      induct: even_name.clone(),
      cidx: Nat::from(1u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    };

    // Odd.succ : Even → Odd
    let odd_succ_type = LeanExpr::all(
      Name::anon(),
      even_type.clone(),
      odd_type.clone(),
      crate::ix::env::BinderInfo::Default,
    );

    let odd_succ_ctor = ConstructorVal {
      cnst: ConstantVal {
        name: odd_succ.clone(),
        level_params: vec![],
        typ: odd_succ_type,
      },
      induct: odd_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(1u64),
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env.insert(even_name.clone(), LeanConstantInfo::InductInfo(even_ind));
    lean_env.insert(odd_name.clone(), LeanConstantInfo::InductInfo(odd_ind));
    lean_env
      .insert(even_zero.clone(), LeanConstantInfo::CtorInfo(even_zero_ctor));
    lean_env
      .insert(even_succ.clone(), LeanConstantInfo::CtorInfo(even_succ_ctor));
    lean_env
      .insert(odd_succ.clone(), LeanConstantInfo::CtorInfo(odd_succ_ctor));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Should have at least one mutual block
    assert!(!stt.blocks.is_empty(), "Expected mutual block for Even/Odd");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check Even roundtrip
    let recovered_even = dstt.env.get(&even_name).expect("Even not found");
    match &*recovered_even {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, even_name);
        assert_eq!(i.ctors.len(), 2);
        assert_eq!(i.all.len(), 2); // Even and Odd in mutual block
      },
      _ => panic!("Expected InductInfo for Even"),
    }

    // Check Odd roundtrip
    let recovered_odd = dstt.env.get(&odd_name).expect("Odd not found");
    match &*recovered_odd {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, odd_name);
        assert_eq!(i.ctors.len(), 1);
        assert_eq!(i.all.len(), 2);
      },
      _ => panic!("Expected InductInfo for Odd"),
    }

    // Check all constructors exist
    assert!(dstt.env.contains_key(&even_zero));
    assert!(dstt.env.contains_key(&even_succ));
    assert!(dstt.env.contains_key(&odd_succ));
  }

  #[test]
  fn test_roundtrip_inductive_with_recursor() {
    use crate::ix::decompile::decompile_env;
    use crate::ix::env::{ConstantVal, InductiveVal, RecursorVal};

    // Create Empty type with recursor (no constructors)
    // inductive Empty : Type
    // Empty.rec.{u} : (motive : Empty → Sort u) → (e : Empty) → motive e
    let empty_name = Name::str(Name::anon(), "Empty".to_string());
    let empty_rec_name = Name::str(empty_name.clone(), "rec".to_string());
    let u = Name::str(Name::anon(), "u".to_string());

    let type0 = LeanExpr::sort(Level::succ(Level::zero())); // Type
    let empty_type = LeanExpr::cnst(empty_name.clone(), vec![]);

    let inductive = InductiveVal {
      cnst: ConstantVal {
        name: empty_name.clone(),
        level_params: vec![],
        typ: type0.clone(),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![empty_name.clone()],
      ctors: vec![], // No constructors!
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };

    // Empty.rec.{u} : (motive : Empty → Sort u) → (e : Empty) → motive e
    let motive_type = LeanExpr::all(
      Name::anon(),
      empty_type.clone(),
      LeanExpr::sort(Level::param(u.clone())),
      crate::ix::env::BinderInfo::Default,
    );
    let rec_type = LeanExpr::all(
      Name::str(Name::anon(), "motive".to_string()),
      motive_type,
      LeanExpr::all(
        Name::str(Name::anon(), "e".to_string()),
        empty_type.clone(),
        LeanExpr::app(
          LeanExpr::bvar(Nat::from(1u64)),
          LeanExpr::bvar(Nat::from(0u64)),
        ),
        crate::ix::env::BinderInfo::Default,
      ),
      crate::ix::env::BinderInfo::Implicit,
    );

    let recursor = RecursorVal {
      cnst: ConstantVal {
        name: empty_rec_name.clone(),
        level_params: vec![u.clone()],
        typ: rec_type,
      },
      all: vec![empty_name.clone()],
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      num_motives: Nat::from(1u64),
      num_minors: Nat::from(0u64), // No minor premises for Empty
      rules: vec![],               // No rules since no constructors
      k: true,
      is_unsafe: false,
    };

    let mut lean_env = LeanEnv::default();
    lean_env
      .insert(empty_name.clone(), LeanConstantInfo::InductInfo(inductive));
    lean_env
      .insert(empty_rec_name.clone(), LeanConstantInfo::RecInfo(recursor));
    let lean_env = Arc::new(lean_env);

    // Compile
    let stt = compile_env(&lean_env).expect("compile_env failed");

    // Decompile
    let dstt = decompile_env(&stt).expect("decompile_env failed");

    // Check inductive roundtrip
    let recovered_ind = dstt.env.get(&empty_name).expect("Empty not found");
    match &*recovered_ind {
      LeanConstantInfo::InductInfo(i) => {
        assert_eq!(i.cnst.name, empty_name);
        assert_eq!(i.ctors.len(), 0);
      },
      _ => panic!("Expected InductInfo"),
    }

    // Check recursor roundtrip
    let recovered_rec =
      dstt.env.get(&empty_rec_name).expect("Empty.rec not found");
    match &*recovered_rec {
      LeanConstantInfo::RecInfo(r) => {
        assert_eq!(r.cnst.name, empty_rec_name);
        assert_eq!(r.rules.len(), 0);
        assert_eq!(r.cnst.level_params.len(), 1);
      },
      _ => panic!("Expected RecInfo"),
    }
  }
}
