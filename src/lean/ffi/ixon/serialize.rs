//! Ixon serialization compatibility FFI.
//!
//! Contains FFI functions for comparing Lean and Rust serialization outputs.

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::ixon::constant::Constant as IxonConstant;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::serialize::put_expr;
use crate::ix::ixon::sharing::hash_expr;
use crate::ix::ixon::univ::{put_univ, Univ as IxonUniv};
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::{as_ref_unsafe, lean_ctor_get, lean_is_scalar, lean_obj_tag, lean_unbox_u64};

use super::constant::{decode_ixon_address, decode_ixon_constant};
use super::expr::decode_ixon_expr;
use super::univ::decode_ixon_univ;

// =============================================================================
// Old Ixon format FFI (for backward compatibility)
// =============================================================================

use crate::ix::address::Address;
use crate::ix::env::{BinderInfo, DefinitionSafety, QuotKind, ReducibilityHints};
use crate::ix::ixon_old::{
  Axiom, BuiltIn, CheckClaim, Claim, Comm, Constructor, ConstructorProj, DataValue, DefKind,
  Definition, DefinitionProj, Env, EvalClaim, Inductive, InductiveProj, Ixon, Metadata, Metadatum,
  MutConst, Proof, Quotient, Recursor, RecursorProj, RecursorRule, Serialize as SerializeOld,
};
use crate::lean::array::LeanArrayObject;
use crate::lean::ctor::LeanCtorObject;
use crate::lean::nat::Nat;
use crate::lean::collect_list;
use crate::lean_unbox;

fn lean_ptr_to_address(ptr: *const c_void) -> Address {
  let sarray: &LeanSArrayObject = as_ref_unsafe(ptr.cast());
  Address::from_slice(sarray.data()).unwrap()
}

fn lean_ptr_to_definition(ptr: *const c_void) -> Definition {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, typ, value, mode_safety] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let value = lean_ptr_to_address(value);
  let [kind, safety, ..] = (mode_safety as usize).to_le_bytes();
  let kind = match kind {
    0 => DefKind::Definition,
    1 => DefKind::Opaque,
    2 => DefKind::Theorem,
    _ => unreachable!(),
  };
  let safety = match safety {
    0 => DefinitionSafety::Unsafe,
    1 => DefinitionSafety::Safe,
    2 => DefinitionSafety::Partial,
    _ => unreachable!(),
  };
  Definition { lvls, typ, kind, value, safety }
}

fn lean_ptr_to_constructor(ptr: *const c_void) -> Constructor {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, cidx, params, fields, typ, is_unsafe] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let cidx = Nat::from_ptr(cidx);
  let params = Nat::from_ptr(params);
  let fields = Nat::from_ptr(fields);
  let is_unsafe = is_unsafe as usize == 1;
  Constructor { lvls, typ, cidx, params, fields, is_unsafe }
}

fn lean_ptr_to_recursor_rule(ptr: *const c_void) -> RecursorRule {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [fields, rhs] = ctor.objs();
  let fields = Nat::from_ptr(fields);
  let rhs = lean_ptr_to_address(rhs);
  RecursorRule { fields, rhs }
}

fn lean_ptr_to_recursor(ptr: *const c_void) -> Recursor {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, params, indices, motives, minors, typ, rules, k_isunsafe] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let params = Nat::from_ptr(params);
  let indices = Nat::from_ptr(indices);
  let motives = Nat::from_ptr(motives);
  let minors = Nat::from_ptr(minors);
  let rules = collect_list(rules, lean_ptr_to_recursor_rule);
  let [k, is_unsafe, ..] = (k_isunsafe as usize).to_le_bytes();
  let k = k == 1;
  let is_unsafe = is_unsafe == 1;
  Recursor { lvls, typ, params, indices, motives, minors, rules, k, is_unsafe }
}

fn lean_ptr_to_axiom(ptr: *const c_void) -> Axiom {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, typ, is_unsafe] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let is_unsafe = is_unsafe as usize == 1;
  Axiom { is_unsafe, lvls, typ }
}

fn lean_ptr_to_quotient(ptr: *const c_void) -> Quotient {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, typ, kind] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let kind = match kind as usize {
    0 => QuotKind::Type,
    1 => QuotKind::Ctor,
    2 => QuotKind::Lift,
    3 => QuotKind::Ind,
    _ => unreachable!(),
  };
  Quotient { kind, lvls, typ }
}

fn lean_ptr_to_constructor_proj(ptr: *const c_void) -> ConstructorProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [idx, cidx, block] = ctor.objs();
  let [idx, cidx] = [idx, cidx].map(Nat::from_ptr);
  let block = lean_ptr_to_address(block);
  ConstructorProj { idx, cidx, block }
}

fn lean_ptr_to_recursor_proj(ptr: *const c_void) -> RecursorProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [idx, block] = ctor.objs();
  let idx = Nat::from_ptr(idx);
  let block = lean_ptr_to_address(block);
  RecursorProj { idx, block }
}

fn lean_ptr_to_inductive_proj(ptr: *const c_void) -> InductiveProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [idx, block] = ctor.objs();
  let idx = Nat::from_ptr(idx);
  let block = lean_ptr_to_address(block);
  InductiveProj { idx, block }
}

fn lean_ptr_to_definition_proj(ptr: *const c_void) -> DefinitionProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [idx, block] = ctor.objs();
  let idx = Nat::from_ptr(idx);
  let block = lean_ptr_to_address(block);
  DefinitionProj { idx, block }
}

fn lean_ptr_to_inductive(ptr: *const c_void) -> Inductive {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, params, indices, nested, typ, ctors, recr_refl_isunsafe] = ctor.objs();
  let lvls = Nat::from_ptr(lvls);
  let typ = lean_ptr_to_address(typ);
  let params = Nat::from_ptr(params);
  let indices = Nat::from_ptr(indices);
  let ctors = collect_list(ctors, lean_ptr_to_constructor);
  let nested = Nat::from_ptr(nested);
  let [recr, refl, is_unsafe, ..] = (recr_refl_isunsafe as usize).to_le_bytes();
  let recr = recr == 1;
  let refl = refl == 1;
  let is_unsafe = is_unsafe == 1;
  Inductive { lvls, typ, params, indices, ctors, nested, recr, refl, is_unsafe }
}

fn lean_ptr_to_mut_const(ptr: *const c_void) -> MutConst {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner] = ctor.objs();
  match ctor.tag() {
    0 => MutConst::Defn(lean_ptr_to_definition(inner)),
    1 => MutConst::Indc(lean_ptr_to_inductive(inner)),
    2 => MutConst::Recr(lean_ptr_to_recursor(inner)),
    _ => unreachable!(),
  }
}

fn lean_ptr_to_eval_claim(ptr: *const c_void) -> EvalClaim {
  let evals: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, typ, input, output] = evals.objs().map(lean_ptr_to_address);
  EvalClaim { lvls, typ, input, output }
}

fn lean_ptr_to_check_claim(ptr: *const c_void) -> CheckClaim {
  let checks: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [lvls, typ, value] = checks.objs().map(lean_ptr_to_address);
  CheckClaim { lvls, typ, value }
}

fn lean_ptr_to_proof(ptr: *const c_void) -> Proof {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [claim_ptr, proof_ptr] = ctor.objs();
  let claim_ctor: &LeanCtorObject = as_ref_unsafe(claim_ptr.cast());
  let [claim_inner] = claim_ctor.objs();
  let claim = match claim_ctor.tag() {
    0 => Claim::Evals(lean_ptr_to_eval_claim(claim_inner)),
    1 => Claim::Checks(lean_ptr_to_check_claim(claim_inner)),
    _ => unreachable!(),
  };
  let proof_sarray: &LeanSArrayObject = as_ref_unsafe(proof_ptr.cast());
  let proof = proof_sarray.data().to_vec();
  Proof { claim, proof }
}

fn lean_ptr_to_comm(ptr: *const c_void) -> Comm {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [secret, payload] = ctor.objs().map(lean_ptr_to_address);
  Comm { secret, payload }
}

fn lean_ptr_to_address_pair(ptr: *const c_void) -> (Address, Address) {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [fst, snd] = ctor.objs().map(lean_ptr_to_address);
  (fst, snd)
}

fn lean_ptr_to_meta_address(ptr: *const c_void) -> crate::ix::address::MetaAddress {
  let (data, meta) = lean_ptr_to_address_pair(ptr);
  crate::ix::address::MetaAddress { data, meta }
}

fn lean_ptr_to_env(ptr: *const c_void) -> Env {
  let env = collect_list(ptr, lean_ptr_to_meta_address);
  Env { env }
}

fn lean_ptr_to_builtin(ptr: *const c_void) -> BuiltIn {
  assert!(lean_is_scalar(ptr));
  match lean_unbox!(u8, ptr) {
    0 => BuiltIn::Obj,
    1 => BuiltIn::Neutral,
    2 => BuiltIn::Unreachable,
    _ => unreachable!(),
  }
}

fn lean_ptr_to_data_value(ptr: *const c_void) -> DataValue {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner_ptr] = ctor.objs();
  match ctor.tag() {
    0 => DataValue::OfString(lean_ptr_to_address(inner_ptr)),
    1 => DataValue::OfBool(inner_ptr as usize == 1),
    2 => DataValue::OfName(lean_ptr_to_address(inner_ptr)),
    3 => DataValue::OfNat(lean_ptr_to_address(inner_ptr)),
    4 => DataValue::OfInt(lean_ptr_to_address(inner_ptr)),
    5 => DataValue::OfSyntax(lean_ptr_to_address(inner_ptr)),
    _ => unreachable!(),
  }
}

fn lean_ptr_to_address_data_value_pair(ptr: *const c_void) -> (Address, DataValue) {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [address, data_value] = ctor.objs();
  let address = lean_ptr_to_address(address);
  let data_value = lean_ptr_to_data_value(data_value);
  (address, data_value)
}

fn lean_ptr_to_metadatum(ptr: *const c_void) -> Metadatum {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let [addr] = ctor.objs();
      let addr = lean_ptr_to_address(addr);
      Metadatum::Link(addr)
    }
    1 => {
      let [info] = ctor.objs();
      let info = match info as usize {
        0 => BinderInfo::Default,
        1 => BinderInfo::Implicit,
        2 => BinderInfo::StrictImplicit,
        3 => BinderInfo::InstImplicit,
        _ => unreachable!(),
      };
      Metadatum::Info(info)
    }
    2 => {
      let [hints] = ctor.objs();
      let hints = if lean_is_scalar(hints) {
        match lean_unbox!(usize, hints) {
          0 => ReducibilityHints::Opaque,
          1 => ReducibilityHints::Abbrev,
          _ => unreachable!(),
        }
      } else {
        let ctor: &LeanCtorObject = as_ref_unsafe(hints.cast());
        let [height] = ctor.objs();
        ReducibilityHints::Regular(height as u32)
      };
      Metadatum::Hints(hints)
    }
    3 => {
      let [links] = ctor.objs();
      let links = collect_list(links, lean_ptr_to_address);
      Metadatum::Links(links)
    }
    4 => {
      let [pairs] = ctor.objs();
      let pairs = collect_list(pairs, lean_ptr_to_address_pair);
      Metadatum::Map(pairs)
    }
    5 => {
      let [kvmap] = ctor.objs();
      let kvmap = collect_list(kvmap, lean_ptr_to_address_data_value_pair);
      Metadatum::KVMap(kvmap)
    }
    6 => {
      let [muts] = ctor.objs();
      let muts = collect_list(muts, |ptr| collect_list(ptr, lean_ptr_to_address));
      Metadatum::Muts(muts)
    }
    _ => unreachable!(),
  }
}

fn lean_ptr_to_metadata(ptr: *const c_void) -> Metadata {
  let nodes = collect_list(ptr, lean_ptr_to_metadatum);
  Metadata { nodes }
}

fn lean_ptr_to_ixon(ptr: *const c_void) -> Ixon {
  if lean_is_scalar(ptr) {
    return match lean_unbox!(u8, ptr) {
      0 => Ixon::NAnon,
      3 => Ixon::UZero,
      _ => unreachable!(),
    };
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    1 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::NStr(a, b)
    }
    2 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::NNum(a, b)
    }
    4 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::USucc(a)
    }
    5 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::UMax(a, b)
    }
    6 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::UIMax(a, b)
    }
    7 => {
      let [a] = ctor.objs().map(Nat::from_ptr);
      Ixon::UVar(a)
    }
    8 => {
      let [a] = ctor.objs().map(Nat::from_ptr);
      Ixon::EVar(a)
    }
    9 => {
      let [a_ptr, bs_ptr] = ctor.objs();
      let a = lean_ptr_to_address(a_ptr);
      let bs = collect_list(bs_ptr, lean_ptr_to_address);
      Ixon::ERef(a, bs)
    }
    10 => {
      let [a_ptr, bs_ptr] = ctor.objs();
      let a = Nat::from_ptr(a_ptr);
      let bs = collect_list(bs_ptr, lean_ptr_to_address);
      Ixon::ERec(a, bs)
    }
    11 => {
      let [a_ptr, b_ptr, c_ptr] = ctor.objs();
      let a = lean_ptr_to_address(a_ptr);
      let b = Nat::from_ptr(b_ptr);
      let c = lean_ptr_to_address(c_ptr);
      Ixon::EPrj(a, b, c)
    }
    12 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ESort(a)
    }
    13 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EStr(a)
    }
    14 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ENat(a)
    }
    15 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EApp(a, b)
    }
    16 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ELam(a, b)
    }
    17 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EAll(a, b)
    }
    18 => {
      let [a_ptr, b_ptr, c_ptr, bool_ptr] = ctor.objs();
      let [a, b, c] = [a_ptr, b_ptr, c_ptr].map(lean_ptr_to_address);
      let bool = bool_ptr as usize == 1;
      Ixon::ELet(bool, a, b, c)
    }
    19 => {
      let [a_ptr] = ctor.objs();
      let sarray: &LeanSArrayObject = as_ref_unsafe(a_ptr.cast());
      Ixon::Blob(sarray.data().to_vec())
    }
    20 => {
      let [a] = ctor.objs().map(lean_ptr_to_definition);
      Ixon::Defn(a)
    }
    21 => {
      let [a] = ctor.objs().map(lean_ptr_to_recursor);
      Ixon::Recr(a)
    }
    22 => {
      let [a] = ctor.objs().map(lean_ptr_to_axiom);
      Ixon::Axio(a)
    }
    23 => {
      let [a] = ctor.objs().map(lean_ptr_to_quotient);
      Ixon::Quot(a)
    }
    24 => {
      let [a] = ctor.objs().map(lean_ptr_to_constructor_proj);
      Ixon::CPrj(a)
    }
    25 => {
      let [a] = ctor.objs().map(lean_ptr_to_recursor_proj);
      Ixon::RPrj(a)
    }
    26 => {
      let [a] = ctor.objs().map(lean_ptr_to_inductive_proj);
      Ixon::IPrj(a)
    }
    27 => {
      let [a] = ctor.objs().map(lean_ptr_to_definition_proj);
      Ixon::DPrj(a)
    }
    28 => {
      let [a] = ctor.objs();
      Ixon::Muts(collect_list(a, lean_ptr_to_mut_const))
    }
    29 => {
      let [a] = ctor.objs().map(lean_ptr_to_proof);
      Ixon::Prof(a)
    }
    30 => {
      let [a] = ctor.objs().map(lean_ptr_to_eval_claim);
      Ixon::Eval(a)
    }
    31 => {
      let [a] = ctor.objs().map(lean_ptr_to_check_claim);
      Ixon::Chck(a)
    }
    32 => {
      let [a] = ctor.objs().map(lean_ptr_to_comm);
      Ixon::Comm(a)
    }
    33 => {
      let [a] = ctor.objs().map(lean_ptr_to_env);
      Ixon::Envn(a)
    }
    34 => {
      let [a] = ctor.objs().map(lean_ptr_to_builtin);
      Ixon::Prim(a)
    }
    35 => {
      let [a] = ctor.objs().map(lean_ptr_to_metadata);
      Ixon::Meta(a)
    }
    _ => unreachable!(),
  }
}

// =============================================================================
// FFI Exports - Old format
// =============================================================================

/// Check if Lean's old Ixon serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_lean_rust_serialization(
  ixon_ptr: *const c_void,
  bytes: &LeanSArrayObject,
) -> bool {
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  lean_ptr_to_ixon(ixon_ptr).put(&mut buf);
  buf == bytes_data
}

// =============================================================================
// New Ixon.Expr FFI (for sharing hash compatibility testing)
// =============================================================================

/// Unbox a Lean UInt64, handling both scalar and boxed representations.
fn lean_ptr_to_u64(ptr: *const c_void) -> u64 {
  if lean_is_scalar(ptr) {
    (ptr as usize >> 1) as u64
  } else {
    lean_unbox_u64(ptr)
  }
}

/// Decode a Lean `Ixon.Expr` to a Rust `IxonExpr`.
pub fn lean_ptr_to_ixon_expr(ptr: *const c_void) -> Arc<IxonExpr> {
  if lean_is_scalar(ptr) {
    panic!("Ixon.Expr should not be scalar");
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Sort(idx))
    }
    1 => {
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Var(idx))
    }
    2 => {
      let [univs_ptr] = ctor.objs();
      let ref_idx = ctor.get_scalar_u64(1, 0);
      let univs_arr: &LeanArrayObject = as_ref_unsafe(univs_ptr.cast());
      let univs = univs_arr.to_vec(lean_ptr_to_u64);
      Arc::new(IxonExpr::Ref(ref_idx, univs))
    }
    3 => {
      let [univs_ptr] = ctor.objs();
      let rec_idx = ctor.get_scalar_u64(1, 0);
      let univs_arr: &LeanArrayObject = as_ref_unsafe(univs_ptr.cast());
      let univs = univs_arr.to_vec(lean_ptr_to_u64);
      Arc::new(IxonExpr::Rec(rec_idx, univs))
    }
    4 => {
      let [val_ptr] = ctor.objs();
      let type_idx = ctor.get_scalar_u64(1, 0);
      let field_idx = ctor.get_scalar_u64(1, 8);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      Arc::new(IxonExpr::Prj(type_idx, field_idx, val))
    }
    5 => {
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Str(idx))
    }
    6 => {
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Nat(idx))
    }
    7 => {
      let [fun_ptr, arg_ptr] = ctor.objs();
      let fun_ = lean_ptr_to_ixon_expr(fun_ptr);
      let arg = lean_ptr_to_ixon_expr(arg_ptr);
      Arc::new(IxonExpr::App(fun_, arg))
    }
    8 => {
      let [ty_ptr, body_ptr] = ctor.objs();
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Lam(ty, body))
    }
    9 => {
      let [ty_ptr, body_ptr] = ctor.objs();
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::All(ty, body))
    }
    10 => {
      let [ty_ptr, val_ptr, body_ptr] = ctor.objs();
      let base_ptr = ctor as *const _ as *const u8;
      let non_dep = unsafe { *base_ptr.add(8 + 3 * 8) } != 0;
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Let(non_dep, ty, val, body))
    }
    11 => {
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Share(idx))
    }
    tag => panic!("Unknown Ixon.Expr tag: {}", tag),
  }
}

/// Check if Lean's computed hash matches Rust's computed hash.
#[unsafe(no_mangle)]
pub extern "C" fn rs_expr_hash_matches(expr_ptr: *const c_void, expected_hash: *const c_void) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let hash = hash_expr(&expr);
  let expected = decode_ixon_address(expected_hash);
  Address::from_slice(hash.as_bytes()).map_or(false, |h| h == expected)
}

/// Decode a Lean `Ixon.Univ` to a Rust `IxonUniv`.
fn lean_ptr_to_ixon_univ(ptr: *const c_void) -> Arc<IxonUniv> {
  if lean_is_scalar(ptr) {
    return IxonUniv::zero();
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    1 => {
      let [inner] = ctor.objs();
      IxonUniv::succ(lean_ptr_to_ixon_univ(inner))
    }
    2 => {
      let [a, b] = ctor.objs();
      IxonUniv::max(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    }
    3 => {
      let [a, b] = ctor.objs();
      IxonUniv::imax(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    }
    4 => IxonUniv::var(ctor.get_scalar_u64(0, 0)),
    tag => panic!("Unknown Ixon.Univ tag: {}", tag),
  }
}

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_univ_serialization(univ_ptr: *const c_void, bytes: &LeanSArrayObject) -> bool {
  let univ = lean_ptr_to_ixon_univ(univ_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_univ(&univ, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Expr serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_expr_serialization(expr_ptr: *const c_void, bytes: &LeanSArrayObject) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_expr(&expr, &mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Constant serialization matches Rust.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_constant_serialization(constant_ptr: *const c_void, bytes: &LeanSArrayObject) -> bool {
  let constant = decode_ixon_constant(constant_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

/// Check if Lean's Ixon.Env serialization can be deserialized by Rust and content matches.
/// Due to HashMap ordering differences, we compare deserialized content rather than bytes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_eq_env_serialization(raw_env_ptr: *const c_void, bytes: &LeanSArrayObject) -> bool {
  use super::env::decode_raw_env;
  use crate::ix::ixon::env::Env;

  let decoded = decode_raw_env(raw_env_ptr);
  let bytes_data = bytes.data();

  // Deserialize Lean's bytes using Rust's deserializer
  let rust_env = match Env::get(&mut &bytes_data[..]) {
    Ok(env) => env,
    Err(_) => return false,
  };

  // Compare content: check that all items from decoded RawEnv are in the deserialized Env
  // Consts
  if rust_env.consts.len() != decoded.consts.len() {
    return false;
  }
  for rc in &decoded.consts {
    match rust_env.consts.get(&rc.addr) {
      Some(c) if *c == rc.constant => {}
      _ => return false,
    }
  }

  // Blobs
  if rust_env.blobs.len() != decoded.blobs.len() {
    return false;
  }
  for rb in &decoded.blobs {
    match rust_env.blobs.get(&rb.addr) {
      Some(b) if *b == rb.bytes => {}
      _ => return false,
    }
  }

  // Comms
  if rust_env.comms.len() != decoded.comms.len() {
    return false;
  }
  for rc in &decoded.comms {
    let expected_comm = crate::ix::ixon::comm::Comm {
      secret: rc.comm.secret.clone(),
      payload: rc.comm.payload.clone(),
    };
    match rust_env.comms.get(&rc.addr) {
      Some(c) if *c == expected_comm => {}
      _ => return false,
    }
  }

  // Named: compare by checking all entries exist with matching addresses
  if rust_env.named.len() != decoded.named.len() {
    return false;
  }
  for rn in &decoded.named {
    match rust_env.named.get(&rn.name) {
      Some(named) if named.addr == rn.addr => {}
      _ => return false,
    }
  }

  true
}
