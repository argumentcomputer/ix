use std::ffi::c_void;
use std::sync::Arc;

use crate::{
  ix::address::{Address, MetaAddress},
  ix::env::{BinderInfo, DefinitionSafety, QuotKind, ReducibilityHints},
  ix::ixon::expr::Expr as IxonExpr,
  ix::ixon::sharing::hash_expr,
  ix::ixon_old::{
    Axiom, BuiltIn, CheckClaim, Claim, Comm, Constructor, ConstructorProj,
    DataValue, DefKind, Definition, DefinitionProj, Env, EvalClaim, Inductive,
    InductiveProj, Ixon, Metadata, Metadatum, MutConst, Proof, Quotient,
    Recursor, RecursorProj, RecursorRule, Serialize,
  },
  lean::{
    array::LeanArrayObject, as_ref_unsafe, collect_list, ctor::LeanCtorObject,
    lean_is_scalar, lean_unbox_u64, nat::Nat, sarray::LeanSArrayObject,
  },
  lean_unbox,
};

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
  let [lvls, params, indices, motives, minors, typ, rules, k_isunsafe] =
    ctor.objs();
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
  let [lvls, params, indices, nested, typ, ctors, recr_refl_isunsafe] =
    ctor.objs();
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

fn lean_ptr_to_meta_address(ptr: *const c_void) -> MetaAddress {
  let (data, meta) = lean_ptr_to_address_pair(ptr);
  MetaAddress { data, meta }
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

fn lean_ptr_to_address_data_value_pair(
  ptr: *const c_void,
) -> (Address, DataValue) {
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
    },
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
    },
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
    },
    3 => {
      let [links] = ctor.objs();
      let links = collect_list(links, lean_ptr_to_address);
      Metadatum::Links(links)
    },
    4 => {
      let [pairs] = ctor.objs();
      let pairs = collect_list(pairs, lean_ptr_to_address_pair);
      Metadatum::Map(pairs)
    },
    5 => {
      let [kvmap] = ctor.objs();
      let kvmap = collect_list(kvmap, lean_ptr_to_address_data_value_pair);
      Metadatum::KVMap(kvmap)
    },
    6 => {
      let [muts] = ctor.objs();
      let muts =
        collect_list(muts, |ptr| collect_list(ptr, lean_ptr_to_address));
      Metadatum::Muts(muts)
    },
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
    },
    2 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::NNum(a, b)
    },
    4 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::USucc(a)
    },
    5 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::UMax(a, b)
    },
    6 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::UIMax(a, b)
    },
    7 => {
      let [a] = ctor.objs().map(Nat::from_ptr);
      Ixon::UVar(a)
    },
    8 => {
      let [a] = ctor.objs().map(Nat::from_ptr);
      Ixon::EVar(a)
    },
    9 => {
      let [a_ptr, bs_ptr] = ctor.objs();
      let a = lean_ptr_to_address(a_ptr);
      let bs = collect_list(bs_ptr, lean_ptr_to_address);
      Ixon::ERef(a, bs)
    },
    10 => {
      let [a_ptr, bs_ptr] = ctor.objs();
      let a = Nat::from_ptr(a_ptr);
      let bs = collect_list(bs_ptr, lean_ptr_to_address);
      Ixon::ERec(a, bs)
    },
    11 => {
      let [a_ptr, b_ptr, c_ptr] = ctor.objs();
      let a = lean_ptr_to_address(a_ptr);
      let b = Nat::from_ptr(b_ptr);
      let c = lean_ptr_to_address(c_ptr);
      Ixon::EPrj(a, b, c)
    },
    12 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ESort(a)
    },
    13 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EStr(a)
    },
    14 => {
      let [a] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ENat(a)
    },
    15 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EApp(a, b)
    },
    16 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::ELam(a, b)
    },
    17 => {
      let [a, b] = ctor.objs().map(lean_ptr_to_address);
      Ixon::EAll(a, b)
    },
    18 => {
      let [a_ptr, b_ptr, c_ptr, bool_ptr] = ctor.objs();
      let [a, b, c] = [a_ptr, b_ptr, c_ptr].map(lean_ptr_to_address);
      let bool = bool_ptr as usize == 1;
      Ixon::ELet(bool, a, b, c)
    },
    19 => {
      let [a_ptr] = ctor.objs();
      let sarray: &LeanSArrayObject = as_ref_unsafe(a_ptr.cast());
      Ixon::Blob(sarray.data().to_vec())
    },
    20 => {
      let [a] = ctor.objs().map(lean_ptr_to_definition);
      Ixon::Defn(a)
    },
    21 => {
      let [a] = ctor.objs().map(lean_ptr_to_recursor);
      Ixon::Recr(a)
    },
    22 => {
      let [a] = ctor.objs().map(lean_ptr_to_axiom);
      Ixon::Axio(a)
    },
    23 => {
      let [a] = ctor.objs().map(lean_ptr_to_quotient);
      Ixon::Quot(a)
    },
    24 => {
      let [a] = ctor.objs().map(lean_ptr_to_constructor_proj);
      Ixon::CPrj(a)
    },
    25 => {
      let [a] = ctor.objs().map(lean_ptr_to_recursor_proj);
      Ixon::RPrj(a)
    },
    26 => {
      let [a] = ctor.objs().map(lean_ptr_to_inductive_proj);
      Ixon::IPrj(a)
    },
    27 => {
      let [a] = ctor.objs().map(lean_ptr_to_definition_proj);
      Ixon::DPrj(a)
    },
    28 => {
      let [a] = ctor.objs();
      Ixon::Muts(collect_list(a, lean_ptr_to_mut_const))
    },
    29 => {
      let [a] = ctor.objs().map(lean_ptr_to_proof);
      Ixon::Prof(a)
    },
    30 => {
      let [a] = ctor.objs().map(lean_ptr_to_eval_claim);
      Ixon::Eval(a)
    },
    31 => {
      let [a] = ctor.objs().map(lean_ptr_to_check_claim);
      Ixon::Chck(a)
    },
    32 => {
      let [a] = ctor.objs().map(lean_ptr_to_comm);
      Ixon::Comm(a)
    },
    33 => {
      let [a] = ctor.objs().map(lean_ptr_to_env);
      Ixon::Envn(a)
    },
    34 => {
      let [a] = ctor.objs().map(lean_ptr_to_builtin);
      Ixon::Prim(a)
    },
    35 => {
      let [a] = ctor.objs().map(lean_ptr_to_metadata);
      Ixon::Meta(a)
    },
    _ => unreachable!(),
  }
}

#[unsafe(no_mangle)]
extern "C" fn rs_eq_lean_rust_serialization(
  ixon_ptr: *const c_void,
  bytes: &LeanSArrayObject,
) -> bool {
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  lean_ptr_to_ixon(ixon_ptr).put(&mut buf);
  buf == bytes_data
}

// ============================================================================
// New Ixon.Expr FFI (for sharing hash compatibility testing)
// ============================================================================

/// Unbox a Lean UInt64, handling both scalar and boxed representations.
fn lean_ptr_to_u64(ptr: *const c_void) -> u64 {
  if lean_is_scalar(ptr) {
    // Small values stored as tagged pointers
    (ptr as usize >> 1) as u64
  } else {
    // Boxed values
    lean_unbox_u64(ptr)
  }
}

/// Decode a Lean `Ixon.Expr` to a Rust `IxonExpr`.
/// Lean ABI: object fields come first (in decl order), then scalar fields.
/// UInt64 is scalar (8 bytes), Bool is scalar (1 byte), Expr/Array are objects.
fn lean_ptr_to_ixon_expr(ptr: *const c_void) -> Arc<IxonExpr> {
  if lean_is_scalar(ptr) {
    panic!("Ixon.Expr should not be scalar");
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    0 => {
      // sort : UInt64 → Expr (0 obj, 1 scalar)
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Sort(idx))
    },
    1 => {
      // var : UInt64 → Expr (0 obj, 1 scalar)
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Var(idx))
    },
    2 => {
      // ref : UInt64 → Array UInt64 → Expr (1 obj: Array, 1 scalar: UInt64)
      let [univs_ptr] = ctor.objs();
      let ref_idx = ctor.get_scalar_u64(1, 0);
      let univs_arr: &LeanArrayObject = as_ref_unsafe(univs_ptr.cast());
      let univs = univs_arr.to_vec(lean_ptr_to_u64);
      Arc::new(IxonExpr::Ref(ref_idx, univs))
    },
    3 => {
      // recur : UInt64 → Array UInt64 → Expr (1 obj: Array, 1 scalar: UInt64)
      let [univs_ptr] = ctor.objs();
      let rec_idx = ctor.get_scalar_u64(1, 0);
      let univs_arr: &LeanArrayObject = as_ref_unsafe(univs_ptr.cast());
      let univs = univs_arr.to_vec(lean_ptr_to_u64);
      Arc::new(IxonExpr::Rec(rec_idx, univs))
    },
    4 => {
      // prj : UInt64 → UInt64 → Expr → Expr (1 obj: Expr, 2 scalars: UInt64, UInt64)
      let [val_ptr] = ctor.objs();
      let type_idx = ctor.get_scalar_u64(1, 0);
      let field_idx = ctor.get_scalar_u64(1, 8);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      Arc::new(IxonExpr::Prj(type_idx, field_idx, val))
    },
    5 => {
      // str : UInt64 → Expr (0 obj, 1 scalar)
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Str(idx))
    },
    6 => {
      // nat : UInt64 → Expr (0 obj, 1 scalar)
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Nat(idx))
    },
    7 => {
      // app : Expr → Expr → Expr (2 obj)
      let [fun_ptr, arg_ptr] = ctor.objs();
      let fun_ = lean_ptr_to_ixon_expr(fun_ptr);
      let arg = lean_ptr_to_ixon_expr(arg_ptr);
      Arc::new(IxonExpr::App(fun_, arg))
    },
    8 => {
      // lam : Expr → Expr → Expr (2 obj)
      let [ty_ptr, body_ptr] = ctor.objs();
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Lam(ty, body))
    },
    9 => {
      // all : Expr → Expr → Expr (2 obj)
      let [ty_ptr, body_ptr] = ctor.objs();
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::All(ty, body))
    },
    10 => {
      // letE : Bool → Expr → Expr → Expr → Expr (3 obj: Expr, Expr, Expr; 1 scalar: Bool)
      let [ty_ptr, val_ptr, body_ptr] = ctor.objs();
      // Bool is stored as u8 in scalar area
      let base_ptr = ctor as *const _ as *const u8;
      let non_dep = unsafe { *base_ptr.add(8 + 3 * 8) } != 0;
      let ty = lean_ptr_to_ixon_expr(ty_ptr);
      let val = lean_ptr_to_ixon_expr(val_ptr);
      let body = lean_ptr_to_ixon_expr(body_ptr);
      Arc::new(IxonExpr::Let(non_dep, ty, val, body))
    },
    11 => {
      // share : UInt64 → Expr (0 obj, 1 scalar)
      let idx = ctor.get_scalar_u64(0, 0);
      Arc::new(IxonExpr::Share(idx))
    },
    tag => panic!("Unknown Ixon.Expr tag: {}", tag),
  }
}

/// Check if Lean's computed hash matches Rust's computed hash.
/// Takes the Expr and the expected hash (as Address), returns bool.
#[unsafe(no_mangle)]
extern "C" fn rs_expr_hash_matches(
  expr_ptr: *const c_void,
  expected_hash: *const c_void,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let hash = hash_expr(&expr);
  let expected = lean_ptr_to_address(expected_hash);
  Address::from_slice(hash.as_bytes()).map_or(false, |h| h == expected)
}

// ============================================================================
// New Ixon.Univ FFI (for serialization and hash compatibility testing)
// ============================================================================

use crate::ix::ixon::univ::{Univ as IxonUniv, put_univ};

/// Decode a Lean `Ixon.Univ` to a Rust `IxonUniv`.
/// Lean ABI: scalar ctors have no fields or only scalar fields that fit in pointer.
/// Univ: zero (0 fields) is scalar; succ/max/imax/var are boxed.
/// Tags match constructor indices: zero=0, succ=1, max=2, imax=3, var=4
fn lean_ptr_to_ixon_univ(ptr: *const c_void) -> Arc<IxonUniv> {
  if lean_is_scalar(ptr) {
    // Only zero is scalar (no fields)
    return IxonUniv::zero();
  }
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  match ctor.tag() {
    1 => {
      // succ : Univ → Univ
      let [inner] = ctor.objs();
      IxonUniv::succ(lean_ptr_to_ixon_univ(inner))
    },
    2 => {
      // max : Univ → Univ → Univ
      let [a, b] = ctor.objs();
      IxonUniv::max(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    3 => {
      // imax : Univ → Univ → Univ
      let [a, b] = ctor.objs();
      IxonUniv::imax(lean_ptr_to_ixon_univ(a), lean_ptr_to_ixon_univ(b))
    },
    4 => {
      // var : UInt64 → Univ (0 obj, 1 scalar)
      IxonUniv::var(ctor.get_scalar_u64(0, 0))
    },
    tag => panic!("Unknown Ixon.Univ tag: {}", tag),
  }
}

/// Check if Lean's Ixon.Univ serialization matches Rust.
#[unsafe(no_mangle)]
extern "C" fn rs_eq_univ_serialization(
  univ_ptr: *const c_void,
  bytes: &LeanSArrayObject,
) -> bool {
  let univ = lean_ptr_to_ixon_univ(univ_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_univ(&univ, &mut buf);
  buf == bytes_data
}

// ============================================================================
// New Ixon.Expr serialization FFI
// ============================================================================

use crate::ix::ixon::serialize::put_expr;

/// Check if Lean's Ixon.Expr serialization matches Rust.
#[unsafe(no_mangle)]
extern "C" fn rs_eq_expr_serialization(
  expr_ptr: *const c_void,
  bytes: &LeanSArrayObject,
) -> bool {
  let expr = lean_ptr_to_ixon_expr(expr_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  put_expr(&expr, &mut buf);
  buf == bytes_data
}

// ============================================================================
// New Ixon.Constant FFI
// ============================================================================

use crate::ix::ixon::constant::{
  Constant as IxonConstant, ConstantInfo as IxonConstantInfo,
  Definition as NewDefinition, Axiom as NewAxiom, Quotient as NewQuotient,
  Recursor as NewRecursor, RecursorRule as NewRecursorRule,
  Constructor as NewConstructor, Inductive as NewInductive,
  InductiveProj as NewInductiveProj, ConstructorProj as NewConstructorProj,
  RecursorProj as NewRecursorProj, DefinitionProj as NewDefinitionProj,
  MutConst as NewMutConst, DefKind as NewDefKind,
};

/// Decode a new-format Definition from Lean
/// Definition: kind(u8), safety(u8), lvls(u64), typ(obj), value(obj)
/// Lean ABI: objects first [typ, value], scalars sorted by SIZE DESCENDING [lvls:u64, kind:u8, safety:u8]
fn lean_ptr_to_new_definition(ptr: *const c_void) -> NewDefinition {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 2 object fields: typ, value
  let [typ_ptr, value_ptr] = ctor.objs();
  // Scalar area layout (sorted by size desc): lvls(u64 @0), kind(u8 @8), safety(u8 @9)
  let lvls = ctor.get_scalar_u64(2, 0);
  let kind_byte = ctor.get_scalar_u8(2, 8);
  let safety_byte = ctor.get_scalar_u8(2, 9);
  let kind = match kind_byte {
    0 => NewDefKind::Definition,
    1 => NewDefKind::Opaque,
    2 => NewDefKind::Theorem,
    _ => panic!("Unknown DefKind: {}", kind_byte),
  };
  let safety = match safety_byte {
    0 => DefinitionSafety::Unsafe,
    1 => DefinitionSafety::Safe,
    2 => DefinitionSafety::Partial,
    _ => panic!("Unknown DefinitionSafety: {}", safety_byte),
  };
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  let value = lean_ptr_to_ixon_expr(value_ptr);
  NewDefinition { kind, safety, lvls, typ, value }
}

/// Decode RecursorRule from Lean
/// RecursorRule: fields(scalar u64), rhs(obj)
fn lean_ptr_to_new_recursor_rule(ptr: *const c_void) -> NewRecursorRule {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object field: rhs
  let [rhs_ptr] = ctor.objs();
  // 1 scalar: fields (u64)
  let fields = ctor.get_scalar_u64(1, 0);
  let rhs = lean_ptr_to_ixon_expr(rhs_ptr);
  NewRecursorRule { fields, rhs }
}

/// Decode a new-format Recursor from Lean
/// Recursor: k(bool), isUnsafe(bool), lvls(u64), params(u64), indices(u64), motives(u64), minors(u64), typ(obj), rules(obj Array)
/// Lean ABI: scalars sorted by SIZE DESCENDING: [lvls, params, indices, motives, minors (u64s), k, isUnsafe (u8s)]
fn lean_ptr_to_new_recursor(ptr: *const c_void) -> NewRecursor {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 2 object fields: typ, rules (Array)
  let [typ_ptr, rules_ptr] = ctor.objs();
  // Scalars sorted by size: lvls@0, params@8, indices@16, motives@24, minors@32, k@40, isUnsafe@41
  let lvls = ctor.get_scalar_u64(2, 0);
  let params = ctor.get_scalar_u64(2, 8);
  let indices = ctor.get_scalar_u64(2, 16);
  let motives = ctor.get_scalar_u64(2, 24);
  let minors = ctor.get_scalar_u64(2, 32);
  let k = ctor.get_scalar_bool(2, 40);
  let is_unsafe = ctor.get_scalar_bool(2, 41);
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  // rules is Array RecursorRule, not List
  let rules_arr: &LeanArrayObject = as_ref_unsafe(rules_ptr.cast());
  let rules = rules_arr.to_vec(lean_ptr_to_new_recursor_rule);
  NewRecursor { k, is_unsafe, lvls, params, indices, motives, minors, typ, rules }
}

/// Decode a new-format Axiom from Lean
/// Axiom: isUnsafe(bool), lvls(u64), typ(obj)
/// Lean ABI: scalars sorted by SIZE DESCENDING: [lvls:u64@0, isUnsafe:u8@8]
fn lean_ptr_to_new_axiom(ptr: *const c_void) -> NewAxiom {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object field: typ
  let [typ_ptr] = ctor.objs();
  // Scalars sorted by size: lvls@0, isUnsafe@8
  let lvls = ctor.get_scalar_u64(1, 0);
  let is_unsafe = ctor.get_scalar_bool(1, 8);
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  NewAxiom { is_unsafe, lvls, typ }
}

/// Decode a new-format Quotient from Lean
/// Quotient: kind(QuotKind u8), lvls(u64), typ(obj)
/// Lean ABI: scalars sorted by SIZE DESCENDING: [lvls:u64@0, kind:u8@8]
fn lean_ptr_to_new_quotient(ptr: *const c_void) -> NewQuotient {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object field: typ
  let [typ_ptr] = ctor.objs();
  // Scalars sorted by size: lvls@0, kind@8
  let lvls = ctor.get_scalar_u64(1, 0);
  let kind_byte = ctor.get_scalar_u8(1, 8);
  let kind = match kind_byte {
    0 => QuotKind::Type,
    1 => QuotKind::Ctor,
    2 => QuotKind::Lift,
    3 => QuotKind::Ind,
    _ => panic!("Unknown QuotKind: {}", kind_byte),
  };
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  NewQuotient { kind, lvls, typ }
}

/// Decode a new-format Constructor from Lean
/// Constructor: isUnsafe(bool), lvls(u64), cidx(u64), params(u64), fields(u64), typ(obj)
/// Lean ABI: scalars sorted by SIZE DESCENDING: [lvls, cidx, params, fields (u64s), isUnsafe (u8)]
fn lean_ptr_to_new_constructor(ptr: *const c_void) -> NewConstructor {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object field: typ
  let [typ_ptr] = ctor.objs();
  // Scalars sorted by size: lvls@0, cidx@8, params@16, fields@24, isUnsafe@32
  let lvls = ctor.get_scalar_u64(1, 0);
  let cidx = ctor.get_scalar_u64(1, 8);
  let params = ctor.get_scalar_u64(1, 16);
  let fields = ctor.get_scalar_u64(1, 24);
  let is_unsafe = ctor.get_scalar_bool(1, 32);
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  NewConstructor { is_unsafe, lvls, cidx, params, fields, typ }
}

/// Decode a new-format Inductive from Lean
/// Inductive: recr(bool), refl(bool), isUnsafe(bool), lvls(u64), params(u64), indices(u64), nested(u64), typ(obj), ctors(obj Array)
/// Lean ABI: scalars sorted by SIZE DESCENDING: [lvls, params, indices, nested (u64s), recr, refl, isUnsafe (u8s)]
fn lean_ptr_to_new_inductive(ptr: *const c_void) -> NewInductive {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 2 object fields: typ, ctors (Array)
  let [typ_ptr, ctors_ptr] = ctor.objs();
  // Scalars sorted by size: lvls@0, params@8, indices@16, nested@24, recr@32, refl@33, isUnsafe@34
  let lvls = ctor.get_scalar_u64(2, 0);
  let params = ctor.get_scalar_u64(2, 8);
  let indices = ctor.get_scalar_u64(2, 16);
  let nested = ctor.get_scalar_u64(2, 24);
  let recr = ctor.get_scalar_bool(2, 32);
  let refl = ctor.get_scalar_bool(2, 33);
  let is_unsafe = ctor.get_scalar_bool(2, 34);
  let typ = lean_ptr_to_ixon_expr(typ_ptr);
  // ctors is Array Constructor, not List
  let ctors_arr: &LeanArrayObject = as_ref_unsafe(ctors_ptr.cast());
  let ctors = ctors_arr.to_vec(lean_ptr_to_new_constructor);
  NewInductive { recr, refl, is_unsafe, lvls, params, indices, nested, typ, ctors }
}

/// Decode InductiveProj from Lean
/// InductiveProj: idx(u64), block(obj Address)
fn lean_ptr_to_new_inductive_proj(ptr: *const c_void) -> NewInductiveProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object: block
  let [block_ptr] = ctor.objs();
  let idx = ctor.get_scalar_u64(1, 0);
  let block = lean_ptr_to_address(block_ptr);
  NewInductiveProj { idx, block }
}

/// Decode ConstructorProj from Lean
/// ConstructorProj: idx(u64), cidx(u64), block(obj Address)
fn lean_ptr_to_new_constructor_proj(ptr: *const c_void) -> NewConstructorProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object: block
  let [block_ptr] = ctor.objs();
  let idx = ctor.get_scalar_u64(1, 0);
  let cidx = ctor.get_scalar_u64(1, 8);
  let block = lean_ptr_to_address(block_ptr);
  NewConstructorProj { idx, cidx, block }
}

/// Decode RecursorProj from Lean
/// RecursorProj: idx(u64), block(obj Address)
fn lean_ptr_to_new_recursor_proj(ptr: *const c_void) -> NewRecursorProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object: block
  let [block_ptr] = ctor.objs();
  let idx = ctor.get_scalar_u64(1, 0);
  let block = lean_ptr_to_address(block_ptr);
  NewRecursorProj { idx, block }
}

/// Decode DefinitionProj from Lean
/// DefinitionProj: idx(u64), block(obj Address)
fn lean_ptr_to_new_definition_proj(ptr: *const c_void) -> NewDefinitionProj {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // 1 object: block
  let [block_ptr] = ctor.objs();
  let idx = ctor.get_scalar_u64(1, 0);
  let block = lean_ptr_to_address(block_ptr);
  NewDefinitionProj { idx, block }
}

/// Decode MutConst from Lean
fn lean_ptr_to_new_mutconst(ptr: *const c_void) -> NewMutConst {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner] = ctor.objs();
  match ctor.tag() {
    0 => NewMutConst::Defn(lean_ptr_to_new_definition(inner)),
    1 => NewMutConst::Indc(lean_ptr_to_new_inductive(inner)),
    2 => NewMutConst::Recr(lean_ptr_to_new_recursor(inner)),
    _ => panic!("Unknown MutConst tag: {}", ctor.tag()),
  }
}

/// Decode ConstantInfo from Lean
fn lean_ptr_to_constant_info(ptr: *const c_void) -> IxonConstantInfo {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  let [inner] = ctor.objs();
  match ctor.tag() {
    0 => IxonConstantInfo::Defn(lean_ptr_to_new_definition(inner)),
    1 => IxonConstantInfo::Recr(lean_ptr_to_new_recursor(inner)),
    2 => IxonConstantInfo::Axio(lean_ptr_to_new_axiom(inner)),
    3 => IxonConstantInfo::Quot(lean_ptr_to_new_quotient(inner)),
    4 => IxonConstantInfo::CPrj(lean_ptr_to_new_constructor_proj(inner)),
    5 => IxonConstantInfo::RPrj(lean_ptr_to_new_recursor_proj(inner)),
    6 => IxonConstantInfo::IPrj(lean_ptr_to_new_inductive_proj(inner)),
    7 => IxonConstantInfo::DPrj(lean_ptr_to_new_definition_proj(inner)),
    8 => {
      // muts is Array MutConst, not List
      let muts_arr: &LeanArrayObject = as_ref_unsafe(inner.cast());
      IxonConstantInfo::Muts(muts_arr.to_vec(lean_ptr_to_new_mutconst))
    },
    _ => panic!("Unknown ConstantInfo tag: {}", ctor.tag()),
  }
}

/// Decode Constant from Lean
fn lean_ptr_to_constant(ptr: *const c_void) -> IxonConstant {
  let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
  // Constant: info, sharing, refs, univs
  let [info_ptr, sharing_ptr, refs_ptr, univs_ptr] = ctor.objs();

  let info = lean_ptr_to_constant_info(info_ptr);

  // sharing is Array Expr
  let sharing_arr: &LeanArrayObject = as_ref_unsafe(sharing_ptr.cast());
  let sharing = sharing_arr.to_vec(lean_ptr_to_ixon_expr);

  // refs is Array Address
  let refs_arr: &LeanArrayObject = as_ref_unsafe(refs_ptr.cast());
  let refs = refs_arr.to_vec(lean_ptr_to_address);

  // univs is Array Univ
  let univs_arr: &LeanArrayObject = as_ref_unsafe(univs_ptr.cast());
  let univs = univs_arr.to_vec(lean_ptr_to_ixon_univ);

  IxonConstant { info, sharing, refs, univs }
}

/// Check if Lean's Ixon.Constant serialization matches Rust.
#[unsafe(no_mangle)]
extern "C" fn rs_eq_constant_serialization(
  constant_ptr: *const c_void,
  bytes: &LeanSArrayObject,
) -> bool {
  let constant = lean_ptr_to_constant(constant_ptr);
  let bytes_data = bytes.data();
  let mut buf = Vec::with_capacity(bytes_data.len());
  constant.put(&mut buf);
  buf == bytes_data
}

// ============================================================================
// Cross-implementation compilation comparison FFI
// ============================================================================

use crate::ix::compile::{compile_expr, BlockCache, CompileState};
use crate::ix::mutual::MutCtx;
use crate::ix::env::Name;
use super::lean_env::{lean_ptr_to_expr, Cache as LeanCache, GlobalCache};

/// Compare Lean's compiled expression output with Rust's compilation of the same input.
/// Takes:
/// - lean_expr_ptr: pointer to Lean.Expr
/// - lean_output: serialized Ixon.Expr from Lean's compiler
/// - univ_ctx_size: number of universe parameters in context (for de Bruijn indexing)
/// Returns true if Rust compiles to the same bytes.
#[unsafe(no_mangle)]
extern "C" fn rs_compare_expr_compilation(
  lean_expr_ptr: *const c_void,
  lean_output: &LeanSArrayObject,
  univ_ctx_size: u64,
) -> bool {
  // Decode Lean.Expr to Rust's representation
  let global_cache = GlobalCache::default();
  let mut cache = LeanCache::new(&global_cache);
  let lean_expr = lean_ptr_to_expr(lean_expr_ptr, &mut cache);

  // Create universe params for de Bruijn indexing (u0, u1, u2, ...)
  let univ_params: Vec<Name> = (0..univ_ctx_size)
    .map(|i| Name::str(Name::anon(), format!("u{}", i)))
    .collect();
  let mut_ctx = MutCtx::default();

  // Create minimal compile state (no environment needed for simple exprs)
  let compile_stt = CompileState::new_empty();
  let mut block_cache = BlockCache::default();

  // Compile with Rust
  let rust_expr = match compile_expr(&lean_expr, &univ_params, &mut_ctx, &mut block_cache, &compile_stt) {
    Ok(expr) => expr,
    Err(_) => return false,
  };

  // Serialize Rust's output
  let mut rust_bytes = Vec::new();
  put_expr(&rust_expr, &mut rust_bytes);

  // Compare byte-for-byte
  let lean_bytes = lean_output.data();
  rust_bytes == lean_bytes
}

use crate::ix::compile::compile_const;
use crate::ix::graph::NameSet;
use crate::ix::env::{Env as LeanEnv, ConstantInfo as LeanConstantInfo};
use super::lean_env::lean_ptr_to_constant_info as decode_lean_constant;

/// Compare Lean's compiled Constant output with Rust's compilation of the same input.
/// Takes:
/// - const_info_ptr: pointer to Lean.ConstantInfo
/// - lean_output: serialized Ixon.Constant from Lean's compiler
/// Returns true if Rust produces the same bytes.
#[unsafe(no_mangle)]
extern "C" fn rs_compare_constant_compilation(
  const_info_ptr: *const c_void,
  lean_output: &LeanSArrayObject,
) -> bool {
  // Decode Lean.ConstantInfo to Rust's representation
  let global_cache = GlobalCache::default();
  let mut cache = LeanCache::new(&global_cache);
  let const_info: LeanConstantInfo = decode_lean_constant(const_info_ptr, &mut cache);

  // Get the constant's name
  let name = const_info.get_name().clone();

  // Create a minimal environment with just this constant
  let mut env = LeanEnv::default();
  env.insert(name.clone(), const_info);
  let env = Arc::new(env);

  // Create all set (just this constant)
  let mut all = NameSet::default();
  all.insert(name.clone());

  // Create minimal compile state
  let compile_stt = CompileState::new_empty();
  let mut block_cache = BlockCache::default();

  // Compile with Rust
  let rust_addr = match compile_const(&name, &all, &env, &mut block_cache, &compile_stt) {
    Ok(addr) => addr,
    Err(e) => {
      eprintln!("Rust compilation failed: {:?}", e);
      return false;
    },
  };

  // Get the compiled constant
  let rust_const = match compile_stt.env.get_const(&rust_addr) {
    Some(c) => c,
    None => {
      eprintln!("Compiled constant not found at address");
      return false;
    },
  };

  // Serialize Rust's output
  let mut rust_bytes = Vec::new();
  rust_const.put(&mut rust_bytes);

  // Compare byte-for-byte
  let lean_bytes = lean_output.data();
  if rust_bytes != lean_bytes {
    eprintln!("Byte mismatch:");
    eprintln!("  Lean bytes ({} total): {:?}...", lean_bytes.len(), &lean_bytes[..lean_bytes.len().min(50)]);
    eprintln!("  Rust bytes ({} total): {:?}...", rust_bytes.len(), &rust_bytes[..rust_bytes.len().min(50)]);
  }
  rust_bytes == lean_bytes
}

use super::lean_env::lean_ptr_to_name;
use crate::ix::compile::compile_env;

/// Compare Lean's compiled environment with Rust's compilation.
/// Takes:
/// - env_consts_ptr: pointer to List (Name × ConstantInfo) from Lean environment
/// - lean_compiled_ptr: pointer to List (Name × ByteArray) - compiled constants from Lean
/// Returns the number of mismatches (0 = success)
#[unsafe(no_mangle)]
extern "C" fn rs_compare_env_compilation(
  env_consts_ptr: *const c_void,
  lean_compiled_ptr: *const c_void,
) -> u64 {
  use std::collections::HashMap;

  // Phase 1: Decode Lean environment
  let start_decode = std::time::Instant::now();
  let lean_env = super::lean_env::lean_ptr_to_env(env_consts_ptr);
  let env_len = lean_env.len();
  let lean_env = Arc::new(lean_env);
  println!("  Rust decode env: {:.2}s ({} constants)",
    start_decode.elapsed().as_secs_f32(), env_len);

  // Phase 2: Compile with Rust
  let start_compile = std::time::Instant::now();
  let rust_stt = match compile_env(&lean_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("Rust compilation failed: {:?}", e);
      return u64::MAX;
    }
  };
  println!("  Rust compile env: {:.2}s", start_compile.elapsed().as_secs_f32());

  // Phase 3: Decode Lean's compiled constants
  let start_lean_decode = std::time::Instant::now();
  let global_cache = GlobalCache::default();
  let lean_compiled: HashMap<Name, Vec<u8>> = {
    let mut map = HashMap::new();
    let mut ptr = lean_compiled_ptr;
    while !lean_is_scalar(ptr) {
      let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
      let [pair_ptr, tail_ptr] = ctor.objs();

      // Decode (Name, ByteArray) pair
      let pair: &LeanCtorObject = as_ref_unsafe(pair_ptr.cast());
      let [name_ptr, bytes_ptr] = pair.objs();

      let name = lean_ptr_to_name(name_ptr, &global_cache);
      let bytes_arr: &LeanSArrayObject = as_ref_unsafe(bytes_ptr.cast());
      let bytes = bytes_arr.data().to_vec();

      map.insert(name, bytes);
      ptr = tail_ptr;
    }
    map
  };
  println!("  Decode Lean compiled: {:.2}s ({} constants)",
    start_lean_decode.elapsed().as_secs_f32(), lean_compiled.len());

  // Phase 4: Compare each constant
  let start_compare = std::time::Instant::now();
  let mut mismatches = 0u64;
  let mut missing_in_rust = 0u64;
  let mut missing_in_lean = 0u64;

  for (name, lean_bytes) in &lean_compiled {
    // Look up in Rust's compiled state
    let rust_addr = match rust_stt.name_to_addr.get(name) {
      Some(addr) => addr.clone(),
      None => {
        if mismatches + missing_in_rust < 10 {
          eprintln!("Missing in Rust: {:?}", name);
        }
        missing_in_rust += 1;
        continue;
      }
    };

    let rust_const = match rust_stt.env.get_const(&rust_addr) {
      Some(c) => c,
      None => {
        if mismatches + missing_in_rust < 10 {
          eprintln!("Rust addr not found: {:?} -> {:?}", name, rust_addr);
        }
        missing_in_rust += 1;
        continue;
      }
    };

    // Serialize Rust's constant
    let mut rust_bytes = Vec::new();
    rust_const.put(&mut rust_bytes);

    // Compare
    if rust_bytes != *lean_bytes {
      if mismatches < 10 {
        eprintln!("Mismatch for {:?}:", name);
        eprintln!("  Lean: {} bytes, Rust: {} bytes", lean_bytes.len(), rust_bytes.len());
        if lean_bytes.len() <= 100 {
          eprintln!("  Lean bytes: {:?}", lean_bytes);
        }
        if rust_bytes.len() <= 100 {
          eprintln!("  Rust bytes: {:?}", rust_bytes);
        }
      }
      mismatches += 1;
    }
  }

  // Check for constants in Rust but not in Lean
  for entry in rust_stt.name_to_addr.iter() {
    let name = entry.key();
    if !lean_compiled.contains_key(name) {
      if missing_in_lean < 10 {
        eprintln!("Missing in Lean: {:?}", name);
      }
      missing_in_lean += 1;
    }
  }

  println!("  Compare: {:.2}s", start_compare.elapsed().as_secs_f32());

  let total_errors = mismatches + missing_in_rust + missing_in_lean;
  if total_errors > 0 {
    eprintln!("Cross-impl comparison: {} mismatches, {} missing in Rust, {} missing in Lean",
      mismatches, missing_in_rust, missing_in_lean);
  } else {
    println!("Cross-impl comparison: all {} constants match!", lean_compiled.len());
  }

  total_errors
}

/// FFI: Test Env serialization roundtrip.
/// Takes:
/// - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
/// Returns: true if Rust can deserialize and re-serialize to the same bytes
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_roundtrip(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let bytes_arr: &LeanSArrayObject = as_ref_unsafe(lean_bytes_ptr.cast());
  let lean_bytes = bytes_arr.data().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  let env = match Env::get(&mut slice) {
    Ok(e) => e,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      return false;
    }
  };

  // Re-serialize
  let mut rust_bytes = Vec::new();
  env.put(&mut rust_bytes);

  // Compare
  if lean_bytes != rust_bytes {
    eprintln!("Env roundtrip mismatch:");
    eprintln!("  Input:  {} bytes", lean_bytes.len());
    eprintln!("  Output: {} bytes", rust_bytes.len());
    if lean_bytes.len() <= 200 {
      eprintln!("  Input bytes:  {:?}", lean_bytes);
    }
    if rust_bytes.len() <= 200 {
      eprintln!("  Output bytes: {:?}", rust_bytes);
    }
    return false;
  }

  true
}

/// FFI: Compare Env serialization between Lean and Rust.
/// Takes:
/// - lean_bytes_ptr: pointer to ByteArray containing serialized Env from Lean
/// Returns: true if Rust can deserialize and the counts match
#[unsafe(no_mangle)]
extern "C" fn rs_env_serde_check(lean_bytes_ptr: *const c_void) -> bool {
  use crate::ix::ixon::env::Env;

  // Get bytes from Lean ByteArray
  let bytes_arr: &LeanSArrayObject = as_ref_unsafe(lean_bytes_ptr.cast());
  let lean_bytes = bytes_arr.data().to_vec();

  // Try to deserialize with Rust
  let mut slice = lean_bytes.as_slice();
  match Env::get(&mut slice) {
    Ok(_) => true,
    Err(e) => {
      eprintln!("Rust Env::get failed: {}", e);
      false
    }
  }
}

// ============================================================================
// Incremental Block-by-Block Compilation Comparison FFI
// ============================================================================

use std::collections::HashMap;

/// Rust-compiled environment holding blocks indexed by low-link name.
/// Each block is stored as serialized bytes for comparison with Lean output.
pub struct RustCompiledEnv {
  /// Map from low-link name to (serialized constant bytes, sharing vector length)
  blocks: HashMap<Name, (Vec<u8>, usize)>,
  /// The full compile state for accessing pre-sharing expressions
  compile_state: CompileState,
}

/// Result of comparing a single block between Lean and Rust.
#[repr(C)]
pub struct BlockComparisonResult {
  /// Whether the bytes match exactly
  matches: u8,
  /// Size of Lean's serialized constant in bytes
  lean_bytes_size: u64,
  /// Size of Rust's serialized constant in bytes
  rust_bytes_size: u64,
  /// Length of Lean's sharing vector
  lean_sharing_len: u64,
  /// Length of Rust's sharing vector
  rust_sharing_len: u64,
  /// Offset of first differing byte (u64::MAX if matches)
  first_diff_offset: u64,
}

/// FFI: Simple test to verify FFI round-trip works.
/// Takes a Lean.Name and returns a magic number to verify the call succeeded.
#[unsafe(no_mangle)]
extern "C" fn rs_test_ffi_roundtrip(
  name_ptr: *const c_void,
) -> u64 {
  // Decode the Name to verify FFI works
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

  // Return a magic number plus the hash of the name to verify it worked
  let hash = name.get_hash();
  let hash_bytes = hash.as_bytes();
  let hash_prefix = u64::from_le_bytes(hash_bytes[0..8].try_into().unwrap_or([0u8; 8]));

  // Magic number 0xDEADBEEF plus hash prefix
  0xDEAD_BEEF_0000_0000 | (hash_prefix & 0x0000_0000_FFFF_FFFF)
}

/// FFI: Compile entire environment with Rust, returning a handle to RustCompiledEnv.
/// Takes:
/// - env_consts_ptr: pointer to List (Name × ConstantInfo) from Lean environment
/// Returns: pointer to RustCompiledEnv (or null on failure)
#[unsafe(no_mangle)]
extern "C" fn rs_compile_env_rust_first(
  env_consts_ptr: *const c_void,
) -> *mut RustCompiledEnv {

  // Decode Lean environment
  let start_decode = std::time::Instant::now();
  let lean_env = super::lean_env::lean_ptr_to_env(env_consts_ptr);
  let env_len = lean_env.len();
  let lean_env = Arc::new(lean_env);
  println!("  [Rust] Decode env: {:.2}s ({} constants)",
    start_decode.elapsed().as_secs_f32(), env_len);

  // Compile with Rust
  let start_compile = std::time::Instant::now();
  let rust_stt = match compile_env(&lean_env) {
    Ok(stt) => stt,
    Err(e) => {
      eprintln!("Rust compilation failed: {:?}", e);
      return std::ptr::null_mut();
    }
  };
  println!("  [Rust] Compile env: {:.2}s", start_compile.elapsed().as_secs_f32());

  // Build block map: lowlink name -> (serialized bytes, sharing len)
  let start_extract = std::time::Instant::now();
  let mut blocks: HashMap<Name, (Vec<u8>, usize)> = HashMap::new();

  // Iterate over all names and their addresses
  for entry in rust_stt.name_to_addr.iter() {
    let name = entry.key().clone();
    let addr = entry.value().clone();

    // Skip if we already have this block (multiple names map to same block)
    if blocks.contains_key(&name) {
      continue;
    }

    // Get the compiled constant
    if let Some(constant) = rust_stt.env.get_const(&addr) {
      let mut bytes = Vec::new();
      constant.put(&mut bytes);
      let sharing_len = constant.sharing.len();
      blocks.insert(name, (bytes, sharing_len));
    }
  }

  println!("  [Rust] Extract {} blocks: {:.2}s",
    blocks.len(), start_extract.elapsed().as_secs_f32());

  // Return boxed RustCompiledEnv with full compile state for pre-sharing access
  Box::into_raw(Box::new(RustCompiledEnv { blocks, compile_state: rust_stt }))
}

/// FFI: Compare a single block and return packed result.
/// Returns a packed u64: high 32 bits = matches (1) or error code (0 = mismatch, 2 = not found)
///                       low 32 bits = first diff offset (if mismatch)
/// Use rs_get_block_details for detailed comparison info on mismatches.
#[unsafe(no_mangle)]
extern "C" fn rs_compare_block(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  lean_bytes: &LeanSArrayObject,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.data();

  // Look up Rust's compiled block
  let rust_bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => {
      // Block not found in Rust compilation: code 2
      return 2u64 << 32;
    }
  };

  // Compare bytes
  if rust_bytes == lean_data {
    // Match: code 1
    return 1u64 << 32;
  }

  // Mismatch: code 0, with first diff offset
  let first_diff_offset = rust_bytes.iter()
    .zip(lean_data.iter())
    .position(|(a, b)| a != b)
    .map(|i| i as u32)
    .unwrap_or_else(|| {
      // One is a prefix of the other
      rust_bytes.len().min(lean_data.len()) as u32
    });

  first_diff_offset as u64
}

/// FFI: Get detailed comparison info for a block.
/// Returns (matches, lean_size, rust_size, lean_sharing, rust_sharing, first_diff) packed into array.
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_details(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  lean_bytes: &LeanSArrayObject,
  lean_sharing_len: u64,
  out: *mut u64,
) {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };
  let lean_data = lean_bytes.data();
  let out_slice = unsafe { std::slice::from_raw_parts_mut(out, 6) };

  // Look up Rust's compiled block
  let (rust_bytes, rust_sharing_len) = match rust_env.blocks.get(&name) {
    Some(block) => block,
    None => {
      // Block not found in Rust compilation
      out_slice[0] = 0; // matches
      out_slice[1] = lean_data.len() as u64;
      out_slice[2] = 0; // rust bytes
      out_slice[3] = lean_sharing_len;
      out_slice[4] = 0; // rust sharing
      out_slice[5] = 0; // first diff
      return;
    }
  };

  // Compare bytes
  let matches = rust_bytes == lean_data;
  let first_diff_offset = if matches {
    u64::MAX
  } else {
    rust_bytes.iter()
      .zip(lean_data.iter())
      .position(|(a, b)| a != b)
      .map(|i| i as u64)
      .unwrap_or_else(|| {
        rust_bytes.len().min(lean_data.len()) as u64
      })
  };

  out_slice[0] = if matches { 1 } else { 0 };
  out_slice[1] = lean_data.len() as u64;
  out_slice[2] = rust_bytes.len() as u64;
  out_slice[3] = lean_sharing_len;
  out_slice[4] = *rust_sharing_len as u64;
  out_slice[5] = first_diff_offset;
}

/// FFI: Free a RustCompiledEnv.
#[unsafe(no_mangle)]
extern "C" fn rs_free_rust_env(rust_env: *mut RustCompiledEnv) {
  if !rust_env.is_null() {
    unsafe { drop(Box::from_raw(rust_env)); }
  }
}

/// FFI: Get the number of blocks in a RustCompiledEnv.
#[unsafe(no_mangle)]
extern "C" fn rs_get_rust_env_block_count(rust_env: *const RustCompiledEnv) -> u64 {
  if rust_env.is_null() {
    return 0;
  }
  let rust_env = unsafe { &*rust_env };
  rust_env.blocks.len() as u64
}

/// FFI: Get Rust's compiled bytes for a block.
/// Writes bytes to the provided buffer and returns the length.
/// If buffer is null, just returns the length needed.
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_bytes_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes.len() as u64,
    None => 0,
  }
}

/// FFI: Copy Rust's compiled bytes into a pre-allocated Lean ByteArray.
#[unsafe(no_mangle)]
extern "C" fn rs_copy_block_bytes(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  dest: *mut c_void,  // Lean ByteArray
) {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  let bytes = match rust_env.blocks.get(&name) {
    Some((bytes, _)) => bytes,
    None => return,
  };

  // Copy into the Lean ByteArray
  let dest_arr: &mut LeanSArrayObject = unsafe { &mut *dest.cast() };
  dest_arr.set_data(bytes);
}

/// FFI: Get Rust's sharing vector length for a block.
#[unsafe(no_mangle)]
extern "C" fn rs_get_block_sharing_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  match rust_env.blocks.get(&name) {
    Some((_, sharing_len)) => *sharing_len as u64,
    None => 0,
  }
}

// ============================================================================
// Pre-sharing expression extraction FFI
// ============================================================================

use crate::ix::ixon::constant::ConstantInfo;

/// Expand Share(idx) references in an expression using the sharing vector.
/// This reconstructs the "pre-sharing" expression from the post-sharing representation.
fn unshare_expr(expr: &Arc<IxonExpr>, sharing: &[Arc<IxonExpr>]) -> Arc<IxonExpr> {
  match expr.as_ref() {
    IxonExpr::Share(idx) => {
      // Recursively unshare the sharing vector entry
      if (*idx as usize) < sharing.len() {
        unshare_expr(&sharing[*idx as usize], sharing)
      } else {
        expr.clone() // Invalid index, keep as-is
      }
    }
    IxonExpr::App(f, a) => {
      Arc::new(IxonExpr::App(unshare_expr(f, sharing), unshare_expr(a, sharing)))
    }
    IxonExpr::Lam(t, b) => {
      Arc::new(IxonExpr::Lam(unshare_expr(t, sharing), unshare_expr(b, sharing)))
    }
    IxonExpr::All(t, b) => {
      Arc::new(IxonExpr::All(unshare_expr(t, sharing), unshare_expr(b, sharing)))
    }
    IxonExpr::Let(nd, t, v, b) => {
      Arc::new(IxonExpr::Let(*nd, unshare_expr(t, sharing), unshare_expr(v, sharing), unshare_expr(b, sharing)))
    }
    IxonExpr::Prj(ti, fi, v) => {
      Arc::new(IxonExpr::Prj(*ti, *fi, unshare_expr(v, sharing)))
    }
    // Leaf nodes - no children to unshare
    _ => expr.clone(),
  }
}

/// FFI: Get the pre-sharing root expressions for a constant.
/// Returns the number of root expressions, and writes serialized expressions to the output buffer.
/// Each expression is serialized without sharing (Share nodes are expanded).
///
/// Output format: [n_exprs:u64, len1:u64, expr1_bytes..., len2:u64, expr2_bytes..., ...]
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
  out_buf: *mut c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  let addr = match rust_env.compile_state.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => {
      eprintln!("rs_get_pre_sharing_exprs: name not found: {:?}", name);
      return 0;
    }
  };

  // Get the constant (note: contains post-sharing expressions)
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => {
      eprintln!("rs_get_pre_sharing_exprs: constant not found at addr");
      return 0;
    }
  };

  // Get the sharing vector for unsharing
  let sharing = &constant.sharing;

  // Extract root expressions based on constant type
  let root_exprs: Vec<&Arc<IxonExpr>> = match &constant.info {
    ConstantInfo::Defn(d) => vec![&d.typ, &d.value],
    ConstantInfo::Recr(r) => {
      let mut exprs = vec![&r.typ];
      for rule in &r.rules {
        exprs.push(&rule.rhs);
      }
      exprs
    }
    ConstantInfo::Axio(a) => vec![&a.typ],
    ConstantInfo::Quot(q) => vec![&q.typ],
    ConstantInfo::IPrj(_) |
    ConstantInfo::CPrj(_) |
    ConstantInfo::RPrj(_) |
    ConstantInfo::DPrj(_) => {
      // Projections don't have expressions to analyze
      return 0;
    }
    ConstantInfo::Muts(muts) => {
      let mut exprs = Vec::new();
      for mc in muts {
        match mc {
          crate::ix::ixon::constant::MutConst::Defn(d) => {
            exprs.push(&d.typ);
            exprs.push(&d.value);
          }
          crate::ix::ixon::constant::MutConst::Indc(i) => {
            exprs.push(&i.typ);
            for ctor in &i.ctors {
              exprs.push(&ctor.typ);
            }
          }
          crate::ix::ixon::constant::MutConst::Recr(r) => {
            exprs.push(&r.typ);
            for rule in &r.rules {
              exprs.push(&rule.rhs);
            }
          }
        }
      }
      exprs
    }
  };

  let n_exprs = root_exprs.len();

  // Unshare and serialize each expression (expand Share nodes)
  let mut all_bytes: Vec<u8> = Vec::new();

  // Write number of expressions
  all_bytes.extend_from_slice(&(n_exprs as u64).to_le_bytes());

  for expr in &root_exprs {
    // Expand Share(idx) references to get the pre-sharing expression
    let unshared = unshare_expr(expr, sharing);
    let mut expr_bytes: Vec<u8> = Vec::new();
    put_expr(&unshared, &mut expr_bytes);

    // Write length then bytes
    all_bytes.extend_from_slice(&(expr_bytes.len() as u64).to_le_bytes());
    all_bytes.extend_from_slice(&expr_bytes);
  }

  // Write to output buffer
  let out_arr: &mut LeanSArrayObject = unsafe { &mut *out_buf.cast() };
  out_arr.set_data(&all_bytes);

  n_exprs as u64
}

/// FFI: Get the length needed for pre-sharing expressions buffer.
#[unsafe(no_mangle)]
extern "C" fn rs_get_pre_sharing_exprs_len(
  rust_env: *const RustCompiledEnv,
  lowlink_name: *const c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(lowlink_name, &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  let addr = match rust_env.compile_state.name_to_addr.get(&name) {
    Some(a) => a.clone(),
    None => return 0,
  };

  // Get the constant (note: contains post-sharing expressions)
  let constant = match rust_env.compile_state.env.get_const(&addr) {
    Some(c) => c,
    None => return 0,
  };

  // Get the sharing vector for unsharing
  let sharing = &constant.sharing;

  // Extract root expressions based on constant type
  let root_exprs: Vec<&Arc<IxonExpr>> = match &constant.info {
    ConstantInfo::Defn(d) => vec![&d.typ, &d.value],
    ConstantInfo::Recr(r) => {
      let mut exprs = vec![&r.typ];
      for rule in &r.rules {
        exprs.push(&rule.rhs);
      }
      exprs
    }
    ConstantInfo::Axio(a) => vec![&a.typ],
    ConstantInfo::Quot(q) => vec![&q.typ],
    ConstantInfo::IPrj(_) |
    ConstantInfo::CPrj(_) |
    ConstantInfo::RPrj(_) |
    ConstantInfo::DPrj(_) => return 0,
    ConstantInfo::Muts(muts) => {
      let mut exprs = Vec::new();
      for mc in muts {
        match mc {
          crate::ix::ixon::constant::MutConst::Defn(d) => {
            exprs.push(&d.typ);
            exprs.push(&d.value);
          }
          crate::ix::ixon::constant::MutConst::Indc(i) => {
            exprs.push(&i.typ);
            for ctor in &i.ctors {
              exprs.push(&ctor.typ);
            }
          }
          crate::ix::ixon::constant::MutConst::Recr(r) => {
            exprs.push(&r.typ);
            for rule in &r.rules {
              exprs.push(&rule.rhs);
            }
          }
        }
      }
      exprs
    }
  };

  // Compute total size (with unsharing)
  let mut total: u64 = 8; // n_exprs header
  for expr in &root_exprs {
    // Expand Share(idx) references to get the pre-sharing expression
    let unshared = unshare_expr(expr, sharing);
    let mut expr_bytes: Vec<u8> = Vec::new();
    put_expr(&unshared, &mut expr_bytes);
    total += 8 + expr_bytes.len() as u64; // length prefix + bytes
  }

  total
}

// ============================================================================
// Cross-implementation sharing analysis FFI
// ============================================================================

use crate::ix::ixon::sharing::{analyze_block, decide_sharing, build_sharing_vec};

/// FFI: Run Rust's sharing analysis on Lean-provided Ixon.Expr array.
/// Returns the number of shared items Rust would produce.
#[unsafe(no_mangle)]
extern "C" fn rs_analyze_sharing_count(
  exprs_ptr: *const c_void,
) -> u64 {
  let exprs_arr: &LeanArrayObject = as_ref_unsafe(exprs_ptr.cast());
  let exprs: Vec<Arc<IxonExpr>> = exprs_arr.to_vec(lean_ptr_to_ixon_expr);

  let (info_map, _ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);

  shared_hashes.len() as u64
}

/// FFI: Run Rust's full sharing pipeline on Lean-provided Ixon.Expr array.
/// Writes the sharing vector and rewritten exprs to output arrays.
/// Returns number of shared items.
#[unsafe(no_mangle)]
extern "C" fn rs_run_sharing_analysis(
  exprs_ptr: *const c_void,
  out_sharing_vec: *mut c_void,
  out_rewritten: *mut c_void,
) -> u64 {
  let exprs_arr: &LeanArrayObject = as_ref_unsafe(exprs_ptr.cast());
  let exprs: Vec<Arc<IxonExpr>> = exprs_arr.to_vec(lean_ptr_to_ixon_expr);

  let (info_map, ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);
  let (rewritten_exprs, sharing_vec) =
    build_sharing_vec(&exprs, &shared_hashes, &ptr_to_hash, &info_map);

  // Serialize sharing vector to bytes
  let mut sharing_bytes: Vec<u8> = Vec::new();
  for expr in &sharing_vec {
    put_expr(expr, &mut sharing_bytes);
  }

  // Serialize rewritten exprs to bytes
  let mut rewritten_bytes: Vec<u8> = Vec::new();
  for expr in &rewritten_exprs {
    put_expr(expr, &mut rewritten_bytes);
  }

  // Write to output arrays
  let sharing_out: &mut LeanSArrayObject = unsafe { &mut *out_sharing_vec.cast() };
  sharing_out.set_data(&sharing_bytes);

  let rewritten_out: &mut LeanSArrayObject = unsafe { &mut *out_rewritten.cast() };
  rewritten_out.set_data(&rewritten_bytes);

  shared_hashes.len() as u64
}

/// FFI: Compare Lean's sharing analysis with Rust's on the same input.
/// Takes: exprs (Array Expr), lean_sharing (Array Expr), lean_rewritten (Array Expr)
/// Returns packed u64:
///   - bits 0-31: 1 if sharing vectors match, 0 otherwise
///   - bits 32-47: Lean sharing count
///   - bits 48-63: Rust sharing count
#[unsafe(no_mangle)]
extern "C" fn rs_compare_sharing_analysis(
  exprs_ptr: *const c_void,
  lean_sharing_ptr: *const c_void,
  _lean_rewritten_ptr: *const c_void,
) -> u64 {
  // Decode input expressions
  let exprs_arr: &LeanArrayObject = as_ref_unsafe(exprs_ptr.cast());
  let exprs: Vec<Arc<IxonExpr>> = exprs_arr.to_vec(lean_ptr_to_ixon_expr);

  // Decode Lean's sharing vector
  let lean_sharing_arr: &LeanArrayObject = as_ref_unsafe(lean_sharing_ptr.cast());
  let lean_sharing: Vec<Arc<IxonExpr>> = lean_sharing_arr.to_vec(lean_ptr_to_ixon_expr);

  // Run Rust's sharing analysis
  let (info_map, ptr_to_hash) = analyze_block(&exprs, false);
  let shared_hashes = decide_sharing(&info_map);
  let (_rewritten_exprs, rust_sharing) =
    build_sharing_vec(&exprs, &shared_hashes, &ptr_to_hash, &info_map);

  // Compare sharing vectors
  let lean_count = lean_sharing.len() as u64;
  let rust_count = rust_sharing.len() as u64;

  // Serialize both to bytes for comparison
  let mut lean_bytes: Vec<u8> = Vec::new();
  for expr in &lean_sharing {
    put_expr(expr, &mut lean_bytes);
  }

  let mut rust_bytes: Vec<u8> = Vec::new();
  for expr in &rust_sharing {
    put_expr(expr, &mut rust_bytes);
  }

  let matches = if lean_bytes == rust_bytes { 1u64 } else { 0u64 };

  // Pack result: matches | (lean_count << 32) | (rust_count << 48)
  matches | (lean_count << 32) | (rust_count << 48)
}

/// FFI: Look up a constant's compiled address from RustCompiledEnv.
/// Copies the 32-byte blake3 hash into the provided ByteArray.
/// Returns 1 on success, 0 if name not found.
#[unsafe(no_mangle)]
extern "C" fn rs_lookup_const_addr(
  rust_env: *const RustCompiledEnv,
  name_ptr: *const c_void,
  out_addr: *mut c_void,
) -> u64 {
  let global_cache = GlobalCache::default();
  let name = lean_ptr_to_name(name_ptr, &global_cache);

  let rust_env = unsafe { &*rust_env };

  // Look up the address for this name
  match rust_env.compile_state.name_to_addr.get(&name) {
    Some(addr_ref) => {
      // Copy the 32-byte address into the output ByteArray
      let out_arr: &mut LeanSArrayObject = unsafe { &mut *out_addr.cast() };
      out_arr.set_data(addr_ref.as_bytes());
      1
    }
    None => 0,
  }
}

/// FFI: Get the total number of compiled constants in RustCompiledEnv.
#[unsafe(no_mangle)]
extern "C" fn rs_get_compiled_const_count(
  rust_env: *const RustCompiledEnv,
) -> u64 {
  let rust_env = unsafe { &*rust_env };
  rust_env.compile_state.name_to_addr.len() as u64
}

/// FFI: Debug sharing analysis - print usage counts for subterms with usage >= 2.
/// This helps diagnose why Lean and Rust make different sharing decisions.
#[unsafe(no_mangle)]
extern "C" fn rs_debug_sharing_analysis(
  exprs_ptr: *const c_void,
) {
  let exprs_arr: &LeanArrayObject = as_ref_unsafe(exprs_ptr.cast());
  let exprs: Vec<Arc<IxonExpr>> = exprs_arr.to_vec(lean_ptr_to_ixon_expr);

  println!("[Rust] Analyzing {} input expressions", exprs.len());

  let (info_map, _ptr_to_hash) = analyze_block(&exprs, false);
  let topo_order = crate::ix::ixon::sharing::topological_sort(&info_map);
  let effective_sizes =
    crate::ix::ixon::sharing::compute_effective_sizes(&info_map, &topo_order);

  println!("[Rust] Found {} unique subterms", info_map.len());

  // Collect subterms with usage >= 2
  let mut candidates: Vec<_> = info_map
    .iter()
    .filter(|(_, info)| info.usage_count >= 2)
    .filter_map(|(hash, info)| {
      let eff_size = *effective_sizes.get(hash)?;
      Some((hash, info, eff_size))
    })
    .collect();

  // Sort by usage count descending
  candidates.sort_by(|a, b| b.1.usage_count.cmp(&a.1.usage_count));

  println!("[Rust] Subterms with usage >= 2:");
  for (hash, info, eff_size) in candidates {
    let n = info.usage_count;
    let potential = (n as isize - 1) * (eff_size as isize) - (n as isize + eff_size as isize);
    println!(
      "  usage={} eff_size={} potential={} hash={:.8}",
      n, eff_size, potential, hash
    );
    println!("    expr={:?}", info.expr);
  }
}
