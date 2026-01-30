//! Ixon constant types build/decode/roundtrip FFI.
//!
//! Includes: Definition, Axiom, Quotient, RecursorRule, Recursor, Constructor,
//! Inductive, InductiveProj, ConstructorProj, RecursorProj, DefinitionProj,
//! MutConst, ConstantInfo, Constant

use std::ffi::c_void;
use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::constant::{
  Axiom as IxonAxiom, Constant as IxonConstant, ConstantInfo as IxonConstantInfo,
  Constructor as IxonConstructor, ConstructorProj, DefKind, Definition as IxonDefinition,
  DefinitionProj, Inductive as IxonInductive, InductiveProj, MutConst, Quotient as IxonQuotient,
  Recursor as IxonRecursor, RecursorProj, RecursorRule as IxonRecursorRule,
};
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray, lean_array_set_core,
  lean_ctor_get, lean_ctor_set, lean_obj_tag, lean_sarray_cptr,
};

use super::expr::{build_ixon_expr, build_ixon_expr_array, decode_ixon_expr, decode_ixon_expr_array};
use super::univ::{build_ixon_univ_array, decode_ixon_univ_array};

/// Build Address from Ixon Address type (which is just a [u8; 32]).
pub fn build_address_from_ixon(addr: &Address) -> *mut c_void {
  unsafe {
    let ba = lean_alloc_sarray(1, 32, 32);
    let data_ptr = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(addr.as_bytes().as_ptr(), data_ptr, 32);
    ba
  }
}

/// Build an Array of Addresses.
pub fn build_address_array(addrs: &[Address]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(addrs.len(), addrs.len());
    for (i, addr) in addrs.iter().enumerate() {
      let addr_obj = build_address_from_ixon(addr);
      lean_array_set_core(arr, i, addr_obj);
    }
    arr
  }
}

/// Build Ixon.Definition
/// Lean stores scalar fields ordered by size (largest first).
/// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
pub fn build_ixon_definition(def: &IxonDefinition) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&def.typ);
    let value_obj = build_ixon_expr(&def.value);
    // 2 obj fields, 16 scalar bytes (lvls(8) + kind(1) + safety(1) + padding(6))
    let obj = lean_alloc_ctor(0, 2, 16);
    lean_ctor_set(obj, 0, typ_obj);
    lean_ctor_set(obj, 1, value_obj);
    let base = obj as *mut u8;
    let scalar_base = base.add(2 * 8 + 8); // offset 24

    // lvls at offset 0 (8 bytes) - largest scalar first
    *(scalar_base as *mut u64) = def.lvls;
    // kind at offset 8 (1 byte)
    let kind_val: u8 = match def.kind {
      DefKind::Definition => 0,
      DefKind::Opaque => 1,
      DefKind::Theorem => 2,
    };
    *scalar_base.add(8) = kind_val;
    // safety at offset 9 (1 byte)
    let safety_val: u8 = match def.safety {
      crate::ix::env::DefinitionSafety::Unsafe => 0,
      crate::ix::env::DefinitionSafety::Safe => 1,
      crate::ix::env::DefinitionSafety::Partial => 2,
    };
    *scalar_base.add(9) = safety_val;
    obj
  }
}

/// Build Ixon.RecursorRule
pub fn build_ixon_recursor_rule(rule: &IxonRecursorRule) -> *mut c_void {
  unsafe {
    let rhs_obj = build_ixon_expr(&rule.rhs);
    // 1 obj field, 8 scalar bytes
    let obj = lean_alloc_ctor(0, 1, 8);
    lean_ctor_set(obj, 0, rhs_obj);
    let base = obj as *mut u8;
    *(base.add(8 + 8) as *mut u64) = rule.fields;
    obj
  }
}

/// Build Ixon.Recursor
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
pub fn build_ixon_recursor(rec: &IxonRecursor) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&rec.typ);
    // Build rules array
    let rules_arr = lean_alloc_array(rec.rules.len(), rec.rules.len());
    for (i, rule) in rec.rules.iter().enumerate() {
      let rule_obj = build_ixon_recursor_rule(rule);
      lean_array_set_core(rules_arr, i, rule_obj);
    }
    // 2 obj fields (typ, rules), 48 scalar bytes (5×8 + 1 + 1 + 6 padding)
    let obj = lean_alloc_ctor(0, 2, 48);
    lean_ctor_set(obj, 0, typ_obj);
    lean_ctor_set(obj, 1, rules_arr);
    let base = obj as *mut u8;
    let scalar_base = base.add(2 * 8 + 8);
    // u64 fields first
    *(scalar_base as *mut u64) = rec.lvls;
    *(scalar_base.add(8) as *mut u64) = rec.params;
    *(scalar_base.add(16) as *mut u64) = rec.indices;
    *(scalar_base.add(24) as *mut u64) = rec.motives;
    *(scalar_base.add(32) as *mut u64) = rec.minors;
    // bool fields last
    *scalar_base.add(40) = if rec.k { 1 } else { 0 };
    *scalar_base.add(41) = if rec.is_unsafe { 1 } else { 0 };
    obj
  }
}

/// Build Ixon.Axiom
/// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
pub fn build_ixon_axiom(ax: &IxonAxiom) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&ax.typ);
    // 1 obj field, 16 scalar bytes (lvls(8) + isUnsafe(1) + padding(7))
    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, typ_obj);
    let base = obj as *mut u8;
    let scalar_base = base.add(8 + 8);
    // lvls at offset 0
    *(scalar_base as *mut u64) = ax.lvls;
    // isUnsafe at offset 8
    *scalar_base.add(8) = if ax.is_unsafe { 1 } else { 0 };
    obj
  }
}

/// Build Ixon.Quotient
/// QuotKind is a simple enum stored as scalar u8, not object field.
/// Scalars ordered by size: lvls(8) + kind(1) + padding(7)
pub fn build_ixon_quotient(quot: &IxonQuotient) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&quot.typ);
    // 1 obj field (typ), 16 scalar bytes (lvls(8) + kind(1) + padding(7))
    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, typ_obj);
    let base = obj as *mut u8;
    let scalar_base = base.add(8 + 8);
    // lvls at offset 0
    *(scalar_base as *mut u64) = quot.lvls;
    // kind at offset 8
    let kind_val: u8 = match quot.kind {
      crate::ix::env::QuotKind::Type => 0,
      crate::ix::env::QuotKind::Ctor => 1,
      crate::ix::env::QuotKind::Lift => 2,
      crate::ix::env::QuotKind::Ind => 3,
    };
    *scalar_base.add(8) = kind_val;
    obj
  }
}

/// Build Ixon.Constructor
/// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
pub fn build_ixon_constructor(ctor: &IxonConstructor) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&ctor.typ);
    // 1 obj field, 40 scalar bytes (4×8 + 1 + 7 padding)
    let obj = lean_alloc_ctor(0, 1, 40);
    lean_ctor_set(obj, 0, typ_obj);
    let base = obj as *mut u8;
    let scalar_base = base.add(8 + 8);
    // u64 fields first
    *(scalar_base as *mut u64) = ctor.lvls;
    *(scalar_base.add(8) as *mut u64) = ctor.cidx;
    *(scalar_base.add(16) as *mut u64) = ctor.params;
    *(scalar_base.add(24) as *mut u64) = ctor.fields;
    // bool field last
    *scalar_base.add(32) = if ctor.is_unsafe { 1 } else { 0 };
    obj
  }
}

/// Build Ixon.Inductive
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
pub fn build_ixon_inductive(ind: &IxonInductive) -> *mut c_void {
  unsafe {
    let typ_obj = build_ixon_expr(&ind.typ);
    // Build ctors array
    let ctors_arr = lean_alloc_array(ind.ctors.len(), ind.ctors.len());
    for (i, ctor) in ind.ctors.iter().enumerate() {
      let ctor_obj = build_ixon_constructor(ctor);
      lean_array_set_core(ctors_arr, i, ctor_obj);
    }
    // 2 obj fields, 40 scalar bytes (4×8 + 3 + 5 padding)
    let obj = lean_alloc_ctor(0, 2, 40);
    lean_ctor_set(obj, 0, typ_obj);
    lean_ctor_set(obj, 1, ctors_arr);
    let base = obj as *mut u8;
    let scalar_base = base.add(2 * 8 + 8);
    // u64 fields first
    *(scalar_base as *mut u64) = ind.lvls;
    *(scalar_base.add(8) as *mut u64) = ind.params;
    *(scalar_base.add(16) as *mut u64) = ind.indices;
    *(scalar_base.add(24) as *mut u64) = ind.nested;
    // bool fields last
    *scalar_base.add(32) = if ind.recr { 1 } else { 0 };
    *scalar_base.add(33) = if ind.refl { 1 } else { 0 };
    *scalar_base.add(34) = if ind.is_unsafe { 1 } else { 0 };
    obj
  }
}

/// Build Ixon.InductiveProj
pub fn build_inductive_proj(proj: &InductiveProj) -> *mut c_void {
  unsafe {
    let block_obj = build_address_from_ixon(&proj.block);
    let obj = lean_alloc_ctor(0, 1, 8);
    lean_ctor_set(obj, 0, block_obj);
    let base = obj as *mut u8;
    *(base.add(8 + 8) as *mut u64) = proj.idx;
    obj
  }
}

/// Build Ixon.ConstructorProj
pub fn build_constructor_proj(proj: &ConstructorProj) -> *mut c_void {
  unsafe {
    let block_obj = build_address_from_ixon(&proj.block);
    let obj = lean_alloc_ctor(0, 1, 16);
    lean_ctor_set(obj, 0, block_obj);
    let base = obj as *mut u8;
    *(base.add(8 + 8) as *mut u64) = proj.idx;
    *(base.add(8 + 16) as *mut u64) = proj.cidx;
    obj
  }
}

/// Build Ixon.RecursorProj
pub fn build_recursor_proj(proj: &RecursorProj) -> *mut c_void {
  unsafe {
    let block_obj = build_address_from_ixon(&proj.block);
    let obj = lean_alloc_ctor(0, 1, 8);
    lean_ctor_set(obj, 0, block_obj);
    let base = obj as *mut u8;
    *(base.add(8 + 8) as *mut u64) = proj.idx;
    obj
  }
}

/// Build Ixon.DefinitionProj
pub fn build_definition_proj(proj: &DefinitionProj) -> *mut c_void {
  unsafe {
    let block_obj = build_address_from_ixon(&proj.block);
    let obj = lean_alloc_ctor(0, 1, 8);
    lean_ctor_set(obj, 0, block_obj);
    let base = obj as *mut u8;
    *(base.add(8 + 8) as *mut u64) = proj.idx;
    obj
  }
}

/// Build Ixon.MutConst
pub fn build_mut_const(mc: &MutConst) -> *mut c_void {
  unsafe {
    match mc {
      MutConst::Defn(def) => {
        let def_obj = build_ixon_definition(def);
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, def_obj);
        obj
      }
      MutConst::Indc(ind) => {
        let ind_obj = build_ixon_inductive(ind);
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, ind_obj);
        obj
      }
      MutConst::Recr(rec) => {
        let rec_obj = build_ixon_recursor(rec);
        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, rec_obj);
        obj
      }
    }
  }
}

/// Build Ixon.ConstantInfo (9 constructors)
pub fn build_ixon_constant_info(info: &IxonConstantInfo) -> *mut c_void {
  unsafe {
    match info {
      IxonConstantInfo::Defn(def) => {
        let def_obj = build_ixon_definition(def);
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, def_obj);
        obj
      }
      IxonConstantInfo::Recr(rec) => {
        let rec_obj = build_ixon_recursor(rec);
        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, rec_obj);
        obj
      }
      IxonConstantInfo::Axio(ax) => {
        let ax_obj = build_ixon_axiom(ax);
        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, ax_obj);
        obj
      }
      IxonConstantInfo::Quot(quot) => {
        let quot_obj = build_ixon_quotient(quot);
        let obj = lean_alloc_ctor(3, 1, 0);
        lean_ctor_set(obj, 0, quot_obj);
        obj
      }
      IxonConstantInfo::CPrj(proj) => {
        let proj_obj = build_constructor_proj(proj);
        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, proj_obj);
        obj
      }
      IxonConstantInfo::RPrj(proj) => {
        let proj_obj = build_recursor_proj(proj);
        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, proj_obj);
        obj
      }
      IxonConstantInfo::IPrj(proj) => {
        let proj_obj = build_inductive_proj(proj);
        let obj = lean_alloc_ctor(6, 1, 0);
        lean_ctor_set(obj, 0, proj_obj);
        obj
      }
      IxonConstantInfo::DPrj(proj) => {
        let proj_obj = build_definition_proj(proj);
        let obj = lean_alloc_ctor(7, 1, 0);
        lean_ctor_set(obj, 0, proj_obj);
        obj
      }
      IxonConstantInfo::Muts(muts) => {
        let arr = lean_alloc_array(muts.len(), muts.len());
        for (i, mc) in muts.iter().enumerate() {
          let mc_obj = build_mut_const(mc);
          lean_array_set_core(arr, i, mc_obj);
        }
        let obj = lean_alloc_ctor(8, 1, 0);
        lean_ctor_set(obj, 0, arr);
        obj
      }
    }
  }
}

/// Build Ixon.Constant
pub fn build_ixon_constant(constant: &IxonConstant) -> *mut c_void {
  unsafe {
    let info_obj = build_ixon_constant_info(&constant.info);
    let sharing_obj = build_ixon_expr_array(&constant.sharing);
    let refs_obj = build_address_array(&constant.refs);
    let univs_obj = build_ixon_univ_array(&constant.univs);
    let obj = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(obj, 0, info_obj);
    lean_ctor_set(obj, 1, sharing_obj);
    lean_ctor_set(obj, 2, refs_obj);
    lean_ctor_set(obj, 3, univs_obj);
    obj
  }
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode a ByteArray (Address) to Address.
pub fn decode_ixon_address(ptr: *const c_void) -> Address {
  let ba: &LeanSArrayObject = unsafe { as_ref_unsafe(ptr.cast()) };
  let bytes = ba.data();
  Address::from_slice(&bytes[..32]).expect("Address should be 32 bytes")
}

/// Decode Array Address.
pub fn decode_ixon_address_array(ptr: *const c_void) -> Vec<Address> {
  let arr: &crate::lean::array::LeanArrayObject = unsafe { as_ref_unsafe(ptr.cast()) };
  arr.to_vec(|a| decode_ixon_address(a))
}

/// Decode Ixon.Definition.
/// Lean stores scalar fields ordered by size (largest first).
/// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
pub fn decode_ixon_definition(ptr: *const c_void) -> IxonDefinition {
  unsafe {
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let value_ptr = lean_ctor_get(ptr as *mut _, 1);

    let base = ptr as *const u8;
    // Scalars start after header (8) + 2 obj fields (16) = offset 24
    let scalar_base = base.add(24);

    // lvls at offset 0 (8 bytes) - largest scalar first
    let lvls = *(scalar_base as *const u64);
    // kind at offset 8 (1 byte)
    let kind_val = *scalar_base.add(8);
    let kind = match kind_val {
      0 => DefKind::Definition,
      1 => DefKind::Opaque,
      2 => DefKind::Theorem,
      _ => panic!("Invalid DefKind: {}", kind_val),
    };
    // safety at offset 9 (1 byte)
    let safety_val = *scalar_base.add(9);
    let safety = match safety_val {
      0 => crate::ix::env::DefinitionSafety::Unsafe,
      1 => crate::ix::env::DefinitionSafety::Safe,
      2 => crate::ix::env::DefinitionSafety::Partial,
      _ => panic!("Invalid DefinitionSafety: {}", safety_val),
    };

    IxonDefinition {
      kind,
      safety,
      lvls,
      typ: Arc::new(decode_ixon_expr(typ_ptr)),
      value: Arc::new(decode_ixon_expr(value_ptr)),
    }
  }
}

/// Decode Ixon.RecursorRule.
pub fn decode_ixon_recursor_rule(ptr: *const c_void) -> IxonRecursorRule {
  unsafe {
    let rhs_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let fields = *(base.add(8 + 8) as *const u64);
    IxonRecursorRule { fields, rhs: Arc::new(decode_ixon_expr(rhs_ptr)) }
  }
}

/// Decode Ixon.Recursor.
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
pub fn decode_ixon_recursor(ptr: *const c_void) -> IxonRecursor {
  unsafe {
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let rules_ptr = lean_ctor_get(ptr as *mut _, 1);
    let base = ptr as *const u8;
    let scalar_base = base.add(2 * 8 + 8);
    // u64 fields first
    let lvls = *(scalar_base as *const u64);
    let params = *(scalar_base.add(8) as *const u64);
    let indices = *(scalar_base.add(16) as *const u64);
    let motives = *(scalar_base.add(24) as *const u64);
    let minors = *(scalar_base.add(32) as *const u64);
    // bool fields last
    let k = *scalar_base.add(40) != 0;
    let is_unsafe = *scalar_base.add(41) != 0;

    let rules_arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(rules_ptr.cast());
    let rules = rules_arr.to_vec(|r| decode_ixon_recursor_rule(r));

    IxonRecursor {
      k,
      is_unsafe,
      lvls,
      params,
      indices,
      motives,
      minors,
      typ: Arc::new(decode_ixon_expr(typ_ptr)),
      rules,
    }
  }
}

/// Decode Ixon.Axiom.
/// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
pub fn decode_ixon_axiom(ptr: *const c_void) -> IxonAxiom {
  unsafe {
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let scalar_base = base.add(8 + 8);
    // lvls at offset 0
    let lvls = *(scalar_base as *const u64);
    // isUnsafe at offset 8
    let is_unsafe = *scalar_base.add(8) != 0;
    IxonAxiom { is_unsafe, lvls, typ: Arc::new(decode_ixon_expr(typ_ptr)) }
  }
}

/// Decode Ixon.Quotient.
/// QuotKind is a scalar (not object field). Scalars: lvls(8) + kind(1) + padding(7)
pub fn decode_ixon_quotient(ptr: *const c_void) -> IxonQuotient {
  unsafe {
    // typ is the only object field (at index 0)
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let scalar_base = base.add(8 + 8);
    // lvls at offset 0
    let lvls = *(scalar_base as *const u64);
    // kind at offset 8
    let kind_val = *scalar_base.add(8);
    let kind = match kind_val {
      0 => crate::ix::env::QuotKind::Type,
      1 => crate::ix::env::QuotKind::Ctor,
      2 => crate::ix::env::QuotKind::Lift,
      3 => crate::ix::env::QuotKind::Ind,
      _ => panic!("Invalid QuotKind: {}", kind_val),
    };
    IxonQuotient {
      kind,
      lvls,
      typ: Arc::new(decode_ixon_expr(typ_ptr)),
    }
  }
}

/// Decode Ixon.Constructor.
/// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
pub fn decode_ixon_constructor(ptr: *const c_void) -> IxonConstructor {
  unsafe {
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let scalar_base = base.add(8 + 8);
    // u64 fields first
    let lvls = *(scalar_base as *const u64);
    let cidx = *(scalar_base.add(8) as *const u64);
    let params = *(scalar_base.add(16) as *const u64);
    let fields = *(scalar_base.add(24) as *const u64);
    // bool field last
    let is_unsafe = *scalar_base.add(32) != 0;
    IxonConstructor {
      is_unsafe,
      lvls,
      cidx,
      params,
      fields,
      typ: Arc::new(decode_ixon_expr(typ_ptr)),
    }
  }
}

/// Decode Ixon.Inductive.
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
pub fn decode_ixon_inductive(ptr: *const c_void) -> IxonInductive {
  unsafe {
    let typ_ptr = lean_ctor_get(ptr as *mut _, 0);
    let ctors_ptr = lean_ctor_get(ptr as *mut _, 1);
    let base = ptr as *const u8;
    let scalar_base = base.add(2 * 8 + 8);
    // u64 fields first
    let lvls = *(scalar_base as *const u64);
    let params = *(scalar_base.add(8) as *const u64);
    let indices = *(scalar_base.add(16) as *const u64);
    let nested = *(scalar_base.add(24) as *const u64);
    // bool fields last
    let recr = *scalar_base.add(32) != 0;
    let refl = *scalar_base.add(33) != 0;
    let is_unsafe = *scalar_base.add(34) != 0;

    let ctors_arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(ctors_ptr.cast());
    let ctors = ctors_arr.to_vec(|c| decode_ixon_constructor(c));

    IxonInductive {
      recr,
      refl,
      is_unsafe,
      lvls,
      params,
      indices,
      nested,
      typ: Arc::new(decode_ixon_expr(typ_ptr)),
      ctors,
    }
  }
}

/// Decode Ixon.InductiveProj.
pub fn decode_ixon_inductive_proj(ptr: *const c_void) -> InductiveProj {
  unsafe {
    let block_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let idx = *(base.add(8 + 8) as *const u64);
    InductiveProj { idx, block: decode_ixon_address(block_ptr) }
  }
}

/// Decode Ixon.ConstructorProj.
pub fn decode_ixon_constructor_proj(ptr: *const c_void) -> ConstructorProj {
  unsafe {
    let block_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let idx = *(base.add(8 + 8) as *const u64);
    let cidx = *(base.add(8 + 16) as *const u64);
    ConstructorProj { idx, cidx, block: decode_ixon_address(block_ptr) }
  }
}

/// Decode Ixon.RecursorProj.
pub fn decode_ixon_recursor_proj(ptr: *const c_void) -> RecursorProj {
  unsafe {
    let block_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let idx = *(base.add(8 + 8) as *const u64);
    RecursorProj { idx, block: decode_ixon_address(block_ptr) }
  }
}

/// Decode Ixon.DefinitionProj.
pub fn decode_ixon_definition_proj(ptr: *const c_void) -> DefinitionProj {
  unsafe {
    let block_ptr = lean_ctor_get(ptr as *mut _, 0);
    let base = ptr as *const u8;
    let idx = *(base.add(8 + 8) as *const u64);
    DefinitionProj { idx, block: decode_ixon_address(block_ptr) }
  }
}

/// Decode Ixon.MutConst.
pub fn decode_ixon_mut_const(ptr: *const c_void) -> MutConst {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
    match tag {
      0 => MutConst::Defn(decode_ixon_definition(inner_ptr)),
      1 => MutConst::Indc(decode_ixon_inductive(inner_ptr)),
      2 => MutConst::Recr(decode_ixon_recursor(inner_ptr)),
      _ => panic!("Invalid Ixon.MutConst tag: {}", tag),
    }
  }
}

/// Decode Ixon.ConstantInfo.
pub fn decode_ixon_constant_info(ptr: *const c_void) -> IxonConstantInfo {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let inner_ptr = lean_ctor_get(ptr as *mut _, 0);
    match tag {
      0 => IxonConstantInfo::Defn(decode_ixon_definition(inner_ptr)),
      1 => IxonConstantInfo::Recr(decode_ixon_recursor(inner_ptr)),
      2 => IxonConstantInfo::Axio(decode_ixon_axiom(inner_ptr)),
      3 => IxonConstantInfo::Quot(decode_ixon_quotient(inner_ptr)),
      4 => IxonConstantInfo::CPrj(decode_ixon_constructor_proj(inner_ptr)),
      5 => IxonConstantInfo::RPrj(decode_ixon_recursor_proj(inner_ptr)),
      6 => IxonConstantInfo::IPrj(decode_ixon_inductive_proj(inner_ptr)),
      7 => IxonConstantInfo::DPrj(decode_ixon_definition_proj(inner_ptr)),
      8 => {
        let muts_arr: &crate::lean::array::LeanArrayObject = as_ref_unsafe(inner_ptr.cast());
        let muts = muts_arr.to_vec(|m| decode_ixon_mut_const(m));
        IxonConstantInfo::Muts(muts)
      }
      _ => panic!("Invalid Ixon.ConstantInfo tag: {}", tag),
    }
  }
}

/// Decode Ixon.Constant.
pub fn decode_ixon_constant(ptr: *const c_void) -> IxonConstant {
  unsafe {
    let info_ptr = lean_ctor_get(ptr as *mut _, 0);
    let sharing_ptr = lean_ctor_get(ptr as *mut _, 1);
    let refs_ptr = lean_ctor_get(ptr as *mut _, 2);
    let univs_ptr = lean_ctor_get(ptr as *mut _, 3);

    IxonConstant {
      info: decode_ixon_constant_info(info_ptr),
      sharing: decode_ixon_expr_array(sharing_ptr),
      refs: decode_ixon_address_array(refs_ptr),
      univs: decode_ixon_univ_array(univs_ptr),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Definition.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition(ptr: *const c_void) -> *mut c_void {
  let def = decode_ixon_definition(ptr);
  build_ixon_definition(&def)
}

/// Round-trip Ixon.Recursor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor(ptr: *const c_void) -> *mut c_void {
  let rec = decode_ixon_recursor(ptr);
  build_ixon_recursor(&rec)
}

/// Round-trip Ixon.Axiom.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_axiom(ptr: *const c_void) -> *mut c_void {
  let ax = decode_ixon_axiom(ptr);
  build_ixon_axiom(&ax)
}

/// Round-trip Ixon.Quotient.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quotient(ptr: *const c_void) -> *mut c_void {
  let quot = decode_ixon_quotient(ptr);
  build_ixon_quotient(&quot)
}

/// Round-trip Ixon.ConstantInfo.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_info(ptr: *const c_void) -> *mut c_void {
  let info = decode_ixon_constant_info(ptr);
  build_ixon_constant_info(&info)
}

/// Round-trip Ixon.Constant.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant(ptr: *const c_void) -> *mut c_void {
  let constant = decode_ixon_constant(ptr);
  build_ixon_constant(&constant)
}

/// Round-trip Ixon.RecursorRule.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_rule(ptr: *const c_void) -> *mut c_void {
  let rule = decode_ixon_recursor_rule(ptr);
  build_ixon_recursor_rule(&rule)
}

/// Round-trip Ixon.Constructor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor(ptr: *const c_void) -> *mut c_void {
  let ctor = decode_ixon_constructor(ptr);
  build_ixon_constructor(&ctor)
}

/// Round-trip Ixon.Inductive.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive(ptr: *const c_void) -> *mut c_void {
  let ind = decode_ixon_inductive(ptr);
  build_ixon_inductive(&ind)
}

/// Round-trip Ixon.InductiveProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive_proj(ptr: *const c_void) -> *mut c_void {
  let proj = decode_ixon_inductive_proj(ptr);
  build_inductive_proj(&proj)
}

/// Round-trip Ixon.ConstructorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor_proj(ptr: *const c_void) -> *mut c_void {
  let proj = decode_ixon_constructor_proj(ptr);
  build_constructor_proj(&proj)
}

/// Round-trip Ixon.RecursorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_proj(ptr: *const c_void) -> *mut c_void {
  let proj = decode_ixon_recursor_proj(ptr);
  build_recursor_proj(&proj)
}

/// Round-trip Ixon.DefinitionProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_proj(ptr: *const c_void) -> *mut c_void {
  let proj = decode_ixon_definition_proj(ptr);
  build_definition_proj(&proj)
}

/// Round-trip Ixon.MutConst.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_mut_const(ptr: *const c_void) -> *mut c_void {
  let mc = decode_ixon_mut_const(ptr);
  build_mut_const(&mc)
}
