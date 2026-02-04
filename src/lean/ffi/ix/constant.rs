//! Ix.ConstantInfo build/decode/roundtrip FFI.
//!
//! ConstantInfo variants:
//! - Tag 0: axiomInfo (v : AxiomVal)
//! - Tag 1: defnInfo (v : DefinitionVal)
//! - Tag 2: thmInfo (v : TheoremVal)
//! - Tag 3: opaqueInfo (v : OpaqueVal)
//! - Tag 4: quotInfo (v : QuotVal)
//! - Tag 5: inductInfo (v : InductiveVal)
//! - Tag 6: ctorInfo (v : ConstructorVal)
//! - Tag 7: recInfo (v : RecursorVal)

use std::ffi::c_void;

use crate::ix::env::{
  AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety,
  DefinitionVal, InductiveVal, Name, OpaqueVal, QuotKind, QuotVal,
  RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
};
use crate::lean::array::LeanArrayObject;
use crate::lean::nat::Nat;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core,
  lean_box_fn, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8,
  lean_is_scalar, lean_obj_tag,
};

use super::super::builder::LeanBuildCache;
use super::super::primitives::build_nat;
use super::expr::{build_expr, decode_ix_expr};
use super::name::{
  build_name, build_name_array, decode_ix_name, decode_name_array,
};

/// Build a Ix.ConstantVal structure.
pub fn build_constant_val(
  cache: &mut LeanBuildCache,
  cv: &ConstantVal,
) -> *mut c_void {
  unsafe {
    // ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
    let name_obj = build_name(cache, &cv.name);
    let level_params_obj = build_name_array(cache, &cv.level_params);
    let type_obj = build_expr(cache, &cv.typ);

    let obj = lean_alloc_ctor(0, 3, 0);
    lean_ctor_set(obj, 0, name_obj);
    lean_ctor_set(obj, 1, level_params_obj);
    lean_ctor_set(obj, 2, type_obj);
    obj
  }
}

/// Build ReducibilityHints.
/// NOTE: In Lean 4, 0-field constructors are boxed scalars when the inductive has
/// other constructors with fields. So opaque and abbrev use lean_box_fn.
pub fn build_reducibility_hints(hints: &ReducibilityHints) -> *mut c_void {
  unsafe {
    match hints {
      // | opaque -- tag 0, boxed as scalar
      ReducibilityHints::Opaque => lean_box_fn(0),
      // | abbrev -- tag 1, boxed as scalar
      ReducibilityHints::Abbrev => lean_box_fn(1),
      // | regular (h : UInt32) -- tag 2, object constructor
      ReducibilityHints::Regular(h) => {
        // UInt32 is a scalar, stored inline
        let obj = lean_alloc_ctor(2, 0, 4);
        // Set the uint32 at offset 0 in the scalar area
        let ptr = obj.cast::<u8>();
        *(ptr.add(8).cast::<u32>()) = *h;
        obj
      },
    }
  }
}

/// Build a Ix.ConstantInfo from a Rust ConstantInfo.
pub fn build_constant_info(
  cache: &mut LeanBuildCache,
  info: &ConstantInfo,
) -> *mut c_void {
  unsafe {
    match info {
      // | axiomInfo (v : AxiomVal) -- tag 0
      ConstantInfo::AxiomInfo(v) => {
        // AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let axiom_val = lean_alloc_ctor(0, 1, 1);
        lean_ctor_set(axiom_val, 0, cnst_obj);
        lean_ctor_set_uint8(axiom_val, 8, v.is_unsafe as u8);

        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, axiom_val);
        obj
      },
      // | defnInfo (v : DefinitionVal) -- tag 1
      ConstantInfo::DefnInfo(v) => {
        // DefinitionVal = { cnst, value, hints, safety, all }
        // NOTE: safety (DefinitionSafety) is a small enum stored as SCALAR
        // Memory layout: 4 obj fields (cnst, value, hints, all), 1 scalar byte (safety)
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let value_obj = build_expr(cache, &v.value);
        let hints_obj = build_reducibility_hints(&v.hints);
        let all_obj = build_name_array(cache, &v.all);
        let safety_byte = match v.safety {
          DefinitionSafety::Unsafe => 0u8,
          DefinitionSafety::Safe => 1u8,
          DefinitionSafety::Partial => 2u8,
        };

        let defn_val = lean_alloc_ctor(0, 4, 1); // 4 obj fields, 1 scalar byte
        lean_ctor_set(defn_val, 0, cnst_obj);
        lean_ctor_set(defn_val, 1, value_obj);
        lean_ctor_set(defn_val, 2, hints_obj);
        lean_ctor_set(defn_val, 3, all_obj);
        lean_ctor_set_uint8(defn_val, 4 * 8, safety_byte);

        let obj = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(obj, 0, defn_val);
        obj
      },
      // | thmInfo (v : TheoremVal) -- tag 2
      ConstantInfo::ThmInfo(v) => {
        // TheoremVal = { cnst, value, all }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let value_obj = build_expr(cache, &v.value);
        let all_obj = build_name_array(cache, &v.all);

        let thm_val = lean_alloc_ctor(0, 3, 0);
        lean_ctor_set(thm_val, 0, cnst_obj);
        lean_ctor_set(thm_val, 1, value_obj);
        lean_ctor_set(thm_val, 2, all_obj);

        let obj = lean_alloc_ctor(2, 1, 0);
        lean_ctor_set(obj, 0, thm_val);
        obj
      },
      // | opaqueInfo (v : OpaqueVal) -- tag 3
      ConstantInfo::OpaqueInfo(v) => {
        // OpaqueVal = { cnst, value, isUnsafe, all }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let value_obj = build_expr(cache, &v.value);
        let all_obj = build_name_array(cache, &v.all);

        let opaque_val = lean_alloc_ctor(0, 3, 1);
        lean_ctor_set(opaque_val, 0, cnst_obj);
        lean_ctor_set(opaque_val, 1, value_obj);
        lean_ctor_set(opaque_val, 2, all_obj);
        lean_ctor_set_uint8(opaque_val, 3 * 8, v.is_unsafe as u8);

        let obj = lean_alloc_ctor(3, 1, 0);
        lean_ctor_set(obj, 0, opaque_val);
        obj
      },
      // | quotInfo (v : QuotVal) -- tag 4
      ConstantInfo::QuotInfo(v) => {
        // QuotVal = { cnst, kind }
        // NOTE: QuotKind is a small enum stored as SCALAR
        // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let kind_byte = match v.kind {
          QuotKind::Type => 0u8,
          QuotKind::Ctor => 1u8,
          QuotKind::Lift => 2u8,
          QuotKind::Ind => 3u8,
        };

        let quot_val = lean_alloc_ctor(0, 1, 1); // 1 obj field, 1 scalar byte
        lean_ctor_set(quot_val, 0, cnst_obj);
        lean_ctor_set_uint8(quot_val, 8, kind_byte);

        let obj = lean_alloc_ctor(4, 1, 0);
        lean_ctor_set(obj, 0, quot_val);
        obj
      },
      // | inductInfo (v : InductiveVal) -- tag 5
      ConstantInfo::InductInfo(v) => {
        // InductiveVal = { cnst, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let num_params_obj = build_nat(&v.num_params);
        let num_indices_obj = build_nat(&v.num_indices);
        let all_obj = build_name_array(cache, &v.all);
        let ctors_obj = build_name_array(cache, &v.ctors);
        let num_nested_obj = build_nat(&v.num_nested);

        // 6 object fields, 3 scalar bytes for bools
        let induct_val = lean_alloc_ctor(0, 6, 3);
        lean_ctor_set(induct_val, 0, cnst_obj);
        lean_ctor_set(induct_val, 1, num_params_obj);
        lean_ctor_set(induct_val, 2, num_indices_obj);
        lean_ctor_set(induct_val, 3, all_obj);
        lean_ctor_set(induct_val, 4, ctors_obj);
        lean_ctor_set(induct_val, 5, num_nested_obj);
        lean_ctor_set_uint8(induct_val, 6 * 8, v.is_rec as u8);
        lean_ctor_set_uint8(induct_val, 6 * 8 + 1, v.is_unsafe as u8);
        lean_ctor_set_uint8(induct_val, 6 * 8 + 2, v.is_reflexive as u8);

        let obj = lean_alloc_ctor(5, 1, 0);
        lean_ctor_set(obj, 0, induct_val);
        obj
      },
      // | ctorInfo (v : ConstructorVal) -- tag 6
      ConstantInfo::CtorInfo(v) => {
        // ConstructorVal = { cnst, induct, cidx, numParams, numFields, isUnsafe }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let induct_obj = build_name(cache, &v.induct);
        let cidx_obj = build_nat(&v.cidx);
        let num_params_obj = build_nat(&v.num_params);
        let num_fields_obj = build_nat(&v.num_fields);

        // 5 object fields, 1 scalar byte for bool
        let ctor_val = lean_alloc_ctor(0, 5, 1);
        lean_ctor_set(ctor_val, 0, cnst_obj);
        lean_ctor_set(ctor_val, 1, induct_obj);
        lean_ctor_set(ctor_val, 2, cidx_obj);
        lean_ctor_set(ctor_val, 3, num_params_obj);
        lean_ctor_set(ctor_val, 4, num_fields_obj);
        lean_ctor_set_uint8(ctor_val, 5 * 8, v.is_unsafe as u8);

        let obj = lean_alloc_ctor(6, 1, 0);
        lean_ctor_set(obj, 0, ctor_val);
        obj
      },
      // | recInfo (v : RecursorVal) -- tag 7
      ConstantInfo::RecInfo(v) => {
        // RecursorVal = { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
        let cnst_obj = build_constant_val(cache, &v.cnst);
        let all_obj = build_name_array(cache, &v.all);
        let num_params_obj = build_nat(&v.num_params);
        let num_indices_obj = build_nat(&v.num_indices);
        let num_motives_obj = build_nat(&v.num_motives);
        let num_minors_obj = build_nat(&v.num_minors);
        let rules_obj = build_recursor_rules(cache, &v.rules);

        // 7 object fields, 2 scalar bytes for bools
        let rec_val = lean_alloc_ctor(0, 7, 2);
        lean_ctor_set(rec_val, 0, cnst_obj);
        lean_ctor_set(rec_val, 1, all_obj);
        lean_ctor_set(rec_val, 2, num_params_obj);
        lean_ctor_set(rec_val, 3, num_indices_obj);
        lean_ctor_set(rec_val, 4, num_motives_obj);
        lean_ctor_set(rec_val, 5, num_minors_obj);
        lean_ctor_set(rec_val, 6, rules_obj);
        lean_ctor_set_uint8(rec_val, 7 * 8, v.k as u8);
        lean_ctor_set_uint8(rec_val, 7 * 8 + 1, v.is_unsafe as u8);

        let obj = lean_alloc_ctor(7, 1, 0);
        lean_ctor_set(obj, 0, rec_val);
        obj
      },
    }
  }
}

/// Build an Array of RecursorRule.
fn build_recursor_rules(
  cache: &mut LeanBuildCache,
  rules: &[RecursorRule],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(rules.len(), rules.len());
    for (i, rule) in rules.iter().enumerate() {
      // RecursorRule = { ctor : Name, nFields : Nat, rhs : Expr }
      let ctor_obj = build_name(cache, &rule.ctor);
      let n_fields_obj = build_nat(&rule.n_fields);
      let rhs_obj = build_expr(cache, &rule.rhs);

      let rule_obj = lean_alloc_ctor(0, 3, 0);
      lean_ctor_set(rule_obj, 0, ctor_obj);
      lean_ctor_set(rule_obj, 1, n_fields_obj);
      lean_ctor_set(rule_obj, 2, rhs_obj);

      lean_array_set_core(arr, i, rule_obj);
    }
    arr
  }
}

// =============================================================================
// ConstantInfo Decoders
// =============================================================================

/// Decode Ix.ConstantVal from Lean pointer.
/// ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
pub fn decode_constant_val(ptr: *const c_void) -> ConstantVal {
  unsafe {
    let name_ptr = lean_ctor_get(ptr as *mut _, 0);
    let level_params_ptr = lean_ctor_get(ptr as *mut _, 1);
    let type_ptr = lean_ctor_get(ptr as *mut _, 2);

    let name = decode_ix_name(name_ptr);

    let level_params_obj: &LeanArrayObject =
      as_ref_unsafe(level_params_ptr.cast());
    let level_params: Vec<Name> =
      level_params_obj.data().iter().map(|&p| decode_ix_name(p)).collect();

    let typ = decode_ix_expr(type_ptr);

    ConstantVal { name, level_params, typ }
  }
}

/// Decode Lean.ReducibilityHints from Lean pointer.
/// | opaque -- tag 0
/// | abbrev -- tag 1
/// | regular (h : UInt32) -- tag 2
///
/// NOTE: In Lean 4, boxed scalars are `(tag << 1) | 1`:
/// - opaque (tag 0) → scalar value 1
/// - abbrev (tag 1) → scalar value 3
pub fn decode_reducibility_hints(ptr: *const c_void) -> ReducibilityHints {
  unsafe {
    if lean_is_scalar(ptr) {
      // Unbox the scalar: tag = (ptr >> 1)
      let tag = (ptr as usize) >> 1;
      match tag {
        0 => return ReducibilityHints::Opaque,
        1 => return ReducibilityHints::Abbrev,
        _ => panic!("Invalid ReducibilityHints scalar tag: {}", tag),
      }
    }

    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => ReducibilityHints::Opaque,
      1 => ReducibilityHints::Abbrev,
      2 => {
        // regular: 0 obj fields, 4 scalar bytes (UInt32)
        let ctor_ptr = ptr.cast::<u8>();
        let h = *(ctor_ptr.add(8).cast::<u32>());
        ReducibilityHints::Regular(h)
      },
      _ => panic!("Invalid ReducibilityHints tag: {}", tag),
    }
  }
}

/// Decode Ix.RecursorRule from Lean pointer.
/// RecursorRule = { ctor : Name, nfields : Nat, rhs : Expr }
fn decode_recursor_rule(ptr: *const c_void) -> RecursorRule {
  unsafe {
    let ctor_ptr = lean_ctor_get(ptr as *mut _, 0);
    let n_fields_ptr = lean_ctor_get(ptr as *mut _, 1);
    let rhs_ptr = lean_ctor_get(ptr as *mut _, 2);

    RecursorRule {
      ctor: decode_ix_name(ctor_ptr),
      n_fields: Nat::from_ptr(n_fields_ptr),
      rhs: decode_ix_expr(rhs_ptr),
    }
  }
}

/// Decode Ix.ConstantInfo from Lean pointer.
pub fn decode_constant_info(ptr: *const c_void) -> ConstantInfo {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    let inner_ptr = lean_ctor_get(ptr as *mut _, 0);

    match tag {
      0 => {
        // axiomInfo: AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
        // Structure: 1 obj field (cnst), 1 scalar byte (isUnsafe)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(1, 0) != 0;

        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: decode_constant_val(cnst_ptr),
          is_unsafe,
        })
      },
      1 => {
        // defnInfo: DefinitionVal = { cnst, value, hints, safety, all }
        // NOTE: safety (DefinitionSafety) is a small enum and is stored as a SCALAR field
        // Memory layout: 4 obj fields (cnst, value, hints, all), 1 scalar byte (safety)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let hints_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 3); // all is at index 3, not 4!

        // safety is a scalar at offset 4*8 = 32 bytes from start of object fields
        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let safety_byte = ctor.get_scalar_u8(4, 0); // 4 obj fields, offset 0 in scalar area
        let safety = match safety_byte {
          0 => DefinitionSafety::Unsafe,
          1 => DefinitionSafety::Safe,
          2 => DefinitionSafety::Partial,
          _ => panic!("Invalid DefinitionSafety: {}", safety_byte),
        };

        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          hints: decode_reducibility_hints(hints_ptr),
          safety,
          all: decode_name_array(all_ptr),
        })
      },
      2 => {
        // thmInfo: TheoremVal = { cnst, value, all }
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 2);

        ConstantInfo::ThmInfo(TheoremVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          all: decode_name_array(all_ptr),
        })
      },
      3 => {
        // opaqueInfo: OpaqueVal = { cnst, value, isUnsafe, all }
        // Structure: 3 obj fields (cnst, value, all), 1 scalar byte (isUnsafe)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let value_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(3, 0) != 0;

        ConstantInfo::OpaqueInfo(OpaqueVal {
          cnst: decode_constant_val(cnst_ptr),
          value: decode_ix_expr(value_ptr),
          is_unsafe,
          all: decode_name_array(all_ptr),
        })
      },
      4 => {
        // quotInfo: QuotVal = { cnst, kind }
        // NOTE: QuotKind is a small enum (4 0-field ctors), stored as SCALAR
        // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let kind_byte = ctor.get_scalar_u8(1, 0); // 1 obj field, offset 0 in scalar area
        let kind = match kind_byte {
          0 => QuotKind::Type,
          1 => QuotKind::Ctor,
          2 => QuotKind::Lift,
          3 => QuotKind::Ind,
          _ => panic!("Invalid QuotKind: {}", kind_byte),
        };

        ConstantInfo::QuotInfo(QuotVal {
          cnst: decode_constant_val(cnst_ptr),
          kind,
        })
      },
      5 => {
        // inductInfo: InductiveVal = { cnst, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }
        // 6 obj fields, 3 scalar bytes
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let num_indices_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let ctors_ptr = lean_ctor_get(inner_ptr as *mut _, 4);
        let num_nested_ptr = lean_ctor_get(inner_ptr as *mut _, 5);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let is_rec = ctor.get_scalar_u8(6, 0) != 0;
        let is_unsafe = ctor.get_scalar_u8(6, 1) != 0;
        let is_reflexive = ctor.get_scalar_u8(6, 2) != 0;

        ConstantInfo::InductInfo(InductiveVal {
          cnst: decode_constant_val(cnst_ptr),
          num_params: Nat::from_ptr(num_params_ptr),
          num_indices: Nat::from_ptr(num_indices_ptr),
          all: decode_name_array(all_ptr),
          ctors: decode_name_array(ctors_ptr),
          num_nested: Nat::from_ptr(num_nested_ptr),
          is_rec,
          is_unsafe,
          is_reflexive,
        })
      },
      6 => {
        // ctorInfo: ConstructorVal = { cnst, induct, cidx, numParams, numFields, isUnsafe }
        // 5 obj fields, 1 scalar byte
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let induct_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let cidx_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let num_fields_ptr = lean_ctor_get(inner_ptr as *mut _, 4);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let is_unsafe = ctor.get_scalar_u8(5, 0) != 0;

        ConstantInfo::CtorInfo(ConstructorVal {
          cnst: decode_constant_val(cnst_ptr),
          induct: decode_ix_name(induct_ptr),
          cidx: Nat::from_ptr(cidx_ptr),
          num_params: Nat::from_ptr(num_params_ptr),
          num_fields: Nat::from_ptr(num_fields_ptr),
          is_unsafe,
        })
      },
      7 => {
        // recInfo: RecursorVal = { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
        // 7 obj fields, 2 scalar bytes
        let cnst_ptr = lean_ctor_get(inner_ptr as *mut _, 0);
        let all_ptr = lean_ctor_get(inner_ptr as *mut _, 1);
        let num_params_ptr = lean_ctor_get(inner_ptr as *mut _, 2);
        let num_indices_ptr = lean_ctor_get(inner_ptr as *mut _, 3);
        let num_motives_ptr = lean_ctor_get(inner_ptr as *mut _, 4);
        let num_minors_ptr = lean_ctor_get(inner_ptr as *mut _, 5);
        let rules_ptr = lean_ctor_get(inner_ptr as *mut _, 6);

        let ctor: &crate::lean::ctor::LeanCtorObject =
          as_ref_unsafe(inner_ptr.cast());
        let k = ctor.get_scalar_u8(7, 0) != 0;
        let is_unsafe = ctor.get_scalar_u8(7, 1) != 0;

        let rules_obj: &LeanArrayObject = as_ref_unsafe(rules_ptr.cast());
        let rules: Vec<RecursorRule> =
          rules_obj.data().iter().map(|&p| decode_recursor_rule(p)).collect();

        ConstantInfo::RecInfo(RecursorVal {
          cnst: decode_constant_val(cnst_ptr),
          all: decode_name_array(all_ptr),
          num_params: Nat::from_ptr(num_params_ptr),
          num_indices: Nat::from_ptr(num_indices_ptr),
          num_motives: Nat::from_ptr(num_motives_ptr),
          num_minors: Nat::from_ptr(num_minors_ptr),
          rules,
          k,
          is_unsafe,
        })
      },
      _ => panic!("Invalid ConstantInfo tag: {}", tag),
    }
  }
}

/// Round-trip an Ix.ConstantInfo: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_constant_info(
  info_ptr: *const c_void,
) -> *mut c_void {
  let info = decode_constant_info(info_ptr);
  let mut cache = LeanBuildCache::new();
  build_constant_info(&mut cache, &info)
}
