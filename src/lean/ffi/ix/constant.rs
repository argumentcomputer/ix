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

use crate::ix::env::{
  AxiomVal, ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety,
  DefinitionVal, InductiveVal, Name, OpaqueVal, QuotKind, QuotVal,
  RecursorRule, RecursorVal, ReducibilityHints, TheoremVal,
};
use crate::lean::nat::Nat;
use crate::lean::object::{LeanIxConstantInfo, LeanArray, LeanCtor, LeanObject};

use crate::lean::ffi::builder::LeanBuildCache;
use crate::lean::ffi::ix::expr::{build_expr, decode_ix_expr};
use crate::lean::ffi::ix::name::{
  build_name, build_name_array, decode_ix_name, decode_name_array,
};
use crate::lean::ffi::primitives::build_nat;

/// Build a Ix.ConstantVal structure.
pub fn build_constant_val(
  cache: &mut LeanBuildCache,
  cv: &ConstantVal,
) -> LeanObject {
  // ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
  let name_obj = build_name(cache, &cv.name);
  let level_params_obj = build_name_array(cache, &cv.level_params);
  let type_obj = build_expr(cache, &cv.typ);

  let obj = LeanCtor::alloc(0, 3, 0);
  obj.set(0, name_obj);
  obj.set(1, level_params_obj);
  obj.set(2, type_obj);
  *obj
}

/// Build ReducibilityHints.
/// NOTE: In Lean 4, 0-field constructors are boxed scalars when the inductive has
/// other constructors with fields. So opaque and abbrev use box_usize.
pub fn build_reducibility_hints(hints: &ReducibilityHints) -> LeanObject {
  match hints {
    // | opaque -- tag 0, boxed as scalar
    ReducibilityHints::Opaque => LeanObject::box_usize(0),
    // | abbrev -- tag 1, boxed as scalar
    ReducibilityHints::Abbrev => LeanObject::box_usize(1),
    // | regular (h : UInt32) -- tag 2, object constructor
    ReducibilityHints::Regular(h) => {
      // UInt32 is a scalar, stored inline
      let obj = LeanCtor::alloc(2, 0, 4);
      // Set the uint32 at offset 0 in the scalar area
      unsafe {
        let ptr = obj.as_ptr().cast::<u8>();
        *(ptr.add(8).cast::<u32>().cast_mut()) = *h;
      }
      *obj
    },
  }
}

/// Build a Ix.ConstantInfo from a Rust ConstantInfo.
pub fn build_constant_info(
  cache: &mut LeanBuildCache,
  info: &ConstantInfo,
) -> LeanIxConstantInfo {
  let result = match info {
    // | axiomInfo (v : AxiomVal) -- tag 0
    ConstantInfo::AxiomInfo(v) => {
      // AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
      let cnst_obj = build_constant_val(cache, &v.cnst);
      let axiom_val = LeanCtor::alloc(0, 1, 1);
      axiom_val.set(0, cnst_obj);
      axiom_val.set_u8(8, v.is_unsafe as u8);

      let obj = LeanCtor::alloc(0, 1, 0);
      obj.set(0, axiom_val);
      *obj
    },
    // | defnInfo (v : DefinitionVal) -- tag 1
    ConstantInfo::DefnInfo(v) => {
      // DefinitionVal = { cnst, value, hints, safety, all }
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

      let defn_val = LeanCtor::alloc(0, 4, 1);
      defn_val.set(0, cnst_obj);
      defn_val.set(1, value_obj);
      defn_val.set(2, hints_obj);
      defn_val.set(3, all_obj);
      defn_val.set_u8(4 * 8, safety_byte);

      let obj = LeanCtor::alloc(1, 1, 0);
      obj.set(0, defn_val);
      *obj
    },
    // | thmInfo (v : TheoremVal) -- tag 2
    ConstantInfo::ThmInfo(v) => {
      // TheoremVal = { cnst, value, all }
      let cnst_obj = build_constant_val(cache, &v.cnst);
      let value_obj = build_expr(cache, &v.value);
      let all_obj = build_name_array(cache, &v.all);

      let thm_val = LeanCtor::alloc(0, 3, 0);
      thm_val.set(0, cnst_obj);
      thm_val.set(1, value_obj);
      thm_val.set(2, all_obj);

      let obj = LeanCtor::alloc(2, 1, 0);
      obj.set(0, thm_val);
      *obj
    },
    // | opaqueInfo (v : OpaqueVal) -- tag 3
    ConstantInfo::OpaqueInfo(v) => {
      // OpaqueVal = { cnst, value, isUnsafe, all }
      let cnst_obj = build_constant_val(cache, &v.cnst);
      let value_obj = build_expr(cache, &v.value);
      let all_obj = build_name_array(cache, &v.all);

      let opaque_val = LeanCtor::alloc(0, 3, 1);
      opaque_val.set(0, cnst_obj);
      opaque_val.set(1, value_obj);
      opaque_val.set(2, all_obj);
      opaque_val.set_u8(3 * 8, v.is_unsafe as u8);

      let obj = LeanCtor::alloc(3, 1, 0);
      obj.set(0, opaque_val);
      *obj
    },
    // | quotInfo (v : QuotVal) -- tag 4
    ConstantInfo::QuotInfo(v) => {
      // QuotVal = { cnst, kind }
      // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
      let cnst_obj = build_constant_val(cache, &v.cnst);
      let kind_byte = match v.kind {
        QuotKind::Type => 0u8,
        QuotKind::Ctor => 1u8,
        QuotKind::Lift => 2u8,
        QuotKind::Ind => 3u8,
      };

      let quot_val = LeanCtor::alloc(0, 1, 1);
      quot_val.set(0, cnst_obj);
      quot_val.set_u8(8, kind_byte);

      let obj = LeanCtor::alloc(4, 1, 0);
      obj.set(0, quot_val);
      *obj
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
      let induct_val = LeanCtor::alloc(0, 6, 3);
      induct_val.set(0, cnst_obj);
      induct_val.set(1, num_params_obj);
      induct_val.set(2, num_indices_obj);
      induct_val.set(3, all_obj);
      induct_val.set(4, ctors_obj);
      induct_val.set(5, num_nested_obj);
      induct_val.set_u8(6 * 8, v.is_rec as u8);
      induct_val.set_u8(6 * 8 + 1, v.is_unsafe as u8);
      induct_val.set_u8(6 * 8 + 2, v.is_reflexive as u8);

      let obj = LeanCtor::alloc(5, 1, 0);
      obj.set(0, induct_val);
      *obj
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
      let ctor_val = LeanCtor::alloc(0, 5, 1);
      ctor_val.set(0, cnst_obj);
      ctor_val.set(1, induct_obj);
      ctor_val.set(2, cidx_obj);
      ctor_val.set(3, num_params_obj);
      ctor_val.set(4, num_fields_obj);
      ctor_val.set_u8(5 * 8, v.is_unsafe as u8);

      let obj = LeanCtor::alloc(6, 1, 0);
      obj.set(0, ctor_val);
      *obj
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
      let rec_val = LeanCtor::alloc(0, 7, 2);
      rec_val.set(0, cnst_obj);
      rec_val.set(1, all_obj);
      rec_val.set(2, num_params_obj);
      rec_val.set(3, num_indices_obj);
      rec_val.set(4, num_motives_obj);
      rec_val.set(5, num_minors_obj);
      rec_val.set(6, rules_obj);
      rec_val.set_u8(7 * 8, v.k as u8);
      rec_val.set_u8(7 * 8 + 1, v.is_unsafe as u8);

      let obj = LeanCtor::alloc(7, 1, 0);
      obj.set(0, rec_val);
      *obj
    },
  };

  LeanIxConstantInfo::new(result)
}

/// Build an Array of RecursorRule.
fn build_recursor_rules(
  cache: &mut LeanBuildCache,
  rules: &[RecursorRule],
) -> LeanArray {
  let arr = LeanArray::alloc(rules.len());
  for (i, rule) in rules.iter().enumerate() {
    // RecursorRule = { ctor : Name, nFields : Nat, rhs : Expr }
    let ctor_obj = build_name(cache, &rule.ctor);
    let n_fields_obj = build_nat(&rule.n_fields);
    let rhs_obj = build_expr(cache, &rule.rhs);

    let rule_obj = LeanCtor::alloc(0, 3, 0);
    rule_obj.set(0, ctor_obj);
    rule_obj.set(1, n_fields_obj);
    rule_obj.set(2, rhs_obj);

    arr.set(i, rule_obj);
  }
  arr
}

// =============================================================================
// ConstantInfo Decoders
// =============================================================================

/// Decode Ix.ConstantVal from Lean object.
/// ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
pub fn decode_constant_val(obj: LeanObject) -> ConstantVal {
  let ctor = obj.as_ctor();
  let name = decode_ix_name(ctor.get(0));
  let level_params: Vec<Name> = ctor.get(1).as_array().map(decode_ix_name);
  let typ = decode_ix_expr(ctor.get(2));

  ConstantVal { name, level_params, typ }
}

/// Decode Lean.ReducibilityHints from Lean object.
pub fn decode_reducibility_hints(obj: LeanObject) -> ReducibilityHints {
  if obj.is_scalar() {
    let tag = obj.as_ptr() as usize >> 1;
    match tag {
      0 => return ReducibilityHints::Opaque,
      1 => return ReducibilityHints::Abbrev,
      _ => panic!("Invalid ReducibilityHints scalar tag: {}", tag),
    }
  }

  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => ReducibilityHints::Opaque,
    1 => ReducibilityHints::Abbrev,
    2 => {
      // regular: 0 obj fields, 4 scalar bytes (UInt32)
      let h = unsafe { *(obj.as_ptr().cast::<u8>().add(8).cast::<u32>()) };
      ReducibilityHints::Regular(h)
    },
    _ => panic!("Invalid ReducibilityHints tag: {}", ctor.tag()),
  }
}

/// Decode Ix.RecursorRule from Lean object.
fn decode_recursor_rule(obj: LeanObject) -> RecursorRule {
  let ctor = obj.as_ctor();
  RecursorRule {
    ctor: decode_ix_name(ctor.get(0)),
    n_fields: Nat::from_obj(ctor.get(1)),
    rhs: decode_ix_expr(ctor.get(2)),
  }
}

/// Decode Ix.ConstantInfo from Lean object.
pub fn decode_constant_info(obj: LeanObject) -> ConstantInfo {
  let outer = obj.as_ctor();
  let inner_obj = outer.get(0);
  let inner = inner_obj.as_ctor();

  match outer.tag() {
    0 => {
      let is_unsafe = inner.scalar_u8(1, 0) != 0;

      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: decode_constant_val(inner.get(0)),
        is_unsafe,
      })
    },
    1 => {
      let safety_byte = inner.scalar_u8(4, 0);
      let safety = match safety_byte {
        0 => DefinitionSafety::Unsafe,
        1 => DefinitionSafety::Safe,
        2 => DefinitionSafety::Partial,
        _ => panic!("Invalid DefinitionSafety: {}", safety_byte),
      };

      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: decode_constant_val(inner.get(0)),
        value: decode_ix_expr(inner.get(1)),
        hints: decode_reducibility_hints(inner.get(2)),
        safety,
        all: decode_name_array(inner.get(3)),
      })
    },
    2 => ConstantInfo::ThmInfo(TheoremVal {
      cnst: decode_constant_val(inner.get(0)),
      value: decode_ix_expr(inner.get(1)),
      all: decode_name_array(inner.get(2)),
    }),
    3 => {
      let is_unsafe = inner.scalar_u8(3, 0) != 0;

      ConstantInfo::OpaqueInfo(OpaqueVal {
        cnst: decode_constant_val(inner.get(0)),
        value: decode_ix_expr(inner.get(1)),
        is_unsafe,
        all: decode_name_array(inner.get(2)),
      })
    },
    4 => {
      let kind_byte = inner.scalar_u8(1, 0);
      let kind = match kind_byte {
        0 => QuotKind::Type,
        1 => QuotKind::Ctor,
        2 => QuotKind::Lift,
        3 => QuotKind::Ind,
        _ => panic!("Invalid QuotKind: {}", kind_byte),
      };

      ConstantInfo::QuotInfo(QuotVal {
        cnst: decode_constant_val(inner.get(0)),
        kind,
      })
    },
    5 => {
      let is_rec = inner.scalar_u8(6, 0) != 0;
      let is_unsafe = inner.scalar_u8(6, 1) != 0;
      let is_reflexive = inner.scalar_u8(6, 2) != 0;

      ConstantInfo::InductInfo(InductiveVal {
        cnst: decode_constant_val(inner.get(0)),
        num_params: Nat::from_obj(inner.get(1)),
        num_indices: Nat::from_obj(inner.get(2)),
        all: decode_name_array(inner.get(3)),
        ctors: decode_name_array(inner.get(4)),
        num_nested: Nat::from_obj(inner.get(5)),
        is_rec,
        is_unsafe,
        is_reflexive,
      })
    },
    6 => {
      let is_unsafe = inner.scalar_u8(5, 0) != 0;

      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: decode_constant_val(inner.get(0)),
        induct: decode_ix_name(inner.get(1)),
        cidx: Nat::from_obj(inner.get(2)),
        num_params: Nat::from_obj(inner.get(3)),
        num_fields: Nat::from_obj(inner.get(4)),
        is_unsafe,
      })
    },
    7 => {
      let k = inner.scalar_u8(7, 0) != 0;
      let is_unsafe = inner.scalar_u8(7, 1) != 0;

      let rules: Vec<RecursorRule> =
        inner.get(6).as_array().map(decode_recursor_rule);

      ConstantInfo::RecInfo(RecursorVal {
        cnst: decode_constant_val(inner.get(0)),
        all: decode_name_array(inner.get(1)),
        num_params: Nat::from_obj(inner.get(2)),
        num_indices: Nat::from_obj(inner.get(3)),
        num_motives: Nat::from_obj(inner.get(4)),
        num_minors: Nat::from_obj(inner.get(5)),
        rules,
        k,
        is_unsafe,
      })
    },
    _ => panic!("Invalid ConstantInfo tag: {}", outer.tag()),
  }
}

/// Round-trip an Ix.ConstantInfo: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_constant_info(
  info_ptr: LeanIxConstantInfo,
) -> LeanIxConstantInfo {
  let info = decode_constant_info(*info_ptr);
  let mut cache = LeanBuildCache::new();
  build_constant_info(&mut cache, &info)
}
