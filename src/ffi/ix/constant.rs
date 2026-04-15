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
use crate::lean::{
  LeanIxAxiomVal, LeanIxConstantInfo, LeanIxConstantVal, LeanIxConstructorVal,
  LeanIxDefinitionVal, LeanIxExpr, LeanIxInductiveVal, LeanIxName,
  LeanIxOpaqueVal, LeanIxQuotVal, LeanIxRecursorRule, LeanIxRecursorVal,
  LeanIxReducibilityHints, LeanIxReducibilityHintsRegular,
};
use lean_ffi::nat::Nat;
#[cfg(feature = "test-ffi")]
use lean_ffi::object::LeanBorrowed;
use lean_ffi::object::{
  LeanArray, LeanCtor, LeanCtorScalar, LeanOwned, LeanRef,
};

use crate::ffi::builder::LeanBuildCache;

// =============================================================================
// ConstantVal
// =============================================================================

impl LeanIxConstantVal<LeanOwned> {
  /// Build a Ix.ConstantVal structure.
  pub fn build(cache: &mut LeanBuildCache, cv: &ConstantVal) -> Self {
    // ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
    let name_obj = LeanIxName::build(cache, &cv.name);
    let level_params_obj = LeanIxName::build_array(cache, &cv.level_params);
    let type_obj = LeanIxExpr::build(cache, &cv.typ);

    let obj = LeanCtor::alloc(0, 3, 0);
    obj.set(0, name_obj);
    obj.set(1, level_params_obj);
    obj.set(2, type_obj);
    Self::new(obj.into())
  }
}

impl<R: LeanRef> LeanIxConstantVal<R> {
  /// Decode Ix.ConstantVal from Lean object.
  /// ConstantVal = { name : Name, levelParams : Array Name, type : Expr }
  pub fn decode(&self) -> ConstantVal {
    let ctor = self.as_ctor();
    let name = LeanIxName(ctor.get(0)).decode();
    let level_params: Vec<Name> =
      ctor.get(1).as_array().map(|x| LeanIxName(x).decode());
    let typ = LeanIxExpr(ctor.get(2)).decode();

    ConstantVal { name, level_params, typ }
  }
}

// =============================================================================
// ReducibilityHints
// =============================================================================

impl LeanIxReducibilityHints<LeanOwned> {
  /// Build ReducibilityHints.
  /// NOTE: In Lean 4, 0-field constructors are boxed scalars when the inductive has
  /// other constructors with fields. So opaque and abbrev use box_usize.
  pub fn build(hints: &ReducibilityHints) -> Self {
    let obj = match hints {
      // | opaque -- tag 0, boxed as scalar
      ReducibilityHints::Opaque => LeanOwned::box_usize(0),
      // | abbrev -- tag 1, boxed as scalar
      ReducibilityHints::Abbrev => LeanOwned::box_usize(1),
      // | regular (h : UInt32) -- tag 2, object constructor
      ReducibilityHints::Regular(h) => {
        // UInt32 is a scalar, stored inline
        let ctor = LeanIxReducibilityHintsRegular::alloc();
        ctor.set_num_32(0, *h);
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxReducibilityHints<R> {
  /// Decode Lean.ReducibilityHints from Lean object.
  pub fn decode(&self) -> ReducibilityHints {
    if self.inner().is_scalar() {
      let tag = self.inner().unbox_usize();
      match tag {
        0 => return ReducibilityHints::Opaque,
        1 => return ReducibilityHints::Abbrev,
        _ => panic!("Invalid ReducibilityHints scalar tag: {}", tag),
      }
    }

    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => ReducibilityHints::Opaque,
      1 => ReducibilityHints::Abbrev,
      2 => {
        // regular: 0 obj fields, 4 scalar bytes (UInt32)
        let ctor = LeanIxReducibilityHintsRegular::from_ctor(ctor);
        ReducibilityHints::Regular(ctor.get_num_32(0))
      },
      _ => panic!("Invalid ReducibilityHints tag: {}", ctor.tag()),
    }
  }
}

// =============================================================================
// RecursorRule
// =============================================================================

impl<R: LeanRef> LeanIxRecursorRule<R> {
  /// Decode Ix.RecursorRule from Lean object.
  pub fn decode(&self) -> RecursorRule {
    let ctor = self.as_ctor();
    RecursorRule {
      ctor: LeanIxName(ctor.get(0)).decode(),
      n_fields: Nat::from_obj(&ctor.get(1)),
      rhs: LeanIxExpr(ctor.get(2)).decode(),
    }
  }
}

// =============================================================================
// ConstantInfo
// =============================================================================

impl LeanIxRecursorRule<LeanOwned> {
  /// Build an Array of RecursorRule.
  pub fn build_array(
    cache: &mut LeanBuildCache,
    rules: &[RecursorRule],
  ) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(rules.len());
    for (i, rule) in rules.iter().enumerate() {
      // RecursorRule = { ctor : Name, nFields : Nat, rhs : Expr }
      let ctor_obj = LeanIxName::build(cache, &rule.ctor);
      let n_fields_obj = Nat::to_lean(&rule.n_fields);
      let rhs_obj = LeanIxExpr::build(cache, &rule.rhs);

      let rule_obj = LeanCtor::alloc(0, 3, 0);
      rule_obj.set(0, ctor_obj);
      rule_obj.set(1, n_fields_obj);
      rule_obj.set(2, rhs_obj);

      arr.set(i, rule_obj);
    }
    arr
  }
}

impl LeanIxConstantInfo<LeanOwned> {
  /// Build a Ix.ConstantInfo from a Rust ConstantInfo.
  pub fn build(cache: &mut LeanBuildCache, info: &ConstantInfo) -> Self {
    let result: LeanOwned = match info {
      // | axiomInfo (v : AxiomVal) -- tag 0
      ConstantInfo::AxiomInfo(v) => {
        // AxiomVal = { cnst : ConstantVal, isUnsafe : Bool }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let ctor = LeanIxAxiomVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_num_8(0, v.is_unsafe as u8);

        let obj = LeanCtor::alloc(0, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | defnInfo (v : DefinitionVal) -- tag 1
      ConstantInfo::DefnInfo(v) => {
        // DefinitionVal = { cnst, value, hints, safety, all }
        // Memory layout: 4 obj fields (cnst, value, hints, all), 1 scalar byte (safety)
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let value_obj = LeanIxExpr::build(cache, &v.value);
        let hints_obj = LeanIxReducibilityHints::build(&v.hints);
        let all_obj = LeanIxName::build_array(cache, &v.all);
        let safety_byte = match v.safety {
          DefinitionSafety::Unsafe => 0u8,
          DefinitionSafety::Safe => 1u8,
          DefinitionSafety::Partial => 2u8,
        };

        let ctor = LeanIxDefinitionVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_obj(1, value_obj);
        ctor.set_obj(2, hints_obj);
        ctor.set_obj(3, all_obj);
        ctor.set_num_8(0, safety_byte);

        let obj = LeanCtor::alloc(1, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | thmInfo (v : TheoremVal) -- tag 2
      ConstantInfo::ThmInfo(v) => {
        // TheoremVal = { cnst, value, all }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let value_obj = LeanIxExpr::build(cache, &v.value);
        let all_obj = LeanIxName::build_array(cache, &v.all);

        let thm_val = LeanCtor::alloc(0, 3, 0);
        thm_val.set(0, cnst_obj);
        thm_val.set(1, value_obj);
        thm_val.set(2, all_obj);

        let obj = LeanCtor::alloc(2, 1, 0);
        obj.set(0, thm_val);
        obj.into()
      },
      // | opaqueInfo (v : OpaqueVal) -- tag 3
      ConstantInfo::OpaqueInfo(v) => {
        // OpaqueVal = { cnst, value, isUnsafe, all }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let value_obj = LeanIxExpr::build(cache, &v.value);
        let all_obj = LeanIxName::build_array(cache, &v.all);

        let ctor = LeanIxOpaqueVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_obj(1, value_obj);
        ctor.set_obj(2, all_obj);
        ctor.set_num_8(0, v.is_unsafe as u8);

        let obj = LeanCtor::alloc(3, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | quotInfo (v : QuotVal) -- tag 4
      ConstantInfo::QuotInfo(v) => {
        // QuotVal = { cnst, kind }
        // Memory layout: 1 obj field (cnst), 1 scalar byte (kind)
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let kind_byte = match v.kind {
          QuotKind::Type => 0u8,
          QuotKind::Ctor => 1u8,
          QuotKind::Lift => 2u8,
          QuotKind::Ind => 3u8,
        };

        let ctor = LeanIxQuotVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_num_8(0, kind_byte);

        let obj = LeanCtor::alloc(4, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | inductInfo (v : InductiveVal) -- tag 5
      ConstantInfo::InductInfo(v) => {
        // InductiveVal = { cnst, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let num_params_obj = Nat::to_lean(&v.num_params);
        let num_indices_obj = Nat::to_lean(&v.num_indices);
        let all_obj = LeanIxName::build_array(cache, &v.all);
        let ctors_obj = LeanIxName::build_array(cache, &v.ctors);
        let num_nested_obj = Nat::to_lean(&v.num_nested);

        // 6 object fields, 3 scalar bytes for bools
        let ctor = LeanIxInductiveVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_obj(1, num_params_obj);
        ctor.set_obj(2, num_indices_obj);
        ctor.set_obj(3, all_obj);
        ctor.set_obj(4, ctors_obj);
        ctor.set_obj(5, num_nested_obj);
        ctor.set_num_8(0, v.is_rec as u8);
        ctor.set_num_8(1, v.is_unsafe as u8);
        ctor.set_num_8(2, v.is_reflexive as u8);

        let obj = LeanCtor::alloc(5, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | ctorInfo (v : ConstructorVal) -- tag 6
      ConstantInfo::CtorInfo(v) => {
        // ConstructorVal = { cnst, induct, cidx, numParams, numFields, isUnsafe }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let induct_obj = LeanIxName::build(cache, &v.induct);
        let cidx_obj = Nat::to_lean(&v.cidx);
        let num_params_obj = Nat::to_lean(&v.num_params);
        let num_fields_obj = Nat::to_lean(&v.num_fields);

        // 5 object fields, 1 scalar byte for bool
        let ctor = LeanIxConstructorVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_obj(1, induct_obj);
        ctor.set_obj(2, cidx_obj);
        ctor.set_obj(3, num_params_obj);
        ctor.set_obj(4, num_fields_obj);
        ctor.set_num_8(0, v.is_unsafe as u8);

        let obj = LeanCtor::alloc(6, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
      // | recInfo (v : RecursorVal) -- tag 7
      ConstantInfo::RecInfo(v) => {
        // RecursorVal = { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
        let cnst_obj = LeanIxConstantVal::build(cache, &v.cnst);
        let all_obj = LeanIxName::build_array(cache, &v.all);
        let num_params_obj = Nat::to_lean(&v.num_params);
        let num_indices_obj = Nat::to_lean(&v.num_indices);
        let num_motives_obj = Nat::to_lean(&v.num_motives);
        let num_minors_obj = Nat::to_lean(&v.num_minors);
        let rules_obj = LeanIxRecursorRule::build_array(cache, &v.rules);

        // 7 object fields, 2 scalar bytes for bools
        let ctor = LeanIxRecursorVal::alloc();
        ctor.set_obj(0, cnst_obj);
        ctor.set_obj(1, all_obj);
        ctor.set_obj(2, num_params_obj);
        ctor.set_obj(3, num_indices_obj);
        ctor.set_obj(4, num_motives_obj);
        ctor.set_obj(5, num_minors_obj);
        ctor.set_obj(6, rules_obj);
        ctor.set_num_8(0, v.k as u8);
        ctor.set_num_8(1, v.is_unsafe as u8);

        let obj = LeanCtor::alloc(7, 1, 0);
        obj.set(0, ctor);
        obj.into()
      },
    };

    Self::new(result)
  }
}

impl<R: LeanRef> LeanIxConstantInfo<R> {
  /// Decode Ix.ConstantInfo from Lean object.
  pub fn decode(&self) -> ConstantInfo {
    let outer = self.as_ctor();
    let inner_obj = outer.get(0);
    let inner = inner_obj.as_ctor();

    match outer.tag() {
      0 => {
        let ctor = LeanIxAxiomVal::from_ctor(inner);
        let is_unsafe = ctor.get_num_8(0) != 0;

        ConstantInfo::AxiomInfo(AxiomVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          is_unsafe,
        })
      },
      1 => {
        let ctor = LeanIxDefinitionVal::from_ctor(inner);
        let safety_byte = ctor.get_num_8(0);
        let safety = match safety_byte {
          0 => DefinitionSafety::Unsafe,
          1 => DefinitionSafety::Safe,
          2 => DefinitionSafety::Partial,
          _ => panic!("Invalid DefinitionSafety: {}", safety_byte),
        };

        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          value: LeanIxExpr(inner.get(1)).decode(),
          hints: LeanIxReducibilityHints(inner.get(2)).decode(),
          safety,
          all: LeanIxName::decode_array(inner.get(3).as_array()),
        })
      },
      2 => ConstantInfo::ThmInfo(TheoremVal {
        cnst: LeanIxConstantVal(inner.get(0)).decode(),
        value: LeanIxExpr(inner.get(1)).decode(),
        all: LeanIxName::decode_array(inner.get(2).as_array()),
      }),
      3 => {
        let ctor = LeanIxOpaqueVal::from_ctor(inner);
        let is_unsafe = ctor.get_num_8(0) != 0;

        ConstantInfo::OpaqueInfo(OpaqueVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          value: LeanIxExpr(inner.get(1)).decode(),
          is_unsafe,
          all: LeanIxName::decode_array(inner.get(2).as_array()),
        })
      },
      4 => {
        let ctor = LeanIxQuotVal::from_ctor(inner);
        let kind_byte = ctor.get_num_8(0);
        let kind = match kind_byte {
          0 => QuotKind::Type,
          1 => QuotKind::Ctor,
          2 => QuotKind::Lift,
          3 => QuotKind::Ind,
          _ => panic!("Invalid QuotKind: {}", kind_byte),
        };

        ConstantInfo::QuotInfo(QuotVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          kind,
        })
      },
      5 => {
        let ctor = LeanIxInductiveVal::from_ctor(inner);
        let is_rec = ctor.get_num_8(0) != 0;
        let is_unsafe = ctor.get_num_8(1) != 0;
        let is_reflexive = ctor.get_num_8(2) != 0;

        ConstantInfo::InductInfo(InductiveVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          num_params: Nat::from_obj(&inner.get(1)),
          num_indices: Nat::from_obj(&inner.get(2)),
          all: LeanIxName::decode_array(inner.get(3).as_array()),
          ctors: LeanIxName::decode_array(inner.get(4).as_array()),
          num_nested: Nat::from_obj(&inner.get(5)),
          is_rec,
          is_unsafe,
          is_reflexive,
        })
      },
      6 => {
        let ctor = LeanIxConstructorVal::from_ctor(inner);
        let is_unsafe = ctor.get_num_8(0) != 0;

        ConstantInfo::CtorInfo(ConstructorVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          induct: LeanIxName(inner.get(1)).decode(),
          cidx: Nat::from_obj(&inner.get(2)),
          num_params: Nat::from_obj(&inner.get(3)),
          num_fields: Nat::from_obj(&inner.get(4)),
          is_unsafe,
        })
      },
      7 => {
        let ctor = LeanIxRecursorVal::from_ctor(inner);
        let k = ctor.get_num_8(0) != 0;
        let is_unsafe = ctor.get_num_8(1) != 0;

        let rules: Vec<RecursorRule> =
          inner.get(6).as_array().map(|x| LeanIxRecursorRule(x).decode());

        ConstantInfo::RecInfo(RecursorVal {
          cnst: LeanIxConstantVal(inner.get(0)).decode(),
          all: LeanIxName::decode_array(inner.get(1).as_array()),
          num_params: Nat::from_obj(&inner.get(2)),
          num_indices: Nat::from_obj(&inner.get(3)),
          num_motives: Nat::from_obj(&inner.get(4)),
          num_minors: Nat::from_obj(&inner.get(5)),
          rules,
          k,
          is_unsafe,
        })
      },
      _ => panic!("Invalid ConstantInfo tag: {}", outer.tag()),
    }
  }
}

/// Round-trip an Ix.ConstantInfo: decode from Lean, re-encode via LeanBuildCache.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_constant_info(
  info_ptr: LeanIxConstantInfo<LeanBorrowed<'_>>,
) -> LeanIxConstantInfo<LeanOwned> {
  let info = info_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxConstantInfo::build(&mut cache, &info)
}
