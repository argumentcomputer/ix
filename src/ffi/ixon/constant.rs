//! Ixon constant types build/decode/roundtrip FFI.
//!
//! Includes: Definition, Axiom, Quotient, RecursorRule, Recursor, Constructor,
//! Inductive, InductiveProj, ConstructorProj, RecursorProj, DefinitionProj,
//! MutConst, ConstantInfo, Constant

use std::sync::Arc;

use crate::ix::ixon::constant::{
  Axiom as IxonAxiom, Constant as IxonConstant,
  ConstantInfo as IxonConstantInfo, Constructor as IxonConstructor,
  ConstructorProj, DefKind, Definition as IxonDefinition, DefinitionProj,
  Inductive as IxonInductive, InductiveProj, MutConst,
  Quotient as IxonQuotient, Recursor as IxonRecursor, RecursorProj,
  RecursorRule as IxonRecursorRule,
};
use crate::lean::{
  LeanIxAddress, LeanIxonAxiom, LeanIxonConstant, LeanIxonConstantInfo,
  LeanIxonConstructor, LeanIxonConstructorProj, LeanIxonDefinition,
  LeanIxonDefinitionProj, LeanIxonExpr, LeanIxonInductive,
  LeanIxonInductiveProj, LeanIxonMutConst, LeanIxonQuotient, LeanIxonRecursor,
  LeanIxonRecursorProj, LeanIxonRecursorRule, LeanIxonUniv,
};
use lean_ffi::object::{LeanArray, LeanCtor};

// =============================================================================
// Definition
// =============================================================================

impl LeanIxonDefinition {
  /// Build Ixon.Definition
  /// Lean stores scalar fields ordered by size (largest first).
  /// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
  pub fn build(def: &IxonDefinition) -> Self {
    let typ_obj = LeanIxonExpr::build(&def.typ);
    let value_obj = LeanIxonExpr::build(&def.value);
    // 2 obj fields, 16 scalar bytes (lvls(8) + kind(1) + safety(1) + padding(6))
    let ctor = LeanCtor::alloc(0, 2, 16);
    ctor.set(0, typ_obj);
    ctor.set(1, value_obj);
    // Scalar offsets from obj_cptr: 2*8=16 for lvls, 2*8+8=24 for kind, 2*8+9=25 for safety
    ctor.set_scalar_u64(2, 0, def.lvls);
    let kind_val: u8 = match def.kind {
      DefKind::Definition => 0,
      DefKind::Opaque => 1,
      DefKind::Theorem => 2,
    };
    ctor.set_scalar_u8(2, 8, kind_val);
    let safety_val: u8 = match def.safety {
      crate::ix::env::DefinitionSafety::Unsafe => 0,
      crate::ix::env::DefinitionSafety::Safe => 1,
      crate::ix::env::DefinitionSafety::Partial => 2,
    };
    ctor.set_scalar_u8(2, 9, safety_val);
    Self::new(*ctor)
  }

  /// Decode Ixon.Definition.
  /// Lean stores scalar fields ordered by size (largest first).
  /// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
  pub fn decode(self) -> IxonDefinition {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let value = Arc::new(LeanIxonExpr::new(ctor.get(1)).decode());
    let lvls = ctor.scalar_u64(2, 0);
    let kind_val = ctor.scalar_u8(2, 8);
    let kind = match kind_val {
      0 => DefKind::Definition,
      1 => DefKind::Opaque,
      2 => DefKind::Theorem,
      _ => panic!("Invalid DefKind: {}", kind_val),
    };
    let safety_val = ctor.scalar_u8(2, 9);
    let safety = match safety_val {
      0 => crate::ix::env::DefinitionSafety::Unsafe,
      1 => crate::ix::env::DefinitionSafety::Safe,
      2 => crate::ix::env::DefinitionSafety::Partial,
      _ => panic!("Invalid DefinitionSafety: {}", safety_val),
    };
    IxonDefinition { kind, safety, lvls, typ, value }
  }
}

// =============================================================================
// RecursorRule
// =============================================================================

impl LeanIxonRecursorRule {
  /// Build Ixon.RecursorRule
  pub fn build(rule: &IxonRecursorRule) -> Self {
    let rhs_obj = LeanIxonExpr::build(&rule.rhs);
    // 1 obj field, 8 scalar bytes
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, rhs_obj);
    ctor.set_scalar_u64(1, 0, rule.fields);
    Self::new(*ctor)
  }

  /// Decode Ixon.RecursorRule.
  pub fn decode(self) -> IxonRecursorRule {
    let ctor = self.as_ctor();
    let rhs = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let fields = ctor.scalar_u64(1, 0);
    IxonRecursorRule { fields, rhs }
  }
}

// =============================================================================
// Recursor
// =============================================================================

impl LeanIxonRecursor {
  /// Build Ixon.Recursor
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
  pub fn build(rec: &IxonRecursor) -> Self {
    let typ_obj = LeanIxonExpr::build(&rec.typ);
    // Build rules array
    let rules_arr = LeanArray::alloc(rec.rules.len());
    for (i, rule) in rec.rules.iter().enumerate() {
      rules_arr.set(i, LeanIxonRecursorRule::build(rule));
    }
    // 2 obj fields (typ, rules), 48 scalar bytes (5×8 + 1 + 1 + 6 padding)
    let ctor = LeanCtor::alloc(0, 2, 48);
    ctor.set(0, typ_obj);
    ctor.set(1, rules_arr);
    // Scalar offsets from obj_cptr: 2*8=16 base
    ctor.set_scalar_u64(2, 0, rec.lvls);
    ctor.set_scalar_u64(2, 8, rec.params);
    ctor.set_scalar_u64(2, 16, rec.indices);
    ctor.set_scalar_u64(2, 24, rec.motives);
    ctor.set_scalar_u64(2, 32, rec.minors);
    ctor.set_scalar_u8(2, 40, if rec.k { 1 } else { 0 });
    ctor.set_scalar_u8(2, 41, if rec.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Recursor.
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
  pub fn decode(self) -> IxonRecursor {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let rules_arr = ctor.get(1).as_array();
    let rules = rules_arr.map(|x| LeanIxonRecursorRule::new(x).decode());
    let lvls = ctor.scalar_u64(2, 0);
    let params = ctor.scalar_u64(2, 8);
    let indices = ctor.scalar_u64(2, 16);
    let motives = ctor.scalar_u64(2, 24);
    let minors = ctor.scalar_u64(2, 32);
    let k = ctor.scalar_u8(2, 40) != 0;
    let is_unsafe = ctor.scalar_u8(2, 41) != 0;
    IxonRecursor {
      k,
      is_unsafe,
      lvls,
      params,
      indices,
      motives,
      minors,
      typ,
      rules,
    }
  }
}

// =============================================================================
// Axiom
// =============================================================================

impl LeanIxonAxiom {
  /// Build Ixon.Axiom
  /// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
  pub fn build(ax: &IxonAxiom) -> Self {
    let typ_obj = LeanIxonExpr::build(&ax.typ);
    // 1 obj field, 16 scalar bytes (lvls(8) + isUnsafe(1) + padding(7))
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, typ_obj);
    // Scalar offsets from obj_cptr: 1*8=8 base
    ctor.set_scalar_u64(1, 0, ax.lvls);
    ctor.set_scalar_u8(1, 8, if ax.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Axiom.
  /// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
  pub fn decode(self) -> IxonAxiom {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let lvls = ctor.scalar_u64(1, 0);
    let is_unsafe = ctor.scalar_u8(1, 8) != 0;
    IxonAxiom { is_unsafe, lvls, typ }
  }
}

// =============================================================================
// Quotient
// =============================================================================

impl LeanIxonQuotient {
  /// Build Ixon.Quotient
  /// QuotKind is a simple enum stored as scalar u8, not object field.
  /// Scalars ordered by size: lvls(8) + kind(1) + padding(7)
  pub fn build(quot: &IxonQuotient) -> Self {
    let typ_obj = LeanIxonExpr::build(&quot.typ);
    // 1 obj field (typ), 16 scalar bytes (lvls(8) + kind(1) + padding(7))
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, typ_obj);
    // Scalar offsets from obj_cptr: 1*8=8 base
    ctor.set_scalar_u64(1, 0, quot.lvls);
    let kind_val: u8 = match quot.kind {
      crate::ix::env::QuotKind::Type => 0,
      crate::ix::env::QuotKind::Ctor => 1,
      crate::ix::env::QuotKind::Lift => 2,
      crate::ix::env::QuotKind::Ind => 3,
    };
    ctor.set_scalar_u8(1, 8, kind_val);
    Self::new(*ctor)
  }

  /// Decode Ixon.Quotient.
  /// QuotKind is a scalar (not object field). Scalars: lvls(8) + kind(1) + padding(7)
  pub fn decode(self) -> IxonQuotient {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let lvls = ctor.scalar_u64(1, 0);
    let kind_val = ctor.scalar_u8(1, 8);
    let kind = match kind_val {
      0 => crate::ix::env::QuotKind::Type,
      1 => crate::ix::env::QuotKind::Ctor,
      2 => crate::ix::env::QuotKind::Lift,
      3 => crate::ix::env::QuotKind::Ind,
      _ => panic!("Invalid QuotKind: {}", kind_val),
    };
    IxonQuotient { kind, lvls, typ }
  }
}

// =============================================================================
// Constructor
// =============================================================================

impl LeanIxonConstructor {
  /// Build Ixon.Constructor
  /// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
  pub fn build(c: &IxonConstructor) -> Self {
    let typ_obj = LeanIxonExpr::build(&c.typ);
    // 1 obj field, 40 scalar bytes (4×8 + 1 + 7 padding)
    let ctor = LeanCtor::alloc(0, 1, 40);
    ctor.set(0, typ_obj);
    // Scalar offsets from obj_cptr: 1*8=8 base
    ctor.set_scalar_u64(1, 0, c.lvls);
    ctor.set_scalar_u64(1, 8, c.cidx);
    ctor.set_scalar_u64(1, 16, c.params);
    ctor.set_scalar_u64(1, 24, c.fields);
    ctor.set_scalar_u8(1, 32, if c.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Constructor.
  /// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
  pub fn decode(self) -> IxonConstructor {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let lvls = ctor.scalar_u64(1, 0);
    let cidx = ctor.scalar_u64(1, 8);
    let params = ctor.scalar_u64(1, 16);
    let fields = ctor.scalar_u64(1, 24);
    let is_unsafe = ctor.scalar_u8(1, 32) != 0;
    IxonConstructor { is_unsafe, lvls, cidx, params, fields, typ }
  }
}

// =============================================================================
// Inductive
// =============================================================================

impl LeanIxonInductive {
  /// Build Ixon.Inductive
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
  pub fn build(ind: &IxonInductive) -> Self {
    let typ_obj = LeanIxonExpr::build(&ind.typ);
    // Build ctors array
    let ctors_arr = LeanArray::alloc(ind.ctors.len());
    for (i, c) in ind.ctors.iter().enumerate() {
      ctors_arr.set(i, LeanIxonConstructor::build(c));
    }
    // 2 obj fields, 40 scalar bytes (4×8 + 3 + 5 padding)
    let ctor = LeanCtor::alloc(0, 2, 40);
    ctor.set(0, typ_obj);
    ctor.set(1, ctors_arr);
    // Scalar offsets from obj_cptr: 2*8=16 base
    ctor.set_scalar_u64(2, 0, ind.lvls);
    ctor.set_scalar_u64(2, 8, ind.params);
    ctor.set_scalar_u64(2, 16, ind.indices);
    ctor.set_scalar_u64(2, 24, ind.nested);
    ctor.set_scalar_u8(2, 32, if ind.recr { 1 } else { 0 });
    ctor.set_scalar_u8(2, 33, if ind.refl { 1 } else { 0 });
    ctor.set_scalar_u8(2, 34, if ind.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Inductive.
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
  pub fn decode(self) -> IxonInductive {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0)).decode());
    let ctors_arr = ctor.get(1).as_array();
    let ctors = ctors_arr.map(|x| LeanIxonConstructor::new(x).decode());
    let lvls = ctor.scalar_u64(2, 0);
    let params = ctor.scalar_u64(2, 8);
    let indices = ctor.scalar_u64(2, 16);
    let nested = ctor.scalar_u64(2, 24);
    let recr = ctor.scalar_u8(2, 32) != 0;
    let refl = ctor.scalar_u8(2, 33) != 0;
    let is_unsafe = ctor.scalar_u8(2, 34) != 0;
    IxonInductive {
      recr,
      refl,
      is_unsafe,
      lvls,
      params,
      indices,
      nested,
      typ,
      ctors,
    }
  }
}

// =============================================================================
// Projection Types
// =============================================================================

impl LeanIxonInductiveProj {
  pub fn build(proj: &InductiveProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, block_obj);
    ctor.set_scalar_u64(1, 0, proj.idx);
    Self::new(*ctor)
  }

  pub fn decode(self) -> InductiveProj {
    let ctor = self.as_ctor();
    let block = LeanIxAddress::new(ctor.get(0)).decode();
    let idx = ctor.scalar_u64(1, 0);
    InductiveProj { idx, block }
  }
}

impl LeanIxonConstructorProj {
  pub fn build(proj: &ConstructorProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, block_obj);
    ctor.set_scalar_u64(1, 0, proj.idx);
    ctor.set_scalar_u64(1, 8, proj.cidx);
    Self::new(*ctor)
  }

  pub fn decode(self) -> ConstructorProj {
    let ctor = self.as_ctor();
    let block = LeanIxAddress::new(ctor.get(0)).decode();
    let idx = ctor.scalar_u64(1, 0);
    let cidx = ctor.scalar_u64(1, 8);
    ConstructorProj { idx, cidx, block }
  }
}

impl LeanIxonRecursorProj {
  pub fn build(proj: &RecursorProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, block_obj);
    ctor.set_scalar_u64(1, 0, proj.idx);
    Self::new(*ctor)
  }

  pub fn decode(self) -> RecursorProj {
    let ctor = self.as_ctor();
    let block = LeanIxAddress::new(ctor.get(0)).decode();
    let idx = ctor.scalar_u64(1, 0);
    RecursorProj { idx, block }
  }
}

impl LeanIxonDefinitionProj {
  pub fn build(proj: &DefinitionProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, block_obj);
    ctor.set_scalar_u64(1, 0, proj.idx);
    Self::new(*ctor)
  }

  pub fn decode(self) -> DefinitionProj {
    let ctor = self.as_ctor();
    let block = LeanIxAddress::new(ctor.get(0)).decode();
    let idx = ctor.scalar_u64(1, 0);
    DefinitionProj { idx, block }
  }
}

// =============================================================================
// MutConst
// =============================================================================

impl LeanIxonMutConst {
  pub fn build(mc: &MutConst) -> Self {
    let obj = match mc {
      MutConst::Defn(def) => {
        let def_obj = LeanIxonDefinition::build(def);
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, def_obj);
        *ctor
      },
      MutConst::Indc(ind) => {
        let ind_obj = LeanIxonInductive::build(ind);
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, ind_obj);
        *ctor
      },
      MutConst::Recr(rec) => {
        let rec_obj = LeanIxonRecursor::build(rec);
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, rec_obj);
        *ctor
      },
    };
    Self::new(obj)
  }

  pub fn decode(self) -> MutConst {
    let ctor = self.as_ctor();
    let inner = ctor.get(0);
    match ctor.tag() {
      0 => MutConst::Defn(LeanIxonDefinition::new(inner).decode()),
      1 => MutConst::Indc(LeanIxonInductive::new(inner).decode()),
      2 => MutConst::Recr(LeanIxonRecursor::new(inner).decode()),
      tag => panic!("Invalid Ixon.MutConst tag: {}", tag),
    }
  }
}

// =============================================================================
// ConstantInfo
// =============================================================================

impl LeanIxonConstantInfo {
  /// Build Ixon.ConstantInfo (9 constructors)
  pub fn build(info: &IxonConstantInfo) -> Self {
    let obj = match info {
      IxonConstantInfo::Defn(def) => {
        let def_obj = LeanIxonDefinition::build(def);
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, def_obj);
        *ctor
      },
      IxonConstantInfo::Recr(rec) => {
        let rec_obj = LeanIxonRecursor::build(rec);
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, rec_obj);
        *ctor
      },
      IxonConstantInfo::Axio(ax) => {
        let ax_obj = LeanIxonAxiom::build(ax);
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, ax_obj);
        *ctor
      },
      IxonConstantInfo::Quot(quot) => {
        let quot_obj = LeanIxonQuotient::build(quot);
        let ctor = LeanCtor::alloc(3, 1, 0);
        ctor.set(0, quot_obj);
        *ctor
      },
      IxonConstantInfo::CPrj(proj) => {
        let proj_obj = LeanIxonConstructorProj::build(proj);
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, proj_obj);
        *ctor
      },
      IxonConstantInfo::RPrj(proj) => {
        let proj_obj = LeanIxonRecursorProj::build(proj);
        let ctor = LeanCtor::alloc(5, 1, 0);
        ctor.set(0, proj_obj);
        *ctor
      },
      IxonConstantInfo::IPrj(proj) => {
        let proj_obj = LeanIxonInductiveProj::build(proj);
        let ctor = LeanCtor::alloc(6, 1, 0);
        ctor.set(0, proj_obj);
        *ctor
      },
      IxonConstantInfo::DPrj(proj) => {
        let proj_obj = LeanIxonDefinitionProj::build(proj);
        let ctor = LeanCtor::alloc(7, 1, 0);
        ctor.set(0, proj_obj);
        *ctor
      },
      IxonConstantInfo::Muts(muts) => {
        let arr = LeanArray::alloc(muts.len());
        for (i, mc) in muts.iter().enumerate() {
          arr.set(i, LeanIxonMutConst::build(mc));
        }
        let ctor = LeanCtor::alloc(8, 1, 0);
        ctor.set(0, arr);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ConstantInfo.
  pub fn decode(self) -> IxonConstantInfo {
    let ctor = self.as_ctor();
    let inner = ctor.get(0);
    match ctor.tag() {
      0 => IxonConstantInfo::Defn(LeanIxonDefinition::new(inner).decode()),
      1 => IxonConstantInfo::Recr(LeanIxonRecursor::new(inner).decode()),
      2 => IxonConstantInfo::Axio(LeanIxonAxiom::new(inner).decode()),
      3 => IxonConstantInfo::Quot(LeanIxonQuotient::new(inner).decode()),
      4 => IxonConstantInfo::CPrj(LeanIxonConstructorProj::new(inner).decode()),
      5 => IxonConstantInfo::RPrj(LeanIxonRecursorProj::new(inner).decode()),
      6 => IxonConstantInfo::IPrj(LeanIxonInductiveProj::new(inner).decode()),
      7 => IxonConstantInfo::DPrj(LeanIxonDefinitionProj::new(inner).decode()),
      8 => {
        let arr = inner.as_array();
        let muts = arr.map(|x| LeanIxonMutConst::new(x).decode());
        IxonConstantInfo::Muts(muts)
      },
      tag => panic!("Invalid Ixon.ConstantInfo tag: {}", tag),
    }
  }
}

// =============================================================================
// Constant
// =============================================================================

impl LeanIxonConstant {
  /// Build Ixon.Constant
  pub fn build(constant: &IxonConstant) -> Self {
    let info_obj = LeanIxonConstantInfo::build(&constant.info);
    let sharing_obj = LeanIxonExpr::build_array(&constant.sharing);
    let refs_obj = LeanIxAddress::build_array(&constant.refs);
    let univs_obj = LeanIxonUniv::build_array(&constant.univs);
    let ctor = LeanCtor::alloc(0, 4, 0);
    ctor.set(0, info_obj);
    ctor.set(1, sharing_obj);
    ctor.set(2, refs_obj);
    ctor.set(3, univs_obj);
    Self::new(*ctor)
  }

  /// Decode Ixon.Constant.
  pub fn decode(self) -> IxonConstant {
    let ctor = self.as_ctor();
    IxonConstant {
      info: LeanIxonConstantInfo::new(ctor.get(0)).decode(),
      sharing: LeanIxonExpr::decode_array(ctor.get(1).as_array()),
      refs: LeanIxAddress::decode_array(ctor.get(2).as_array()),
      univs: LeanIxonUniv::decode_array(ctor.get(3).as_array()),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Definition.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition(
  obj: LeanIxonDefinition,
) -> LeanIxonDefinition {
  let def = obj.decode();
  LeanIxonDefinition::build(&def)
}

/// Round-trip Ixon.Recursor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor(
  obj: LeanIxonRecursor,
) -> LeanIxonRecursor {
  let rec = obj.decode();
  LeanIxonRecursor::build(&rec)
}

/// Round-trip Ixon.Axiom.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_axiom(obj: LeanIxonAxiom) -> LeanIxonAxiom {
  let ax = obj.decode();
  LeanIxonAxiom::build(&ax)
}

/// Round-trip Ixon.Quotient.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quotient(
  obj: LeanIxonQuotient,
) -> LeanIxonQuotient {
  let quot = obj.decode();
  LeanIxonQuotient::build(&quot)
}

/// Round-trip Ixon.ConstantInfo.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_info(
  obj: LeanIxonConstantInfo,
) -> LeanIxonConstantInfo {
  let info = obj.decode();
  LeanIxonConstantInfo::build(&info)
}

/// Round-trip Ixon.Constant.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant(
  obj: LeanIxonConstant,
) -> LeanIxonConstant {
  let constant = obj.decode();
  LeanIxonConstant::build(&constant)
}

/// Round-trip Ixon.RecursorRule.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_rule(
  obj: LeanIxonRecursorRule,
) -> LeanIxonRecursorRule {
  let rule = obj.decode();
  LeanIxonRecursorRule::build(&rule)
}

/// Round-trip Ixon.Constructor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor(
  obj: LeanIxonConstructor,
) -> LeanIxonConstructor {
  let c = obj.decode();
  LeanIxonConstructor::build(&c)
}

/// Round-trip Ixon.Inductive.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive(
  obj: LeanIxonInductive,
) -> LeanIxonInductive {
  let ind = obj.decode();
  LeanIxonInductive::build(&ind)
}

/// Round-trip Ixon.InductiveProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive_proj(
  obj: LeanIxonInductiveProj,
) -> LeanIxonInductiveProj {
  let proj = obj.decode();
  LeanIxonInductiveProj::build(&proj)
}

/// Round-trip Ixon.ConstructorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor_proj(
  obj: LeanIxonConstructorProj,
) -> LeanIxonConstructorProj {
  let proj = obj.decode();
  LeanIxonConstructorProj::build(&proj)
}

/// Round-trip Ixon.RecursorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_proj(
  obj: LeanIxonRecursorProj,
) -> LeanIxonRecursorProj {
  let proj = obj.decode();
  LeanIxonRecursorProj::build(&proj)
}

/// Round-trip Ixon.DefinitionProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_proj(
  obj: LeanIxonDefinitionProj,
) -> LeanIxonDefinitionProj {
  let proj = obj.decode();
  LeanIxonDefinitionProj::build(&proj)
}

/// Round-trip Ixon.MutConst.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_mut_const(
  obj: LeanIxonMutConst,
) -> LeanIxonMutConst {
  let mc = obj.decode();
  LeanIxonMutConst::build(&mc)
}
