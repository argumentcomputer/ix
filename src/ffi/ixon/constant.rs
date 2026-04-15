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
  LeanIxonConstantInfoAxio, LeanIxonConstantInfoCPrj, LeanIxonConstantInfoDPrj,
  LeanIxonConstantInfoDefn, LeanIxonConstantInfoIPrj, LeanIxonConstantInfoMuts,
  LeanIxonConstantInfoQuot, LeanIxonConstantInfoRPrj, LeanIxonConstantInfoRecr,
  LeanIxonConstructor, LeanIxonConstructorProj, LeanIxonDefinition,
  LeanIxonDefinitionProj, LeanIxonExpr, LeanIxonInductive,
  LeanIxonInductiveProj, LeanIxonMutConst, LeanIxonMutConstDefn,
  LeanIxonMutConstIndc, LeanIxonMutConstRecr, LeanIxonQuotient,
  LeanIxonRecursor, LeanIxonRecursorProj, LeanIxonRecursorRule, LeanIxonUniv,
};
#[cfg(feature = "test-ffi")]
use lean_ffi::object::LeanBorrowed;
use lean_ffi::object::{LeanArray, LeanOwned, LeanRef};

// =============================================================================
// Definition
// =============================================================================

impl LeanIxonDefinition<LeanOwned> {
  /// Build Ixon.Definition
  /// Lean stores scalar fields ordered by size (largest first).
  /// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
  pub fn build(def: &IxonDefinition) -> Self {
    let typ_obj = LeanIxonExpr::build(&def.typ);
    let value_obj = LeanIxonExpr::build(&def.value);
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_obj(1, value_obj);
    ctor.set_num_64(0, def.lvls);
    let kind_val: u8 = match def.kind {
      DefKind::Definition => 0,
      DefKind::Opaque => 1,
      DefKind::Theorem => 2,
    };
    ctor.set_num_8(0, kind_val);
    let safety_val: u8 = match def.safety {
      crate::ix::env::DefinitionSafety::Unsafe => 0,
      crate::ix::env::DefinitionSafety::Safe => 1,
      crate::ix::env::DefinitionSafety::Partial => 2,
    };
    ctor.set_num_8(1, safety_val);
    ctor
  }
}

impl<R: LeanRef> LeanIxonDefinition<R> {
  /// Decode Ixon.Definition.
  /// Lean stores scalar fields ordered by size (largest first).
  /// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
  pub fn decode(&self) -> IxonDefinition {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let value =
      Arc::new(LeanIxonExpr::new(ctor.get(1).to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let kind_val = self.get_num_8(0);
    let kind = match kind_val {
      0 => DefKind::Definition,
      1 => DefKind::Opaque,
      2 => DefKind::Theorem,
      _ => panic!("Invalid DefKind: {}", kind_val),
    };
    let safety_val = self.get_num_8(1);
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

impl LeanIxonRecursorRule<LeanOwned> {
  /// Build Ixon.RecursorRule
  pub fn build(rule: &IxonRecursorRule) -> Self {
    let rhs_obj = LeanIxonExpr::build(&rule.rhs);
    let ctor = Self::alloc();
    ctor.set_obj(0, rhs_obj);
    ctor.set_num_64(0, rule.fields);
    ctor
  }
}

impl<R: LeanRef> LeanIxonRecursorRule<R> {
  /// Decode Ixon.RecursorRule.
  pub fn decode(&self) -> IxonRecursorRule {
    let ctor = self.as_ctor();
    let rhs = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let fields = self.get_num_64(0);
    IxonRecursorRule { fields, rhs }
  }
}

// =============================================================================
// Recursor
// =============================================================================

impl LeanIxonRecursor<LeanOwned> {
  /// Build Ixon.Recursor
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
  pub fn build(rec: &IxonRecursor) -> Self {
    let typ_obj = LeanIxonExpr::build(&rec.typ);
    // Build rules array
    let rules_arr = LeanArray::alloc(rec.rules.len());
    for (i, rule) in rec.rules.iter().enumerate() {
      rules_arr.set(i, LeanIxonRecursorRule::build(rule));
    }
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_obj(1, rules_arr);
    ctor.set_num_64(0, rec.lvls);
    ctor.set_num_64(1, rec.params);
    ctor.set_num_64(2, rec.indices);
    ctor.set_num_64(3, rec.motives);
    ctor.set_num_64(4, rec.minors);
    ctor.set_num_8(0, rec.k as u8);
    ctor.set_num_8(1, rec.is_unsafe as u8);
    ctor
  }
}

impl<R: LeanRef> LeanIxonRecursor<R> {
  /// Decode Ixon.Recursor.
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
  pub fn decode(&self) -> IxonRecursor {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let rules_arr = ctor.get(1).as_array();
    let rules =
      rules_arr.map(|x| LeanIxonRecursorRule::new(x.to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let params = self.get_num_64(1);
    let indices = self.get_num_64(2);
    let motives = self.get_num_64(3);
    let minors = self.get_num_64(4);
    let k = self.get_num_8(0) != 0;
    let is_unsafe = self.get_num_8(1) != 0;
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

impl LeanIxonAxiom<LeanOwned> {
  /// Build Ixon.Axiom
  /// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
  pub fn build(ax: &IxonAxiom) -> Self {
    let typ_obj = LeanIxonExpr::build(&ax.typ);
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_num_64(0, ax.lvls);
    ctor.set_num_8(0, ax.is_unsafe as u8);
    ctor
  }
}

impl<R: LeanRef> LeanIxonAxiom<R> {
  /// Decode Ixon.Axiom.
  /// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
  pub fn decode(&self) -> IxonAxiom {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let is_unsafe = self.get_num_8(0) != 0;
    IxonAxiom { is_unsafe, lvls, typ }
  }
}

// =============================================================================
// Quotient
// =============================================================================

impl LeanIxonQuotient<LeanOwned> {
  /// Build Ixon.Quotient
  /// QuotKind is a simple enum stored as scalar u8, not object field.
  /// Scalars ordered by size: lvls(8) + kind(1) + padding(7)
  pub fn build(quot: &IxonQuotient) -> Self {
    let typ_obj = LeanIxonExpr::build(&quot.typ);
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_num_64(0, quot.lvls);
    let kind_val: u8 = match quot.kind {
      crate::ix::env::QuotKind::Type => 0,
      crate::ix::env::QuotKind::Ctor => 1,
      crate::ix::env::QuotKind::Lift => 2,
      crate::ix::env::QuotKind::Ind => 3,
    };
    ctor.set_num_8(0, kind_val);
    ctor
  }
}

impl<R: LeanRef> LeanIxonQuotient<R> {
  /// Decode Ixon.Quotient.
  /// QuotKind is a scalar (not object field). Scalars: lvls(8) + kind(1) + padding(7)
  pub fn decode(&self) -> IxonQuotient {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let kind_val = self.get_num_8(0);
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

impl LeanIxonConstructor<LeanOwned> {
  /// Build Ixon.Constructor
  /// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
  pub fn build(c: &IxonConstructor) -> Self {
    let typ_obj = LeanIxonExpr::build(&c.typ);
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_num_64(0, c.lvls);
    ctor.set_num_64(1, c.cidx);
    ctor.set_num_64(2, c.params);
    ctor.set_num_64(3, c.fields);
    ctor.set_num_8(0, c.is_unsafe as u8);
    ctor
  }
}

impl<R: LeanRef> LeanIxonConstructor<R> {
  /// Decode Ixon.Constructor.
  /// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
  pub fn decode(&self) -> IxonConstructor {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let cidx = self.get_num_64(1);
    let params = self.get_num_64(2);
    let fields = self.get_num_64(3);
    let is_unsafe = self.get_num_8(0) != 0;
    IxonConstructor { is_unsafe, lvls, cidx, params, fields, typ }
  }
}

// =============================================================================
// Inductive
// =============================================================================

impl LeanIxonInductive<LeanOwned> {
  /// Build Ixon.Inductive
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
  pub fn build(ind: &IxonInductive) -> Self {
    let typ_obj = LeanIxonExpr::build(&ind.typ);
    // Build ctors array
    let ctors_arr = LeanArray::alloc(ind.ctors.len());
    for (i, c) in ind.ctors.iter().enumerate() {
      ctors_arr.set(i, LeanIxonConstructor::build(c));
    }
    let ctor = Self::alloc();
    ctor.set_obj(0, typ_obj);
    ctor.set_obj(1, ctors_arr);
    ctor.set_num_64(0, ind.lvls);
    ctor.set_num_64(1, ind.params);
    ctor.set_num_64(2, ind.indices);
    ctor.set_num_64(3, ind.nested);
    ctor.set_num_8(0, ind.recr as u8);
    ctor.set_num_8(1, ind.refl as u8);
    ctor.set_num_8(2, ind.is_unsafe as u8);
    ctor
  }
}

impl<R: LeanRef> LeanIxonInductive<R> {
  /// Decode Ixon.Inductive.
  /// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
  pub fn decode(&self) -> IxonInductive {
    let ctor = self.as_ctor();
    let typ = Arc::new(LeanIxonExpr::new(ctor.get(0).to_owned_ref()).decode());
    let ctors_arr = ctor.get(1).as_array();
    let ctors =
      ctors_arr.map(|x| LeanIxonConstructor::new(x.to_owned_ref()).decode());
    let lvls = self.get_num_64(0);
    let params = self.get_num_64(1);
    let indices = self.get_num_64(2);
    let nested = self.get_num_64(3);
    let recr = self.get_num_8(0) != 0;
    let refl = self.get_num_8(1) != 0;
    let is_unsafe = self.get_num_8(2) != 0;
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

impl LeanIxonInductiveProj<LeanOwned> {
  pub fn build(proj: &InductiveProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = Self::alloc();
    ctor.set_obj(0, block_obj);
    ctor.set_num_64(0, proj.idx);
    ctor
  }
}

impl<R: LeanRef> LeanIxonInductiveProj<R> {
  pub fn decode(&self) -> InductiveProj {
    let ctor = self.as_ctor();
    let block =
      LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
    let idx = self.get_num_64(0);
    InductiveProj { idx, block }
  }
}

impl LeanIxonConstructorProj<LeanOwned> {
  pub fn build(proj: &ConstructorProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = Self::alloc();
    ctor.set_obj(0, block_obj);
    ctor.set_num_64(0, proj.idx);
    ctor.set_num_64(1, proj.cidx);
    ctor
  }
}

impl<R: LeanRef> LeanIxonConstructorProj<R> {
  pub fn decode(&self) -> ConstructorProj {
    let ctor = self.as_ctor();
    let block =
      LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
    let idx = self.get_num_64(0);
    let cidx = self.get_num_64(1);
    ConstructorProj { idx, cidx, block }
  }
}

impl LeanIxonRecursorProj<LeanOwned> {
  pub fn build(proj: &RecursorProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = Self::alloc();
    ctor.set_obj(0, block_obj);
    ctor.set_num_64(0, proj.idx);
    ctor
  }
}

impl<R: LeanRef> LeanIxonRecursorProj<R> {
  pub fn decode(&self) -> RecursorProj {
    let ctor = self.as_ctor();
    let block =
      LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
    let idx = self.get_num_64(0);
    RecursorProj { idx, block }
  }
}

impl LeanIxonDefinitionProj<LeanOwned> {
  pub fn build(proj: &DefinitionProj) -> Self {
    let block_obj = LeanIxAddress::build(&proj.block);
    let ctor = Self::alloc();
    ctor.set_obj(0, block_obj);
    ctor.set_num_64(0, proj.idx);
    ctor
  }
}

impl<R: LeanRef> LeanIxonDefinitionProj<R> {
  pub fn decode(&self) -> DefinitionProj {
    let ctor = self.as_ctor();
    let block =
      LeanIxAddress::from_borrowed(ctor.get(0).as_byte_array()).decode();
    let idx = self.get_num_64(0);
    DefinitionProj { idx, block }
  }
}

// =============================================================================
// MutConst
// =============================================================================

impl LeanIxonMutConst<LeanOwned> {
  pub fn build(mc: &MutConst) -> Self {
    let obj = match mc {
      MutConst::Defn(def) => {
        let ctor = LeanIxonMutConstDefn::alloc();
        ctor.set_obj(0, LeanIxonDefinition::build(def));
        ctor.into()
      },
      MutConst::Indc(ind) => {
        let ctor = LeanIxonMutConstIndc::alloc();
        ctor.set_obj(0, LeanIxonInductive::build(ind));
        ctor.into()
      },
      MutConst::Recr(rec) => {
        let ctor = LeanIxonMutConstRecr::alloc();
        ctor.set_obj(0, LeanIxonRecursor::build(rec));
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxonMutConst<R> {
  pub fn decode(&self) -> MutConst {
    let ctor = self.as_ctor();
    let inner = ctor.get(0);
    match ctor.tag() {
      0 => {
        MutConst::Defn(LeanIxonDefinition::new(inner.to_owned_ref()).decode())
      },
      1 => {
        MutConst::Indc(LeanIxonInductive::new(inner.to_owned_ref()).decode())
      },
      2 => MutConst::Recr(LeanIxonRecursor::new(inner.to_owned_ref()).decode()),
      tag => panic!("Invalid Ixon.MutConst tag: {}", tag),
    }
  }
}

// =============================================================================
// ConstantInfo
// =============================================================================

impl LeanIxonConstantInfo<LeanOwned> {
  /// Build Ixon.ConstantInfo (9 constructors)
  pub fn build(info: &IxonConstantInfo) -> Self {
    let obj = match info {
      IxonConstantInfo::Defn(def) => {
        let ctor = LeanIxonConstantInfoDefn::alloc();
        ctor.set_obj(0, LeanIxonDefinition::build(def));
        ctor.into()
      },
      IxonConstantInfo::Recr(rec) => {
        let ctor = LeanIxonConstantInfoRecr::alloc();
        ctor.set_obj(0, LeanIxonRecursor::build(rec));
        ctor.into()
      },
      IxonConstantInfo::Axio(ax) => {
        let ctor = LeanIxonConstantInfoAxio::alloc();
        ctor.set_obj(0, LeanIxonAxiom::build(ax));
        ctor.into()
      },
      IxonConstantInfo::Quot(quot) => {
        let ctor = LeanIxonConstantInfoQuot::alloc();
        ctor.set_obj(0, LeanIxonQuotient::build(quot));
        ctor.into()
      },
      IxonConstantInfo::CPrj(proj) => {
        let ctor = LeanIxonConstantInfoCPrj::alloc();
        ctor.set_obj(0, LeanIxonConstructorProj::build(proj));
        ctor.into()
      },
      IxonConstantInfo::RPrj(proj) => {
        let ctor = LeanIxonConstantInfoRPrj::alloc();
        ctor.set_obj(0, LeanIxonRecursorProj::build(proj));
        ctor.into()
      },
      IxonConstantInfo::IPrj(proj) => {
        let ctor = LeanIxonConstantInfoIPrj::alloc();
        ctor.set_obj(0, LeanIxonInductiveProj::build(proj));
        ctor.into()
      },
      IxonConstantInfo::DPrj(proj) => {
        let ctor = LeanIxonConstantInfoDPrj::alloc();
        ctor.set_obj(0, LeanIxonDefinitionProj::build(proj));
        ctor.into()
      },
      IxonConstantInfo::Muts(muts) => {
        let arr = LeanArray::alloc(muts.len());
        for (i, mc) in muts.iter().enumerate() {
          arr.set(i, LeanIxonMutConst::build(mc));
        }
        let ctor = LeanIxonConstantInfoMuts::alloc();
        ctor.set_obj(0, arr);
        ctor.into()
      },
    };
    Self::new(obj)
  }
}

impl<R: LeanRef> LeanIxonConstantInfo<R> {
  /// Decode Ixon.ConstantInfo.
  pub fn decode(&self) -> IxonConstantInfo {
    let ctor = self.as_ctor();
    let inner = ctor.get(0);
    match ctor.tag() {
      0 => IxonConstantInfo::Defn(
        LeanIxonDefinition::new(inner.to_owned_ref()).decode(),
      ),
      1 => IxonConstantInfo::Recr(
        LeanIxonRecursor::new(inner.to_owned_ref()).decode(),
      ),
      2 => IxonConstantInfo::Axio(
        LeanIxonAxiom::new(inner.to_owned_ref()).decode(),
      ),
      3 => IxonConstantInfo::Quot(
        LeanIxonQuotient::new(inner.to_owned_ref()).decode(),
      ),
      4 => IxonConstantInfo::CPrj(
        LeanIxonConstructorProj::new(inner.to_owned_ref()).decode(),
      ),
      5 => IxonConstantInfo::RPrj(
        LeanIxonRecursorProj::new(inner.to_owned_ref()).decode(),
      ),
      6 => IxonConstantInfo::IPrj(
        LeanIxonInductiveProj::new(inner.to_owned_ref()).decode(),
      ),
      7 => IxonConstantInfo::DPrj(
        LeanIxonDefinitionProj::new(inner.to_owned_ref()).decode(),
      ),
      8 => {
        let arr = inner.as_array();
        let muts =
          arr.map(|x| LeanIxonMutConst::new(x.to_owned_ref()).decode());
        IxonConstantInfo::Muts(muts)
      },
      tag => panic!("Invalid Ixon.ConstantInfo tag: {}", tag),
    }
  }
}

// =============================================================================
// Constant
// =============================================================================

impl LeanIxonConstant<LeanOwned> {
  /// Build Ixon.Constant
  pub fn build(constant: &IxonConstant) -> Self {
    let info_obj = LeanIxonConstantInfo::build(&constant.info);
    let sharing_obj = LeanIxonExpr::build_array(&constant.sharing);
    let refs_obj = LeanIxAddress::build_array(&constant.refs);
    let univs_obj = LeanIxonUniv::build_array(&constant.univs);
    let ctor = LeanIxonConstant::alloc();
    ctor.set_obj(0, info_obj);
    ctor.set_obj(1, sharing_obj);
    ctor.set_obj(2, refs_obj);
    ctor.set_obj(3, univs_obj);
    Self::new(ctor.into())
  }
}

impl<R: LeanRef> LeanIxonConstant<R> {
  /// Decode Ixon.Constant.
  pub fn decode(&self) -> IxonConstant {
    let ctor = self.as_ctor();
    IxonConstant {
      info: LeanIxonConstantInfo::new(ctor.get(0).to_owned_ref()).decode(),
      sharing: LeanIxonExpr::decode_array(&ctor.get(1).as_array()),
      refs: LeanIxAddress::decode_array(ctor.get(2).as_array()),
      univs: LeanIxonUniv::decode_array(&ctor.get(3).as_array()),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Definition.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition(
  obj: LeanIxonDefinition<LeanBorrowed<'_>>,
) -> LeanIxonDefinition<LeanOwned> {
  let def = obj.decode();
  LeanIxonDefinition::build(&def)
}

/// Round-trip Ixon.Recursor.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor(
  obj: LeanIxonRecursor<LeanBorrowed<'_>>,
) -> LeanIxonRecursor<LeanOwned> {
  let rec = obj.decode();
  LeanIxonRecursor::build(&rec)
}

/// Round-trip Ixon.Axiom.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_axiom(
  obj: LeanIxonAxiom<LeanBorrowed<'_>>,
) -> LeanIxonAxiom<LeanOwned> {
  let ax = obj.decode();
  LeanIxonAxiom::build(&ax)
}

/// Round-trip Ixon.Quotient.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quotient(
  obj: LeanIxonQuotient<LeanBorrowed<'_>>,
) -> LeanIxonQuotient<LeanOwned> {
  let quot = obj.decode();
  LeanIxonQuotient::build(&quot)
}

/// Round-trip Ixon.ConstantInfo.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_info(
  obj: LeanIxonConstantInfo<LeanBorrowed<'_>>,
) -> LeanIxonConstantInfo<LeanOwned> {
  let info = obj.decode();
  LeanIxonConstantInfo::build(&info)
}

/// Round-trip Ixon.Constant.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant(
  obj: LeanIxonConstant<LeanBorrowed<'_>>,
) -> LeanIxonConstant<LeanOwned> {
  let constant = obj.decode();
  LeanIxonConstant::build(&constant)
}

/// Round-trip Ixon.RecursorRule.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_rule(
  obj: LeanIxonRecursorRule<LeanBorrowed<'_>>,
) -> LeanIxonRecursorRule<LeanOwned> {
  let rule = obj.decode();
  LeanIxonRecursorRule::build(&rule)
}

/// Round-trip Ixon.Constructor.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor(
  obj: LeanIxonConstructor<LeanBorrowed<'_>>,
) -> LeanIxonConstructor<LeanOwned> {
  let c = obj.decode();
  LeanIxonConstructor::build(&c)
}

/// Round-trip Ixon.Inductive.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive(
  obj: LeanIxonInductive<LeanBorrowed<'_>>,
) -> LeanIxonInductive<LeanOwned> {
  let ind = obj.decode();
  LeanIxonInductive::build(&ind)
}

/// Round-trip Ixon.InductiveProj.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive_proj(
  obj: LeanIxonInductiveProj<LeanBorrowed<'_>>,
) -> LeanIxonInductiveProj<LeanOwned> {
  let proj = obj.decode();
  LeanIxonInductiveProj::build(&proj)
}

/// Round-trip Ixon.ConstructorProj.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor_proj(
  obj: LeanIxonConstructorProj<LeanBorrowed<'_>>,
) -> LeanIxonConstructorProj<LeanOwned> {
  let proj = obj.decode();
  LeanIxonConstructorProj::build(&proj)
}

/// Round-trip Ixon.RecursorProj.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_proj(
  obj: LeanIxonRecursorProj<LeanBorrowed<'_>>,
) -> LeanIxonRecursorProj<LeanOwned> {
  let proj = obj.decode();
  LeanIxonRecursorProj::build(&proj)
}

/// Round-trip Ixon.DefinitionProj.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_proj(
  obj: LeanIxonDefinitionProj<LeanBorrowed<'_>>,
) -> LeanIxonDefinitionProj<LeanOwned> {
  let proj = obj.decode();
  LeanIxonDefinitionProj::build(&proj)
}

/// Round-trip Ixon.MutConst.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_mut_const(
  obj: LeanIxonMutConst<LeanBorrowed<'_>>,
) -> LeanIxonMutConst<LeanOwned> {
  let mc = obj.decode();
  LeanIxonMutConst::build(&mc)
}
