//! Ixon constant types build/decode/roundtrip FFI.
//!
//! Includes: Definition, Axiom, Quotient, RecursorRule, Recursor, Constructor,
//! Inductive, InductiveProj, ConstructorProj, RecursorProj, DefinitionProj,
//! MutConst, ConstantInfo, Constant

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::constant::{
  Axiom, Constant, ConstantInfo, Constructor, ConstructorProj, DefKind,
  Definition, DefinitionProj, Inductive, InductiveProj, MutConst, Quotient,
  Recursor, RecursorProj, RecursorRule,
};
use crate::lean::obj::{
  IxAddress, IxonAxiom, IxonConstant, IxonConstantInfo, IxonConstructor,
  IxonConstructorProj, IxonDefinition, IxonDefinitionProj, IxonExpr,
  IxonInductive, IxonInductiveProj, IxonMutConst, IxonQuotient, IxonRecursor,
  IxonRecursorProj, IxonRecursorRule, LeanArray, LeanByteArray, LeanCtor,
  LeanObj,
};

use super::univ::*;

impl IxAddress {
  /// Build Address from Ixon Address type (which is just a [u8; 32]).
  pub fn build_from_ixon(addr: &Address) -> Self {
    LeanByteArray::from_bytes(addr.as_bytes())
  }

  /// Build an Array of Addresses.
  pub fn build_array(addrs: &[Address]) -> LeanArray {
    let arr = LeanArray::alloc(addrs.len());
    for (i, addr) in addrs.iter().enumerate() {
      arr.set(i, Self::build_from_ixon(addr));
    }
    arr
  }

  /// Decode a ByteArray (Address) to Address.
  pub fn decode_ixon(self) -> Address {
    Address::from_slice(&self.as_bytes()[..32]).expect("Address should be 32 bytes")
  }

  /// Decode Array Address.
  pub fn decode_array(obj: LeanObj) -> Vec<Address> {
    let arr = unsafe { LeanArray::from_raw(obj.as_ptr()) };
    arr.map(|elem| {
      let ba = unsafe { LeanByteArray::from_raw(elem.as_ptr()) };
      ba.decode_ixon()
    })
  }
}

impl IxonDefinition {
  /// Build Ixon.Definition
  pub fn build(def: &Definition) -> Self {
    let typ_obj = IxonExpr::build(&def.typ);
    let value_obj = IxonExpr::build(&def.value);
    let ctor = LeanCtor::alloc(0, 2, 16);
    ctor.set(0, typ_obj);
    ctor.set(1, value_obj);
    ctor.set_u64(2 * 8, def.lvls);
    let kind_val: u8 = match def.kind {
      DefKind::Definition => 0,
      DefKind::Opaque => 1,
      DefKind::Theorem => 2,
    };
    ctor.set_u8(2 * 8 + 8, kind_val);
    let safety_val: u8 = match def.safety {
      crate::ix::env::DefinitionSafety::Unsafe => 0,
      crate::ix::env::DefinitionSafety::Safe => 1,
      crate::ix::env::DefinitionSafety::Partial => 2,
    };
    ctor.set_u8(2 * 8 + 9, safety_val);
    Self::new(*ctor)
  }

  /// Decode Ixon.Definition.
  pub fn decode(self) -> Definition {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(2, 0);
    let kind_val = ctor.scalar_u8(2, 8);
    let kind = match kind_val {
      0 => DefKind::Definition,
      1 => DefKind::Opaque,
      2 => DefKind::Theorem,
      _ => panic!("Invalid DefKind: {kind_val}"),
    };
    let safety_val = ctor.scalar_u8(2, 9);
    let safety = match safety_val {
      0 => crate::ix::env::DefinitionSafety::Unsafe,
      1 => crate::ix::env::DefinitionSafety::Safe,
      2 => crate::ix::env::DefinitionSafety::Partial,
      _ => panic!("Invalid DefinitionSafety: {safety_val}"),
    };
    Definition {
      kind,
      safety,
      lvls,
      typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()),
      value: Arc::new(IxonExpr::new(ctor.get(1)).decode()),
    }
  }
}

impl IxonRecursorRule {
  /// Build Ixon.RecursorRule
  pub fn build(rule: &RecursorRule) -> Self {
    let rhs_obj = IxonExpr::build(&rule.rhs);
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, rhs_obj);
    ctor.set_u64(8, rule.fields);
    Self::new(*ctor)
  }

  /// Decode Ixon.RecursorRule.
  pub fn decode(self) -> RecursorRule {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let fields = ctor.scalar_u64(1, 0);
    RecursorRule { fields, rhs: Arc::new(IxonExpr::new(ctor.get(0)).decode()) }
  }
}

impl IxonRecursor {
  /// Build Ixon.Recursor
  pub fn build(rec: &Recursor) -> Self {
    let typ_obj = IxonExpr::build(&rec.typ);
    let rules_arr = LeanArray::alloc(rec.rules.len());
    for (i, rule) in rec.rules.iter().enumerate() {
      rules_arr.set(i, IxonRecursorRule::build(rule));
    }
    let ctor = LeanCtor::alloc(0, 2, 48);
    ctor.set(0, typ_obj);
    ctor.set(1, rules_arr);
    ctor.set_u64(2 * 8, rec.lvls);
    ctor.set_u64(2 * 8 + 8, rec.params);
    ctor.set_u64(2 * 8 + 16, rec.indices);
    ctor.set_u64(2 * 8 + 24, rec.motives);
    ctor.set_u64(2 * 8 + 32, rec.minors);
    ctor.set_u8(2 * 8 + 40, if rec.k { 1 } else { 0 });
    ctor.set_u8(2 * 8 + 41, if rec.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Recursor.
  pub fn decode(self) -> Recursor {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(2, 0);
    let params = ctor.scalar_u64(2, 8);
    let indices = ctor.scalar_u64(2, 16);
    let motives = ctor.scalar_u64(2, 24);
    let minors = ctor.scalar_u64(2, 32);
    let k = ctor.scalar_bool(2, 40);
    let is_unsafe = ctor.scalar_bool(2, 41);
    let rules_arr = unsafe { LeanArray::from_raw(ctor.get(1).as_ptr()) };
    let rules = rules_arr.map(|r| IxonRecursorRule::new(r).decode());
    Recursor {
      k,
      is_unsafe,
      lvls,
      params,
      indices,
      motives,
      minors,
      typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()),
      rules,
    }
  }
}

impl IxonAxiom {
  /// Build Ixon.Axiom
  pub fn build(ax: &Axiom) -> Self {
    let typ_obj = IxonExpr::build(&ax.typ);
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, typ_obj);
    ctor.set_u64(8, ax.lvls);
    ctor.set_u8(8 + 8, if ax.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Axiom.
  pub fn decode(self) -> Axiom {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(1, 0);
    let is_unsafe = ctor.scalar_bool(1, 8);
    Axiom {
      is_unsafe,
      lvls,
      typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()),
    }
  }
}

impl IxonQuotient {
  /// Build Ixon.Quotient
  pub fn build(quot: &Quotient) -> Self {
    let typ_obj = IxonExpr::build(&quot.typ);
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, typ_obj);
    ctor.set_u64(8, quot.lvls);
    let kind_val: u8 = match quot.kind {
      crate::ix::env::QuotKind::Type => 0,
      crate::ix::env::QuotKind::Ctor => 1,
      crate::ix::env::QuotKind::Lift => 2,
      crate::ix::env::QuotKind::Ind => 3,
    };
    ctor.set_u8(8 + 8, kind_val);
    Self::new(*ctor)
  }

  /// Decode Ixon.Quotient.
  pub fn decode(self) -> Quotient {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(1, 0);
    let kind_val = ctor.scalar_u8(1, 8);
    let kind = match kind_val {
      0 => crate::ix::env::QuotKind::Type,
      1 => crate::ix::env::QuotKind::Ctor,
      2 => crate::ix::env::QuotKind::Lift,
      3 => crate::ix::env::QuotKind::Ind,
      _ => panic!("Invalid QuotKind: {kind_val}"),
    };
    Quotient { kind, lvls, typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()) }
  }
}

impl IxonConstructor {
  /// Build Ixon.Constructor
  pub fn build(c: &Constructor) -> Self {
    let typ_obj = IxonExpr::build(&c.typ);
    let ctor = LeanCtor::alloc(0, 1, 40);
    ctor.set(0, typ_obj);
    ctor.set_u64(8, c.lvls);
    ctor.set_u64(8 + 8, c.cidx);
    ctor.set_u64(8 + 16, c.params);
    ctor.set_u64(8 + 24, c.fields);
    ctor.set_u8(8 + 32, if c.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Constructor.
  pub fn decode(self) -> Constructor {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(1, 0);
    let cidx = ctor.scalar_u64(1, 8);
    let params = ctor.scalar_u64(1, 16);
    let fields = ctor.scalar_u64(1, 24);
    let is_unsafe = ctor.scalar_bool(1, 32);
    Constructor {
      is_unsafe,
      lvls,
      cidx,
      params,
      fields,
      typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()),
    }
  }
}

impl IxonInductive {
  /// Build Ixon.Inductive
  pub fn build(ind: &Inductive) -> Self {
    let typ_obj = IxonExpr::build(&ind.typ);
    let ctors_arr = LeanArray::alloc(ind.ctors.len());
    for (i, c) in ind.ctors.iter().enumerate() {
      ctors_arr.set(i, IxonConstructor::build(c));
    }
    let ctor = LeanCtor::alloc(0, 2, 40);
    ctor.set(0, typ_obj);
    ctor.set(1, ctors_arr);
    ctor.set_u64(2 * 8, ind.lvls);
    ctor.set_u64(2 * 8 + 8, ind.params);
    ctor.set_u64(2 * 8 + 16, ind.indices);
    ctor.set_u64(2 * 8 + 24, ind.nested);
    ctor.set_u8(2 * 8 + 32, if ind.recr { 1 } else { 0 });
    ctor.set_u8(2 * 8 + 33, if ind.refl { 1 } else { 0 });
    ctor.set_u8(2 * 8 + 34, if ind.is_unsafe { 1 } else { 0 });
    Self::new(*ctor)
  }

  /// Decode Ixon.Inductive.
  pub fn decode(self) -> Inductive {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let lvls = ctor.scalar_u64(2, 0);
    let params = ctor.scalar_u64(2, 8);
    let indices = ctor.scalar_u64(2, 16);
    let nested = ctor.scalar_u64(2, 24);
    let recr = ctor.scalar_bool(2, 32);
    let refl = ctor.scalar_bool(2, 33);
    let is_unsafe = ctor.scalar_bool(2, 34);
    let ctors_arr = unsafe { LeanArray::from_raw(ctor.get(1).as_ptr()) };
    let ctors = ctors_arr.map(|c| IxonConstructor::new(c).decode());
    Inductive {
      recr,
      refl,
      is_unsafe,
      lvls,
      params,
      indices,
      nested,
      typ: Arc::new(IxonExpr::new(ctor.get(0)).decode()),
      ctors,
    }
  }
}

impl IxonInductiveProj {
  /// Build Ixon.InductiveProj
  pub fn build(proj: &InductiveProj) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, IxAddress::build_from_ixon(&proj.block));
    ctor.set_u64(8, proj.idx);
    Self::new(*ctor)
  }

  /// Decode Ixon.InductiveProj.
  pub fn decode(self) -> InductiveProj {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let idx = ctor.scalar_u64(1, 0);
    let ba = unsafe { LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    InductiveProj { idx, block: ba.decode_ixon() }
  }
}

impl IxonConstructorProj {
  /// Build Ixon.ConstructorProj
  pub fn build(proj: &ConstructorProj) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 16);
    ctor.set(0, IxAddress::build_from_ixon(&proj.block));
    ctor.set_u64(8, proj.idx);
    ctor.set_u64(8 + 8, proj.cidx);
    Self::new(*ctor)
  }

  /// Decode Ixon.ConstructorProj.
  pub fn decode(self) -> ConstructorProj {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let idx = ctor.scalar_u64(1, 0);
    let cidx = ctor.scalar_u64(1, 8);
    let ba = unsafe { LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    ConstructorProj { idx, cidx, block: ba.decode_ixon() }
  }
}

impl IxonRecursorProj {
  /// Build Ixon.RecursorProj
  pub fn build(proj: &RecursorProj) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, IxAddress::build_from_ixon(&proj.block));
    ctor.set_u64(8, proj.idx);
    Self::new(*ctor)
  }

  /// Decode Ixon.RecursorProj.
  pub fn decode(self) -> RecursorProj {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let idx = ctor.scalar_u64(1, 0);
    let ba = unsafe { LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    RecursorProj { idx, block: ba.decode_ixon() }
  }
}

impl IxonDefinitionProj {
  /// Build Ixon.DefinitionProj
  pub fn build(proj: &DefinitionProj) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 8);
    ctor.set(0, IxAddress::build_from_ixon(&proj.block));
    ctor.set_u64(8, proj.idx);
    Self::new(*ctor)
  }

  /// Decode Ixon.DefinitionProj.
  pub fn decode(self) -> DefinitionProj {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    let idx = ctor.scalar_u64(1, 0);
    let ba = unsafe { LeanByteArray::from_raw(ctor.get(0).as_ptr()) };
    DefinitionProj { idx, block: ba.decode_ixon() }
  }
}

impl IxonMutConst {
  /// Build Ixon.MutConst
  pub fn build(mc: &MutConst) -> Self {
    let obj = match mc {
      MutConst::Defn(def) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, IxonDefinition::build(def));
        *ctor
      },
      MutConst::Indc(ind) => {
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, IxonInductive::build(ind));
        *ctor
      },
      MutConst::Recr(rec) => {
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, IxonRecursor::build(rec));
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.MutConst.
  pub fn decode(self) -> MutConst {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    match ctor.tag() {
      0 => MutConst::Defn(IxonDefinition::new(ctor.get(0)).decode()),
      1 => MutConst::Indc(IxonInductive::new(ctor.get(0)).decode()),
      2 => MutConst::Recr(IxonRecursor::new(ctor.get(0)).decode()),
      tag => panic!("Invalid Ixon.MutConst tag: {tag}"),
    }
  }
}

impl IxonConstantInfo {
  /// Build Ixon.ConstantInfo (9 constructors)
  pub fn build(info: &ConstantInfo) -> Self {
    let obj = match info {
      ConstantInfo::Defn(def) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, IxonDefinition::build(def));
        *ctor
      },
      ConstantInfo::Recr(rec) => {
        let ctor = LeanCtor::alloc(1, 1, 0);
        ctor.set(0, IxonRecursor::build(rec));
        *ctor
      },
      ConstantInfo::Axio(ax) => {
        let ctor = LeanCtor::alloc(2, 1, 0);
        ctor.set(0, IxonAxiom::build(ax));
        *ctor
      },
      ConstantInfo::Quot(quot) => {
        let ctor = LeanCtor::alloc(3, 1, 0);
        ctor.set(0, IxonQuotient::build(quot));
        *ctor
      },
      ConstantInfo::CPrj(proj) => {
        let ctor = LeanCtor::alloc(4, 1, 0);
        ctor.set(0, IxonConstructorProj::build(proj));
        *ctor
      },
      ConstantInfo::RPrj(proj) => {
        let ctor = LeanCtor::alloc(5, 1, 0);
        ctor.set(0, IxonRecursorProj::build(proj));
        *ctor
      },
      ConstantInfo::IPrj(proj) => {
        let ctor = LeanCtor::alloc(6, 1, 0);
        ctor.set(0, IxonInductiveProj::build(proj));
        *ctor
      },
      ConstantInfo::DPrj(proj) => {
        let ctor = LeanCtor::alloc(7, 1, 0);
        ctor.set(0, IxonDefinitionProj::build(proj));
        *ctor
      },
      ConstantInfo::Muts(muts) => {
        let arr = LeanArray::alloc(muts.len());
        for (i, mc) in muts.iter().enumerate() {
          arr.set(i, IxonMutConst::build(mc));
        }
        let ctor = LeanCtor::alloc(8, 1, 0);
        ctor.set(0, arr);
        *ctor
      },
    };
    Self::new(obj)
  }

  /// Decode Ixon.ConstantInfo.
  pub fn decode(self) -> ConstantInfo {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    match ctor.tag() {
      0 => ConstantInfo::Defn(IxonDefinition::new(ctor.get(0)).decode()),
      1 => ConstantInfo::Recr(IxonRecursor::new(ctor.get(0)).decode()),
      2 => ConstantInfo::Axio(IxonAxiom::new(ctor.get(0)).decode()),
      3 => ConstantInfo::Quot(IxonQuotient::new(ctor.get(0)).decode()),
      4 => {
        ConstantInfo::CPrj(IxonConstructorProj::new(ctor.get(0)).decode())
      },
      5 => ConstantInfo::RPrj(IxonRecursorProj::new(ctor.get(0)).decode()),
      6 => ConstantInfo::IPrj(IxonInductiveProj::new(ctor.get(0)).decode()),
      7 => {
        ConstantInfo::DPrj(IxonDefinitionProj::new(ctor.get(0)).decode())
      },
      8 => {
        let arr = unsafe { LeanArray::from_raw(ctor.get(0).as_ptr()) };
        let muts = arr.map(|m| IxonMutConst::new(m).decode());
        ConstantInfo::Muts(muts)
      },
      tag => panic!("Invalid Ixon.ConstantInfo tag: {tag}"),
    }
  }
}

impl IxonConstant {
  /// Build Ixon.Constant
  pub fn build(constant: &Constant) -> Self {
    let info_obj = IxonConstantInfo::build(&constant.info);
    let sharing_obj = IxonExpr::build_array(&constant.sharing);
    let refs_obj = IxAddress::build_array(&constant.refs);
    let univs_obj = IxonUniv::build_array(&constant.univs);
    let ctor = LeanCtor::alloc(0, 4, 0);
    ctor.set(0, info_obj);
    ctor.set(1, sharing_obj);
    ctor.set(2, refs_obj);
    ctor.set(3, univs_obj);
    Self::new(*ctor)
  }

  /// Decode Ixon.Constant.
  pub fn decode(self) -> Constant {
    let ctor = unsafe { LeanCtor::from_raw(self.as_ptr()) };
    Constant {
      info: IxonConstantInfo::new(ctor.get(0)).decode(),
      sharing: IxonExpr::decode_array(ctor.get(1)),
      refs: IxAddress::decode_array(ctor.get(2)),
      univs: IxonUniv::decode_array(ctor.get(3)),
    }
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Definition.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition(obj: LeanObj) -> LeanObj {
  let def = IxonDefinition::new(obj).decode();
  IxonDefinition::build(&def).into()
}

/// Round-trip Ixon.Recursor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor(obj: LeanObj) -> LeanObj {
  let rec = IxonRecursor::new(obj).decode();
  IxonRecursor::build(&rec).into()
}

/// Round-trip Ixon.Axiom.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_axiom(obj: LeanObj) -> LeanObj {
  let ax = IxonAxiom::new(obj).decode();
  IxonAxiom::build(&ax).into()
}

/// Round-trip Ixon.Quotient.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quotient(obj: LeanObj) -> LeanObj {
  let quot = IxonQuotient::new(obj).decode();
  IxonQuotient::build(&quot).into()
}

/// Round-trip Ixon.ConstantInfo.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_info(obj: LeanObj) -> LeanObj {
  let info = IxonConstantInfo::new(obj).decode();
  IxonConstantInfo::build(&info).into()
}

/// Round-trip Ixon.Constant.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant(obj: LeanObj) -> LeanObj {
  let constant = IxonConstant::new(obj).decode();
  IxonConstant::build(&constant).into()
}

/// Round-trip Ixon.RecursorRule.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_rule(obj: LeanObj) -> LeanObj {
  let rule = IxonRecursorRule::new(obj).decode();
  IxonRecursorRule::build(&rule).into()
}

/// Round-trip Ixon.Constructor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor(obj: LeanObj) -> LeanObj {
  let c = IxonConstructor::new(obj).decode();
  IxonConstructor::build(&c).into()
}

/// Round-trip Ixon.Inductive.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive(obj: LeanObj) -> LeanObj {
  let ind = IxonInductive::new(obj).decode();
  IxonInductive::build(&ind).into()
}

/// Round-trip Ixon.InductiveProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive_proj(obj: LeanObj) -> LeanObj {
  let proj = IxonInductiveProj::new(obj).decode();
  IxonInductiveProj::build(&proj).into()
}

/// Round-trip Ixon.ConstructorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor_proj(
  obj: LeanObj,
) -> LeanObj {
  let proj = IxonConstructorProj::new(obj).decode();
  IxonConstructorProj::build(&proj).into()
}

/// Round-trip Ixon.RecursorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_proj(obj: LeanObj) -> LeanObj {
  let proj = IxonRecursorProj::new(obj).decode();
  IxonRecursorProj::build(&proj).into()
}

/// Round-trip Ixon.DefinitionProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_proj(
  obj: LeanObj,
) -> LeanObj {
  let proj = IxonDefinitionProj::new(obj).decode();
  IxonDefinitionProj::build(&proj).into()
}

/// Round-trip Ixon.MutConst.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_mut_const(obj: LeanObj) -> LeanObj {
  let mc = IxonMutConst::new(obj).decode();
  IxonMutConst::build(&mc).into()
}
