//! Ixon constant types build/decode/roundtrip FFI.
//!
//! Includes: Definition, Axiom, Quotient, RecursorRule, Recursor, Constructor,
//! Inductive, InductiveProj, ConstructorProj, RecursorProj, DefinitionProj,
//! MutConst, ConstantInfo, Constant

use std::sync::Arc;

use crate::ix::address::Address;
use crate::ix::ixon::constant::{
  Axiom as IxonAxiom, Constant as IxonConstant,
  ConstantInfo as IxonConstantInfo, Constructor as IxonConstructor,
  ConstructorProj, DefKind, Definition as IxonDefinition, DefinitionProj,
  Inductive as IxonInductive, InductiveProj, MutConst,
  Quotient as IxonQuotient, Recursor as IxonRecursor, RecursorProj,
  RecursorRule as IxonRecursorRule,
};
use crate::lean::obj::{IxAddress, LeanArray, LeanByteArray, LeanCtor, LeanObj};

use crate::lean::ffi::ixon::expr::{
  build_ixon_expr, build_ixon_expr_array, decode_ixon_expr,
  decode_ixon_expr_array,
};
use crate::lean::ffi::ixon::univ::{build_ixon_univ_array, decode_ixon_univ_array};

/// Build Address from Ixon Address type (which is just a [u8; 32]).
pub fn build_address_from_ixon(addr: &Address) -> IxAddress {
  LeanByteArray::from_bytes(addr.as_bytes())
}

/// Build an Array of Addresses.
pub fn build_address_array(addrs: &[Address]) -> LeanArray {
  let arr = LeanArray::alloc(addrs.len());
  for (i, addr) in addrs.iter().enumerate() {
    arr.set(i, build_address_from_ixon(addr));
  }
  arr
}

/// Build Ixon.Definition
/// Lean stores scalar fields ordered by size (largest first).
/// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
pub fn build_ixon_definition(def: &IxonDefinition) -> LeanObj {
  let typ_obj = build_ixon_expr(&def.typ);
  let value_obj = build_ixon_expr(&def.value);
  // 2 obj fields, 16 scalar bytes (lvls(8) + kind(1) + safety(1) + padding(6))
  let ctor = LeanCtor::alloc(0, 2, 16);
  ctor.set(0, typ_obj);
  ctor.set(1, value_obj);
  // Scalar offsets from obj_cptr: 2*8=16 for lvls, 2*8+8=24 for kind, 2*8+9=25 for safety
  ctor.set_u64(16, def.lvls);
  let kind_val: u8 = match def.kind {
    DefKind::Definition => 0,
    DefKind::Opaque => 1,
    DefKind::Theorem => 2,
  };
  ctor.set_u8(24, kind_val);
  let safety_val: u8 = match def.safety {
    crate::ix::env::DefinitionSafety::Unsafe => 0,
    crate::ix::env::DefinitionSafety::Safe => 1,
    crate::ix::env::DefinitionSafety::Partial => 2,
  };
  ctor.set_u8(25, safety_val);
  *ctor
}

/// Build Ixon.RecursorRule
pub fn build_ixon_recursor_rule(rule: &IxonRecursorRule) -> LeanObj {
  let rhs_obj = build_ixon_expr(&rule.rhs);
  // 1 obj field, 8 scalar bytes
  let ctor = LeanCtor::alloc(0, 1, 8);
  ctor.set(0, rhs_obj);
  ctor.set_u64(8, rule.fields);
  *ctor
}

/// Build Ixon.Recursor
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
pub fn build_ixon_recursor(rec: &IxonRecursor) -> LeanObj {
  let typ_obj = build_ixon_expr(&rec.typ);
  // Build rules array
  let rules_arr = LeanArray::alloc(rec.rules.len());
  for (i, rule) in rec.rules.iter().enumerate() {
    rules_arr.set(i, build_ixon_recursor_rule(rule));
  }
  // 2 obj fields (typ, rules), 48 scalar bytes (5×8 + 1 + 1 + 6 padding)
  let ctor = LeanCtor::alloc(0, 2, 48);
  ctor.set(0, typ_obj);
  ctor.set(1, rules_arr);
  // Scalar offsets from obj_cptr: 2*8=16 base
  ctor.set_u64(16, rec.lvls);
  ctor.set_u64(24, rec.params);
  ctor.set_u64(32, rec.indices);
  ctor.set_u64(40, rec.motives);
  ctor.set_u64(48, rec.minors);
  ctor.set_u8(56, if rec.k { 1 } else { 0 });
  ctor.set_u8(57, if rec.is_unsafe { 1 } else { 0 });
  *ctor
}

/// Build Ixon.Axiom
/// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
pub fn build_ixon_axiom(ax: &IxonAxiom) -> LeanObj {
  let typ_obj = build_ixon_expr(&ax.typ);
  // 1 obj field, 16 scalar bytes (lvls(8) + isUnsafe(1) + padding(7))
  let ctor = LeanCtor::alloc(0, 1, 16);
  ctor.set(0, typ_obj);
  // Scalar offsets from obj_cptr: 1*8=8 base
  ctor.set_u64(8, ax.lvls);
  ctor.set_u8(16, if ax.is_unsafe { 1 } else { 0 });
  *ctor
}

/// Build Ixon.Quotient
/// QuotKind is a simple enum stored as scalar u8, not object field.
/// Scalars ordered by size: lvls(8) + kind(1) + padding(7)
pub fn build_ixon_quotient(quot: &IxonQuotient) -> LeanObj {
  let typ_obj = build_ixon_expr(&quot.typ);
  // 1 obj field (typ), 16 scalar bytes (lvls(8) + kind(1) + padding(7))
  let ctor = LeanCtor::alloc(0, 1, 16);
  ctor.set(0, typ_obj);
  // Scalar offsets from obj_cptr: 1*8=8 base
  ctor.set_u64(8, quot.lvls);
  let kind_val: u8 = match quot.kind {
    crate::ix::env::QuotKind::Type => 0,
    crate::ix::env::QuotKind::Ctor => 1,
    crate::ix::env::QuotKind::Lift => 2,
    crate::ix::env::QuotKind::Ind => 3,
  };
  ctor.set_u8(16, kind_val);
  *ctor
}

/// Build Ixon.Constructor
/// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
pub fn build_ixon_constructor(c: &IxonConstructor) -> LeanObj {
  let typ_obj = build_ixon_expr(&c.typ);
  // 1 obj field, 40 scalar bytes (4×8 + 1 + 7 padding)
  let ctor = LeanCtor::alloc(0, 1, 40);
  ctor.set(0, typ_obj);
  // Scalar offsets from obj_cptr: 1*8=8 base
  ctor.set_u64(8, c.lvls);
  ctor.set_u64(16, c.cidx);
  ctor.set_u64(24, c.params);
  ctor.set_u64(32, c.fields);
  ctor.set_u8(40, if c.is_unsafe { 1 } else { 0 });
  *ctor
}

/// Build Ixon.Inductive
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
pub fn build_ixon_inductive(ind: &IxonInductive) -> LeanObj {
  let typ_obj = build_ixon_expr(&ind.typ);
  // Build ctors array
  let ctors_arr = LeanArray::alloc(ind.ctors.len());
  for (i, c) in ind.ctors.iter().enumerate() {
    ctors_arr.set(i, build_ixon_constructor(c));
  }
  // 2 obj fields, 40 scalar bytes (4×8 + 3 + 5 padding)
  let ctor = LeanCtor::alloc(0, 2, 40);
  ctor.set(0, typ_obj);
  ctor.set(1, ctors_arr);
  // Scalar offsets from obj_cptr: 2*8=16 base
  ctor.set_u64(16, ind.lvls);
  ctor.set_u64(24, ind.params);
  ctor.set_u64(32, ind.indices);
  ctor.set_u64(40, ind.nested);
  ctor.set_u8(48, if ind.recr { 1 } else { 0 });
  ctor.set_u8(49, if ind.refl { 1 } else { 0 });
  ctor.set_u8(50, if ind.is_unsafe { 1 } else { 0 });
  *ctor
}

/// Build Ixon.InductiveProj
pub fn build_inductive_proj(proj: &InductiveProj) -> LeanObj {
  let block_obj = build_address_from_ixon(&proj.block);
  let ctor = LeanCtor::alloc(0, 1, 8);
  ctor.set(0, block_obj);
  ctor.set_u64(8, proj.idx);
  *ctor
}

/// Build Ixon.ConstructorProj
pub fn build_constructor_proj(proj: &ConstructorProj) -> LeanObj {
  let block_obj = build_address_from_ixon(&proj.block);
  let ctor = LeanCtor::alloc(0, 1, 16);
  ctor.set(0, block_obj);
  ctor.set_u64(8, proj.idx);
  ctor.set_u64(16, proj.cidx);
  *ctor
}

/// Build Ixon.RecursorProj
pub fn build_recursor_proj(proj: &RecursorProj) -> LeanObj {
  let block_obj = build_address_from_ixon(&proj.block);
  let ctor = LeanCtor::alloc(0, 1, 8);
  ctor.set(0, block_obj);
  ctor.set_u64(8, proj.idx);
  *ctor
}

/// Build Ixon.DefinitionProj
pub fn build_definition_proj(proj: &DefinitionProj) -> LeanObj {
  let block_obj = build_address_from_ixon(&proj.block);
  let ctor = LeanCtor::alloc(0, 1, 8);
  ctor.set(0, block_obj);
  ctor.set_u64(8, proj.idx);
  *ctor
}

/// Build Ixon.MutConst
pub fn build_mut_const(mc: &MutConst) -> LeanObj {
  match mc {
    MutConst::Defn(def) => {
      let def_obj = build_ixon_definition(def);
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, def_obj);
      *ctor
    },
    MutConst::Indc(ind) => {
      let ind_obj = build_ixon_inductive(ind);
      let ctor = LeanCtor::alloc(1, 1, 0);
      ctor.set(0, ind_obj);
      *ctor
    },
    MutConst::Recr(rec) => {
      let rec_obj = build_ixon_recursor(rec);
      let ctor = LeanCtor::alloc(2, 1, 0);
      ctor.set(0, rec_obj);
      *ctor
    },
  }
}

/// Build Ixon.ConstantInfo (9 constructors)
pub fn build_ixon_constant_info(info: &IxonConstantInfo) -> LeanObj {
  match info {
    IxonConstantInfo::Defn(def) => {
      let def_obj = build_ixon_definition(def);
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, def_obj);
      *ctor
    },
    IxonConstantInfo::Recr(rec) => {
      let rec_obj = build_ixon_recursor(rec);
      let ctor = LeanCtor::alloc(1, 1, 0);
      ctor.set(0, rec_obj);
      *ctor
    },
    IxonConstantInfo::Axio(ax) => {
      let ax_obj = build_ixon_axiom(ax);
      let ctor = LeanCtor::alloc(2, 1, 0);
      ctor.set(0, ax_obj);
      *ctor
    },
    IxonConstantInfo::Quot(quot) => {
      let quot_obj = build_ixon_quotient(quot);
      let ctor = LeanCtor::alloc(3, 1, 0);
      ctor.set(0, quot_obj);
      *ctor
    },
    IxonConstantInfo::CPrj(proj) => {
      let proj_obj = build_constructor_proj(proj);
      let ctor = LeanCtor::alloc(4, 1, 0);
      ctor.set(0, proj_obj);
      *ctor
    },
    IxonConstantInfo::RPrj(proj) => {
      let proj_obj = build_recursor_proj(proj);
      let ctor = LeanCtor::alloc(5, 1, 0);
      ctor.set(0, proj_obj);
      *ctor
    },
    IxonConstantInfo::IPrj(proj) => {
      let proj_obj = build_inductive_proj(proj);
      let ctor = LeanCtor::alloc(6, 1, 0);
      ctor.set(0, proj_obj);
      *ctor
    },
    IxonConstantInfo::DPrj(proj) => {
      let proj_obj = build_definition_proj(proj);
      let ctor = LeanCtor::alloc(7, 1, 0);
      ctor.set(0, proj_obj);
      *ctor
    },
    IxonConstantInfo::Muts(muts) => {
      let arr = LeanArray::alloc(muts.len());
      for (i, mc) in muts.iter().enumerate() {
        arr.set(i, build_mut_const(mc));
      }
      let ctor = LeanCtor::alloc(8, 1, 0);
      ctor.set(0, arr);
      *ctor
    },
  }
}

/// Build Ixon.Constant
pub fn build_ixon_constant(constant: &IxonConstant) -> LeanObj {
  let info_obj = build_ixon_constant_info(&constant.info);
  let sharing_obj = build_ixon_expr_array(&constant.sharing);
  let refs_obj = build_address_array(&constant.refs);
  let univs_obj = build_ixon_univ_array(&constant.univs);
  let ctor = LeanCtor::alloc(0, 4, 0);
  ctor.set(0, info_obj);
  ctor.set(1, sharing_obj);
  ctor.set(2, refs_obj);
  ctor.set(3, univs_obj);
  *ctor
}

// =============================================================================
// Decode Functions
// =============================================================================

/// Decode a ByteArray (Address) to Address.
pub fn decode_ixon_address(obj: LeanObj) -> Address {
  let ba = obj.as_byte_array();
  Address::from_slice(&ba.as_bytes()[..32]).expect("Address should be 32 bytes")
}

/// Decode Array Address.
pub fn decode_ixon_address_array(obj: LeanObj) -> Vec<Address> {
  let arr = obj.as_array();
  arr.map(decode_ixon_address)
}

/// Decode Ixon.Definition.
/// Lean stores scalar fields ordered by size (largest first).
/// Layout: header(8) + typ(8) + value(8) + lvls(8) + kind(1) + safety(1) + padding(6)
pub fn decode_ixon_definition(obj: LeanObj) -> IxonDefinition {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
  let value = Arc::new(decode_ixon_expr(ctor.get(1)));
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

/// Decode Ixon.RecursorRule.
pub fn decode_ixon_recursor_rule(obj: LeanObj) -> IxonRecursorRule {
  let ctor = obj.as_ctor();
  let rhs = Arc::new(decode_ixon_expr(ctor.get(0)));
  let fields = ctor.scalar_u64(1, 0);
  IxonRecursorRule { fields, rhs }
}

/// Decode Ixon.Recursor.
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + motives(8) + minors(8) + k(1) + isUnsafe(1) + padding(6)
pub fn decode_ixon_recursor(obj: LeanObj) -> IxonRecursor {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
  let rules_arr = ctor.get(1).as_array();
  let rules = rules_arr.map(decode_ixon_recursor_rule);
  let lvls = ctor.scalar_u64(2, 0);
  let params = ctor.scalar_u64(2, 8);
  let indices = ctor.scalar_u64(2, 16);
  let motives = ctor.scalar_u64(2, 24);
  let minors = ctor.scalar_u64(2, 32);
  let k = ctor.scalar_u8(2, 40) != 0;
  let is_unsafe = ctor.scalar_u8(2, 41) != 0;
  IxonRecursor { k, is_unsafe, lvls, params, indices, motives, minors, typ, rules }
}

/// Decode Ixon.Axiom.
/// Scalars ordered by size: lvls(8) + isUnsafe(1) + padding(7)
pub fn decode_ixon_axiom(obj: LeanObj) -> IxonAxiom {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
  let lvls = ctor.scalar_u64(1, 0);
  let is_unsafe = ctor.scalar_u8(1, 8) != 0;
  IxonAxiom { is_unsafe, lvls, typ }
}

/// Decode Ixon.Quotient.
/// QuotKind is a scalar (not object field). Scalars: lvls(8) + kind(1) + padding(7)
pub fn decode_ixon_quotient(obj: LeanObj) -> IxonQuotient {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
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

/// Decode Ixon.Constructor.
/// Scalars ordered by size: lvls(8) + cidx(8) + params(8) + fields(8) + isUnsafe(1) + padding(7)
pub fn decode_ixon_constructor(obj: LeanObj) -> IxonConstructor {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
  let lvls = ctor.scalar_u64(1, 0);
  let cidx = ctor.scalar_u64(1, 8);
  let params = ctor.scalar_u64(1, 16);
  let fields = ctor.scalar_u64(1, 24);
  let is_unsafe = ctor.scalar_u8(1, 32) != 0;
  IxonConstructor { is_unsafe, lvls, cidx, params, fields, typ }
}

/// Decode Ixon.Inductive.
/// Scalars ordered by size: lvls(8) + params(8) + indices(8) + nested(8) + recr(1) + refl(1) + isUnsafe(1) + padding(5)
pub fn decode_ixon_inductive(obj: LeanObj) -> IxonInductive {
  let ctor = obj.as_ctor();
  let typ = Arc::new(decode_ixon_expr(ctor.get(0)));
  let ctors_arr = ctor.get(1).as_array();
  let ctors = ctors_arr.map(decode_ixon_constructor);
  let lvls = ctor.scalar_u64(2, 0);
  let params = ctor.scalar_u64(2, 8);
  let indices = ctor.scalar_u64(2, 16);
  let nested = ctor.scalar_u64(2, 24);
  let recr = ctor.scalar_u8(2, 32) != 0;
  let refl = ctor.scalar_u8(2, 33) != 0;
  let is_unsafe = ctor.scalar_u8(2, 34) != 0;
  IxonInductive { recr, refl, is_unsafe, lvls, params, indices, nested, typ, ctors }
}

/// Decode Ixon.InductiveProj.
pub fn decode_ixon_inductive_proj(obj: LeanObj) -> InductiveProj {
  let ctor = obj.as_ctor();
  let block = decode_ixon_address(ctor.get(0));
  let idx = ctor.scalar_u64(1, 0);
  InductiveProj { idx, block }
}

/// Decode Ixon.ConstructorProj.
pub fn decode_ixon_constructor_proj(obj: LeanObj) -> ConstructorProj {
  let ctor = obj.as_ctor();
  let block = decode_ixon_address(ctor.get(0));
  let idx = ctor.scalar_u64(1, 0);
  let cidx = ctor.scalar_u64(1, 8);
  ConstructorProj { idx, cidx, block }
}

/// Decode Ixon.RecursorProj.
pub fn decode_ixon_recursor_proj(obj: LeanObj) -> RecursorProj {
  let ctor = obj.as_ctor();
  let block = decode_ixon_address(ctor.get(0));
  let idx = ctor.scalar_u64(1, 0);
  RecursorProj { idx, block }
}

/// Decode Ixon.DefinitionProj.
pub fn decode_ixon_definition_proj(obj: LeanObj) -> DefinitionProj {
  let ctor = obj.as_ctor();
  let block = decode_ixon_address(ctor.get(0));
  let idx = ctor.scalar_u64(1, 0);
  DefinitionProj { idx, block }
}

/// Decode Ixon.MutConst.
pub fn decode_ixon_mut_const(obj: LeanObj) -> MutConst {
  let ctor = obj.as_ctor();
  let inner = ctor.get(0);
  match ctor.tag() {
    0 => MutConst::Defn(decode_ixon_definition(inner)),
    1 => MutConst::Indc(decode_ixon_inductive(inner)),
    2 => MutConst::Recr(decode_ixon_recursor(inner)),
    tag => panic!("Invalid Ixon.MutConst tag: {}", tag),
  }
}

/// Decode Ixon.ConstantInfo.
pub fn decode_ixon_constant_info(obj: LeanObj) -> IxonConstantInfo {
  let ctor = obj.as_ctor();
  let inner = ctor.get(0);
  match ctor.tag() {
    0 => IxonConstantInfo::Defn(decode_ixon_definition(inner)),
    1 => IxonConstantInfo::Recr(decode_ixon_recursor(inner)),
    2 => IxonConstantInfo::Axio(decode_ixon_axiom(inner)),
    3 => IxonConstantInfo::Quot(decode_ixon_quotient(inner)),
    4 => IxonConstantInfo::CPrj(decode_ixon_constructor_proj(inner)),
    5 => IxonConstantInfo::RPrj(decode_ixon_recursor_proj(inner)),
    6 => IxonConstantInfo::IPrj(decode_ixon_inductive_proj(inner)),
    7 => IxonConstantInfo::DPrj(decode_ixon_definition_proj(inner)),
    8 => {
      let arr = inner.as_array();
      let muts = arr.map(decode_ixon_mut_const);
      IxonConstantInfo::Muts(muts)
    },
    tag => panic!("Invalid Ixon.ConstantInfo tag: {}", tag),
  }
}

/// Decode Ixon.Constant.
pub fn decode_ixon_constant(obj: LeanObj) -> IxonConstant {
  let ctor = obj.as_ctor();
  IxonConstant {
    info: decode_ixon_constant_info(ctor.get(0)),
    sharing: decode_ixon_expr_array(ctor.get(1)),
    refs: decode_ixon_address_array(ctor.get(2)),
    univs: decode_ixon_univ_array(ctor.get(3)),
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip Ixon.Definition.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition(obj: LeanObj) -> LeanObj {
  let def = decode_ixon_definition(obj);
  build_ixon_definition(&def)
}

/// Round-trip Ixon.Recursor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor(obj: LeanObj) -> LeanObj {
  let rec = decode_ixon_recursor(obj);
  build_ixon_recursor(&rec)
}

/// Round-trip Ixon.Axiom.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_axiom(obj: LeanObj) -> LeanObj {
  let ax = decode_ixon_axiom(obj);
  build_ixon_axiom(&ax)
}

/// Round-trip Ixon.Quotient.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_quotient(obj: LeanObj) -> LeanObj {
  let quot = decode_ixon_quotient(obj);
  build_ixon_quotient(&quot)
}

/// Round-trip Ixon.ConstantInfo.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant_info(obj: LeanObj) -> LeanObj {
  let info = decode_ixon_constant_info(obj);
  build_ixon_constant_info(&info)
}

/// Round-trip Ixon.Constant.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constant(obj: LeanObj) -> LeanObj {
  let constant = decode_ixon_constant(obj);
  build_ixon_constant(&constant)
}

/// Round-trip Ixon.RecursorRule.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_rule(obj: LeanObj) -> LeanObj {
  let rule = decode_ixon_recursor_rule(obj);
  build_ixon_recursor_rule(&rule)
}

/// Round-trip Ixon.Constructor.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor(obj: LeanObj) -> LeanObj {
  let c = decode_ixon_constructor(obj);
  build_ixon_constructor(&c)
}

/// Round-trip Ixon.Inductive.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive(obj: LeanObj) -> LeanObj {
  let ind = decode_ixon_inductive(obj);
  build_ixon_inductive(&ind)
}

/// Round-trip Ixon.InductiveProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_inductive_proj(obj: LeanObj) -> LeanObj {
  let proj = decode_ixon_inductive_proj(obj);
  build_inductive_proj(&proj)
}

/// Round-trip Ixon.ConstructorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_constructor_proj(obj: LeanObj) -> LeanObj {
  let proj = decode_ixon_constructor_proj(obj);
  build_constructor_proj(&proj)
}

/// Round-trip Ixon.RecursorProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_recursor_proj(obj: LeanObj) -> LeanObj {
  let proj = decode_ixon_recursor_proj(obj);
  build_recursor_proj(&proj)
}

/// Round-trip Ixon.DefinitionProj.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_definition_proj(obj: LeanObj) -> LeanObj {
  let proj = decode_ixon_definition_proj(obj);
  build_definition_proj(&proj)
}

/// Round-trip Ixon.MutConst.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ixon_mut_const(obj: LeanObj) -> LeanObj {
  let mc = decode_ixon_mut_const(obj);
  build_mut_const(&mc)
}
