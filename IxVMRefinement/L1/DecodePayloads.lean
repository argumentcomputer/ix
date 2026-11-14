import Ix.IxVM.Refinement.DeserializeBinders
import IxC.Ixon.Verify.BoundedConstant
import IxC.Ixon.Verify.Framing
import IxVMRefinement.Obs.IxonDeserialize
import IxVMRefinement.L1.Hashed

/-! # Payload and side-table deserialization specs for `IxonDeserialize`

Refines every payload, projection, mutual-member, and side-table decoder in `IxonDeserialize`
against `Ixon.GetM` (`IxC.Ixon.Codec`):

* Heap representations (`RepIxonAddressRef`, `RepDefinition`, `RepRecursorRule`, `RepRecursor`,
  `RepAxiom`, `RepQuotient`, `RepFieldMode`, `RepConstructor`, `RepInductive`,
  `RepInductiveProj`, `RepConstructorProj`, `RepRecursorProj`, `RepDefinitionProj`,
  `RepMutConst`, `RepConstantInfo`, `RepConstant`) and heap-extension monotonicity.
* Address and side-table readers (`get_address`, `get_address_list`, `get_refs`, `get_univs`,
  `get_sharing`).
* Projection readers (`get_definition_proj`, `get_inductive_proj`, `get_recursor_proj`,
  `get_constructor_proj`).
* Payload readers (`unpack_def_asserts`, `unpack_def_kind_safety`, `get_definition`,
  `get_recursor_rule`, `get_recursor_rule_list`, `get_recursor`, `get_axiom`, `get_quotient`,
  `get_field_mode_list`, `get_constructor_modes`, `get_constructor`, `get_constructor_list`,
  `get_inductive`, `get_mut_const`, `get_mut_const_list`).
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN
open IxVM.Refinement.Deserialize

local notation "W" => IxVM.Refinement.Obs.W

/-! ## Prepared list enum names -/

abbrev recursorRuleListEnum : String := Names.«Lists::Node<Ixon::RecursorRule>»
abbrev constructorListEnum : String := Names.«Lists::Node<Ixon::Constructor>»
abbrev mutConstListEnum : String := Names.«Lists::Node<Ixon::MutConst>»
abbrev fieldModeListEnum : String := Names.«Lists::Node<Field>»

/-! ## Value encodings and heap representations -/

/-- Boolean value encoded as a field element `0` or `1`. -/
def repBoolField (b : Bool) : SourceValue F :=
  .field (if b then 1 else 0)

/-- `Ix.DefKind` constructor value in `Ixon::DefKind`. -/
def repDefKindVal : Ix.DefKind → SourceValue F
  | .defn => .construct "Ixon::DefKind" "Definition" []
  | .opaq => .construct "Ixon::DefKind" "Opaque" []
  | .thm => .construct "Ixon::DefKind" "Theorem" []

/-- `Ix.DefinitionSafety` constructor value in `Ixon::DefinitionSafety`. -/
def repDefSafetyVal : Ix.DefinitionSafety → SourceValue F
  | .unsaf => .construct "Ixon::DefinitionSafety" "Unsafe" []
  | .safe => .construct "Ixon::DefinitionSafety" "Safe" []
  | .part => .construct "Ixon::DefinitionSafety" "Partial" []

/-- `Ix.QuotKind` constructor value in `Ixon::QuotKind`. -/
def repQuotKindVal : Ix.QuotKind → SourceValue F
  | .type => .construct "Ixon::QuotKind" "Typ" []
  | .ctor => .construct "Ixon::QuotKind" "Ctor" []
  | .lift => .construct "Ixon::QuotKind" "Lift" []
  | .ind => .construct "Ixon::QuotKind" "Ind" []

/-- Heap reference to a 32-byte `Address` cell. -/
def RepIxonAddressRef (h : Heap F) (a : Address) (ptr : SourceValue F) : Prop :=
  ∃ d : Vector UInt8 32, a = ixAddr d ∧ Aiur.Library.Bytes.RepAddressRef addressTy h d ptr

theorem RepIxonAddressRef.mono {h₁ h₂ : Heap F} {a : Address} {ptr : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepIxonAddressRef h₁ a ptr) :
    RepIxonAddressRef h₂ a ptr := by
  obtain ⟨d, rfl, n, v, rfl, cell, hv⟩ := rep
  exact ⟨d, rfl, n, v, rfl, ext.getElem?_eq cell, hv⟩

theorem repIxonAddressRef_heapMono₂ : HeapMono₂ RepIxonAddressRef :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- Heap representation of `Ixon.Definition`. -/
def RepDefinition (h : Heap F) (d : Ixon.Definition) (v : SourceValue F) : Prop :=
  ∃ typPtr valPtr,
    v = .construct "Ixon::Definition" "Mk"
      [repDefKindVal d.kind, repDefSafetyVal d.safety,
       .field ((d.asserts.toCode.toNat : Nat) : F), u64Value d.lvls.toNat,
       typPtr, valPtr] ∧
    RepExpr h d.typ typPtr ∧
    RepExpr h d.value valPtr

theorem RepDefinition.mono {h₁ h₂ : Heap F} {d : Ixon.Definition} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepDefinition h₁ d v) : RepDefinition h₂ d v := by
  obtain ⟨typPtr, valPtr, rfl, htyp, hval⟩ := rep
  exact ⟨typPtr, valPtr, rfl, htyp.mono ext, hval.mono ext⟩

/-- Heap representation of `Ixon.RecursorRule`. -/
def RepRecursorRule (h : Heap F) (ru : Ixon.RecursorRule) (v : SourceValue F) : Prop :=
  ∃ rhsPtr,
    v = .construct "Ixon::RecursorRule" "Mk" [u64Value ru.fields.toNat, rhsPtr] ∧
    RepExpr h ru.rhs rhsPtr

theorem RepRecursorRule.mono {h₁ h₂ : Heap F} {ru : Ixon.RecursorRule} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepRecursorRule h₁ ru v) : RepRecursorRule h₂ ru v := by
  obtain ⟨rhsPtr, rfl, hrhs⟩ := rep
  exact ⟨rhsPtr, rfl, hrhs.mono ext⟩

theorem repRecursorRule_heapMono₂ : HeapMono₂ RepRecursorRule :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- Heap representation of `Ixon.Recursor`. -/
def RepRecursor (h : Heap F) (rc : Ixon.Recursor) (v : SourceValue F) : Prop :=
  ∃ typPtr rulesPtr,
    v = .construct "Ixon::Recursor" "Mk"
      [repBoolField rc.k, repBoolField rc.isUnsafe,
       u64Value rc.lvls.toNat, u64Value rc.params.toNat, u64Value rc.indices.toNat,
       u64Value rc.motives.toNat, u64Value rc.minors.toNat, typPtr, rulesPtr] ∧
    RepExpr h rc.typ typPtr ∧
    Aiur.Library.List.RepList recursorRuleListEnum RepRecursorRule h rc.rules.toList rulesPtr

theorem RepRecursor.mono {h₁ h₂ : Heap F} {rc : Ixon.Recursor} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepRecursor h₁ rc v) : RepRecursor h₂ rc v := by
  obtain ⟨typPtr, rulesPtr, rfl, htyp, hrules⟩ := rep
  exact ⟨typPtr, rulesPtr, rfl, htyp.mono ext,
    hrules.mono repRecursorRule_heapMono₂ ext⟩

/-- Heap representation of `Ixon.Axiom`. -/
def RepAxiom (h : Heap F) (ax : Ixon.Axiom) (v : SourceValue F) : Prop :=
  ∃ typPtr,
    v = .construct "Ixon::Axiom" "Mk"
      [repBoolField ax.isUnsafe, u64Value ax.lvls.toNat, typPtr] ∧
    RepExpr h ax.typ typPtr

theorem RepAxiom.mono {h₁ h₂ : Heap F} {ax : Ixon.Axiom} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepAxiom h₁ ax v) : RepAxiom h₂ ax v := by
  obtain ⟨typPtr, rfl, htyp⟩ := rep
  exact ⟨typPtr, rfl, htyp.mono ext⟩

/-- Heap representation of `Ixon.Quotient`. -/
def RepQuotient (h : Heap F) (q : Ixon.Quotient) (v : SourceValue F) : Prop :=
  ∃ typPtr,
    v = .construct "Ixon::Quotient" "Mk"
      [repQuotKindVal q.kind, u64Value q.lvls.toNat, typPtr] ∧
    RepExpr h q.typ typPtr

theorem RepQuotient.mono {h₁ h₂ : Heap F} {q : Ixon.Quotient} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepQuotient h₁ q v) : RepQuotient h₂ q v := by
  obtain ⟨typPtr, rfl, htyp⟩ := rep
  exact ⟨typPtr, rfl, htyp.mono ext⟩

/-- Value representation of `Ixon.FieldMode`. -/
def RepFieldMode (_h : Heap F) (m : Ixon.FieldMode) (v : SourceValue F) : Prop :=
  v = .field ((m.toCode.toNat : Nat) : F)

theorem repFieldMode_heapMono₂ : HeapMono₂ RepFieldMode :=
  fun _ _ _ _ _ rep => rep

/-- Heap representation of `Ixon.Constructor`. -/
def RepConstructor (h : Heap F) (ct : Ixon.Constructor) (v : SourceValue F) : Prop :=
  ∃ modesPtr typPtr,
    v = .construct "Ixon::Constructor" "Mk"
      [repBoolField ct.isUnsafe, u64Value ct.lvls.toNat, u64Value ct.cidx.toNat,
       u64Value ct.params.toNat, u64Value ct.fields.toNat, modesPtr, typPtr] ∧
    Aiur.Library.List.RepList fieldModeListEnum RepFieldMode h ct.fieldModes.toArray.toList modesPtr ∧
    RepExpr h ct.typ typPtr

theorem RepConstructor.mono {h₁ h₂ : Heap F} {ct : Ixon.Constructor} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepConstructor h₁ ct v) : RepConstructor h₂ ct v := by
  obtain ⟨modesPtr, typPtr, rfl, hmodes, htyp⟩ := rep
  exact ⟨modesPtr, typPtr, rfl, hmodes.mono repFieldMode_heapMono₂ ext, htyp.mono ext⟩

theorem repConstructor_heapMono₂ : HeapMono₂ RepConstructor :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- Heap representation of `Ixon.Inductive`. -/
def RepInductive (h : Heap F) (ind : Ixon.Inductive) (v : SourceValue F) : Prop :=
  ∃ typPtr ctorsPtr,
    v = .construct "Ixon::Inductive" "Mk"
      [repBoolField ind.isUnsafe, u64Value ind.lvls.toNat,
       u64Value ind.params.toNat, u64Value ind.indices.toNat, typPtr, ctorsPtr] ∧
    RepExpr h ind.typ typPtr ∧
    Aiur.Library.List.RepList constructorListEnum RepConstructor h ind.ctors.toList ctorsPtr

theorem RepInductive.mono {h₁ h₂ : Heap F} {ind : Ixon.Inductive} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepInductive h₁ ind v) : RepInductive h₂ ind v := by
  obtain ⟨typPtr, ctorsPtr, rfl, htyp, hctors⟩ := rep
  exact ⟨typPtr, ctorsPtr, rfl, htyp.mono ext, hctors.mono repConstructor_heapMono₂ ext⟩

/-- Heap representation of `Ixon.InductiveProj`. -/
def RepInductiveProj (h : Heap F) (p : Ixon.InductiveProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::InductiveProj" "Mk" [u64Value p.idx.toNat, blkPtr] ∧
    RepIxonAddressRef h p.block blkPtr

theorem RepInductiveProj.mono {h₁ h₂ : Heap F} {p : Ixon.InductiveProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepInductiveProj h₁ p v) : RepInductiveProj h₂ p v := by
  obtain ⟨blkPtr, rfl, hblk⟩ := rep
  exact ⟨blkPtr, rfl, hblk.mono ext⟩

/-- Heap representation of `Ixon.ConstructorProj`. -/
def RepConstructorProj (h : Heap F) (p : Ixon.ConstructorProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::ConstructorProj" "Mk"
      [u64Value p.idx.toNat, u64Value p.cidx.toNat, blkPtr] ∧
    RepIxonAddressRef h p.block blkPtr

theorem RepConstructorProj.mono {h₁ h₂ : Heap F} {p : Ixon.ConstructorProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepConstructorProj h₁ p v) : RepConstructorProj h₂ p v := by
  obtain ⟨blkPtr, rfl, hblk⟩ := rep
  exact ⟨blkPtr, rfl, hblk.mono ext⟩

/-- Heap representation of `Ixon.RecursorProj`. -/
def RepRecursorProj (h : Heap F) (p : Ixon.RecursorProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::RecursorProj" "Mk" [u64Value p.idx.toNat, blkPtr] ∧
    RepIxonAddressRef h p.block blkPtr

theorem RepRecursorProj.mono {h₁ h₂ : Heap F} {p : Ixon.RecursorProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepRecursorProj h₁ p v) : RepRecursorProj h₂ p v := by
  obtain ⟨blkPtr, rfl, hblk⟩ := rep
  exact ⟨blkPtr, rfl, hblk.mono ext⟩

/-- Heap representation of `Ixon.DefinitionProj`. -/
def RepDefinitionProj (h : Heap F) (p : Ixon.DefinitionProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::DefinitionProj" "Mk" [u64Value p.idx.toNat, blkPtr] ∧
    RepIxonAddressRef h p.block blkPtr

theorem RepDefinitionProj.mono {h₁ h₂ : Heap F} {p : Ixon.DefinitionProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepDefinitionProj h₁ p v) : RepDefinitionProj h₂ p v := by
  obtain ⟨blkPtr, rfl, hblk⟩ := rep
  exact ⟨blkPtr, rfl, hblk.mono ext⟩

/-- Heap representation of `Ixon.MutConst`. -/
def RepMutConst (h : Heap F) : Ixon.MutConst → SourceValue F → Prop
  | .defn d, v => ∃ dv, v = .construct "Ixon::MutConst" "Defn" [dv] ∧ RepDefinition h d dv
  | .indc i, v => ∃ iv, v = .construct "Ixon::MutConst" "Indc" [iv] ∧ RepInductive h i iv
  | .recr r, v => ∃ rv, v = .construct "Ixon::MutConst" "Recr" [rv] ∧ RepRecursor h r rv

theorem RepMutConst.mono {h₁ h₂ : Heap F} {mc : Ixon.MutConst} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepMutConst h₁ mc v) : RepMutConst h₂ mc v := by
  cases mc with
  | defn d =>
    obtain ⟨dv, rfl, hdv⟩ := rep
    exact ⟨dv, rfl, hdv.mono ext⟩
  | indc i =>
    obtain ⟨iv, rfl, hiv⟩ := rep
    exact ⟨iv, rfl, hiv.mono ext⟩
  | recr r =>
    obtain ⟨rv, rfl, hrv⟩ := rep
    exact ⟨rv, rfl, hrv.mono ext⟩

theorem repMutConst_heapMono₂ : HeapMono₂ RepMutConst :=
  fun _ _ _ _ ext rep => rep.mono ext

/-- Heap representation of `Ixon.ConstantInfo`. -/
def RepConstantInfo (h : Heap F) : Ixon.ConstantInfo → SourceValue F → Prop
  | .defn d, v => ∃ dv, v = .construct "Ixon::ConstantInfo" "Defn" [dv] ∧ RepDefinition h d dv
  | .recr r, v => ∃ rv, v = .construct "Ixon::ConstantInfo" "Recr" [rv] ∧ RepRecursor h r rv
  | .axio a, v => ∃ av, v = .construct "Ixon::ConstantInfo" "Axio" [av] ∧ RepAxiom h a av
  | .quot q, v => ∃ qv, v = .construct "Ixon::ConstantInfo" "Quot" [qv] ∧ RepQuotient h q qv
  | .cPrj p, v => ∃ pv, v = .construct "Ixon::ConstantInfo" "CPrj" [pv] ∧ RepConstructorProj h p pv
  | .rPrj p, v => ∃ pv, v = .construct "Ixon::ConstantInfo" "RPrj" [pv] ∧ RepRecursorProj h p pv
  | .iPrj p, v => ∃ pv, v = .construct "Ixon::ConstantInfo" "IPrj" [pv] ∧ RepInductiveProj h p pv
  | .dPrj p, v => ∃ pv, v = .construct "Ixon::ConstantInfo" "DPrj" [pv] ∧ RepDefinitionProj h p pv
  | .muts ms, v =>
    ∃ msPtr, v = .construct "Ixon::ConstantInfo" "Muts" [msPtr] ∧
      Aiur.Library.List.RepList mutConstListEnum RepMutConst h ms.toList msPtr

theorem RepConstantInfo.mono {h₁ h₂ : Heap F} {info : Ixon.ConstantInfo} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepConstantInfo h₁ info v) : RepConstantInfo h₂ info v := by
  cases info with
  | defn d => obtain ⟨dv, rfl, hdv⟩ := rep; exact ⟨dv, rfl, hdv.mono ext⟩
  | recr r => obtain ⟨rv, rfl, hrv⟩ := rep; exact ⟨rv, rfl, hrv.mono ext⟩
  | axio a => obtain ⟨av, rfl, hav⟩ := rep; exact ⟨av, rfl, hav.mono ext⟩
  | quot q => obtain ⟨qv, rfl, hqv⟩ := rep; exact ⟨qv, rfl, hqv.mono ext⟩
  | cPrj p => obtain ⟨pv, rfl, hpv⟩ := rep; exact ⟨pv, rfl, hpv.mono ext⟩
  | rPrj p => obtain ⟨pv, rfl, hpv⟩ := rep; exact ⟨pv, rfl, hpv.mono ext⟩
  | iPrj p => obtain ⟨pv, rfl, hpv⟩ := rep; exact ⟨pv, rfl, hpv.mono ext⟩
  | dPrj p => obtain ⟨pv, rfl, hpv⟩ := rep; exact ⟨pv, rfl, hpv.mono ext⟩
  | muts ms =>
    obtain ⟨msPtr, rfl, hms⟩ := rep
    exact ⟨msPtr, rfl, hms.mono repMutConst_heapMono₂ ext⟩

/-- Heap representation of `Ixon.Constant`. -/
def RepConstant (h : Heap F) (c : Ixon.Constant) (v : SourceValue F) : Prop :=
  ∃ infoVal sharingPtr refsPtr univsPtr bindersPtr,
    v = .construct "Ixon::Constant" "Mk"
      [infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr] ∧
    RepConstantInfo h c.info infoVal ∧
    RepShareVec h c.sharing.toList sharingPtr ∧
    Aiur.Library.List.RepList addressListEnum RepIxonAddressRef h c.refs.toList refsPtr ∧
    Aiur.Library.List.RepList univListEnum RepUnivPtr h c.univs.toList univsPtr ∧
    Aiur.Library.List.RepList binderBlockListEnum RepBinderBlock h c.binders.toList bindersPtr

theorem RepConstant.mono {h₁ h₂ : Heap F} {c : Ixon.Constant} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RepConstant h₁ c v) : RepConstant h₂ c v := by
  obtain ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, rfl,
    hinfo, hsh, hrefs, hunivs, hbinders⟩ := rep
  exact ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, rfl,
    hinfo.mono ext,
    RepShareVec.mono ext hsh,
    hrefs.mono repIxonAddressRef_heapMono₂ ext,
    hunivs.mono repUnivPtr_heapMono₂ ext,
    hbinders.mono repBinderBlock_heapMono₂ ext⟩

/-! ## Arithmetic and `GetM` loop helpers -/

/-- `UInt64::to_field` on `u64Value n` (`n < 2^64`) witnesses `n < 2^56` and returns `.field n`. -/
theorem u64ToField_refines {n : Nat} (hn : n < 18446744073709551616)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn W "UInt64::to_field" [u64Value n] h r h') :
    n < 72057594037927936 ∧ r = .field (n : F) ∧ h' = h := by
  obtain ⟨k0, hk0⟩ := Mirrors.«UInt64::to_field».of_eval ev
  have run := hk0 (k0 + 2) (by omega)
  by_cases hlt : n < 72057594037927936
  · rw [u64ToField_run hlt k0 h, Option.some.injEq, Prod.mk.injEq] at run
    exact ⟨hlt, run.1.symm, run.2.symm⟩
  · rw [u64ToField_none (by omega) hn (k0 + 2) h] at run
    cases run

/-- Natural numbers below `2^56` (hence `< P = 2^64 - 2^32 + 1`) embed injectively into `F`. -/
theorem natCast_inj_56 {a b : Nat} (ha : a < 72057594037927936) (hb : b < 72057594037927936)
    (h : (a : F) = (b : F)) : a = b :=
  IxVM.natCast_inj (by omega) (by omega) h

theorem getArray_getExpr_of_children (count : Nat) {s s' : Ixon.GetState} {xs : List Ixon.Expr}
    (h : getExprChildren count s = .ok xs s') :
    Ixon.getArray Ixon.getExpr count s = .ok xs.toArray s' := by
  induction count generalizing s xs with
  | zero =>
    simp only [getExprChildren, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure]
  | succ count ih =>
    obtain ⟨v, s1, hv, hrest⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨vs, s2, hvs, hpure⟩ := Ixon.Verify.TagN.bind_ok_inv hrest
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv hpure
    have ih' := ih hvs
    rw [Ixon.Verify.BoundedConstant.getArray_succ]
    simp [bind, EStateM.bind, hv, ih', pure, EStateM.pure]

theorem getArray_getUniv_of_children (count : Nat) {s s' : Ixon.GetState} {xs : List Ixon.Univ}
    (h : getUnivChildren count s = .ok xs s') :
    Ixon.getArray Ixon.getUniv count s = .ok xs.toArray s' := by
  induction count generalizing s xs with
  | zero =>
    simp only [getUnivChildren, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure]
  | succ count ih =>
    obtain ⟨v, s1, hv, hrest⟩ := Ixon.Verify.TagN.bind_ok_inv h
    obtain ⟨vs, s2, hvs, hpure⟩ := Ixon.Verify.TagN.bind_ok_inv hrest
    obtain ⟨rfl, rfl⟩ := Ixon.Verify.TagN.pure_ok_inv hpure
    have ih' := ih hvs
    rw [Ixon.Verify.BoundedConstant.getArray_succ]
    simp [bind, EStateM.bind, hv, ih', pure, EStateM.pure]

/-! ## Address, projection, and side-table codecs -/

/-- `IxonDeserialize::get_address` at offset `i` refines `Ixon.Serialize.get` (`Address`). -/
theorem getAddress_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_address" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (a : Address) (addrPtr restPtr : SourceValue F),
      (Ixon.Serialize.get : Ixon.GetM Address) { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok a { idx := i + 32, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [addrPtr, restPtr] ∧
      RepIxonAddressRef h' a addrPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + 32)) restPtr := by
  obtain ⟨ext, hlen, addrPtr, restPtr, rfl, addrRep, dropRep⟩ := getAddress_refines rep ev
  rw [List.drop_drop] at dropRep
  let b1 : ByteArray := ⟨(bytes.take i).toArray⟩
  let b2 : ByteArray := ⟨((bytes.drop i).take 32).toArray⟩
  let b3 : ByteArray := ⟨((bytes.drop i).drop 32).toArray⟩
  have hi_le : i ≤ bytes.length := by
    rw [List.length_drop] at hlen; omega
  have hb1_sz : b1.size = i := by
    simp [b1, ByteArray.size, Nat.min_eq_left hi_le]
  have hb2_sz : b2.size = 32 := by
    simp [b2, ByteArray.size, Nat.min_eq_left hlen]
  have happ : b1 ++ b2 ++ b3 = ⟨bytes.toArray⟩ := by
    apply ByteArray.ext
    simp only [b1, b2, b3, ByteArray.data_append, ← List.toArray_append]
    congr 1
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have hread := Ixon.Verify.Codec.ConstantTables.getBytes_reads b2 b1 b3
  rw [hb2_sz, hb1_sz, happ] at hread
  refine ⟨ext, ixAddr (takeAddress (bytes.drop i) hlen), addrPtr, restPtr, ?_, rfl,
    ⟨takeAddress (bytes.drop i) hlen, rfl, addrRep⟩, dropRep⟩
  change (Address.mk <$> Ixon.getBytes 32) { idx := i, bytes := ⟨bytes.toArray⟩ } = _
  simp only [Functor.map, EStateM.map, hread]
  rfl

/-- `IxonDeserialize::get_address_list` at offset `i` refines `Ixon.getArray Ixon.Serialize.get`. -/
theorem getAddressList_codec_at (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_address_list" [stream, u64Value count] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (addrs : Array Address) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getArray (Ixon.Serialize.get : Ixon.GetM Address) count
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok addrs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList addressListEnum RepIxonAddressRef h' addrs.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' cs with
  | zero =>
    cases «IxonDeserialize::get_address_list».obs ev with
    | n1 m2 cs12 m43 ev14 he41 hm51 he62 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      subst he62 hm51 he41
      have ext := Aiur.Library.List.allocNil_extends addressListEnum h
      refine ⟨ext, #[], 0, (Aiur.Library.List.allocNil addressListEnum h).1, stream,
        by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep addressListEnum RepIxonAddressRef h,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    | n0 m2 cs12 _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp at hiz
  | succ count ih =>
    cases «IxonDeserialize::get_address_list».obs ev with
    | n1 m2 cs12 _ ev14 _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp [Nat.succ_ne_zero] at hiz
    | n0 m2 cs12 m70 cs80 x_addr x_s m105 cs115 v119 m128 cs136 x_rest x_s2 m166
        ev14 ev82 ev138 ev117 he164 hm174 he201 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨ext1, a, addrPtr, restPtr1, hok1, heq1, aRep, hrep1⟩ :=
        getAddress_codec_at rep ev82.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl⟩
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailAddrs, n2, tailPtr, restPtr2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl⟩
      subst he201 hm174 he164
      have ext3 := Aiur.Library.List.allocCons_extends addressListEnum addrPtr tailPtr m105
      refine ⟨(ext1.trans ext2).trans ext3, #[a] ++ tailAddrs, 32 + n2,
        (Aiur.Library.List.allocCons addressListEnum addrPtr tailPtr m105).1, restPtr2,
        ?_, rfl, ?_,
        by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · simpa using Aiur.Library.List.allocCons_rep addressListEnum repIxonAddressRef_heapMono₂
          (aRep.mono ext2) tailRep

/-- `IxonDeserialize::get_refs` at offset `i` refines the refs side-table read. -/
theorem getRefs_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_refs" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (refs : Array Address) (n : Nat) (listPtr restPtr : SourceValue F),
      (do
        let numRefs := (← Ixon.getTagN 0).value.toNat
        Ixon.getArray Ixon.Serialize.get numRefs : Ixon.GetM (Array Address))
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok refs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList addressListEnum RepIxonAddressRef h' refs.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_refs».obs ev with
  | run m2 cs12 x_len x_s cs39 ev14 ev41 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hlen_lt, hrep1, heq1⟩ :=
      getVecLen_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, refs, n2, listPtr, restPtr2, hok2, rfl, refsRep, hrep2⟩ :=
      getAddressList_codec_at t.value.toNat hlen_lt hrep1 ev41
    refine ⟨ext2, refs, n1 + n2, listPtr, restPtr2, ?_, rfl, refsRep,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    simp [bind, EStateM.bind, hok1, hok2, Nat.add_assoc]

/-- `IxonDeserialize::get_sharing` at offset `i` refines the sharing side-table read. -/
theorem getSharing_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : EvalFn W "IxonDeserialize::get_sharing" [stream] h r h') :
    Heap.Extends h h' ∧
    ∃ (sharing : Array Ixon.Expr) (n : Nat) (listPtr restPtr : SourceValue F),
      (do
        let numSharing := (← Ixon.getTagN 0).value.toNat
        Ixon.getArray Ixon.getExpr numSharing : Ixon.GetM (Array Ixon.Expr))
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok sharing { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepShareVec h' sharing.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨ext, t, n1, n2, exprs, listPtr, restPtr, hok1, _, hok2, _, rfl, listRep, dropRep⟩ :=
    getSharing_refines_at rep ev
  have harr := getArray_getExpr_of_children t.value.toNat hok2
  refine ⟨ext, exprs.toArray, n1 + n2, listPtr, restPtr, ?_, rfl, by simpa using listRep,
    by rw [← Nat.add_assoc]; exact dropRep⟩
  simp [bind, EStateM.bind, hok1, harr, Nat.add_assoc]

/-- `IxonDeserialize::get_univs` at offset `i` refines the universe side-table read. -/
theorem getUnivs_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_univs" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (univs : Array Ixon.Univ) (n : Nat) (listPtr restPtr : SourceValue F),
      (do
        let numUnivs := (← Ixon.getTagN 0).value.toNat
        Ixon.getArray Ixon.getUniv numUnivs : Ixon.GetM (Array Ixon.Univ))
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok univs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList univListEnum RepUnivPtr h' univs.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_univs».obs ev with
  | run m2 cs12 x_len x_s cs39 ev14 ev41 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hlen_lt, hrep1, heq1⟩ :=
      getVecLen_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, univs, n2, listPtr, restPtr2, hok2, _, rfl, listRep, dropRep⟩ :=
      getUnivList_refines_at t.value.toNat hlen_lt hrep1 ev41.erase
    have harr := getArray_getUniv_of_children t.value.toNat hok2
    refine ⟨ext2, univs.toArray, n1 + n2, listPtr, restPtr2, ?_, rfl, by simpa using listRep,
      by rw [← Nat.add_assoc]; exact dropRep⟩
    simp [bind, EStateM.bind, hok1, harr, Nat.add_assoc]

/-- `IxonDeserialize::get_definition_proj` at offset `i` refines `Ixon.getDefinitionProj`. -/
theorem getDefinitionProj_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_definition_proj" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.DefinitionProj) (n : Nat) (prjVal restPtr : SourceValue F),
      Ixon.getDefinitionProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [prjVal, restPtr] ∧
      RepDefinitionProj h' p prjVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_definition_proj».obs ev with
  | run m2 cs12 x_idx x_s m37 cs47 x_block x_s2 ev14 ev49 he75 he108 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, a, addrPtr, restPtr2, hok2, heq2, aRep, hrep2⟩ :=
      getAddress_codec_at hrep1 ev49.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    subst he108 he75
    refine ⟨ext2, ⟨t.value, a⟩, n1 + 32, _, restPtr2, ?_, rfl, ⟨addrPtr, rfl, aRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getDefinitionProj
    simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_inductive_proj` at offset `i` refines `Ixon.getInductiveProj`. -/
theorem getInductiveProj_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_inductive_proj" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.InductiveProj) (n : Nat) (prjVal restPtr : SourceValue F),
      Ixon.getInductiveProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [prjVal, restPtr] ∧
      RepInductiveProj h' p prjVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_inductive_proj».obs ev with
  | run m2 cs12 x_idx x_s m37 cs47 x_block x_s2 ev14 ev49 he75 he108 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, a, addrPtr, restPtr2, hok2, heq2, aRep, hrep2⟩ :=
      getAddress_codec_at hrep1 ev49.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    subst he108 he75
    refine ⟨ext2, ⟨t.value, a⟩, n1 + 32, _, restPtr2, ?_, rfl, ⟨addrPtr, rfl, aRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getInductiveProj
    simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_recursor_proj` at offset `i` refines `Ixon.getRecursorProj`. -/
theorem getRecursorProj_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_recursor_proj" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.RecursorProj) (n : Nat) (prjVal restPtr : SourceValue F),
      Ixon.getRecursorProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [prjVal, restPtr] ∧
      RepRecursorProj h' p prjVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_recursor_proj».obs ev with
  | run m2 cs12 x_idx x_s m37 cs47 x_block x_s2 ev14 ev49 he75 he108 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, a, addrPtr, restPtr2, hok2, heq2, aRep, hrep2⟩ :=
      getAddress_codec_at hrep1 ev49.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    subst he108 he75
    refine ⟨ext2, ⟨t.value, a⟩, n1 + 32, _, restPtr2, ?_, rfl, ⟨addrPtr, rfl, aRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getRecursorProj
    simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_constructor_proj` at offset `i` refines `Ixon.getConstructorProj`. -/
theorem getConstructorProj_codec_at {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constructor_proj" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.ConstructorProj) (n : Nat) (prjVal restPtr : SourceValue F),
      Ixon.getConstructorProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [prjVal, restPtr] ∧
      RepConstructorProj h' p prjVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_constructor_proj».obs ev with
  | run m2 cs12 x_idx x_s m37 cs47 x_cidx x_s2 m72 cs82 x_block x_s3 ev14 ev49 ev84 he110 he151 _ =>
    obtain ⟨rfl, t1, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨rfl, t2, n2, restPtr2, hok2, _, hrep2, heq2⟩ := getTag0_refines_at hrep1 ev49.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨ext3, a, addrPtr, restPtr3, hok3, heq3, aRep, hrep3⟩ :=
      getAddress_codec_at hrep2 ev84.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3
    rcases heq3 with ⟨rfl, rfl⟩
    subst he151 he110
    refine ⟨ext3, ⟨t1.value, t2.value, a⟩, n1 + n2 + 32, _, restPtr3, ?_, rfl,
      ⟨addrPtr, rfl, aRep⟩, by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hrep3⟩
    unfold Ixon.getConstructorProj
    simp [bind, EStateM.bind, hok1, hok2, hok3, pure, EStateM.pure, Nat.add_assoc]

/-! ## Payload codecs: definitions, recursors, axioms, quotients, constructors, inductives -/

private def allocAssertOfCode : Nat → Ixon.AllocAssert
  | 0 => .unrestricted
  | 1 => .noRc
  | _ => .noAlloc

private def defAssertsOfByte (n : Nat) : Ixon.DefAsserts :=
  ⟨allocAssertOfCode (n / 16 % 4), decide (n / 64 % 2 = 1)⟩

private theorem defFlags_decode_nat :
    ∀ n, n < 256 →
      n / 128 = 0 →
      (n / 16 % 2) * (n / 32 % 2) = 0 →
      (n % 16 = 0 ∨ n % 16 = 1 ∨ n % 16 = 2 ∨
       n % 16 = 4 ∨ n % 16 = 5 ∨ n % 16 = 6 ∨
       n % 16 = 8 ∨ n % 16 = 9 ∨ n % 16 = 10) →
      (((UInt8.ofNat n >>> 2) &&& 3 > 2 || (UInt8.ofNat n &&& 3) > 2) = false) ∧
      Ixon.DefAsserts.ofCode? (UInt8.ofNat n >>> 4) = some (defAssertsOfByte n) ∧
      (defAssertsOfByte n).toCode.toNat = n / 16 := by
  decide +kernel

private theorem defFlags_decode (b : UInt8)
    (h7 : b.toNat / 128 = 0)
    (h45 : (b.toNat / 16 % 2) * (b.toNat / 32 % 2) = 0)
    (hlo : b.toNat % 16 = 0 ∨ b.toNat % 16 = 1 ∨ b.toNat % 16 = 2 ∨
           b.toNat % 16 = 4 ∨ b.toNat % 16 = 5 ∨ b.toNat % 16 = 6 ∨
           b.toNat % 16 = 8 ∨ b.toNat % 16 = 9 ∨ b.toNat % 16 = 10) :
    (((b >>> 2) &&& 3 > 2 || (b &&& 3) > 2) = false) ∧
    ∃ a : Ixon.DefAsserts,
      Ixon.DefAsserts.ofCode? (b >>> 4) = some a ∧
      a.toCode.toNat = b.toNat / 16 := by
  have h := defFlags_decode_nat b.toNat b.toNat_lt h7 h45 hlo
  rw [UInt8.ofNat_toNat] at h
  exact ⟨h.1, defAssertsOfByte b.toNat, h.2.1, h.2.2⟩

private theorem defKindSafety_table :
    ∀ n : Nat,
      (n = 0 → Ixon.unpackDefKindSafety n.toUInt8 = (.defn, .unsaf)) ∧
      (n = 1 → Ixon.unpackDefKindSafety n.toUInt8 = (.defn, .safe)) ∧
      (n = 2 → Ixon.unpackDefKindSafety n.toUInt8 = (.defn, .part)) ∧
      (n = 4 → Ixon.unpackDefKindSafety n.toUInt8 = (.opaq, .unsaf)) ∧
      (n = 5 → Ixon.unpackDefKindSafety n.toUInt8 = (.opaq, .safe)) ∧
      (n = 6 → Ixon.unpackDefKindSafety n.toUInt8 = (.opaq, .part)) ∧
      (n = 8 → Ixon.unpackDefKindSafety n.toUInt8 = (.thm, .unsaf)) ∧
      (n = 9 → Ixon.unpackDefKindSafety n.toUInt8 = (.thm, .safe)) ∧
      (n = 10 → Ixon.unpackDefKindSafety n.toUInt8 = (.thm, .part)) := by
  intro n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; rfl)

private theorem lowNibble_eq_nat : ∀ n, n < 256 → (UInt8.ofNat n &&& 15) = (n % 16).toUInt8 := by
  decide +kernel

private theorem lowNibble_eq (b : UInt8) : (b &&& 15) = (b.toNat % 16).toUInt8 := by
  have h := lowNibble_eq_nat b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at h

private theorem unpack_bits_helper {b : UInt8} {m2 : Heap F} {cs12 : List (Call F)}
    {x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198 : SourceValue F}
    {low : Nat} (hlow : low < 16)
    {h : Heap F}
    (ev14 : ObsFn W "UInt8::bit_decomposition" [.field (b.toNat : F)] h
      (.tuple [x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7]) m2 cs12)
    (heq92 : x_b7 = .field 0)
    (op119 : evalBinOp .mul x_b4 x_b5 = .ok v104)
    (heq128 : v104 = .field 0)
    (op161 : evalBinOp .mul (.field 2) x_b5 = .ok y146)
    (op152 : evalBinOp .add x_b4 y146 = .ok x137)
    (op170 : evalBinOp .mul (.field 4) x_b6 = .ok y138)
    (op144 : evalBinOp .add x137 y138 = .ok v129)
    (op213 : evalBinOp .mul (.field 2) x_b1 = .ok y198)
    (op204 : evalBinOp .add x_b0 y198 = .ok x189)
    (op222 : evalBinOp .mul (.field 4) x_b2 = .ok y190)
    (op196 : evalBinOp .add x189 y190 = .ok x181)
    (op231 : evalBinOp .mul (.field 8) x_b3 = .ok y182)
    (op188 : evalBinOp .add x181 y182 = .ok (.field (low : F))) :
    m2 = h ∧ b.toNat / 128 = 0 ∧ (b.toNat / 16 % 2) * (b.toNat / 32 % 2) = 0 ∧
    v129 = .field ((b.toNat / 16 : Nat) : F) ∧ b.toNat % 16 = low := by
  have hb : b.toNat < 256 := b.toNat_lt
  obtain ⟨hbits, rfl⟩ := u8BitDecomposition_refines hb ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbits
  rcases hbits with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hb7 : b.toNat / 128 = 0 := by
    simp only [Value.field.injEq, natCast_eq_zero_iff (by omega)] at heq92
    omega
  subst heq128
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op119
  have h45_cast : (((b.toNat / 16 % 2) * (b.toNat / 32 % 2) : Nat) : F) = 0 := by
    push_cast; exact op119
  have h45 : (b.toNat / 16 % 2) * (b.toNat / 32 % 2) = 0 :=
    (natCast_eq_zero_iff (by omega)).mp h45_cast
  simp only [evalBinOp, Except.ok.injEq] at op161 op152 op170 op144 op213 op204 op222 op196 op231 op188
  subst op161 op152 op170 op144 op213 op204 op222 op196 op231
  simp only [Value.field.injEq] at op188
  have hhi_sum : b.toNat / 16 % 2 + 2 * (b.toNat / 32 % 2) + 4 * (b.toNat / 64 % 2) = b.toNat / 16 := by
    omega
  have hhi_val : (.field (((b.toNat / 16 % 2 : Nat) : F) + (2 : F) * ((b.toNat / 32 % 2 : Nat) : F) +
      (4 : F) * ((b.toNat / 64 % 2 : Nat) : F)) : SourceValue F) = .field ((b.toNat / 16 : Nat) : F) := by
    congr 1
    have hc := congrArg (Nat.cast (R := F)) hhi_sum
    push_cast at hc
    simpa using hc
  have hlo_sum : b.toNat % 2 + 2 * (b.toNat / 2 % 2) + 4 * (b.toNat / 4 % 2) + 8 * (b.toNat / 8 % 2) =
      b.toNat % 16 := by
    omega
  have hlo_cast : ((b.toNat % 16 : Nat) : F) = (low : F) := by
    have hc := congrArg (Nat.cast (R := F)) hlo_sum
    push_cast at hc
    exact hc.symm.trans op188
  have hlo_eq : b.toNat % 16 = low := (natCast_eq_iff (by omega) (by omega)).mp hlo_cast
  exact ⟨rfl, hb7, h45, hhi_val, hlo_eq⟩

/-- `IxonDeserialize::unpack_def_asserts` decodes a packed definition flags byte. -/
theorem unpack_def_asserts_spec {b : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "IxonDeserialize::unpack_def_asserts" [.field (b.toNat : F)] h r h' cs) :
    h' = h ∧
    (((b >>> 2) &&& 3 > 2 || (b &&& 3) > 2) = false) ∧
    ∃ (k : Ix.DefKind) (s : Ix.DefinitionSafety) (a : Ixon.DefAsserts),
      Ixon.DefAsserts.ofCode? (b >>> 4) = some a ∧
      Ixon.unpackDefKindSafety (b &&& 15) = (k, s) ∧
      r = .tuple [repDefKindVal k, repDefSafetyVal s, .field ((a.toCode.toNat : Nat) : F)] := by
  cases «IxonDeserialize::unpack_def_asserts».obs ev with
  | n0 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he242 he268 _ =>
    have op0 : evalBinOp .add x181 y182 = .ok (.field ((0 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 0) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op0
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inl hlo)
    subst he268 he242
    refine ⟨rfl, hvalid, .defn, .unsaf, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).1 hlo]
  | n1 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he280 he306 _ =>
    have op1 : evalBinOp .add x181 y182 = .ok (.field ((1 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 1) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op1
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inr (Or.inl hlo))
    subst he306 he280
    refine ⟨rfl, hvalid, .defn, .safe, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).2.1 hlo]
  | n2 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he318 he344 _ =>
    have op2 : evalBinOp .add x181 y182 = .ok (.field ((2 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 2) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op2
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inr (Or.inr (Or.inl hlo)))
    subst he344 he318
    refine ⟨rfl, hvalid, .defn, .part, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).2.2.1 hlo]
  | n4 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he356 he382 _ =>
    have op4 : evalBinOp .add x181 y182 = .ok (.field ((4 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 4) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op4
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inr (Or.inr (Or.inr (Or.inl hlo))))
    subst he382 he356
    refine ⟨rfl, hvalid, .opaq, .unsaf, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).2.2.2.1 hlo]
  | n5 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he394 he420 _ =>
    have op5 : evalBinOp .add x181 y182 = .ok (.field ((5 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 5) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op5
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlo)))))
    subst he420 he394
    refine ⟨rfl, hvalid, .opaq, .safe, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).2.2.2.2.1 hlo]
  | n6 m2 cs12 x_b0 x_b1 x_b2 x_b3 x_b4 x_b5 x_b6 x_b7 v104 v129 x137 y138 y146 x181 y182 x189 y190 y198
      ev14 heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188 he432 he458 _ =>
    have op6 : evalBinOp .add x181 y182 = .ok (.field ((6 : Nat) : F)) := by simpa using op188
    obtain ⟨rfl, hb7, h45, hv129, hlo⟩ :=
      unpack_bits_helper (low := 6) (by omega) ev14 heq92 op119 heq128
        op161 op152 op170 op144 op213 op204 op222 op196 op231 op6
    obtain ⟨hvalid, a, hof, hcode⟩ := defFlags_decode b hb7 h45 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hlo))))))
    subst he458 he432
    refine ⟨rfl, hvalid, .opaq, .part, a, hof, ?_, by rw [hv129, hcode]; rfl⟩
    rw [lowNibble_eq, (defKindSafety_table (b.toNat % 16)).2.2.2.2.2.1 hlo]

/-- `IxonDeserialize::unpack_def_kind_safety` decodes a definition flags byte (fast path or
assertion-nibble path). -/
theorem unpack_def_kind_safety_spec {b : UInt8} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "IxonDeserialize::unpack_def_kind_safety" [.field (b.toNat : F)] h r h' cs) :
    h' = h ∧
    (((b >>> 2) &&& 3 > 2 || (b &&& 3) > 2) = false) ∧
    ∃ (k : Ix.DefKind) (s : Ix.DefinitionSafety) (a : Ixon.DefAsserts),
      Ixon.DefAsserts.ofCode? (b >>> 4) = some a ∧
      Ixon.unpackDefKindSafety (b &&& 15) = (k, s) ∧
      r = .tuple [repDefKindVal k, repDefSafetyVal s, .field ((a.toCode.toNat : Nat) : F)] := by
  have hb : b.toNat < 256 := b.toNat_lt
  cases «IxonDeserialize::unpack_def_kind_safety».obs ev with
  | n0 m2 cs13 ev15 he33 he58 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb0 : b = 0 := UInt8.ext ((natCast_eq_zero_iff hb).mp (Value.field.inj heq).symm)
    subst hb0 he58 he33
    exact ⟨rfl, rfl, .defn, .unsaf, {}, rfl, rfl, rfl⟩
  | n1 m2 cs13 ev15 he70 he95 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb1 : b = 1 := UInt8.ext ((natCast_eq_one_iff hb).mp (Value.field.inj heq).symm)
    subst hb1 he95 he70
    exact ⟨rfl, rfl, .defn, .safe, {}, rfl, rfl, rfl⟩
  | n2 m2 cs13 ev15 he107 he132 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb2 : b = 2 := UInt8.ext ((natCast_eq_ofNat_iff (n := 2) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb2 he132 he107
    exact ⟨rfl, rfl, .defn, .part, {}, rfl, rfl, rfl⟩
  | n4 m2 cs13 ev15 he144 he169 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb4 : b = 4 := UInt8.ext ((natCast_eq_ofNat_iff (n := 4) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb4 he169 he144
    exact ⟨rfl, rfl, .opaq, .unsaf, {}, rfl, rfl, rfl⟩
  | n5 m2 cs13 ev15 he181 he206 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb5 : b = 5 := UInt8.ext ((natCast_eq_ofNat_iff (n := 5) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb5 he206 he181
    exact ⟨rfl, rfl, .opaq, .safe, {}, rfl, rfl, rfl⟩
  | n6 m2 cs13 ev15 he218 he243 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb6 : b = 6 := UInt8.ext ((natCast_eq_ofNat_iff (n := 6) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb6 he243 he218
    exact ⟨rfl, rfl, .opaq, .part, {}, rfl, rfl, rfl⟩
  | n8 m2 cs13 ev15 he255 he280 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb8 : b = 8 := UInt8.ext ((natCast_eq_ofNat_iff (n := 8) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb8 he280 he255
    exact ⟨rfl, rfl, .thm, .unsaf, {}, rfl, rfl, rfl⟩
  | n9 m2 cs13 ev15 he292 he317 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb9 : b = 9 := UInt8.ext ((natCast_eq_ofNat_iff (n := 9) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb9 he317 he292
    exact ⟨rfl, rfl, .thm, .safe, {}, rfl, rfl, rfl⟩
  | n10 m2 cs13 ev15 he329 he354 _ =>
    obtain ⟨heq, rfl⟩ := u8ToField_refines ev15.erase
    have hb10 : b = 10 := UInt8.ext ((natCast_eq_ofNat_iff (n := 10) hb (by omega)).mp (Value.field.inj heq).symm)
    subst hb10 he354 he329
    exact ⟨rfl, rfl, .thm, .part, {}, rfl, rfl, rfl⟩
  | other v1 m2 cs13 cs363 ev15 _ _ _ _ _ _ _ _ _ ev365 _ =>
    obtain ⟨_, rfl⟩ := u8ToField_refines ev15.erase
    exact unpack_def_asserts_spec ev365

/-- `IxonDeserialize::get_definition` at offset `i` refines `Ixon.getDefinition`, consuming at
least 4 bytes. -/
theorem get_definition_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_definition" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (d : Ixon.Definition) (n : Nat) (defVal restPtr : SourceValue F),
      0 < n ∧
      Ixon.getDefinition { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok d { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [defVal, restPtr] ∧
      RepDefinition h' d defVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_definition».obs ev with
  | run m2 cs12 x_packed x_s m37 cs47 x_kind x_safety x_asserts m77 cs87 x_lvls x_s2
      m112 cs122 x_typ x_s3 m147 cs157 x_value x_s4
      ev14 ev49 ev89 ev124 ev159 he185 he250 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    obtain ⟨rfl, hvalid, k, s, a, hof, hunpack, heq_ks⟩ := unpack_def_kind_safety_spec ev49
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq_ks
    rcases heq_ks with ⟨rfl, rfl, rfl⟩
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at hrep0 ev89.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, typ, n2, typPtr, restPtr2, hn2, _, hok2, heq2, typRep, hrep2⟩ :=
      getExpr_refines_at hrep1 ev124.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨ext3, val, n3, valPtr, restPtr3, hn3, _, hok3, heq3, valRep, hrep3⟩ :=
      getExpr_refines_at hrep2 ev159.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3
    rcases heq3 with ⟨rfl, rfl⟩
    subst he250 he185
    refine ⟨ext2.trans ext3, ⟨k, s, a, t.value, typ, val⟩, 1 + n1 + n2 + n3, _, restPtr3,
      by omega, ?_, rfl, ⟨typPtr, valPtr, rfl, typRep.mono ext3, valRep⟩,
      by rw [← Nat.add_assoc, ← Nat.add_assoc]; exact hrep3⟩
    unfold Ixon.getDefinition
    simp [bind, EStateM.bind, hu8, hvalid, hof, hunpack,
      hok1, hok2, hok3, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_recursor_rule` at offset `i` refines `Ixon.getRecursorRule` and consumes
at least 2 bytes. -/
theorem get_recursor_rule_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_recursor_rule" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ru : Ixon.RecursorRule) (n : Nat) (ruVal restPtr : SourceValue F),
      2 ≤ n ∧
      (bytes.drop (i + n)).length + 2 ≤ (bytes.drop i).length ∧
      Ixon.getRecursorRule { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ru { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [ruVal, restPtr] ∧
      RepRecursorRule h' ru ruVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_recursor_rule».obs ev with
  | run m2 cs12 x_fields x_s m37 cs47 x_rhs x_s2 ev14 ev49 he75 he108 _ =>
    obtain ⟨rfl, t, n1, restPtr1, hok0, _, hrep1, heq1⟩ := getTag0_refines rep ev14.erase
    have hok1 : Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } := getTagN_drop hok0
    obtain ⟨hn1, hlen1⟩ := getTagN_pos hok0
    rw [List.drop_drop] at hrep1
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
    rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, rhs, n2, rhsPtr, restPtr2, hn2, hdrop2, hok2, heq2, rhsRep, hrep2⟩ :=
      getExpr_refines_at hrep1 ev49.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
    rcases heq2 with ⟨rfl, rfl⟩
    subst he108 he75
    have hlen_bound : (bytes.drop (i + (n1 + n2))).length + 2 ≤ (bytes.drop i).length := by
      rw [← Nat.add_assoc]
      simp only [List.length_drop] at hdrop2 hlen1 ⊢
      omega
    refine ⟨ext2, ⟨t.value, rhs⟩, n1 + n2, _, restPtr2, by omega, hlen_bound, ?_, rfl,
      ⟨rhsPtr, rfl, rhsRep⟩, by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getRecursorRule
    simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_recursor_rule_list` at offset `i` refines
`Ixon.getArray Ixon.getRecursorRule count` and consumes at least `2 * count` bytes. -/
theorem get_recursor_rule_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_recursor_rule_list" [stream, u64Value count] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (rules : Array Ixon.RecursorRule) (n : Nat) (listPtr restPtr : SourceValue F),
      count * 2 ≤ (bytes.drop i).length ∧
      Ixon.getArray Ixon.getRecursorRule count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok rules { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList recursorRuleListEnum RepRecursorRule h' rules.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' cs with
  | zero =>
    cases «IxonDeserialize::get_recursor_rule_list».obs ev with
    | n1 m2 cs12 m43 ev14 he41 hm51 he62 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      subst he62 hm51 he41
      have ext := Aiur.Library.List.allocNil_extends recursorRuleListEnum h
      refine ⟨ext, #[], 0, (Aiur.Library.List.allocNil recursorRuleListEnum h).1, stream,
        by omega, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep recursorRuleListEnum RepRecursorRule h,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    | n0 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp at hiz
  | succ count ih =>
    cases «IxonDeserialize::get_recursor_rule_list».obs ev with
    | n1 m2 _ _ ev14 _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp [Nat.succ_ne_zero] at hiz
    | n0 m2 cs12 m70 cs80 x_rule x_s m105 cs115 v119 m128 cs136 x_rest x_s2 m166
        ev14 ev82 ev138 ev117 he164 hm174 he201 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨ext1, ru, n1, ruVal, restPtr1, _, hlen1, hok1, heq1, ruRep, hrep1⟩ :=
        get_recursor_rule_spec rep ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl⟩
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailRules, n2, tailPtr, restPtr2, hlen2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl⟩
      subst he201 hm174 he164
      have ext3 := Aiur.Library.List.allocCons_extends recursorRuleListEnum ruVal tailPtr m105
      refine ⟨(ext1.trans ext2).trans ext3, #[ru] ++ tailRules, n1 + n2,
        (Aiur.Library.List.allocCons recursorRuleListEnum ruVal tailPtr m105).1, restPtr2,
        by omega, ?_, rfl, ?_,
        by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · simpa using Aiur.Library.List.allocCons_rep recursorRuleListEnum repRecursorRule_heapMono₂
          (ruRep.mono ext2) tailRep

private theorem recursorFlags_decode :
    ∀ b : UInt8, b.toNat < 4 →
      ¬ (b > 3) ∧
      repBoolField (Ixon.unpackBools 2 b)[0]! = .field ((b.toNat % 2 : Nat) : F) ∧
      repBoolField (Ixon.unpackBools 2 b)[1]! = .field ((b.toNat / 2 % 2 : Nat) : F) := by
  intro b hb
  have h0123 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
    have hv := b.toNat_lt
    rcases h : b.toNat with _ | _ | _ | _ | n
    · exact Or.inl (UInt8.ext h)
    · exact Or.inr (Or.inl (UInt8.ext h))
    · exact Or.inr (Or.inr (Or.inl (UInt8.ext h)))
    · exact Or.inr (Or.inr (Or.inr (UInt8.ext h)))
    · omega
  rcases h0123 with rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by simp [Ixon.unpackBools, repBoolField], by simp [Ixon.unpackBools, repBoolField]⟩

/-- `IxonDeserialize::get_recursor` at offset `i` refines `Ixon.getRecursor`. -/
theorem get_recursor_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_recursor" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (rc : Ixon.Recursor) (n : Nat) (rcVal restPtr : SourceValue F),
      Ixon.getRecursor { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok rc { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [rcVal, restPtr] ∧
      RepRecursor h' rc rcVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_recursor».obs ev with
  | run m2 cs12 x_bools_byte x_s v47 m50 cs58 v83 m84 cs94 v105 v117
      m130 cs140 x_lvls x_s2 m165 cs175 x_params x_s3 m200 cs210 x_indices x_s4
      m235 cs245 x_motives x_s5 m270 cs280 x_minors x_s6 m305 cs315 x_typ x_s7
      m340 cs350 x_rules_len x_s8 m375 cs385 x_rules x_s9
      ev14 ev60 heq82 ev96 pr115 pr127 ev142 ev177 ev212 ev247 ev282 ev317 ev352 ev387
      he421 he510 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    have ev60' : EvalFn W "UInt8::less_than" [.field (b.toNat : F), .field ((4 : Nat) : F)] h v47 m50 := by
      simpa using ev60.erase
    obtain ⟨hlt_val, rfl⟩ := u8LessThan_refines b.toNat_lt (by omega) ev60'
    subst heq82
    have hb4 : b.toNat < 4 := by
      by_cases hlt : b.toNat < 4
      · exact hlt
      · simp [hlt] at hlt_val
    obtain ⟨hbits, rfl⟩ := u8BitDecomposition_refines b.toNat_lt ev96.erase
    subst hbits
    simp only [projectValue, List.getElem?_cons_zero, List.getElem?_cons_succ, Except.ok.injEq] at pr115 pr127
    subst pr115 pr127
    obtain ⟨hflags_ok, hk_rep, hu_rep⟩ := recursorFlags_decode b hb4
    obtain ⟨rfl, tLvls, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at hrep0 ev142.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1; rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tParams, n2, restPtr2, hok2, _, hrep2, heq2⟩ := getTag0_refines_at hrep1 ev177.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tIndices, n3, restPtr3, hok3, _, hrep3, heq3⟩ := getTag0_refines_at hrep2 ev212.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3; rcases heq3 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tMotives, n4, restPtr4, hok4, _, hrep4, heq4⟩ := getTag0_refines_at hrep3 ev247.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4; rcases heq4 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tMinors, n5, restPtr5, hok5, _, hrep5, heq5⟩ := getTag0_refines_at hrep4 ev282.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq5; rcases heq5 with ⟨rfl, rfl⟩
    obtain ⟨ext6, typ, n6, typPtr, restPtr6, _, _, hok6, heq6, typRep, hrep6⟩ :=
      getExpr_refines_at hrep5 ev317.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq6; rcases heq6 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tRules, n7, restPtr7, hok7, _, hrules_lt, hrep7, heq7⟩ :=
      getVecLen_refines_at hrep6 ev352.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq7; rcases heq7 with ⟨rfl, rfl⟩
    obtain ⟨ext8, rules, n8, rulesPtr, restPtr8, hlen_rules, hok8, heq8, rulesRep, hrep8⟩ :=
      get_recursor_rule_list_spec tRules.value.toNat hrules_lt hrep7 ev387
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq8; rcases heq8 with ⟨rfl, rfl⟩
    subst he510 he421
    have hchk : Ixon.checkCount tRules.value.toNat.toUInt64 2
        { idx := i + 1 + n1 + n2 + n3 + n4 + n5 + n6 + n7, bytes := ⟨bytes.toArray⟩ } =
        .ok () { idx := i + 1 + n1 + n2 + n3 + n4 + n5 + n6 + n7, bytes := ⟨bytes.toArray⟩ } := by
      apply checkCount_ok
      simpa [UInt64.ofNat_toNat] using hlen_rules
    let rc : Ixon.Recursor :=
      ⟨(Ixon.unpackBools 2 b)[0]!, (Ixon.unpackBools 2 b)[1]!,
       tLvls.value, tParams.value, tIndices.value, tMotives.value, tMinors.value, typ, rules⟩
    refine ⟨ext6.trans ext8, rc, 1 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8, _, restPtr8, ?_, rfl,
      ?_, by simp only [Nat.add_assoc] at hrep8 ⊢; exact hrep8⟩
    · have hloop :
        (do
          let mut rs : Array Ixon.RecursorRule := #[]
          for _ in [0:tRules.value.toNat] do
            rs := rs.push (← Ixon.getRecursorRule)
          return (⟨(Ixon.unpackBools 2 b)[0]!, (Ixon.unpackBools 2 b)[1]!,
            tLvls.value, tParams.value, tIndices.value, tMotives.value, tMinors.value,
            typ, rs⟩ : Ixon.Recursor)) =
        (do
          let rs ← Ixon.getArray Ixon.getRecursorRule tRules.value.toNat
          return (⟨(Ixon.unpackBools 2 b)[0]!, (Ixon.unpackBools 2 b)[1]!,
            tLvls.value, tParams.value, tIndices.value, tMotives.value, tMinors.value,
            typ, rs⟩ : Ixon.Recursor)) := by
        simp [Ixon.getArray]
      unfold Ixon.getRecursor
      simp only [bind, EStateM.bind, hu8, hflags_ok, ↓reduceIte,
        hok1, hok2, hok3, hok4, hok5, hok6, hok7, hchk]
      rw [hloop]
      simp [bind, EStateM.bind, hok8, pure, EStateM.pure, Nat.add_assoc]
    · refine ⟨typPtr, rulesPtr, ?_, typRep.mono ext8, rulesRep⟩
      simp only [rc, hk_rep, hu_rep]

/-- `IxonDeserialize::get_axiom` at offset `i` refines `Ixon.getAxiom`. -/
theorem get_axiom_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_axiom" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ax : Ixon.Axiom) (n : Nat) (axVal restPtr : SourceValue F),
      Ixon.getAxiom { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ax { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [axVal, restPtr] ∧
      RepAxiom h' ax axVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_axiom».obs ev with
  | run m2 cs12 x_is_unsafe x_s v36 m37 cs47 m59 cs69 x_lvls x_s2 m94 cs104 x_typ x_s3
      v142 m146 cs154 ev14 ev49 ev71 ev106 he132 ev156 he186 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hb2, _, rfl⟩ := assertWireBool_refines b.toNat_lt ev49.erase
    obtain ⟨_, hdrop1, _⟩ := getU8_of_drop_cons hcons
    have hbeq : decide (b.toNat = 1) = (b == 1) := by
      rcases h : b.toNat with _ | _ | n
      · have hb0 : b = 0 := UInt8.ext h; subst hb0; rfl
      · have hb1 : b = 1 := UInt8.ext h; subst hb1; rfl
      · omega
    have hbool : Ixon.Serialize.get (α := Bool) { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok (b == 1) { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
      rw [← hbeq]; exact getBool_of_drop_cons hcons hb2
    rw [← hdrop1] at hrep0
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at hrep0 ev71.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1; rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, typ, n2, typPtr, restPtr2, _, _, hok2, heq2, typRep, hrep2⟩ :=
      getExpr_refines_at hrep1 ev106.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := u8ToField_refines ev156.erase
    subst he186 he132
    have hbf : (.field (b.toNat : F) : SourceValue F) = repBoolField (b == 1) := by
      rcases h : b.toNat with _ | _ | n
      · have hb0 : b = 0 := UInt8.ext h; subst hb0; rfl
      · have hb1 : b = 1 := UInt8.ext h; subst hb1; rfl
      · omega
    refine ⟨ext2, ⟨b == 1, t.value, typ⟩, 1 + n1 + n2, _, restPtr2, ?_, rfl,
      ⟨typPtr, by rw [hbf], typRep⟩, by simp only [Nat.add_assoc] at hrep2 ⊢; exact hrep2⟩
    unfold Ixon.getAxiom
    simp [bind, EStateM.bind, hbool, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_quotient` at offset `i` refines `Ixon.getQuotient`. -/
theorem get_quotient_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_quotient" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (q : Ixon.Quotient) (n : Nat) (qVal restPtr : SourceValue F),
      Ixon.getQuotient { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok q { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [qVal, restPtr] ∧
      RepQuotient h' q qVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_quotient».obs ev with
  | run m2 cs12 x_kind_byte x_s v36 m37 cs47 m59 cs69 x_lvls x_s2 m94 cs104 x_typ x_s3
      ev14 ev49 ev71 ev106 he132 he173 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    obtain ⟨hb4, rfl, hqk_val⟩ := getQuotKind_refines b.toNat_lt ev49.erase
    obtain ⟨rfl, t, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at hrep0 ev71.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1; rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨ext2, typ, n2, typPtr, restPtr2, _, _, hok2, heq2, typRep, hrep2⟩ :=
      getExpr_refines_at hrep1 ev106.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    subst he173 he132 hqk_val
    have hcases : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
      rcases h : b.toNat with _ | _ | _ | _ | n
      · exact Or.inl (UInt8.ext h)
      · exact Or.inr (Or.inl (UInt8.ext h))
      · exact Or.inr (Or.inr (Or.inl (UInt8.ext h)))
      · exact Or.inr (Or.inr (Or.inr (UInt8.ext h)))
      · omega
    rcases hcases with rfl | rfl | rfl | rfl
    · refine ⟨ext2, ⟨.type, t.value, typ⟩, 1 + n1 + n2, _, restPtr2, ?_, rfl,
        ⟨typPtr, rfl, typRep⟩, by simp only [Nat.add_assoc] at hrep2 ⊢; exact hrep2⟩
      unfold Ixon.getQuotient
      simp [bind, EStateM.bind, hu8, pure, EStateM.pure, hok1, hok2, Nat.add_assoc]
    · refine ⟨ext2, ⟨.ctor, t.value, typ⟩, 1 + n1 + n2, _, restPtr2, ?_, rfl,
        ⟨typPtr, rfl, typRep⟩, by simp only [Nat.add_assoc] at hrep2 ⊢; exact hrep2⟩
      unfold Ixon.getQuotient
      simp [bind, EStateM.bind, hu8, pure, EStateM.pure, hok1, hok2, Nat.add_assoc]
    · refine ⟨ext2, ⟨.lift, t.value, typ⟩, 1 + n1 + n2, _, restPtr2, ?_, rfl,
        ⟨typPtr, rfl, typRep⟩, by simp only [Nat.add_assoc] at hrep2 ⊢; exact hrep2⟩
      unfold Ixon.getQuotient
      simp [bind, EStateM.bind, hu8, pure, EStateM.pure, hok1, hok2, Nat.add_assoc]
    · refine ⟨ext2, ⟨.ind, t.value, typ⟩, 1 + n1 + n2, _, restPtr2, ?_, rfl,
        ⟨typPtr, rfl, typRep⟩, by simp only [Nat.add_assoc] at hrep2 ⊢; exact hrep2⟩
      unfold Ixon.getQuotient
      simp [bind, EStateM.bind, hu8, pure, EStateM.pure, hok1, hok2, Nat.add_assoc]

/-- `IxonDeserialize::get_field_mode_list` at offset `i` refines `Ixon.getArray Ixon.getFieldMode`
and tracks whether any field is `shared`. -/
theorem get_field_mode_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_field_mode_list" [stream, u64Value count] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (modes : Array Ixon.FieldMode) (listPtr restPtr : SourceValue F),
      count ≤ (bytes.drop i).length ∧
      modes.size = count ∧
      Ixon.getArray Ixon.getFieldMode count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok modes { idx := i + count, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, repBoolField (modes.any (· == .shared)), restPtr] ∧
      Aiur.Library.List.RepList fieldModeListEnum RepFieldMode h' modes.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + count)) restPtr := by
  induction count generalizing i stream r h h' cs with
  | zero =>
    cases «IxonDeserialize::get_field_mode_list».obs ev with
    | n1 m2 cs12 m44 ev14 he42 hm52 he69 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      subst he69 hm52 he42
      have ext := Aiur.Library.List.allocNil_extends fieldModeListEnum h
      refine ⟨ext, #[], (Aiur.Library.List.allocNil fieldModeListEnum h).1, stream,
        by omega, rfl, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        rfl, Aiur.Library.List.allocNil_rep fieldModeListEnum RepFieldMode h,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    | n0_n0 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase; simp at hiz
    | n0_n1 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    cases «IxonDeserialize::get_field_mode_list».obs ev with
    | n1 m2 _ _ ev14 _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp [Nat.succ_ne_zero] at hiz
    | n0_n0 m2 cs12 m77 cs87 x_mode x_s m112 cs122 v126 m135 cs143 x_rest x_shared x_s2 m173 cs184 m206
        ev14 ev89 ev145 ev124 ev186 he204 hm214 he247 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev89.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
      rcases heq0 with ⟨rfl, rfl⟩
      obtain ⟨hu8, hdrop1, hlt1⟩ := getU8_of_drop_cons hcons
      rw [← hdrop1] at hrep0
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev145.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailModes, tailPtr, restPtr2, hlen2, hsz2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep0 ev124
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl, rfl⟩
      obtain ⟨heq_b, rfl⟩ := u8ToField_refines ev186.erase
      have hb0 : b = 0 := UInt8.ext ((natCast_eq_zero_iff b.toNat_lt).mp (Value.field.inj heq_b).symm)
      subst hb0 he247 hm214 he204
      have hfm : Ixon.getFieldMode { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok .inherited { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
        unfold Ixon.getFieldMode
        simp [bind, EStateM.bind, hu8, Ixon.FieldMode.ofCode?, pure, EStateM.pure]
      have ext3 := Aiur.Library.List.allocCons_extends fieldModeListEnum (.field 0) tailPtr m112
      have hlen_all : count + 1 ≤ (bytes.drop i).length := by
        rw [hcons, List.length_cons]; rw [hdrop1] at hlen2; omega
      have hany : ((#[Ixon.FieldMode.inherited] ++ tailModes).any (· == .shared)) =
          tailModes.any (· == .shared) := by
        rw [← Array.any_toList, ← Array.any_toList]; simp
      refine ⟨ext2.trans ext3, #[.inherited] ++ tailModes,
        (Aiur.Library.List.allocCons fieldModeListEnum (.field 0) tailPtr m112).1, restPtr2,
        hlen_all, by simp [hsz2]; omega, ?_, by rw [hany], ?_,
        by rw [show i + (count + 1) = i + 1 + count by omega]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hfm, hok2, pure, EStateM.pure]
        rw [show i + 1 + count = i + (count + 1) by omega]
      · simpa using Aiur.Library.List.allocCons_rep fieldModeListEnum repFieldMode_heapMono₂
          (rfl : RepFieldMode m112 .inherited (.field 0)) tailRep
    | n0_n1 m2 cs12 m77 cs87 x_mode x_s m112 cs122 v126 m135 cs143 x_rest x_shared x_s2 m173 cs184 m261
        ev14 ev89 ev145 ev124 ev186 he259 hm269 he301 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev89.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
      rcases heq0 with ⟨rfl, rfl⟩
      obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
      rw [← hdrop1] at hrep0
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev145.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailModes, tailPtr, restPtr2, hlen2, hsz2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep0 ev124
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl, rfl⟩
      obtain ⟨heq_b, rfl⟩ := u8ToField_refines ev186.erase
      have hb1 : b = 1 := UInt8.ext ((natCast_eq_one_iff b.toNat_lt).mp (Value.field.inj heq_b).symm)
      subst hb1 he301 hm269 he259
      have hfm : Ixon.getFieldMode { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok .shared { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
        unfold Ixon.getFieldMode
        simp [bind, EStateM.bind, hu8, Ixon.FieldMode.ofCode?, pure, EStateM.pure]
      have ext3 := Aiur.Library.List.allocCons_extends fieldModeListEnum (.field 1) tailPtr m112
      have hlen_all : count + 1 ≤ (bytes.drop i).length := by
        rw [hcons, List.length_cons]; rw [hdrop1] at hlen2; omega
      have hany : ((#[Ixon.FieldMode.shared] ++ tailModes).any (· == .shared)) = true := by
        rw [← Array.any_toList]; simp
      refine ⟨ext2.trans ext3, #[.shared] ++ tailModes,
        (Aiur.Library.List.allocCons fieldModeListEnum (.field 1) tailPtr m112).1, restPtr2,
        hlen_all, by simp [hsz2]; omega, ?_, by rw [hany]; rfl, ?_,
        by rw [show i + (count + 1) = i + 1 + count by omega]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hfm, hok2, pure, EStateM.pure]
        rw [show i + 1 + count = i + (count + 1) by omega]
      · simpa using Aiur.Library.List.allocCons_rep fieldModeListEnum repFieldMode_heapMono₂
          (rfl : RepFieldMode m112 .shared (.field 1)) tailRep

/-- `IxonDeserialize::get_constructor_modes` refines `Ixon.getConstructorFieldModes`. -/
theorem get_constructor_modes_spec {listed : Bool} {fields : UInt64}
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constructor_modes"
      [repBoolField listed, u64Value fields.toNat, stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (fm : Ixon.FieldModes fields.toNat) (n : Nat) (modesPtr restPtr : SourceValue F),
      Ixon.getConstructorFieldModes listed fields.toNat { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok fm { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [modesPtr, restPtr] ∧
      Aiur.Library.List.RepList fieldModeListEnum RepFieldMode h' fm.toArray.toList modesPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_constructor_modes».obs ev with
  | n0 m21 hv14 he19 hm29 he40 _ =>
    have hlisted : listed = false := by
      cases listed with
      | false => rfl
      | true => simp [repBoolField] at hv14
    subst hlisted he40 hm29 he19
    have ext := Aiur.Library.List.allocNil_extends fieldModeListEnum h
    refine ⟨ext, .inherited, 0, (Aiur.Library.List.allocNil fieldModeListEnum h).1, stream,
      by simp [Ixon.getConstructorFieldModes, pure, EStateM.pure], rfl,
      by simpa [Ixon.FieldModes.toArray] using Aiur.Library.List.allocNil_rep fieldModeListEnum RepFieldMode h,
      Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
  | n1 m48 cs58 x_modes x_shared x_s2 _ hv46 ev60 heq121 he126 he141 _ =>
    have hlisted : listed = true := by
      cases listed with
      | false => simp [repBoolField] at hv46
      | true => rfl
    subst hlisted he141 he126 heq121
    obtain ⟨ext, modes, modesPtr, restPtr, hlen, hsz, hok, heq, modesRep, dropRep⟩ :=
      get_field_mode_list_spec fields.toNat fields.toNat_lt rep ev60
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq
    rcases heq with ⟨rfl, hsh, rfl⟩
    have hany : modes.any (· == .shared) = true := by
      cases h : modes.any (· == .shared) with
      | true => rfl
      | false => simp [repBoolField, h] at hsh
    have hchk : Ixon.checkCount fields.toNat.toUInt64 1 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok () { idx := i, bytes := ⟨bytes.toArray⟩ } := by
      apply checkCount_ok
      simpa [UInt64.ofNat_toNat] using hlen
    let fm : Ixon.FieldModes fields.toNat := .listed ⟨modes, hsz⟩ hany
    have hlisted_eq : Ixon.FieldModes.listed? (n := fields.toNat) modes = some fm := by
      unfold Ixon.FieldModes.listed?
      rw [dite_eq_left hsz, dite_eq_left hany]
    refine ⟨ext, fm, fields.toNat, modesPtr, restPtr, ?_, rfl,
      by simpa [fm, Ixon.FieldModes.toArray] using modesRep, dropRep⟩
    unfold Ixon.getConstructorFieldModes Ixon.getFieldModes
    simp [bind, EStateM.bind, hchk, hok, hlisted_eq, pure, EStateM.pure]

private theorem ctorFlags_decode :
    ∀ b : UInt8, b.toNat < 4 →
      ¬ (b > 3) ∧
      repBoolField (b &&& 1 == 1) = .field ((b.toNat % 2 : Nat) : F) ∧
      repBoolField (b &&& 2 == 2) = .field ((b.toNat / 2 % 2 : Nat) : F) := by
  intro b hb
  have h0123 : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
    rcases h : b.toNat with _ | _ | _ | _ | n
    · exact Or.inl (UInt8.ext h)
    · exact Or.inr (Or.inl (UInt8.ext h))
    · exact Or.inr (Or.inr (Or.inl (UInt8.ext h)))
    · exact Or.inr (Or.inr (Or.inr (UInt8.ext h)))
    · omega
  rcases h0123 with rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by simp [repBoolField], by simp [repBoolField]⟩

/-- `IxonDeserialize::get_constructor` at offset `i` refines `Ixon.getConstructor` and consumes at
least 6 bytes. -/
theorem get_constructor_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constructor" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ct : Ixon.Constructor) (n : Nat) (ctVal restPtr : SourceValue F),
      6 ≤ n ∧
      (bytes.drop (i + n)).length + 6 ≤ (bytes.drop i).length ∧
      Ixon.getConstructor { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ct { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [ctVal, restPtr] ∧
      RepConstructor h' ct ctVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_constructor».obs ev with
  | run m2 cs12 x_flags x_s v47 m50 cs58 v83 m84 cs94
      m106 cs116 x_lvls x_s2 m141 cs151 x_cidx x_s3 m176 cs186 x_params x_s4
      m211 cs221 x_fields x_s5 m246 cs256 v259 x_modes x_s6 m300 cs310 x_typ x_s7 v348
      ev14 ev60 heq82 ev96 ev118 ev153 ev188 ev223 pr270 ev258 ev312 he338 pr363 he414 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop0, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop0] at hrep0
    have ev60' : EvalFn W "UInt8::less_than" [.field (b.toNat : F), .field ((4 : Nat) : F)] h v47 m50 := by
      simpa using ev60.erase
    obtain ⟨hlt_val, rfl⟩ := u8LessThan_refines b.toNat_lt (by omega) ev60'
    subst heq82
    have hb4 : b.toNat < 4 := by
      by_cases hlt : b.toNat < 4
      · exact hlt
      · simp [hlt] at hlt_val
    obtain ⟨hbits, rfl⟩ := u8BitDecomposition_refines b.toNat_lt ev96.erase
    subst hbits
    simp only [projectValue, List.getElem?_cons_zero, List.getElem?_cons_succ, Except.ok.injEq] at pr270 pr363
    subst pr270 pr363
    obtain ⟨hflags_ok, hu_rep, hl_rep⟩ := ctorFlags_decode b hb4
    obtain ⟨rfl, tLvls, n1, restPtr1, hok1_0, _, hrep1, heq1⟩ := getTag0_refines hrep0 ev118.erase
    have hok1 := getTagN_drop hok1_0; obtain ⟨hn1, _⟩ := getTagN_pos hok1_0
    rw [List.drop_drop] at hrep1
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1; rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tCidx, n2, restPtr2, hok2_0, _, hrep2, heq2⟩ := getTag0_refines hrep1 ev153.erase
    have hok2 := getTagN_drop hok2_0; obtain ⟨hn2, _⟩ := getTagN_pos hok2_0
    rw [List.drop_drop] at hrep2
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tParams, n3, restPtr3, hok3_0, _, hrep3, heq3⟩ := getTag0_refines hrep2 ev188.erase
    have hok3 := getTagN_drop hok3_0; obtain ⟨hn3, _⟩ := getTagN_pos hok3_0
    rw [List.drop_drop] at hrep3
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3; rcases heq3 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tFields, n4, restPtr4, hok4_0, _, hrep4, heq4⟩ := getTag0_refines hrep3 ev223.erase
    have hok4 := getTagN_drop hok4_0; obtain ⟨hn4, _⟩ := getTagN_pos hok4_0
    rw [List.drop_drop] at hrep4
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4; rcases heq4 with ⟨rfl, rfl⟩
    have ev258' : ObsFn W "IxonDeserialize::get_constructor_modes"
        [repBoolField (b &&& 2 == 2), u64Value tFields.value.toNat, restPtr4] h
        (.tuple [x_modes, x_s6]) m246 cs256 := by
      rw [hl_rep]; exact ev258
    obtain ⟨ext5, fm, n5, modesPtr, restPtr5, hok5, heq5, modesRep, hrep5⟩ :=
      get_constructor_modes_spec hrep4 ev258'
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq5; rcases heq5 with ⟨rfl, rfl⟩
    obtain ⟨ext6, typ, n6, typPtr, restPtr6, hn6, hdrop6, hok6, heq6, typRep, hrep6⟩ :=
      getExpr_refines_at hrep5 ev312.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq6; rcases heq6 with ⟨rfl, rfl⟩
    subst he414 he338
    have hi_len : 0 < (bytes.drop i).length := by rw [hcons]; simp
    have hlen_bound :
        (bytes.drop (i + (1 + n1 + n2 + n3 + n4 + n5 + n6))).length + 6 ≤ (bytes.drop i).length := by
      simp only [List.length_drop] at hdrop6 hi_len ⊢
      omega
    let ct : Ixon.Constructor :=
      ⟨b &&& 1 == 1, tLvls.value, tCidx.value, tParams.value, tFields.value, fm, typ⟩
    refine ⟨ext5.trans ext6, ct, 1 + n1 + n2 + n3 + n4 + n5 + n6, _, restPtr6,
      by omega, hlen_bound, ?_, rfl, ?_,
      by simp only [Nat.add_assoc] at hrep6 ⊢; exact hrep6⟩
    · unfold Ixon.getConstructor
      simp [bind, EStateM.bind, hu8, hflags_ok,
        hok1, hok2, hok3, hok4, hok5, hok6, pure, EStateM.pure, Nat.add_assoc]
    · refine ⟨modesPtr, typPtr, ?_, modesRep.mono repFieldMode_heapMono₂ ext6, typRep⟩
      simp only [ct, hu_rep]

/-- `IxonDeserialize::get_constructor_list` at offset `i` refines
`Ixon.getArray Ixon.getConstructor count` and consumes at least `6 * count` bytes. -/
theorem get_constructor_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_constructor_list" [stream, u64Value count] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ctors : Array Ixon.Constructor) (n : Nat) (listPtr restPtr : SourceValue F),
      count * 6 ≤ (bytes.drop i).length ∧
      Ixon.getArray Ixon.getConstructor count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ctors { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList constructorListEnum RepConstructor h' ctors.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' cs with
  | zero =>
    cases «IxonDeserialize::get_constructor_list».obs ev with
    | n1 m2 cs12 m43 ev14 he41 hm51 he62 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      subst he62 hm51 he41
      have ext := Aiur.Library.List.allocNil_extends constructorListEnum h
      refine ⟨ext, #[], 0, (Aiur.Library.List.allocNil constructorListEnum h).1, stream,
        by omega, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep constructorListEnum RepConstructor h,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    | n0 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    cases «IxonDeserialize::get_constructor_list».obs ev with
    | n1 m2 _ _ ev14 _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp [Nat.succ_ne_zero] at hiz
    | n0 m2 cs12 m70 cs80 x_ctor x_s m105 cs115 v119 m128 cs136 x_rest x_s2 m166
        ev14 ev82 ev138 ev117 he164 hm174 he201 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨ext1, ct, n1, ctVal, restPtr1, _, hlen1, hok1, heq1, ctRep, hrep1⟩ :=
        get_constructor_spec rep ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl⟩
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailCtors, n2, tailPtr, restPtr2, hlen2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl⟩
      subst he201 hm174 he164
      have ext3 := Aiur.Library.List.allocCons_extends constructorListEnum ctVal tailPtr m105
      refine ⟨(ext1.trans ext2).trans ext3, #[ct] ++ tailCtors, n1 + n2,
        (Aiur.Library.List.allocCons constructorListEnum ctVal tailPtr m105).1, restPtr2,
        by omega, ?_, rfl, ?_,
        by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · simpa using Aiur.Library.List.allocCons_rep constructorListEnum repConstructor_heapMono₂
          (ctRep.mono ext2) tailRep

/-- `IxonDeserialize::get_inductive` at offset `i` refines `Ixon.getInductive`. -/
theorem get_inductive_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_inductive" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ind : Ixon.Inductive) (n : Nat) (indVal restPtr : SourceValue F),
      Ixon.getInductive { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ind { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [indVal, restPtr] ∧
      RepInductive h' ind indVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_inductive».obs ev with
  | run m2 cs12 x_bools_byte x_s v36 m37 cs47 v58 m59 cs69 v80
      m93 cs103 x_lvls x_s2 m128 cs138 x_params x_s3 m163 cs173 x_indices x_s4
      m198 cs208 x_typ x_s5 m233 cs243 x_ctors_len x_s6 m268 cs278 x_ctors x_s7
      ev14 ev49 ev71 pr90 ev105 ev140 ev175 ev210 ev245 ev280 he314 he379 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hb2, _, rfl⟩ := assertWireBool_refines b.toNat_lt ev49.erase
    obtain ⟨_, hdrop1, _⟩ := getU8_of_drop_cons hcons
    have hbeq : decide (b.toNat = 1) = (b == 1) := by
      rcases h : b.toNat with _ | _ | n
      · have hb0 : b = 0 := UInt8.ext h; subst hb0; rfl
      · have hb1 : b = 1 := UInt8.ext h; subst hb1; rfl
      · omega
    have hbool : Ixon.Serialize.get (α := Bool) { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok (b == 1) { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
      rw [← hbeq]; exact getBool_of_drop_cons hcons hb2
    rw [← hdrop1] at hrep0
    obtain ⟨hbits, rfl⟩ := u8BitDecomposition_refines b.toNat_lt ev71.erase
    subst hbits
    simp only [projectValue, List.getElem?_cons_zero, Except.ok.injEq] at pr90
    subst pr90
    have hbf : (.field ((b.toNat % 2 : Nat) : F) : SourceValue F) = repBoolField (b == 1) := by
      rcases h : b.toNat with _ | _ | n
      · have hb0 : b = 0 := UInt8.ext h; subst hb0; rfl
      · have hb1 : b = 1 := UInt8.ext h; subst hb1; rfl
      · omega
    obtain ⟨rfl, tLvls, n1, restPtr1, hok1, _, hrep1, heq1⟩ := getTag0_refines_at hrep0 ev105.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1; rcases heq1 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tParams, n2, restPtr2, hok2, _, hrep2, heq2⟩ := getTag0_refines_at hrep1 ev140.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tIndices, n3, restPtr3, hok3, _, hrep3, heq3⟩ := getTag0_refines_at hrep2 ev175.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq3; rcases heq3 with ⟨rfl, rfl⟩
    obtain ⟨ext4, typ, n4, typPtr, restPtr4, _, _, hok4, heq4, typRep, hrep4⟩ :=
      getExpr_refines_at hrep3 ev210.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq4; rcases heq4 with ⟨rfl, rfl⟩
    obtain ⟨rfl, tCtors, n5, restPtr5, hok5, _, hctors_lt, hrep5, heq5⟩ :=
      getVecLen_refines_at hrep4 ev245.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq5; rcases heq5 with ⟨rfl, rfl⟩
    obtain ⟨ext6, ctors, n6, ctorsPtr, restPtr6, hlen_ctors, hok6, heq6, ctorsRep, hrep6⟩ :=
      get_constructor_list_spec tCtors.value.toNat hctors_lt hrep5 ev280
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq6; rcases heq6 with ⟨rfl, rfl⟩
    subst he379 he314
    have hchk : Ixon.checkCount tCtors.value.toNat.toUInt64 6
        { idx := i + 1 + n1 + n2 + n3 + n4 + n5, bytes := ⟨bytes.toArray⟩ } =
        .ok () { idx := i + 1 + n1 + n2 + n3 + n4 + n5, bytes := ⟨bytes.toArray⟩ } := by
      apply checkCount_ok
      simpa [UInt64.ofNat_toNat] using hlen_ctors
    let ind : Ixon.Inductive := ⟨b == 1, tLvls.value, tParams.value, tIndices.value, typ, ctors⟩
    refine ⟨ext4.trans ext6, ind, 1 + n1 + n2 + n3 + n4 + n5 + n6, _, restPtr6, ?_, rfl,
      ⟨typPtr, ctorsPtr, by rw [hbf], typRep.mono ext6, ctorsRep⟩,
      by simp only [Nat.add_assoc] at hrep6 ⊢; exact hrep6⟩
    have hloop :
      (do
        let mut cs : Array Ixon.Constructor := #[]
        for _ in [0:tCtors.value.toNat] do
          cs := cs.push (← Ixon.getConstructor)
        return (⟨b == 1, tLvls.value, tParams.value, tIndices.value, typ, cs⟩ : Ixon.Inductive)) =
      (do
        let cs ← Ixon.getArray Ixon.getConstructor tCtors.value.toNat
        return (⟨b == 1, tLvls.value, tParams.value, tIndices.value, typ, cs⟩ : Ixon.Inductive)) := by
      simp [Ixon.getArray]
    unfold Ixon.getInductive
    simp only [bind, EStateM.bind, hbool, hok1, hok2, hok3, hok4, hok5, hchk]
    rw [hloop]
    simp [bind, EStateM.bind, hok6, pure, EStateM.pure, Nat.add_assoc]

/-- `IxonDeserialize::get_mut_const` at offset `i` refines `Ixon.getMutConst`. -/
theorem get_mut_const_spec {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_mut_const" [stream] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (mc : Ixon.MutConst) (n : Nat) (mcVal restPtr : SourceValue F),
      Ixon.getMutConst { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok mc { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [mcVal, restPtr] ∧
      RepMutConst h' mc mcVal ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  cases «IxonDeserialize::get_mut_const».obs ev with
  | n0 m2 cs12 x_tag x_s m37 cs48 m64 cs74 x_defn x_s2 ev14 ev50 ev76 he102 he127 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0; rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    obtain ⟨heq_b, rfl⟩ := u8ToField_refines ev50.erase
    have hb0 : b = 0 := UInt8.ext ((natCast_eq_zero_iff b.toNat_lt).mp (Value.field.inj heq_b).symm)
    subst hb0
    obtain ⟨ext2, d, n2, dVal, restPtr2, _, hok2, heq2, dRep, hrep2⟩ := get_definition_spec hrep0 ev76
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    subst he127 he102
    refine ⟨ext2, .defn d, 1 + n2, _, restPtr2, ?_, rfl, ⟨dVal, rfl, dRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getMutConst
    simp [bind, EStateM.bind, hu8, Functor.map, EStateM.map, hok2, Nat.add_assoc]
  | n1 m2 cs12 x_tag x_s m37 cs48 m135 cs145 x_indc x_s2 ev14 ev50 ev147 he173 he198 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0; rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    obtain ⟨heq_b, rfl⟩ := u8ToField_refines ev50.erase
    have hb1 : b = 1 := UInt8.ext ((natCast_eq_one_iff b.toNat_lt).mp (Value.field.inj heq_b).symm)
    subst hb1
    obtain ⟨ext2, ind, n2, indVal, restPtr2, hok2, heq2, indRep, hrep2⟩ := get_inductive_spec hrep0 ev147
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    subst he198 he173
    refine ⟨ext2, .indc ind, 1 + n2, _, restPtr2, ?_, rfl, ⟨indVal, rfl, indRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getMutConst
    simp [bind, EStateM.bind, hu8, Functor.map, EStateM.map, hok2, Nat.add_assoc]
  | n2 m2 cs12 x_tag x_s m37 cs48 m206 cs216 x_recr x_s2 ev14 ev50 ev218 he244 he269 _ =>
    obtain ⟨rfl, b, rest0, restPtr0, hcons, hrep0, heq0⟩ := readByte_refines rep ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq0; rcases heq0 with ⟨rfl, rfl⟩
    obtain ⟨hu8, hdrop1, _⟩ := getU8_of_drop_cons hcons
    rw [← hdrop1] at hrep0
    obtain ⟨heq_b, rfl⟩ := u8ToField_refines ev50.erase
    have hb2 : b = 2 := UInt8.ext ((natCast_eq_ofNat_iff (n := 2) b.toNat_lt (by omega)).mp (Value.field.inj heq_b).symm)
    subst hb2
    obtain ⟨ext2, rc, n2, rcVal, restPtr2, hok2, heq2, rcRep, hrep2⟩ := get_recursor_spec hrep0 ev218
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2; rcases heq2 with ⟨rfl, rfl⟩
    subst he269 he244
    refine ⟨ext2, .recr rc, 1 + n2, _, restPtr2, ?_, rfl, ⟨rcVal, rfl, rcRep⟩,
      by rw [← Nat.add_assoc]; exact hrep2⟩
    unfold Ixon.getMutConst
    simp [bind, EStateM.bind, hu8, Functor.map, EStateM.map, hok2, Nat.add_assoc]

/-- `IxonDeserialize::get_mut_const_list` at offset `i` refines
`Ixon.getArray Ixon.getMutConst count`. -/
theorem get_mut_const_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {stream r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (rep : Aiur.Library.Bytes.RepByteStream byteStreamEnum h (bytes.drop i) stream)
    (ev : ObsFn W "IxonDeserialize::get_mut_const_list" [stream, u64Value count] h r h' cs) :
    Heap.Extends h h' ∧
    ∃ (ms : Array Ixon.MutConst) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getArray Ixon.getMutConst count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ms { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      Aiur.Library.List.RepList mutConstListEnum RepMutConst h' ms.toList listPtr ∧
      Aiur.Library.Bytes.RepByteStream byteStreamEnum h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i stream r h h' cs with
  | zero =>
    cases «IxonDeserialize::get_mut_const_list».obs ev with
    | n1 m2 cs12 m43 ev14 he41 hm51 he62 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      subst he62 hm51 he41
      have ext := Aiur.Library.List.allocNil_extends mutConstListEnum h
      refine ⟨ext, #[], 0, (Aiur.Library.List.allocNil mutConstListEnum h).1, stream,
        by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure], rfl,
        Aiur.Library.List.allocNil_rep mutConstListEnum RepMutConst h,
        Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext rep⟩
    | n0 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    cases «IxonDeserialize::get_mut_const_list».obs ev with
    | n1 m2 _ _ ev14 _ _ _ _ =>
      obtain ⟨hiz, _⟩ := u64IsZero_refines hcount ev14.erase
      simp [Nat.succ_ne_zero] at hiz
    | n0 m2 cs12 m70 cs80 x_mc x_s m105 cs115 v119 m128 cs136 x_rest x_s2 m166
        ev14 ev82 ev138 ev117 he164 hm174 he201 _ =>
      obtain ⟨_, rfl⟩ := u64IsZero_refines hcount ev14.erase
      obtain ⟨ext1, mc, n1, mcVal, restPtr1, hok1, heq1, mcRep, hrep1⟩ :=
        get_mut_const_spec rep ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq1
      rcases heq1 with ⟨rfl, rfl⟩
      obtain ⟨hsp, rfl⟩ := u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp; subst hsp
      obtain ⟨ext2, tailMs, n2, tailPtr, restPtr2, hok2, heq2, tailRep, hrep2⟩ :=
        ih (by omega) hrep1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at heq2
      rcases heq2 with ⟨rfl, rfl⟩
      subst he201 hm174 he164
      have ext3 := Aiur.Library.List.allocCons_extends mutConstListEnum mcVal tailPtr m105
      refine ⟨(ext1.trans ext2).trans ext3, #[mc] ++ tailMs, n1 + n2,
        (Aiur.Library.List.allocCons mutConstListEnum mcVal tailPtr m105).1, restPtr2,
        ?_, rfl, ?_,
        by rw [← Nat.add_assoc]; exact Aiur.Library.Bytes.repByteStream_heapMono₂ byteStreamEnum ext3 hrep2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure, Nat.add_assoc]
      · simpa using Aiur.Library.List.allocCons_rep mutConstListEnum repMutConst_heapMono₂
          (mcRep.mono ext2) tailRep

end IxVM.Refinement.L1
