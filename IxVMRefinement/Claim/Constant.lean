import IxVMRefinement.Core.Seams
import IxVMRefinement.L1.Hashed
import IxVMRefinement.Obs.IxonDeserialize
import Ix.IxVM.Refinement.DeserializeBinders
import IxC.Ixon.Verify.ConstantBounds
import IxC.Ixon.Verify.ConstantTables

/-! # Constant deserialization refinement for L6 (`IxonDeserialize::get_constant`)

Connects `IxonDeserialize::get_constant` and `Ingress::load_verified_constant` to `Ixon.getConstant`
and `Ixon.deConstant`, tracking the exact heap representation (`RepConstant`) consumed by
`KernelClaim::const_idxs_of`, `KernelClaim::record_unsafe`, and `KernelClaim::env_walk` /
`run_check_transitive`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM (F)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

/-! ## Heap representation of `Ixon.Constant` -/

/-- Field representation of a `Bool` (`0` or `1`). -/
def RepBool (b : Bool) (v : SourceValue F) : Prop :=
  v = .field (if b then 1 else 0)

/-- Representation of `Ix.DefKind` (`Ixon::DefKind`). -/
def RepDefKind : Ix.DefKind → SourceValue F → Prop
  | .defn, v => v = .construct "Ixon::DefKind" "Definition" []
  | .opaq, v => v = .construct "Ixon::DefKind" "Opaque" []
  | .thm, v => v = .construct "Ixon::DefKind" "Theorem" []

/-- Representation of `Ix.DefinitionSafety` (`Ixon::DefinitionSafety`). -/
def RepDefinitionSafety : Ix.DefinitionSafety → SourceValue F → Prop
  | .unsaf, v => v = .construct "Ixon::DefinitionSafety" "Unsafe" []
  | .safe, v => v = .construct "Ixon::DefinitionSafety" "Safe" []
  | .part, v => v = .construct "Ixon::DefinitionSafety" "Partial" []

/-- Field representation of `Ixon.DefAsserts` (its 4-bit code). -/
def RepDefAsserts (a : Ixon.DefAsserts) (v : SourceValue F) : Prop :=
  v = .field ((a.toCode.toNat : Nat) : F)

/-- Representation of `Ix.QuotKind` (`Ixon::QuotKind`). -/
def RepQuotKind : Ix.QuotKind → SourceValue F → Prop
  | .type, v => v = .construct "Ixon::QuotKind" "Typ" []
  | .ctor, v => v = .construct "Ixon::QuotKind" "Ctor" []
  | .lift, v => v = .construct "Ixon::QuotKind" "Lift" []
  | .ind, v => v = .construct "Ixon::QuotKind" "Ind" []

/-- Field representation of `Ixon.FieldMode` (`0` inherited, `1` shared). -/
def RepFieldMode : Ixon.FieldMode → SourceValue F → Prop
  | .inherited, v => v = .field 0
  | .shared, v => v = .field 1

theorem repFieldMode_heapMono₂ : HeapMono₂ (fun _ : Heap F => RepFieldMode) :=
  fun _ _ _ _ _ h => h

/-- Representation of `Ixon.Definition` (`Ixon::Definition::Mk`). -/
def RepDefinition (h : Heap F) (d : Ixon.Definition) (v : SourceValue F) : Prop :=
  ∃ kVal sVal aVal tPtr vPtr,
    v = .construct "Ixon::Definition" "Mk"
      [kVal, sVal, aVal, TagN.u64Value d.lvls.toNat, tPtr, vPtr] ∧
    RepDefKind d.kind kVal ∧
    RepDefinitionSafety d.safety sVal ∧
    RepDefAsserts d.asserts aVal ∧
    Deserialize.RepExpr h d.typ tPtr ∧
    Deserialize.RepExpr h d.value vPtr

theorem RepDefinition.mono {h₁ h₂ : Heap F} {d : Ixon.Definition} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepDefinition h₁ d v) : RepDefinition h₂ d v := by
  obtain ⟨kVal, sVal, aVal, tPtr, vPtr, hv, hk, hs, ha, ht, hval⟩ := r
  exact ⟨kVal, sVal, aVal, tPtr, vPtr, hv, hk, hs, ha, ht.mono ext, hval.mono ext⟩

/-- Representation of `Ixon.RecursorRule` (`Ixon::RecursorRule::Mk`). -/
def RepRecursorRule (h : Heap F) (rl : Ixon.RecursorRule) (v : SourceValue F) : Prop :=
  ∃ rhsPtr,
    v = .construct "Ixon::RecursorRule" "Mk" [TagN.u64Value rl.fields.toNat, rhsPtr] ∧
    Deserialize.RepExpr h rl.rhs rhsPtr

theorem RepRecursorRule.mono {h₁ h₂ : Heap F} {rl : Ixon.RecursorRule} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepRecursorRule h₁ rl v) : RepRecursorRule h₂ rl v := by
  obtain ⟨rhsPtr, hv, hrhs⟩ := r
  exact ⟨rhsPtr, hv, hrhs.mono ext⟩

theorem repRecursorRule_heapMono₂ : HeapMono₂ RepRecursorRule :=
  fun _ _ _ _ ext r => r.mono ext

/-- Representation of `Ixon.Recursor` (`Ixon::Recursor::Mk`). -/
def RepRecursor (h : Heap F) (r : Ixon.Recursor) (v : SourceValue F) : Prop :=
  ∃ kVal uVal tPtr rulesPtr,
    v = .construct "Ixon::Recursor" "Mk"
      [kVal, uVal, TagN.u64Value r.lvls.toNat, TagN.u64Value r.params.toNat,
       TagN.u64Value r.indices.toNat, TagN.u64Value r.motives.toNat,
       TagN.u64Value r.minors.toNat, tPtr, rulesPtr] ∧
    RepBool r.k kVal ∧
    RepBool r.isUnsafe uVal ∧
    Deserialize.RepExpr h r.typ tPtr ∧
    RepList Obs.Names.«Lists::Node<Ixon::RecursorRule>» RepRecursorRule h r.rules.toList rulesPtr

theorem RepRecursor.mono {h₁ h₂ : Heap F} {rc : Ixon.Recursor} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepRecursor h₁ rc v) : RepRecursor h₂ rc v := by
  obtain ⟨kVal, uVal, tPtr, rulesPtr, hv, hk, hu, ht, hrules⟩ := r
  exact ⟨kVal, uVal, tPtr, rulesPtr, hv, hk, hu, ht.mono ext,
    repList_heapMono₂ _ repRecursorRule_heapMono₂ ext hrules⟩

/-- Representation of `Ixon.Axiom` (`Ixon::Axiom::Mk`). -/
def RepAxiom (h : Heap F) (a : Ixon.Axiom) (v : SourceValue F) : Prop :=
  ∃ uVal tPtr,
    v = .construct "Ixon::Axiom" "Mk" [uVal, TagN.u64Value a.lvls.toNat, tPtr] ∧
    RepBool a.isUnsafe uVal ∧
    Deserialize.RepExpr h a.typ tPtr

theorem RepAxiom.mono {h₁ h₂ : Heap F} {a : Ixon.Axiom} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepAxiom h₁ a v) : RepAxiom h₂ a v := by
  obtain ⟨uVal, tPtr, hv, hu, ht⟩ := r
  exact ⟨uVal, tPtr, hv, hu, ht.mono ext⟩

/-- Representation of `Ixon.Quotient` (`Ixon::Quotient::Mk`). -/
def RepQuotient (h : Heap F) (q : Ixon.Quotient) (v : SourceValue F) : Prop :=
  ∃ kVal tPtr,
    v = .construct "Ixon::Quotient" "Mk" [kVal, TagN.u64Value q.lvls.toNat, tPtr] ∧
    RepQuotKind q.kind kVal ∧
    Deserialize.RepExpr h q.typ tPtr

theorem RepQuotient.mono {h₁ h₂ : Heap F} {q : Ixon.Quotient} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepQuotient h₁ q v) : RepQuotient h₂ q v := by
  obtain ⟨kVal, tPtr, hv, hk, ht⟩ := r
  exact ⟨kVal, tPtr, hv, hk, ht.mono ext⟩

/-- Representation of `Ixon.Constructor` (`Ixon::Constructor::Mk`). -/
def RepConstructor (h : Heap F) (c : Ixon.Constructor) (v : SourceValue F) : Prop :=
  ∃ uVal modesPtr tPtr,
    v = .construct "Ixon::Constructor" "Mk"
      [uVal, TagN.u64Value c.lvls.toNat, TagN.u64Value c.cidx.toNat,
       TagN.u64Value c.params.toNat, TagN.u64Value c.fields.toNat, modesPtr, tPtr] ∧
    RepBool c.isUnsafe uVal ∧
    RepList Obs.Names.«Lists::Node<Field>» (fun _ => RepFieldMode) h
      c.fieldModes.toArray.toList modesPtr ∧
    Deserialize.RepExpr h c.typ tPtr

theorem RepConstructor.mono {h₁ h₂ : Heap F} {c : Ixon.Constructor} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepConstructor h₁ c v) : RepConstructor h₂ c v := by
  obtain ⟨uVal, modesPtr, tPtr, hv, hu, hm, ht⟩ := r
  exact ⟨uVal, modesPtr, tPtr, hv, hu,
    repList_heapMono₂ _ repFieldMode_heapMono₂ ext hm, ht.mono ext⟩

theorem repConstructor_heapMono₂ : HeapMono₂ RepConstructor :=
  fun _ _ _ _ ext r => r.mono ext

/-- Representation of `Ixon.Inductive` (`Ixon::Inductive::Mk`). -/
def RepInductive (h : Heap F) (ind : Ixon.Inductive) (v : SourceValue F) : Prop :=
  ∃ uVal tPtr ctorsPtr,
    v = .construct "Ixon::Inductive" "Mk"
      [uVal, TagN.u64Value ind.lvls.toNat, TagN.u64Value ind.params.toNat,
       TagN.u64Value ind.indices.toNat, tPtr, ctorsPtr] ∧
    RepBool ind.isUnsafe uVal ∧
    Deserialize.RepExpr h ind.typ tPtr ∧
    RepList Obs.Names.«Lists::Node<Ixon::Constructor>» RepConstructor h ind.ctors.toList ctorsPtr

theorem RepInductive.mono {h₁ h₂ : Heap F} {ind : Ixon.Inductive} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepInductive h₁ ind v) : RepInductive h₂ ind v := by
  obtain ⟨uVal, tPtr, ctorsPtr, hv, hu, ht, hctors⟩ := r
  exact ⟨uVal, tPtr, ctorsPtr, hv, hu, ht.mono ext,
    repList_heapMono₂ _ repConstructor_heapMono₂ ext hctors⟩

/-- Representation of `Ixon.InductiveProj` (`Ixon::InductiveProj::Mk`). -/
def RepInductiveProj (h : Heap F) (p : Ixon.InductiveProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::InductiveProj" "Mk" [TagN.u64Value p.idx.toNat, blkPtr] ∧
    S0.addr h blkPtr p.block

theorem RepInductiveProj.mono {h₁ h₂ : Heap F} {p : Ixon.InductiveProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepInductiveProj h₁ p v) : RepInductiveProj h₂ p v := by
  obtain ⟨blkPtr, hv, hb⟩ := r
  exact ⟨blkPtr, hv, S0.addr_mono ext hb⟩

/-- Representation of `Ixon.ConstructorProj` (`Ixon::ConstructorProj::Mk`). -/
def RepConstructorProj (h : Heap F) (p : Ixon.ConstructorProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::ConstructorProj" "Mk"
      [TagN.u64Value p.idx.toNat, TagN.u64Value p.cidx.toNat, blkPtr] ∧
    S0.addr h blkPtr p.block

theorem RepConstructorProj.mono {h₁ h₂ : Heap F} {p : Ixon.ConstructorProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepConstructorProj h₁ p v) : RepConstructorProj h₂ p v := by
  obtain ⟨blkPtr, hv, hb⟩ := r
  exact ⟨blkPtr, hv, S0.addr_mono ext hb⟩

/-- Representation of `Ixon.RecursorProj` (`Ixon::RecursorProj::Mk`). -/
def RepRecursorProj (h : Heap F) (p : Ixon.RecursorProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::RecursorProj" "Mk" [TagN.u64Value p.idx.toNat, blkPtr] ∧
    S0.addr h blkPtr p.block

theorem RepRecursorProj.mono {h₁ h₂ : Heap F} {p : Ixon.RecursorProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepRecursorProj h₁ p v) : RepRecursorProj h₂ p v := by
  obtain ⟨blkPtr, hv, hb⟩ := r
  exact ⟨blkPtr, hv, S0.addr_mono ext hb⟩

/-- Representation of `Ixon.DefinitionProj` (`Ixon::DefinitionProj::Mk`). -/
def RepDefinitionProj (h : Heap F) (p : Ixon.DefinitionProj) (v : SourceValue F) : Prop :=
  ∃ blkPtr,
    v = .construct "Ixon::DefinitionProj" "Mk" [TagN.u64Value p.idx.toNat, blkPtr] ∧
    S0.addr h blkPtr p.block

theorem RepDefinitionProj.mono {h₁ h₂ : Heap F} {p : Ixon.DefinitionProj} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepDefinitionProj h₁ p v) : RepDefinitionProj h₂ p v := by
  obtain ⟨blkPtr, hv, hb⟩ := r
  exact ⟨blkPtr, hv, S0.addr_mono ext hb⟩

/-- Representation of `Ixon.MutConst` (`Ixon::MutConst`). -/
def RepMutConst (h : Heap F) : Ixon.MutConst → SourceValue F → Prop
  | .defn d, v => ∃ dv, v = .construct "Ixon::MutConst" "Defn" [dv] ∧ RepDefinition h d dv
  | .indc i, v => ∃ iv, v = .construct "Ixon::MutConst" "Indc" [iv] ∧ RepInductive h i iv
  | .recr r, v => ∃ rv, v = .construct "Ixon::MutConst" "Recr" [rv] ∧ RepRecursor h r rv

theorem RepMutConst.mono {h₁ h₂ : Heap F} {mc : Ixon.MutConst} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepMutConst h₁ mc v) : RepMutConst h₂ mc v := by
  cases mc with
  | defn d => obtain ⟨dv, hv, hd⟩ := r; exact ⟨dv, hv, hd.mono ext⟩
  | indc i => obtain ⟨iv, hv, hi⟩ := r; exact ⟨iv, hv, hi.mono ext⟩
  | recr rc => obtain ⟨rv, hv, hrc⟩ := r; exact ⟨rv, hv, hrc.mono ext⟩

theorem repMutConst_heapMono₂ : HeapMono₂ RepMutConst :=
  fun _ _ _ _ ext r => r.mono ext

/-- Representation of `Ixon.ConstantInfo` (`Ixon::ConstantInfo`). -/
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
      ∃ mv, v = .construct "Ixon::ConstantInfo" "Muts" [mv] ∧
        RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h ms.toList mv

theorem RepConstantInfo.mono {h₁ h₂ : Heap F} {ci : Ixon.ConstantInfo} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepConstantInfo h₁ ci v) : RepConstantInfo h₂ ci v := by
  cases ci with
  | defn d => obtain ⟨dv, hv, hd⟩ := r; exact ⟨dv, hv, hd.mono ext⟩
  | recr rc => obtain ⟨rv, hv, hrc⟩ := r; exact ⟨rv, hv, hrc.mono ext⟩
  | axio a => obtain ⟨av, hv, ha⟩ := r; exact ⟨av, hv, ha.mono ext⟩
  | quot q => obtain ⟨qv, hv, hq⟩ := r; exact ⟨qv, hv, hq.mono ext⟩
  | cPrj p => obtain ⟨pv, hv, hp⟩ := r; exact ⟨pv, hv, hp.mono ext⟩
  | rPrj p => obtain ⟨pv, hv, hp⟩ := r; exact ⟨pv, hv, hp.mono ext⟩
  | iPrj p => obtain ⟨pv, hv, hp⟩ := r; exact ⟨pv, hv, hp.mono ext⟩
  | dPrj p => obtain ⟨pv, hv, hp⟩ := r; exact ⟨pv, hv, hp.mono ext⟩
  | muts ms =>
      obtain ⟨mv, hv, hms⟩ := r
      exact ⟨mv, hv, repList_heapMono₂ _ repMutConst_heapMono₂ ext hms⟩

/-- Address-reference element relation `fun h a av => S0.addr h av a` and its heap monotonicity. -/
abbrev RepAddrElem (h : Heap F) (a : _root_.Address) (av : SourceValue F) : Prop :=
  S0.addr h av a

theorem repAddrElem_heapMono₂ : HeapMono₂ RepAddrElem :=
  fun _ _ _ _ ext r => S0.addr_mono ext r

/-- Representation of `Ixon.Constant` (`Ixon::Constant::Mk`). -/
def RepConstant (h : Heap F) (c : Ixon.Constant) (v : SourceValue F) : Prop :=
  ∃ infoVal sharingPtr refsPtr univsPtr bindersPtr,
    v = .construct "Ixon::Constant" "Mk"
      [infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr] ∧
    RepConstantInfo h c.info infoVal ∧
    Deserialize.RepShareVec h c.sharing.toList sharingPtr ∧
    RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h c.refs.toList refsPtr ∧
    RepList Deserialize.univListEnum Deserialize.RepUnivPtr h c.univs.toList univsPtr ∧
    RepList Deserialize.binderBlockListEnum Deserialize.RepBinderBlock h
      c.binders.toList bindersPtr

theorem RepConstant.mono {h₁ h₂ : Heap F} {c : Ixon.Constant} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (r : RepConstant h₁ c v) : RepConstant h₂ c v := by
  obtain ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, hv, hinfo, hsh, hrefs, hunivs, hbinders⟩ := r
  exact ⟨infoVal, sharingPtr, refsPtr, univsPtr, bindersPtr, hv,
    hinfo.mono ext,
    hsh.mono ext,
    repList_heapMono₂ _ repAddrElem_heapMono₂ ext hrefs,
    repList_heapMono₂ _ Deserialize.repUnivPtr_heapMono₂ ext hunivs,
    repList_heapMono₂ _ Deserialize.repBinderBlock_heapMono₂ ext hbinders⟩

/-- Wire-table invariants enforced by `IxonDeserialize::get_constant` (including
`assert_prj_empty_tables`). -/
structure ConstantWireFacts (c : Ixon.Constant) : Prop where
  sharingCount : c.sharing.size < 18446744073709551616
  refsCount : c.refs.size < 18446744073709551616
  univsCount : c.univs.size < 18446744073709551616
  prjEmpty :
    match c.info with
    | .dPrj _ | .iPrj _ | .cPrj _ | .rPrj _ =>
        c.sharing = #[] ∧ c.refs = #[] ∧ c.univs = #[] ∧ c.binders = #[]
    | _ => True

/-! ## Stream, `TagN`, and `getArray` alignment helpers -/

private theorem getTagN0_progress {bytes : List UInt8} {i : Nat}
    {stream r : SourceValue F} {h h' : Heap F}
    (rep : L1.Stream h (bytes.drop i) stream)
    (ev : EvalFn Obs.W "IxonDeserialize::get_tagn0" [stream] h r h') :
    h' = h ∧ ∃ (t : Ixon.TagN) (n : Nat) (restPtr : SourceValue F),
      0 < n ∧
      (bytes.drop (i + n)).length < (bytes.drop i).length ∧
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      t.flag = 0 ∧
      L1.Stream h (bytes.drop (i + n)) restPtr ∧
      r = .tuple [TagN.u64Value t.value.toNat, restPtr] := by
  obtain ⟨rfl, t, n, restPtr, hok0, hflag, hrep, hr⟩ := TagN.getTagN0_refines rep ev
  have hlt := Deserialize.drop_length_lt_of_getTagN hok0
  obtain ⟨hn, _⟩ := Deserialize.getTagN_pos hok0
  rw [List.drop_drop] at hrep hlt
  exact ⟨rfl, t, n, restPtr, hn, hlt, TagN.getTagN_drop hok0, hflag, hrep, hr⟩

private theorem getExprChildren_to_getArray :
    ∀ (count : Nat) {s s' : Ixon.GetState} {xs : List Ixon.Expr},
      Deserialize.getExprChildren count s = .ok xs s' →
      Ixon.getArray Ixon.getExpr count s = .ok xs.toArray s'
  | 0, s, s', xs, h => by
      simp only [Deserialize.getExprChildren, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure]
  | count + 1, s, s', xs, h => by
      simp only [Deserialize.getExprChildren, bind, EStateM.bind] at h
      cases h1 : Ixon.getExpr s with
      | error e st => simp [h1] at h
      | ok head s1 =>
          simp only [h1] at h
          cases h2 : Deserialize.getExprChildren count s1 with
          | error e st => simp [h2] at h
          | ok tail s2 =>
              simp only [h2, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have ih := getExprChildren_to_getArray count h2
              rw [Ixon.Verify.BoundedConstant.getArray_succ]
              simp only [bind, EStateM.bind, h1, ih, pure, EStateM.pure, EStateM.Result.ok.injEq,
                and_true]
              rfl

private theorem getUnivChildren_to_getArray :
    ∀ (count : Nat) {s s' : Ixon.GetState} {xs : List Ixon.Univ},
      Deserialize.getUnivChildren count s = .ok xs s' →
      Ixon.getArray Ixon.getUniv count s = .ok xs.toArray s'
  | 0, s, s', xs, h => by
      simp only [Deserialize.getUnivChildren, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure]
  | count + 1, s, s', xs, h => by
      simp only [Deserialize.getUnivChildren, bind, EStateM.bind] at h
      cases h1 : Ixon.getUniv s with
      | error e st => simp [h1] at h
      | ok head s1 =>
          simp only [h1] at h
          cases h2 : Deserialize.getUnivChildren count s1 with
          | error e st => simp [h2] at h
          | ok tail s2 =>
              simp only [h2, pure, EStateM.pure, EStateM.Result.ok.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have ih := getUnivChildren_to_getArray count h2
              rw [Ixon.Verify.BoundedConstant.getArray_succ]
              simp only [bind, EStateM.bind, h1, ih, pure, EStateM.pure, EStateM.Result.ok.injEq,
                and_true]
              rfl

private theorem uint8_lt4_cases (b : UInt8) (h : b.toNat < 4) :
    b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by
  have hb := b.toNat_lt
  rcases (by omega : b.toNat = 0 ∨ b.toNat = 1 ∨ b.toNat = 2 ∨ b.toNat = 3) with h0 | h1 | h2 | h3
  · exact .inl (UInt8.ext h0)
  · exact .inr (.inl (UInt8.ext h1))
  · exact .inr (.inr (.inl (UInt8.ext h2)))
  · exact .inr (.inr (.inr (UInt8.ext h3)))

private theorem uint8_lt2_cases (b : UInt8) (h : b.toNat < 2) :
    b = 0 ∨ b = 1 := by
  rcases (by omega : b.toNat = 0 ∨ b.toNat = 1) with h0 | h1
  · exact .inl (UInt8.ext h0)
  · exact .inr (UInt8.ext h1)

private theorem byteArray_eq_of_toList {x y : ByteArray} (h : x.data.toList = y.data.toList) :
    x = y := by
  cases x with
  | mk dx =>
    cases y with
    | mk dy =>
      dsimp only at h
      congr 1
      exact Array.ext' h

private theorem getAddress_of_drop {bytes : List UInt8} {i : Nat}
    (hlen : 32 ≤ (bytes.drop i).length) :
    (Ixon.Serialize.get : Ixon.GetM _root_.Address) { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok (ixAddr (Deserialize.takeAddress (bytes.drop i) hlen))
        { idx := i + 32, bytes := ⟨bytes.toArray⟩ } := by
  have hlen' : 32 ≤ bytes.length - i := by rw [List.length_drop] at hlen; exact hlen
  have hi_le : i ≤ bytes.length := by omega
  have hsz : i + 32 ≤ (ByteArray.mk bytes.toArray).size := by
    change i + 32 ≤ bytes.toArray.size
    rw [List.size_toArray]
    omega
  let before : ByteArray := ⟨(bytes.take i).toArray⟩
  let chunk : ByteArray := ⟨((bytes.drop i).take 32).toArray⟩
  let after : ByteArray := ⟨((bytes.drop i).drop 32).toArray⟩
  have hsplit : (⟨bytes.toArray⟩ : ByteArray) = before ++ chunk ++ after := by
    apply byteArray_eq_of_toList
    simp only [before, chunk, after, ByteArray.data_append, Array.toList_append,
      List.toList_toArray]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  have hbef_sz : before.size = i := by
    change (bytes.take i).toArray.size = i
    rw [List.size_toArray, List.length_take, Nat.min_eq_left hi_le]
  have hchk_sz : chunk.size = 32 := by
    change ((bytes.drop i).take 32).toArray.size = 32
    rw [List.size_toArray, List.length_take, List.length_drop, Nat.min_eq_left hlen']
  have hext : (⟨bytes.toArray⟩ : ByteArray).extract i (i + 32) = chunk := by
    rw [hsplit, ← hbef_sz, ← hchk_sz]
    exact Ixon.Verify.Codec.ConstantTables.middle_extract before chunk after
  change (Address.mk <$> Ixon.getBytes 32) { idx := i, bytes := ⟨bytes.toArray⟩ } = _
  simp only [Functor.map, EStateM.map, Ixon.getBytes, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, set, EStateM.set, pure, EStateM.pure, hsz, ↓reduceIte, hext]
  rfl

/-! ## Flag byte unpacking: `unpack_def_asserts` and `unpack_def_kind_safety` -/

private theorem evalBinOp_mul_natCast (a b : Nat) :
    (evalBinOp .mul (.field (a : F)) (.field (b : F)) : Except String (SourceValue F)) =
      .ok (.field ((a * b : Nat) : F)) := by
  simp [evalBinOp, Nat.cast_mul]

private theorem evalBinOp_add_natCast (a b : Nat) :
    (evalBinOp .add (.field (a : F)) (.field (b : F)) : Except String (SourceValue F)) =
      .ok (.field ((a + b : Nat) : F)) := by
  simp [evalBinOp, Nat.cast_add]

private theorem unpack_def_asserts_arith {b : UInt8} {k : Nat}
    {v104 v129 x137 y138 y146 x181 y182 x189 y190 y198 : SourceValue F}
    (hk_lt : k < 16)
    (heq92 : (.field ((b.toNat / 128 % 2 : Nat) : F) : SourceValue F) = .field 0)
    (op119 : evalBinOp .mul (.field ((b.toNat / 16 % 2 : Nat) : F))
      (.field ((b.toNat / 32 % 2 : Nat) : F)) = .ok v104)
    (heq128 : v104 = .field 0)
    (op161 : evalBinOp .mul (.field 2) (.field ((b.toNat / 32 % 2 : Nat) : F)) = .ok y146)
    (op152 : evalBinOp .add (.field ((b.toNat / 16 % 2 : Nat) : F)) y146 = .ok x137)
    (op170 : evalBinOp .mul (.field 4) (.field ((b.toNat / 64 % 2 : Nat) : F)) = .ok y138)
    (op144 : evalBinOp .add x137 y138 = .ok v129)
    (op213 : evalBinOp .mul (.field 2) (.field ((b.toNat / 2 % 2 : Nat) : F)) = .ok y198)
    (op204 : evalBinOp .add (.field ((b.toNat % 2 : Nat) : F)) y198 = .ok x189)
    (op222 : evalBinOp .mul (.field 4) (.field ((b.toNat / 4 % 2 : Nat) : F)) = .ok y190)
    (op196 : evalBinOp .add x189 y190 = .ok x181)
    (op231 : evalBinOp .mul (.field 8) (.field ((b.toNat / 8 % 2 : Nat) : F)) = .ok y182)
    (op188 : evalBinOp .add x181 y182 = .ok (.field (k : F))) :
    ∃ c : Nat,
      (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 5 ∨ c = 6) ∧
      v129 = .field ((c : Nat) : F) ∧
      b = UInt8.ofNat (k + 16 * c) := by
  have hb := b.toNat_lt
  set d0 := b.toNat % 2
  set d1 := b.toNat / 2 % 2
  set d2 := b.toNat / 4 % 2
  set d3 := b.toNat / 8 % 2
  set d4 := b.toNat / 16 % 2
  set d5 := b.toNat / 32 % 2
  set d6 := b.toNat / 64 % 2
  set d7 := b.toNat / 128 % 2
  have hd7 : d7 = 0 := by
    injection heq92 with h7
    exact (Deserialize.natCast_eq_zero_iff (by omega)).mp h7
  rw [evalBinOp_mul_natCast, Except.ok.injEq] at op119
  rw [← op119] at heq128
  have hd45 : d4 * d5 = 0 := by
    injection heq128 with h45
    exact (Deserialize.natCast_eq_zero_iff (by omega)).mp h45
  have hy146 : y146 = .field ((2 * d5 : Nat) : F) := by
    have e := evalBinOp_mul_natCast 2 d5
    simp only [Nat.cast_ofNat] at e
    exact (Except.ok.inj (op161.symm.trans e))
  rw [hy146, evalBinOp_add_natCast, Except.ok.injEq] at op152
  have hy138 : y138 = .field ((4 * d6 : Nat) : F) := by
    have e := evalBinOp_mul_natCast 4 d6
    simp only [Nat.cast_ofNat] at e
    exact (Except.ok.inj (op170.symm.trans e))
  rw [← op152, hy138, evalBinOp_add_natCast, Except.ok.injEq] at op144
  have hy198 : y198 = .field ((2 * d1 : Nat) : F) := by
    have e := evalBinOp_mul_natCast 2 d1
    simp only [Nat.cast_ofNat] at e
    exact (Except.ok.inj (op213.symm.trans e))
  rw [hy198, evalBinOp_add_natCast, Except.ok.injEq] at op204
  have hy190 : y190 = .field ((4 * d2 : Nat) : F) := by
    have e := evalBinOp_mul_natCast 4 d2
    simp only [Nat.cast_ofNat] at e
    exact (Except.ok.inj (op222.symm.trans e))
  rw [← op204, hy190, evalBinOp_add_natCast, Except.ok.injEq] at op196
  have hy182 : y182 = .field ((8 * d3 : Nat) : F) := by
    have e := evalBinOp_mul_natCast 8 d3
    simp only [Nat.cast_ofNat] at e
    exact (Except.ok.inj (op231.symm.trans e))
  rw [← op196, hy182, evalBinOp_add_natCast, Except.ok.injEq] at op188
  have hk_eq : d0 + 2 * d1 + 4 * d2 + 8 * d3 = k := by
    injection op188 with hlo
    have hlo' := (Deserialize.natCast_eq_iff (by omega) (by omega)).mp hlo
    omega
  refine ⟨d4 + 2 * d5 + 4 * d6, by omega, ?_, ?_⟩
  · exact op144.symm
  · apply UInt8.ext
    rw [UInt8.toNat_ofNat']
    omega

theorem unpack_def_asserts_spec {b : UInt8} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::unpack_def_asserts"
      [.field ((b.toNat : Nat) : F)] h r h' calls) :
    h' = h ∧
    ∃ (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (asserts : Ixon.DefAsserts)
      (kVal sVal aVal : SourceValue F),
      (((b >>> 2) &&& 3 > 2) || ((b &&& 3) > 2)) = false ∧
      Ixon.DefAsserts.ofCode? (b >>> 4) = some asserts ∧
      Ixon.unpackDefKindSafety (b &&& 15) = (kind, safety) ∧
      r = .tuple [kVal, sVal, aVal] ∧
      RepDefKind kind kVal ∧
      RepDefinitionSafety safety sVal ∧
      RepDefAsserts asserts aVal := by
  have hb := b.toNat_lt
  rcases Obs.«IxonDeserialize::unpack_def_asserts».obs ev with
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩ |
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩ |
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩ |
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩ |
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩ |
    ⟨m2, cs12, x_b0, x_b1, x_b2, x_b3, x_b4, x_b5, x_b6, x_b7, v104, v129,
      x137, y138, y146, x181, y182, x189, y190, y198,
      ev14, heq92, op119, heq128, op161, op152, op170, op144, op213, op204, op222, op196,
      op231, op188, he_r, he_h, -⟩
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((0 : Nat) : F)) := op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 0) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .defn, .unsaf, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((1 : Nat) : F)) := op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 1) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .defn, .safe, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((2 : Nat) : F)) := by simpa using op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 2) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .defn, .part, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((4 : Nat) : F)) := by simpa using op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 4) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .opaq, .unsaf, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((5 : Nat) : F)) := by simpa using op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 5) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .opaq, .safe, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129
  · obtain ⟨hbts, hm2⟩ := Deserialize.u8BitDecomposition_refines hb ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbts
    rcases hbts with ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩
    rw [hb0] at op204; rw [hb1] at op213; rw [hb2] at op222; rw [hb3] at op231
    rw [hb4] at op119 op152; rw [hb5] at op119 op161; rw [hb6] at op170; rw [hb7] at heq92
    have op188' : evalBinOp .add x181 y182 = .ok (.field ((6 : Nat) : F)) := by simpa using op188
    obtain ⟨c, hc, hv129, hbeq⟩ := unpack_def_asserts_arith (k := 6) (by omega)
      heq92 op119 heq128 op161 op152 op170 op144 op213 op204 op222 op196 op231 op188'
    refine ⟨he_h.trans hm2, .opaq, .part, ?_⟩
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨_, _, _, v129, ?_, rfl, ?_, he_r, rfl, rfl, ?_⟩
    all_goals first | decide | rfl | exact hv129

theorem unpack_def_kind_safety_spec {b : UInt8} {r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::unpack_def_kind_safety"
      [.field ((b.toNat : Nat) : F)] h r h' calls) :
    h' = h ∧
    ∃ (kind : Ix.DefKind) (safety : Ix.DefinitionSafety) (asserts : Ixon.DefAsserts)
      (kVal sVal aVal : SourceValue F),
      (((b >>> 2) &&& 3 > 2) || ((b &&& 3) > 2)) = false ∧
      Ixon.DefAsserts.ofCode? (b >>> 4) = some asserts ∧
      Ixon.unpackDefKindSafety (b &&& 15) = (kind, safety) ∧
      r = .tuple [kVal, sVal, aVal] ∧
      RepDefKind kind kVal ∧
      RepDefinitionSafety safety sVal ∧
      RepDefAsserts asserts aVal := by
  have hb := b.toNat_lt
  rcases Obs.«IxonDeserialize::unpack_def_kind_safety».obs ev with
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨m2, cs13, ev15, he_r, he_h, -⟩ |
    ⟨v1, m2, cs13, cs363, ev15, -, -, -, -, -, -, -, -, -, ev365, -⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 0 := UInt8.ext ((Deserialize.natCast_eq_zero_iff hb).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .defn, .unsaf, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 1 := UInt8.ext ((Deserialize.natCast_eq_one_iff hb).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .defn, .safe, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 2 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .defn, .part, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 4 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .opaq, .unsaf, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 5 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .opaq, .safe, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 6 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .opaq, .part, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 8 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .thm, .unsaf, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 9 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .thm, .safe, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨hv, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    injection hv with hf
    have hbeq : b = 10 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff hb (by omega)).mp hf.symm)
    rw [hbeq]
    exact ⟨he_h.trans hm2, .thm, .part, ⟨.unrestricted, false⟩, _, _, _, by decide, rfl, rfl,
      he_r, rfl, rfl, rfl⟩
  · obtain ⟨_, hm2⟩ := Deserialize.u8ToField_refines ev15.erase
    obtain ⟨hh, rest⟩ := unpack_def_asserts_spec ev365
    exact ⟨hh.trans hm2, rest⟩

/-! ## Leaf payload deserializers -/

theorem get_definition_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_definition" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (d : Ixon.Definition) (n : Nat) (dVal restPtr : SourceValue F),
      Ixon.getDefinition { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok d { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [dVal, restPtr] ∧
      RepDefinition h' d dVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_packed, x_s, m37, cs47, x_kind, x_safety, x_asserts, m77, cs87,
    x_lvls, x_s2, m112, cs122, x_typ, x_s3, m147, cs157, x_value, x_s4,
    ev14, ev49, ev89, ev124, ev159, he185, he250, -⟩ :=
    Obs.«IxonDeserialize::get_definition».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hpacked, hs_eq⟩
  subst x_packed x_s m2
  obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
  rw [← hdrop1] at hs1
  obtain ⟨hm37, kind, safety, asserts, kVal, sVal, aVal, hvalid, hasserts, hunpack, hks_tup,
    hkRep, hsRep, haRep⟩ := unpack_def_kind_safety_spec ev49
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hks_tup
  rcases hks_tup with ⟨rfl, rfl, rfl⟩
  subst m37
  obtain ⟨hm77, lvlsTag, n1, restPtr2, _, _, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev89.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩
  subst m77
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2
  obtain ⟨ext_typ, typ, n2, typPtr, restPtr3, _, _, htyp_ok, htyp_tup, htypRep, hs3⟩ :=
    Deserialize.getExpr_refines_at hs2 ev124.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at htyp_ok hs3
  obtain ⟨ext_val, val, n3, valPtr, restPtr4, _, _, hval_ok, hval_tup, hvalRep, hs4⟩ :=
    Deserialize.getExpr_refines_at hs3 ev159.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hval_tup
  rcases hval_tup with ⟨rfl, rfl⟩
  subst he250
  rw [show i + (1 + n1 + n2) + n3 = i + (1 + n1 + n2 + n3) by omega] at hval_ok hs4
  refine ⟨ext_typ.trans ext_val, ⟨kind, safety, asserts, lvlsTag.value, typ, val⟩,
    1 + n1 + n2 + n3, _, x_s4, ?_, he185,
    ⟨kVal, sVal, aVal, x_typ, x_value, rfl, hkRep, hsRep, haRep,
      htypRep.mono ext_val, hvalRep⟩, hs4⟩
  unfold Ixon.getDefinition
  simp only [bind, EStateM.bind, hb_ok, hvalid, Bool.false_eq_true, ↓reduceIte,
    hasserts, hunpack, hlvls_ok, htyp_ok, hval_ok, pure, EStateM.pure]

theorem get_recursor_rule_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_recursor_rule" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (rl : Ixon.RecursorRule) (n : Nat) (rlVal restPtr : SourceValue F),
      (bytes.drop (i + n)).length + 2 ≤ (bytes.drop i).length ∧
      Ixon.getRecursorRule { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok rl { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [rlVal, restPtr] ∧
      RepRecursorRule h' rl rlVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_fields, x_s, m37, cs47, x_rhs, x_s2, ev14, ev49, he75, he108, -⟩ :=
    Obs.«IxonDeserialize::get_recursor_rule».obs ev
  obtain ⟨hm2, fTag, n1, restPtr1, _, hlt1, hf_ok, _, hs1, hf_tup⟩ :=
    getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hf_tup
  rcases hf_tup with ⟨rfl, rfl⟩
  subst m2
  obtain ⟨ext_rhs, rhs, n2, rhsPtr, restPtr2, _, hlt2, hrhs_ok, hrhs_tup, hrhsRep, hs2⟩ :=
    Deserialize.getExpr_refines_at hs1 ev49.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrhs_tup
  rcases hrhs_tup with ⟨rfl, rfl⟩
  subst he108
  rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hrhs_ok hs2 hlt2
  refine ⟨ext_rhs, ⟨fTag.value, rhs⟩, n1 + n2, _, x_s2, by omega, ?_, he75,
    ⟨x_rhs, rfl, hrhsRep⟩, hs2⟩
  unfold Ixon.getRecursorRule
  simp only [bind, EStateM.bind, hf_ok, hrhs_ok, pure, EStateM.pure]

theorem get_recursor_rule_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_recursor_rule_list"
      [x_stream, TagN.u64Value count] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (rules : Array Ixon.RecursorRule) (n : Nat) (listPtr restPtr : SourceValue F),
      (bytes.drop (i + n)).length + count * 2 ≤ (bytes.drop i).length ∧
      Ixon.getArray Ixon.getRecursorRule count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok rules { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<Ixon::RecursorRule>» RepRecursorRule h' rules.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i x_stream r h h' calls with
  | zero =>
    rcases Obs.«IxonDeserialize::get_recursor_rule_list».obs ev with
      ⟨m2, cs12, m43, ev14, he41, hm51, he62, -⟩ |
      ⟨m2, cs12, m70, cs80, x_rule, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, -⟩
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      have ext := allocNil_extends Obs.Names.«Lists::Node<Ixon::RecursorRule>» h
      have hs' := L1.Stream.mono ext hs
      rw [he62, hm51]
      refine ⟨ext, #[], 0, (allocNil Obs.Names.«Lists::Node<Ixon::RecursorRule>» h).1, x_stream,
        by simp, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        he41, allocNil_rep _ _ h, by simpa using hs'⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      simp at hiz
  | succ count ih =>
    rcases Obs.«IxonDeserialize::get_recursor_rule_list».obs ev with
      ⟨m2, cs12, m43, ev14, -⟩ |
      ⟨m2, cs12, m70, cs80, x_rule, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, ev82, ev138, ev117, he164, hm174, he201, -⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      simp at hiz
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨ext1, rl, n1, rlVal, restPtr1, hlen1, hok1, hrl_tup, hrlRep, hs1⟩ :=
        get_recursor_rule_spec hs ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrl_tup
      rcases hrl_tup with ⟨rfl, rfl⟩
      obtain ⟨hsp, hm128⟩ := Deserialize.u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v119 m128
      obtain ⟨ext2, tailRules, n2, tailPtr, restPtr2, hlen2, hok2, htail_tup, htailRep, hs2⟩ :=
        ih (by omega) hs1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl⟩
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<Ixon::RecursorRule>» x_rule x_rest m105
      have consRep := allocCons_rep Obs.Names.«Lists::Node<Ixon::RecursorRule>»
        repRecursorRule_heapMono₂ (hrlRep.mono ext2) htailRep
      rw [he201, hm174]
      rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hlen2 hok2 hs2
      refine ⟨(ext1.trans ext2).trans ext3, #[rl] ++ tailRules, n1 + n2,
        (allocCons Obs.Names.«Lists::Node<Ixon::RecursorRule>» x_rule x_rest m105).1, x_s2,
        by omega, ?_, he164, by simpa using consRep, L1.Stream.mono ext3 hs2⟩
      rw [Ixon.Verify.BoundedConstant.getArray_succ]
      simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure]

theorem get_recursor_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_recursor" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (rc : Ixon.Recursor) (n : Nat) (rcVal restPtr : SourceValue F),
      Ixon.getRecursor { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok rc { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [rcVal, restPtr] ∧
      RepRecursor h' rc rcVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_bools_byte, x_s, v47, m50, cs58, v83, m84, cs94, v105, v117,
    m130, cs140, x_lvls, x_s2, m165, cs175, x_params, x_s3, m200, cs210, x_indices, x_s4,
    m235, cs245, x_motives, x_s5, m270, cs280, x_minors, x_s6, m305, cs315, x_typ, x_s7,
    m340, cs350, x_rules_len, x_s8, m375, cs385, x_rules, x_s9,
    ev14, ev60, heq82, ev96, pr115, pr127, ev142, ev177, ev212, ev247, ev282, ev317,
    ev352, ev387, he421, he510, -⟩ :=
    Obs.«IxonDeserialize::get_recursor».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hbools_eq, hs_eq⟩
  subst x_bools_byte x_s m2
  obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
  rw [← hdrop1] at hs1
  obtain ⟨hlt_val, hm50⟩ := Deserialize.u8LessThan_refines b.toNat_lt (b := 4) (by omega) ev60.erase
  subst m50
  rw [hlt_val] at heq82
  have hb_lt4 : b.toNat < 4 := by
    by_cases h4 : b.toNat < 4
    · exact h4
    · simp [h4] at heq82
  obtain ⟨hbts, hm84⟩ := Deserialize.u8BitDecomposition_refines b.toNat_lt ev96.erase
  subst m84
  rw [hbts] at pr115 pr127
  simp only [projectValue, Except.ok.injEq] at pr115 pr127
  obtain ⟨hm130, lvlsT, n1, s2Ptr, _, _, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev142.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩; subst m130
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2
  obtain ⟨hm165, paramsT, n2, s3Ptr, _, _, hparams_ok, _, hs3, hparams_tup⟩ :=
    getTagN0_progress hs2 ev177.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hparams_tup
  rcases hparams_tup with ⟨rfl, rfl⟩; subst m165
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at hparams_ok hs3
  obtain ⟨hm200, indicesT, n3, s4Ptr, _, _, hindices_ok, _, hs4, hindices_tup⟩ :=
    getTagN0_progress hs3 ev212.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hindices_tup
  rcases hindices_tup with ⟨rfl, rfl⟩; subst m200
  rw [show i + (1 + n1 + n2) + n3 = i + (1 + n1 + n2 + n3) by omega] at hindices_ok hs4
  obtain ⟨hm235, motivesT, n4, s5Ptr, _, _, hmotives_ok, _, hs5, hmotives_tup⟩ :=
    getTagN0_progress hs4 ev247.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hmotives_tup
  rcases hmotives_tup with ⟨rfl, rfl⟩; subst m235
  rw [show i + (1 + n1 + n2 + n3) + n4 = i + (1 + n1 + n2 + n3 + n4) by omega] at hmotives_ok hs5
  obtain ⟨hm270, minorsT, n5, s6Ptr, _, _, hminors_ok, _, hs6, hminors_tup⟩ :=
    getTagN0_progress hs5 ev282.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hminors_tup
  rcases hminors_tup with ⟨rfl, rfl⟩; subst m270
  rw [show i + (1 + n1 + n2 + n3 + n4) + n5 = i + (1 + n1 + n2 + n3 + n4 + n5) by omega] at
    hminors_ok hs6
  obtain ⟨ext_typ, typ, n6, typPtr, s7Ptr, _, _, htyp_ok, htyp_tup, htypRep, hs7⟩ :=
    Deserialize.getExpr_refines_at hs6 ev317.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  rw [show i + (1 + n1 + n2 + n3 + n4 + n5) + n6 =
    i + (1 + n1 + n2 + n3 + n4 + n5 + n6) by omega] at htyp_ok hs7
  obtain ⟨hm340, rlenT, n7, s8Ptr, _, _, hrlen_ok, _, hs8, hrlen_tup⟩ :=
    getTagN0_progress hs7 ev352.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrlen_tup
  rcases hrlen_tup with ⟨rfl, rfl⟩; subst m340
  rw [show i + (1 + n1 + n2 + n3 + n4 + n5 + n6) + n7 =
    i + (1 + n1 + n2 + n3 + n4 + n5 + n6 + n7) by omega] at hrlen_ok hs8
  obtain ⟨ext_rules, rules, n8, rulesPtr, s9Ptr, hlen_rules, hrules_ok, hrules_tup, hrulesRep, hs9⟩ :=
    get_recursor_rule_list_spec rlenT.value.toNat rlenT.value.toNat_lt hs8 ev387
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrules_tup
  rcases hrules_tup with ⟨rfl, rfl⟩
  subst he510
  rw [show i + (1 + n1 + n2 + n3 + n4 + n5 + n6 + n7) + n8 =
    i + (1 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8) by omega] at hrules_ok hs9 hlen_rules
  have hchk : Ixon.checkCount rlenT.value.toNat.toUInt64 2
      { idx := i + (1 + n1 + n2 + n3 + n4 + n5 + n6 + n7), bytes := ⟨bytes.toArray⟩ } =
      .ok () { idx := i + (1 + n1 + n2 + n3 + n4 + n5 + n6 + n7), bytes := ⟨bytes.toArray⟩ } := by
    have hu : rlenT.value.toNat.toUInt64 = rlenT.value := UInt64.ofNat_toNat
    rw [hu]
    exact Deserialize.checkCount_ok (by omega)
  have hk_flag : ∃ kFlag uFlag : Bool,
      (b > 3) = false ∧
      (Ixon.unpackBools 2 b)[0]! = kFlag ∧
      (Ixon.unpackBools 2 b)[1]! = uFlag ∧
      RepBool kFlag v105 ∧
      RepBool uFlag v117 := by
    rw [← pr115, ← pr127]
    rcases uint8_lt4_cases b hb_lt4 with rfl | rfl | rfl | rfl
    · exact ⟨false, false, by decide, by decide, by decide, rfl, rfl⟩
    · exact ⟨true, false, by decide, by decide, by decide, rfl, rfl⟩
    · exact ⟨false, true, by decide, by decide, by decide, rfl, rfl⟩
    · exact ⟨true, true, by decide, by decide, by decide, rfl, rfl⟩
  obtain ⟨kFlag, uFlag, hgt3, hk0, hu1, hkRep, huRep⟩ := hk_flag
  refine ⟨ext_typ.trans ext_rules,
    ⟨kFlag, uFlag, lvlsT.value, paramsT.value, indicesT.value, motivesT.value, minorsT.value,
      typ, rules⟩,
    1 + n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8, _, x_s9, ?_, he421,
    ⟨v105, v117, x_typ, x_rules, rfl, hkRep, huRep, htypRep.mono ext_rules, hrulesRep⟩, hs9⟩
  rw [Ixon.Verify.Codec.RecursorConstant.getRecursor_eq]
  simp only [Ixon.Verify.Codec.RecursorConstant.getRecursorFromFlags,
    Ixon.Verify.Codec.RecursorConstant.getRecursorAfterFlags,
    Ixon.Verify.Codec.RecursorConstant.getRecursorRules,
    Ixon.Verify.Codec.ConstantTables.getMany_eq_getArray,
    bind, EStateM.bind, hb_ok, hgt3, Bool.false_eq_true, ↓reduceIte,
    hk0, hu1, hlvls_ok, hparams_ok, hindices_ok, hmotives_ok, hminors_ok, htyp_ok,
    hrlen_ok, hchk, hrules_ok, pure, EStateM.pure]

theorem get_axiom_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_axiom" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (a : Ixon.Axiom) (n : Nat) (aVal restPtr : SourceValue F),
      Ixon.getAxiom { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok a { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [aVal, restPtr] ∧
      RepAxiom h' a aVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_is_unsafe, x_s, v36, m37, cs47, m59, cs69, x_lvls, x_s2, m94, cs104,
    x_typ, x_s3, v142, m146, cs154, ev14, ev49, ev71, ev106, he132, ev156, he186, -⟩ :=
    Obs.«IxonDeserialize::get_axiom».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hu_eq, hs_eq⟩
  subst x_is_unsafe x_s m2
  obtain ⟨hb_lt2, _, hm37⟩ := Deserialize.assertWireBool_refines b.toNat_lt ev49.erase
  subst m37
  obtain ⟨hbool_ok, hdrop1⟩ := Deserialize.getBool_of_drop_cons hcons hb_lt2
  rw [← hdrop1] at hs1
  obtain ⟨hm59, lvlsT, n1, s2Ptr, _, _, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev71.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩; subst m59
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2
  obtain ⟨ext_typ, typ, n2, typPtr, s3Ptr, _, _, htyp_ok, htyp_tup, htypRep, hs3⟩ :=
    Deserialize.getExpr_refines_at hs2 ev106.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  obtain ⟨hv142, hm146⟩ := Deserialize.u8ToField_refines ev156.erase
  subst m146 he186
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at htyp_ok hs3
  have huRep : RepBool (b == 1) v142 := by
    rw [hv142]
    rcases uint8_lt2_cases b hb_lt2 with rfl | rfl <;> rfl
  refine ⟨ext_typ, ⟨b == 1, lvlsT.value, typ⟩, 1 + n1 + n2, _, x_s3, ?_, he132,
    ⟨v142, x_typ, rfl, huRep, htypRep⟩, hs3⟩
  unfold Ixon.getAxiom
  simp only [bind, EStateM.bind, hbool_ok, hlvls_ok, htyp_ok, pure, EStateM.pure]

theorem get_quotient_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_quotient" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (q : Ixon.Quotient) (n : Nat) (qVal restPtr : SourceValue F),
      Ixon.getQuotient { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok q { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [qVal, restPtr] ∧
      RepQuotient h' q qVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_kind_byte, x_s, v36, m37, cs47, m59, cs69, x_lvls, x_s2, m94, cs104,
    x_typ, x_s3, ev14, ev49, ev71, ev106, he132, he173, -⟩ :=
    Obs.«IxonDeserialize::get_quotient».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hkb_eq, hs_eq⟩
  subst x_kind_byte x_s m2
  obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
  rw [← hdrop1] at hs1
  obtain ⟨hb_lt4, hm37, hqk⟩ := Deserialize.getQuotKind_refines b.toNat_lt ev49.erase
  subst m37
  obtain ⟨hm59, lvlsT, n1, s2Ptr, _, _, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev71.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩; subst m59
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2
  obtain ⟨ext_typ, typ, n2, typPtr, s3Ptr, _, _, htyp_ok, htyp_tup, htypRep, hs3⟩ :=
    Deserialize.getExpr_refines_at hs2 ev106.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  subst he173
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at htyp_ok hs3
  rcases uint8_lt4_cases b hb_lt4 with rfl | rfl | rfl | rfl
  · refine ⟨ext_typ, ⟨.type, lvlsT.value, typ⟩, 1 + n1 + n2, _, x_s3, ?_, he132,
      ⟨v36, x_typ, rfl, hqk, htypRep⟩, hs3⟩
    unfold Ixon.getQuotient
    simp only [bind, EStateM.bind, hb_ok, hlvls_ok, htyp_ok, pure, EStateM.pure]
  · refine ⟨ext_typ, ⟨.ctor, lvlsT.value, typ⟩, 1 + n1 + n2, _, x_s3, ?_, he132,
      ⟨v36, x_typ, rfl, hqk, htypRep⟩, hs3⟩
    unfold Ixon.getQuotient
    simp only [bind, EStateM.bind, hb_ok, hlvls_ok, htyp_ok, pure, EStateM.pure]
  · refine ⟨ext_typ, ⟨.lift, lvlsT.value, typ⟩, 1 + n1 + n2, _, x_s3, ?_, he132,
      ⟨v36, x_typ, rfl, hqk, htypRep⟩, hs3⟩
    unfold Ixon.getQuotient
    simp only [bind, EStateM.bind, hb_ok, hlvls_ok, htyp_ok, pure, EStateM.pure]
  · refine ⟨ext_typ, ⟨.ind, lvlsT.value, typ⟩, 1 + n1 + n2, _, x_s3, ?_, he132,
      ⟨v36, x_typ, rfl, hqk, htypRep⟩, hs3⟩
    unfold Ixon.getQuotient
    simp only [bind, EStateM.bind, hb_ok, hlvls_ok, htyp_ok, pure, EStateM.pure]

theorem get_field_mode_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_field_mode_list"
      [x_stream, TagN.u64Value count] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (modes : Array Ixon.FieldMode) (n : Nat) (listPtr sharedVal restPtr : SourceValue F),
      modes.size = count ∧
      (bytes.drop (i + n)).length + count ≤ (bytes.drop i).length ∧
      Ixon.getArray Ixon.getFieldMode count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok modes { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, sharedVal, restPtr] ∧
      sharedVal = .field (if modes.any (· == .shared) then 1 else 0) ∧
      RepList Obs.Names.«Lists::Node<Field>» (fun _ => RepFieldMode) h' modes.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i x_stream r h h' calls with
  | zero =>
    rcases Obs.«IxonDeserialize::get_field_mode_list».obs ev with
      ⟨m2, cs12, m44, ev14, he42, hm52, he69, -⟩ |
      ⟨m2, cs12, m77, cs87, x_mode, x_s, m112, cs122, v126, m135, cs143,
        x_rest, x_shared, x_s2, m173, cs184, m206, ev14, -⟩ |
      ⟨m2, cs12, m77, cs87, x_mode, x_s, m112, cs122, v126, m135, cs143,
        x_rest, x_shared, x_s2, m173, cs184, m261, ev14, -⟩
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      have ext := allocNil_extends Obs.Names.«Lists::Node<Field>» h
      have hs' := L1.Stream.mono ext hs
      rw [he69, hm52]
      refine ⟨ext, #[], 0, (allocNil Obs.Names.«Lists::Node<Field>» h).1, .field 0, x_stream,
        rfl, by simp, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        he42, rfl, allocNil_rep _ _ h, by simpa using hs'⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    rcases Obs.«IxonDeserialize::get_field_mode_list».obs ev with
      ⟨m2, cs12, m44, ev14, -⟩ |
      ⟨m2, cs12, m77, cs87, x_mode, x_s, m112, cs122, v126, m135, cs143,
        x_rest, x_shared, x_s2, m173, cs184, m206,
        ev14, ev89, ev145, ev124, ev186, he204, hm214, he247, -⟩ |
      ⟨m2, cs12, m77, cs87, x_mode, x_s, m112, cs122, v126, m135, cs143,
        x_rest, x_shared, x_s2, m173, cs184, m261,
        ev14, ev89, ev145, ev124, ev186, he259, hm269, he301, -⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨hm77, b, rest1, restPtr1, hcons, hs1, hrb⟩ :=
        Deserialize.readByte_refines hs ev89.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
      rcases hrb with ⟨hmode_eq, hs_eq⟩
      subst x_mode x_s m77
      obtain ⟨hb_ok, hdrop1, hlt1⟩ := Deserialize.getU8_of_drop_cons hcons
      rw [← hdrop1] at hs1
      obtain ⟨hsp, hm135⟩ := Deserialize.u64SaturatingPred_refines hcount ev145.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v126 m135
      obtain ⟨ext_tail, tailModes, n2, tailPtr, tailSh, s2Ptr, hsz2, hlen2, hok2,
        htail_tup, hsh_eq, htailRep, hs2⟩ := ih (by omega) hs1 ev124
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl, rfl⟩
      obtain ⟨hbf, hm173⟩ := Deserialize.u8ToField_refines ev186.erase
      subst m173
      injection hbf with hf
      have hb0 : b = 0 := UInt8.ext ((Deserialize.natCast_eq_zero_iff b.toNat_lt).mp hf.symm)
      subst hb0
      have hfm_ok : Ixon.getFieldMode { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok .inherited { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
        unfold Ixon.getFieldMode
        simp only [bind, EStateM.bind, hb_ok, Ixon.FieldMode.ofCode?, pure, EStateM.pure]
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<Field>» (.field 0) x_rest m112
      have consRep := allocCons_rep Obs.Names.«Lists::Node<Field>» repFieldMode_heapMono₂
        (rfl : RepFieldMode .inherited (.field 0)) htailRep
      rw [he247, hm214]
      rw [show i + 1 + n2 = i + (1 + n2) by omega] at hlen2 hok2 hs2
      refine ⟨ext_tail.trans ext3, #[.inherited] ++ tailModes, 1 + n2,
        (allocCons Obs.Names.«Lists::Node<Field>» (.field 0) x_rest m112).1, x_shared, x_s2,
        by simp [hsz2]; omega, by omega, ?_, he204, ?_, by simpa using consRep,
        L1.Stream.mono ext3 hs2⟩
      · rw [Ixon.Verify.BoundedConstant.getArray_succ]
        simp [bind, EStateM.bind, hfm_ok, hok2, pure, EStateM.pure]
      · rw [hsh_eq]; simp
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨hm77, b, rest1, restPtr1, hcons, hs1, hrb⟩ :=
        Deserialize.readByte_refines hs ev89.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
      rcases hrb with ⟨hmode_eq, hs_eq⟩
      subst x_mode x_s m77
      obtain ⟨hb_ok, hdrop1, hlt1⟩ := Deserialize.getU8_of_drop_cons hcons
      rw [← hdrop1] at hs1
      obtain ⟨hsp, hm135⟩ := Deserialize.u64SaturatingPred_refines hcount ev145.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v126 m135
      obtain ⟨ext_tail, tailModes, n2, tailPtr, tailSh, s2Ptr, hsz2, hlen2, hok2,
        htail_tup, _, htailRep, hs2⟩ := ih (by omega) hs1 ev124
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl, rfl⟩
      obtain ⟨hbf, hm173⟩ := Deserialize.u8ToField_refines ev186.erase
      subst m173
      injection hbf with hf
      have hb1 : b = 1 := UInt8.ext ((Deserialize.natCast_eq_one_iff b.toNat_lt).mp hf.symm)
      subst hb1
      have hfm_ok : Ixon.getFieldMode { idx := i, bytes := ⟨bytes.toArray⟩ } =
          .ok .shared { idx := i + 1, bytes := ⟨bytes.toArray⟩ } := by
        unfold Ixon.getFieldMode
        simp only [bind, EStateM.bind, hb_ok, Ixon.FieldMode.ofCode?, pure, EStateM.pure]
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<Field>» (.field 1) x_rest m112
      have consRep := allocCons_rep Obs.Names.«Lists::Node<Field>» repFieldMode_heapMono₂
        (rfl : RepFieldMode .shared (.field 1)) htailRep
      rw [he301, hm269]
      rw [show i + 1 + n2 = i + (1 + n2) by omega] at hlen2 hok2 hs2
      refine ⟨ext_tail.trans ext3, #[.shared] ++ tailModes, 1 + n2,
        (allocCons Obs.Names.«Lists::Node<Field>» (.field 1) x_rest m112).1, .field 1, x_s2,
        by simp [hsz2]; omega, by omega, ?_, he259, by simp, by simpa using consRep,
        L1.Stream.mono ext3 hs2⟩
      rw [Ixon.Verify.BoundedConstant.getArray_succ]
      simp [bind, EStateM.bind, hfm_ok, hok2, pure, EStateM.pure]

theorem get_constructor_modes_spec {listed : Bool} {fields : UInt64}
    {bytes : List UInt8} {i : Nat} {x_listed x_s r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hl : RepBool listed x_listed)
    (hs : L1.Stream h (bytes.drop i) x_s)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constructor_modes"
      [x_listed, TagN.u64Value fields.toNat, x_s] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (fm : Ixon.FieldModes fields.toNat) (n : Nat) (modesPtr restPtr : SourceValue F),
      (bytes.drop (i + n)).length ≤ (bytes.drop i).length ∧
      Ixon.getConstructorFieldModes listed fields.toNat { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok fm { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [modesPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<Field>» (fun _ => RepFieldMode) h'
        fm.toArray.toList modesPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  rcases Obs.«IxonDeserialize::get_constructor_modes».obs ev with
    ⟨m21, hv14, he19, hm29, he40, -⟩ |
    ⟨m48, cs58, x_modes, x_shared, x_s2, hne42, hv46, ev60, heq121, he126, he141, -⟩
  · have hfalse : listed = false := by
      cases listed with
      | false => rfl
      | true => rw [RepBool] at hl; rw [hl] at hv14; simp at hv14
    subst hfalse
    have ext := allocNil_extends Obs.Names.«Lists::Node<Field>» h
    have hs' := L1.Stream.mono ext hs
    rw [he40, hm29]
    refine ⟨ext, .inherited, 0, (allocNil Obs.Names.«Lists::Node<Field>» h).1, x_s,
      by simp, by simp [Ixon.getConstructorFieldModes, pure, EStateM.pure], he19,
      allocNil_rep _ _ h, by simpa using hs'⟩
  · have htrue : listed = true := by
      cases listed with
      | true => rfl
      | false => rw [RepBool] at hl; exact (hne42 hl).elim
    subst htrue
    obtain ⟨ext1, modes, n, modesPtr, shVal, s2Ptr, hsz, hlen, hok, htup, hsh, hrep, hs2⟩ :=
      get_field_mode_list_spec fields.toNat fields.toNat_lt hs ev60
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl, rfl⟩
    subst he141
    have hany : modes.any (· == .shared) = true := by
      rw [hsh] at heq121
      cases h_any : modes.any (· == .shared)
      · simp [h_any] at heq121
      · rfl
    have hchk : Ixon.checkCount fields.toNat.toUInt64 1
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok () { idx := i, bytes := ⟨bytes.toArray⟩ } := by
      have hu : fields.toNat.toUInt64 = fields := UInt64.ofNat_toNat
      rw [hu]
      exact Deserialize.checkCount_ok (by omega)
    have hlisted : Ixon.FieldModes.listed? modes =
        some (.listed ⟨modes, hsz⟩ hany) := by
      unfold Ixon.FieldModes.listed?
      rw [dite_eq_left hsz, dite_eq_left hany]
    refine ⟨ext1, .listed ⟨modes, hsz⟩ hany, n, x_modes, x_s2, by omega, ?_, he126, hrep, hs2⟩
    unfold Ixon.getConstructorFieldModes Ixon.getFieldModes
    simp only [↓reduceIte, bind, EStateM.bind, hchk, hok, hlisted, pure, EStateM.pure]

theorem get_constructor_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constructor" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (c : Ixon.Constructor) (n : Nat) (cVal restPtr : SourceValue F),
      (bytes.drop (i + n)).length + 6 ≤ (bytes.drop i).length ∧
      Ixon.getConstructor { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok c { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [cVal, restPtr] ∧
      RepConstructor h' c cVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_flags, x_s, v47, m50, cs58, v83, m84, cs94, m106, cs116, x_lvls, x_s2,
    m141, cs151, x_cidx, x_s3, m176, cs186, x_params, x_s4, m211, cs221, x_fields, x_s5,
    m246, cs256, v259, x_modes, x_s6, m300, cs310, x_typ, x_s7, v348,
    ev14, ev60, heq82, ev96, ev118, ev153, ev188, ev223, pr270, ev258, ev312,
    he338, pr363, he414, -⟩ :=
    Obs.«IxonDeserialize::get_constructor».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hfl_eq, hs_eq⟩
  subst x_flags x_s m2
  obtain ⟨hb_ok, hdrop1, hlt0⟩ := Deserialize.getU8_of_drop_cons hcons
  rw [← hdrop1] at hs1
  obtain ⟨hlt_val, hm50⟩ := Deserialize.u8LessThan_refines b.toNat_lt (b := 4) (by omega) ev60.erase
  subst m50
  rw [hlt_val] at heq82
  have hb_lt4 : b.toNat < 4 := by
    by_cases h4 : b.toNat < 4
    · exact h4
    · simp [h4] at heq82
  obtain ⟨hbts, hm84⟩ := Deserialize.u8BitDecomposition_refines b.toNat_lt ev96.erase
  subst m84
  rw [hbts] at pr270 pr363
  simp only [projectValue, Except.ok.injEq] at pr270 pr363
  obtain ⟨hm106, lvlsT, n1, s2Ptr, _, hlt1, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev118.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩; subst m106
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2 hlt1
  obtain ⟨hm141, cidxT, n2, s3Ptr, _, hlt2, hcidx_ok, _, hs3, hcidx_tup⟩ :=
    getTagN0_progress hs2 ev153.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hcidx_tup
  rcases hcidx_tup with ⟨rfl, rfl⟩; subst m141
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at hcidx_ok hs3 hlt2
  obtain ⟨hm176, paramsT, n3, s4Ptr, _, hlt3, hparams_ok, _, hs4, hparams_tup⟩ :=
    getTagN0_progress hs3 ev188.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hparams_tup
  rcases hparams_tup with ⟨rfl, rfl⟩; subst m176
  rw [show i + (1 + n1 + n2) + n3 = i + (1 + n1 + n2 + n3) by omega] at hparams_ok hs4 hlt3
  obtain ⟨hm211, fieldsT, n4, s5Ptr, _, hlt4, hfields_ok, _, hs5, hfields_tup⟩ :=
    getTagN0_progress hs4 ev223.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hfields_tup
  rcases hfields_tup with ⟨rfl, rfl⟩; subst m211
  rw [show i + (1 + n1 + n2 + n3) + n4 = i + (1 + n1 + n2 + n3 + n4) by omega] at
    hfields_ok hs5 hlt4
  have hflags_decode :
      (b > 3) = false ∧
      RepBool (b &&& 1 == 1) v348 ∧
      RepBool (b &&& 2 == 2) v259 := by
    rw [← pr363, ← pr270]
    rcases uint8_lt4_cases b hb_lt4 with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, rfl, rfl⟩
  rcases hflags_decode with ⟨hgt3, huRep, hlistRep⟩
  obtain ⟨ext_modes, fm, n5, modesPtr, s6Ptr, hle5, hfm_ok, hfm_tup, hfmRep, hs6⟩ :=
    get_constructor_modes_spec hlistRep hs5 ev258
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hfm_tup
  rcases hfm_tup with ⟨rfl, rfl⟩
  rw [show i + (1 + n1 + n2 + n3 + n4) + n5 =
    i + (1 + n1 + n2 + n3 + n4 + n5) by omega] at hfm_ok hs6 hle5
  obtain ⟨ext_typ, typ, n6, typPtr, s7Ptr, _, hlt6, htyp_ok, htyp_tup, htypRep, hs7⟩ :=
    Deserialize.getExpr_refines_at hs6 ev312.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  subst he414
  rw [show i + (1 + n1 + n2 + n3 + n4 + n5) + n6 =
    i + (1 + n1 + n2 + n3 + n4 + n5 + n6) by omega] at htyp_ok hs7 hlt6
  refine ⟨ext_modes.trans ext_typ,
    ⟨b &&& 1 == 1, lvlsT.value, cidxT.value, paramsT.value, fieldsT.value, fm, typ⟩,
    1 + n1 + n2 + n3 + n4 + n5 + n6, _, x_s7, by omega, ?_, he338,
    ⟨v348, x_modes, x_typ, rfl, huRep,
      repList_heapMono₂ _ repFieldMode_heapMono₂ ext_typ hfmRep, htypRep⟩, hs7⟩
  unfold Ixon.getConstructor
  simp only [bind, EStateM.bind, hb_ok, hgt3, Bool.false_eq_true, ↓reduceIte,
    hlvls_ok, hcidx_ok, hparams_ok, hfields_ok, hfm_ok, htyp_ok, pure, EStateM.pure]

theorem get_constructor_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constructor_list"
      [x_stream, TagN.u64Value count] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ctors : Array Ixon.Constructor) (n : Nat) (listPtr restPtr : SourceValue F),
      (bytes.drop (i + n)).length + count * 6 ≤ (bytes.drop i).length ∧
      Ixon.getArray Ixon.getConstructor count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ctors { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<Ixon::Constructor>» RepConstructor h' ctors.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i x_stream r h h' calls with
  | zero =>
    rcases Obs.«IxonDeserialize::get_constructor_list».obs ev with
      ⟨m2, cs12, m43, ev14, he41, hm51, he62, -⟩ |
      ⟨m2, cs12, m70, cs80, x_ctor, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, -⟩
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      have ext := allocNil_extends Obs.Names.«Lists::Node<Ixon::Constructor>» h
      have hs' := L1.Stream.mono ext hs
      rw [he62, hm51]
      refine ⟨ext, #[], 0, (allocNil Obs.Names.«Lists::Node<Ixon::Constructor>» h).1, x_stream,
        by simp, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        he41, allocNil_rep _ _ h, by simpa using hs'⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      simp at hiz
  | succ count ih =>
    rcases Obs.«IxonDeserialize::get_constructor_list».obs ev with
      ⟨m2, cs12, m43, ev14, -⟩ |
      ⟨m2, cs12, m70, cs80, x_ctor, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, ev82, ev138, ev117, he164, hm174, he201, -⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      simp at hiz
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨ext1, c, n1, cVal, restPtr1, hlen1, hok1, hc_tup, hcRep, hs1⟩ :=
        get_constructor_spec hs ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hc_tup
      rcases hc_tup with ⟨rfl, rfl⟩
      obtain ⟨hsp, hm128⟩ := Deserialize.u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v119 m128
      obtain ⟨ext2, tailCtors, n2, tailPtr, restPtr2, hlen2, hok2, htail_tup, htailRep, hs2⟩ :=
        ih (by omega) hs1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl⟩
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<Ixon::Constructor>» x_ctor x_rest m105
      have consRep := allocCons_rep Obs.Names.«Lists::Node<Ixon::Constructor>»
        repConstructor_heapMono₂ (hcRep.mono ext2) htailRep
      rw [he201, hm174]
      rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hlen2 hok2 hs2
      refine ⟨(ext1.trans ext2).trans ext3, #[c] ++ tailCtors, n1 + n2,
        (allocCons Obs.Names.«Lists::Node<Ixon::Constructor>» x_ctor x_rest m105).1, x_s2,
        by omega, ?_, he164, by simpa using consRep, L1.Stream.mono ext3 hs2⟩
      rw [Ixon.Verify.BoundedConstant.getArray_succ]
      simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure]

theorem get_inductive_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_inductive" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ind : Ixon.Inductive) (n : Nat) (indVal restPtr : SourceValue F),
      Ixon.getInductive { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ind { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [indVal, restPtr] ∧
      RepInductive h' ind indVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_bools_byte, x_s, v36, m37, cs47, v58, m59, cs69, v80,
    m93, cs103, x_lvls, x_s2, m128, cs138, x_params, x_s3, m163, cs173, x_indices, x_s4,
    m198, cs208, x_typ, x_s5, m233, cs243, x_ctors_len, x_s6, m268, cs278, x_ctors, x_s7,
    ev14, ev49, ev71, pr90, ev105, ev140, ev175, ev210, ev245, ev280, he314, he379, -⟩ :=
    Obs.«IxonDeserialize::get_inductive».obs ev
  obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
  rcases hrb with ⟨hb_eq, hs_eq⟩
  subst x_bools_byte x_s m2
  obtain ⟨hb_lt2, _, hm37⟩ := Deserialize.assertWireBool_refines b.toNat_lt ev49.erase
  subst m37
  obtain ⟨hbool_ok, hdrop1⟩ := Deserialize.getBool_of_drop_cons hcons hb_lt2
  rw [← hdrop1] at hs1
  obtain ⟨hbts, hm59⟩ := Deserialize.u8BitDecomposition_refines b.toNat_lt ev71.erase
  subst m59
  rw [hbts] at pr90
  simp only [projectValue, Except.ok.injEq] at pr90
  obtain ⟨hm93, lvlsT, n1, s2Ptr, _, _, hlvls_ok, _, hs2, hlvls_tup⟩ :=
    getTagN0_progress hs1 ev105.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hlvls_tup
  rcases hlvls_tup with ⟨rfl, rfl⟩; subst m93
  rw [show i + 1 + n1 = i + (1 + n1) by omega] at hlvls_ok hs2
  obtain ⟨hm128, paramsT, n2, s3Ptr, _, _, hparams_ok, _, hs3, hparams_tup⟩ :=
    getTagN0_progress hs2 ev140.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hparams_tup
  rcases hparams_tup with ⟨rfl, rfl⟩; subst m128
  rw [show i + (1 + n1) + n2 = i + (1 + n1 + n2) by omega] at hparams_ok hs3
  obtain ⟨hm163, indicesT, n3, s4Ptr, _, _, hindices_ok, _, hs4, hindices_tup⟩ :=
    getTagN0_progress hs3 ev175.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hindices_tup
  rcases hindices_tup with ⟨rfl, rfl⟩; subst m163
  rw [show i + (1 + n1 + n2) + n3 = i + (1 + n1 + n2 + n3) by omega] at hindices_ok hs4
  obtain ⟨ext_typ, typ, n4, typPtr, s5Ptr, _, _, htyp_ok, htyp_tup, htypRep, hs5⟩ :=
    Deserialize.getExpr_refines_at hs4 ev210.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htyp_tup
  rcases htyp_tup with ⟨rfl, rfl⟩
  rw [show i + (1 + n1 + n2 + n3) + n4 = i + (1 + n1 + n2 + n3 + n4) by omega] at htyp_ok hs5
  obtain ⟨hm233, clenT, n5, s6Ptr, _, _, hclen_ok, _, hs6, hclen_tup⟩ :=
    getTagN0_progress hs5 ev245.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hclen_tup
  rcases hclen_tup with ⟨rfl, rfl⟩; subst m233
  rw [show i + (1 + n1 + n2 + n3 + n4) + n5 =
    i + (1 + n1 + n2 + n3 + n4 + n5) by omega] at hclen_ok hs6
  obtain ⟨ext_ctors, ctors, n6, ctorsPtr, s7Ptr, hlen_ctors, hctors_ok, hctors_tup, hctorsRep, hs7⟩ :=
    get_constructor_list_spec clenT.value.toNat clenT.value.toNat_lt hs6 ev280
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hctors_tup
  rcases hctors_tup with ⟨rfl, rfl⟩
  subst he379
  rw [show i + (1 + n1 + n2 + n3 + n4 + n5) + n6 =
    i + (1 + n1 + n2 + n3 + n4 + n5 + n6) by omega] at hctors_ok hs7 hlen_ctors
  have hchk : Ixon.checkCount clenT.value.toNat.toUInt64 6
      { idx := i + (1 + n1 + n2 + n3 + n4 + n5), bytes := ⟨bytes.toArray⟩ } =
      .ok () { idx := i + (1 + n1 + n2 + n3 + n4 + n5), bytes := ⟨bytes.toArray⟩ } := by
    have hu : clenT.value.toNat.toUInt64 = clenT.value := UInt64.ofNat_toNat
    rw [hu]
    exact Deserialize.checkCount_ok (by omega)
  have huRep : RepBool (b == 1) v80 := by
    rw [← pr90]
    rcases uint8_lt2_cases b hb_lt2 with rfl | rfl <;> rfl
  refine ⟨ext_typ.trans ext_ctors,
    ⟨b == 1, lvlsT.value, paramsT.value, indicesT.value, typ, ctors⟩,
    1 + n1 + n2 + n3 + n4 + n5 + n6, _, x_s7, ?_, he314,
    ⟨v80, x_typ, x_ctors, rfl, huRep, htypRep.mono ext_ctors, hctorsRep⟩, hs7⟩
  rw [Ixon.Verify.Codec.MutualConstant.getInductive_eq]
  simp only [Ixon.Verify.Codec.MutualConstant.getInductiveAfterFlags,
    Ixon.Verify.Codec.MutualConstant.getInductiveConstructors,
    Ixon.Verify.Codec.ConstantTables.getMany_eq_getArray,
    bind, EStateM.bind, hbool_ok, hlvls_ok, hparams_ok, hindices_ok, htyp_ok,
    hclen_ok, hchk, hctors_ok, pure, EStateM.pure]

/-! ## Projection payloads, mutual blocks, and `get_constant_info` -/

theorem get_inductive_proj_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_inductive_proj" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.InductiveProj) (n : Nat) (pVal restPtr : SourceValue F),
      Ixon.getInductiveProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [pVal, restPtr] ∧
      RepInductiveProj h' p pVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_idx, x_s, m37, cs47, x_block, x_s2, ev14, ev49, he75, he108, -⟩ :=
    Obs.«IxonDeserialize::get_inductive_proj».obs ev
  obtain ⟨hm2, idxT, n1, sPtr, _, _, hidx_ok, _, hs1, hidx_tup⟩ :=
    getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hidx_tup
  rcases hidx_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨ext_addr, hlen, addrPtr, s2Ptr, haddr_tup, haddrRep, hs2⟩ :=
    Deserialize.getAddress_refines hs1 ev49.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
  rcases haddr_tup with ⟨rfl, rfl⟩
  subst he108
  rw [List.drop_drop, show i + n1 + 32 = i + (n1 + 32) by omega] at hs2
  have haddr_ok := getAddress_of_drop hlen
  rw [show i + n1 + 32 = i + (n1 + 32) by omega] at haddr_ok
  refine ⟨ext_addr, ⟨idxT.value, ixAddr (Deserialize.takeAddress (bytes.drop (i + n1)) hlen)⟩,
    n1 + 32, _, x_s2, ?_, he75,
    ⟨x_block, rfl, ⟨Deserialize.takeAddress (bytes.drop (i + n1)) hlen, haddrRep, rfl⟩⟩, hs2⟩
  unfold Ixon.getInductiveProj
  change (EStateM.bind (Ixon.getTagN 0) fun t =>
    EStateM.bind (Ixon.Serialize.get : Ixon.GetM _root_.Address) fun blk =>
      EStateM.pure ⟨t.value, blk⟩) _ = _
  simp only [EStateM.bind, hidx_ok, haddr_ok, EStateM.pure]

theorem get_constructor_proj_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constructor_proj" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.ConstructorProj) (n : Nat) (pVal restPtr : SourceValue F),
      Ixon.getConstructorProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [pVal, restPtr] ∧
      RepConstructorProj h' p pVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_idx, x_s, m37, cs47, x_cidx, x_s2, m72, cs82, x_block, x_s3,
    ev14, ev49, ev84, he110, he151, -⟩ :=
    Obs.«IxonDeserialize::get_constructor_proj».obs ev
  obtain ⟨hm2, idxT, n1, sPtr, _, _, hidx_ok, _, hs1, hidx_tup⟩ :=
    getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hidx_tup
  rcases hidx_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨hm37, cidxT, n2, s2Ptr, _, _, hcidx_ok, _, hs2, hcidx_tup⟩ :=
    getTagN0_progress hs1 ev49.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hcidx_tup
  rcases hcidx_tup with ⟨rfl, rfl⟩; subst m37
  rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hcidx_ok hs2
  obtain ⟨ext_addr, hlen, addrPtr, s3Ptr, haddr_tup, haddrRep, hs3⟩ :=
    Deserialize.getAddress_refines hs2 ev84.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
  rcases haddr_tup with ⟨rfl, rfl⟩
  subst he151
  rw [List.drop_drop, show i + (n1 + n2) + 32 = i + (n1 + n2 + 32) by omega] at hs3
  have haddr_ok := getAddress_of_drop hlen
  rw [show i + (n1 + n2) + 32 = i + (n1 + n2 + 32) by omega] at haddr_ok
  refine ⟨ext_addr,
    ⟨idxT.value, cidxT.value, ixAddr (Deserialize.takeAddress (bytes.drop (i + (n1 + n2))) hlen)⟩,
    n1 + n2 + 32, _, x_s3, ?_, he110,
    ⟨x_block, rfl, ⟨Deserialize.takeAddress (bytes.drop (i + (n1 + n2))) hlen, haddrRep, rfl⟩⟩,
    hs3⟩
  unfold Ixon.getConstructorProj
  change (EStateM.bind (Ixon.getTagN 0) fun t1 =>
    EStateM.bind (Ixon.getTagN 0) fun t2 =>
      EStateM.bind (Ixon.Serialize.get : Ixon.GetM _root_.Address) fun blk =>
        EStateM.pure ⟨t1.value, t2.value, blk⟩) _ = _
  simp only [EStateM.bind, hidx_ok, hcidx_ok, haddr_ok, EStateM.pure]

theorem get_recursor_proj_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_recursor_proj" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.RecursorProj) (n : Nat) (pVal restPtr : SourceValue F),
      Ixon.getRecursorProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [pVal, restPtr] ∧
      RepRecursorProj h' p pVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_idx, x_s, m37, cs47, x_block, x_s2, ev14, ev49, he75, he108, -⟩ :=
    Obs.«IxonDeserialize::get_recursor_proj».obs ev
  obtain ⟨hm2, idxT, n1, sPtr, _, _, hidx_ok, _, hs1, hidx_tup⟩ :=
    getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hidx_tup
  rcases hidx_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨ext_addr, hlen, addrPtr, s2Ptr, haddr_tup, haddrRep, hs2⟩ :=
    Deserialize.getAddress_refines hs1 ev49.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
  rcases haddr_tup with ⟨rfl, rfl⟩
  subst he108
  rw [List.drop_drop, show i + n1 + 32 = i + (n1 + 32) by omega] at hs2
  have haddr_ok := getAddress_of_drop hlen
  rw [show i + n1 + 32 = i + (n1 + 32) by omega] at haddr_ok
  refine ⟨ext_addr, ⟨idxT.value, ixAddr (Deserialize.takeAddress (bytes.drop (i + n1)) hlen)⟩,
    n1 + 32, _, x_s2, ?_, he75,
    ⟨x_block, rfl, ⟨Deserialize.takeAddress (bytes.drop (i + n1)) hlen, haddrRep, rfl⟩⟩, hs2⟩
  unfold Ixon.getRecursorProj
  change (EStateM.bind (Ixon.getTagN 0) fun t =>
    EStateM.bind (Ixon.Serialize.get : Ixon.GetM _root_.Address) fun blk =>
      EStateM.pure ⟨t.value, blk⟩) _ = _
  simp only [EStateM.bind, hidx_ok, haddr_ok, EStateM.pure]

theorem get_definition_proj_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_definition_proj" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (p : Ixon.DefinitionProj) (n : Nat) (pVal restPtr : SourceValue F),
      Ixon.getDefinitionProj { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok p { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [pVal, restPtr] ∧
      RepDefinitionProj h' p pVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_idx, x_s, m37, cs47, x_block, x_s2, ev14, ev49, he75, he108, -⟩ :=
    Obs.«IxonDeserialize::get_definition_proj».obs ev
  obtain ⟨hm2, idxT, n1, sPtr, _, _, hidx_ok, _, hs1, hidx_tup⟩ :=
    getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hidx_tup
  rcases hidx_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨ext_addr, hlen, addrPtr, s2Ptr, haddr_tup, haddrRep, hs2⟩ :=
    Deserialize.getAddress_refines hs1 ev49.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
  rcases haddr_tup with ⟨rfl, rfl⟩
  subst he108
  rw [List.drop_drop, show i + n1 + 32 = i + (n1 + 32) by omega] at hs2
  have haddr_ok := getAddress_of_drop hlen
  rw [show i + n1 + 32 = i + (n1 + 32) by omega] at haddr_ok
  refine ⟨ext_addr, ⟨idxT.value, ixAddr (Deserialize.takeAddress (bytes.drop (i + n1)) hlen)⟩,
    n1 + 32, _, x_s2, ?_, he75,
    ⟨x_block, rfl, ⟨Deserialize.takeAddress (bytes.drop (i + n1)) hlen, haddrRep, rfl⟩⟩, hs2⟩
  unfold Ixon.getDefinitionProj
  change (EStateM.bind (Ixon.getTagN 0) fun t =>
    EStateM.bind (Ixon.Serialize.get : Ixon.GetM _root_.Address) fun blk =>
      EStateM.pure ⟨t.value, blk⟩) _ = _
  simp only [EStateM.bind, hidx_ok, haddr_ok, EStateM.pure]

theorem get_mut_const_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_mut_const" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (mc : Ixon.MutConst) (n : Nat) (mcVal restPtr : SourceValue F),
      Ixon.getMutConst { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok mc { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [mcVal, restPtr] ∧
      RepMutConst h' mc mcVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  rcases Obs.«IxonDeserialize::get_mut_const».obs ev with
    ⟨m2, cs12, x_tag, x_s, m37, cs48, m64, cs74, x_defn, x_s2, ev14, ev50, ev76, he102, he127, -⟩ |
    ⟨m2, cs12, x_tag, x_s, m37, cs48, m135, cs145, x_indc, x_s2, ev14, ev50, ev147, he173, he198, -⟩ |
    ⟨m2, cs12, x_tag, x_s, m37, cs48, m206, cs216, x_recr, x_s2, ev14, ev50, ev218, he244, he269, -⟩
  · obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
    rcases hrb with ⟨htag_eq, hs_eq⟩; subst x_tag x_s m2
    obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
    rw [← hdrop1] at hs1
    obtain ⟨hbf, hm37⟩ := Deserialize.u8ToField_refines ev50.erase; subst m37
    injection hbf with hf
    have hb0 : b = 0 := UInt8.ext ((Deserialize.natCast_eq_zero_iff b.toNat_lt).mp hf.symm)
    subst hb0
    obtain ⟨ext1, d, n1, dVal, s2Ptr, hd_ok, hd_tup, hdRep, hs2⟩ := get_definition_spec hs1 ev76
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hd_tup
    rcases hd_tup with ⟨rfl, rfl⟩; subst he127
    rw [show i + 1 + n1 = i + (1 + n1) by omega] at hd_ok hs2
    refine ⟨ext1, .defn d, 1 + n1, _, x_s2, ?_, he102, ⟨x_defn, rfl, hdRep⟩, hs2⟩
    unfold Ixon.getMutConst
    simp only [bind, EStateM.bind, hb_ok, Functor.map, EStateM.map, hd_ok]
  · obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
    rcases hrb with ⟨htag_eq, hs_eq⟩; subst x_tag x_s m2
    obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
    rw [← hdrop1] at hs1
    obtain ⟨hbf, hm37⟩ := Deserialize.u8ToField_refines ev50.erase; subst m37
    injection hbf with hf
    have hb1 : b = 1 := UInt8.ext ((Deserialize.natCast_eq_one_iff b.toNat_lt).mp hf.symm)
    subst hb1
    obtain ⟨ext1, ind, n1, indVal, s2Ptr, hi_ok, hi_tup, hiRep, hs2⟩ :=
      get_inductive_spec hs1 ev147
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hi_tup
    rcases hi_tup with ⟨rfl, rfl⟩; subst he198
    rw [show i + 1 + n1 = i + (1 + n1) by omega] at hi_ok hs2
    refine ⟨ext1, .indc ind, 1 + n1, _, x_s2, ?_, he173, ⟨x_indc, rfl, hiRep⟩, hs2⟩
    unfold Ixon.getMutConst
    simp only [bind, EStateM.bind, hb_ok, Functor.map, EStateM.map, hi_ok]
  · obtain ⟨hm2, b, rest1, restPtr1, hcons, hs1, hrb⟩ := Deserialize.readByte_refines hs ev14.erase
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrb
    rcases hrb with ⟨htag_eq, hs_eq⟩; subst x_tag x_s m2
    obtain ⟨hb_ok, hdrop1, _⟩ := Deserialize.getU8_of_drop_cons hcons
    rw [← hdrop1] at hs1
    obtain ⟨hbf, hm37⟩ := Deserialize.u8ToField_refines ev50.erase; subst m37
    injection hbf with hf
    have hb2 : b = 2 := UInt8.ext ((Deserialize.natCast_eq_ofNat_iff b.toNat_lt (by omega)).mp hf.symm)
    subst hb2
    obtain ⟨ext1, rc, n1, rcVal, s2Ptr, hr_ok, hr_tup, hrRep, hs2⟩ :=
      get_recursor_spec hs1 ev218
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr_tup
    rcases hr_tup with ⟨rfl, rfl⟩; subst he269
    rw [show i + 1 + n1 = i + (1 + n1) by omega] at hr_ok hs2
    refine ⟨ext1, .recr rc, 1 + n1, _, x_s2, ?_, he244, ⟨x_recr, rfl, hrRep⟩, hs2⟩
    unfold Ixon.getMutConst
    simp only [bind, EStateM.bind, hb_ok, Functor.map, EStateM.map, hr_ok]

theorem get_mut_const_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_mut_const_list"
      [x_stream, TagN.u64Value count] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ms : Array Ixon.MutConst) (n : Nat) (listPtr restPtr : SourceValue F),
      Ixon.getArray Ixon.getMutConst count { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ms { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<Ixon::MutConst>» RepMutConst h' ms.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i x_stream r h h' calls with
  | zero =>
    rcases Obs.«IxonDeserialize::get_mut_const_list».obs ev with
      ⟨m2, cs12, m43, ev14, he41, hm51, he62, -⟩ |
      ⟨m2, cs12, m70, cs80, x_mc, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, -⟩
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      have ext := allocNil_extends Obs.Names.«Lists::Node<Ixon::MutConst>» h
      have hs' := L1.Stream.mono ext hs
      rw [he62, hm51]
      refine ⟨ext, #[], 0, (allocNil Obs.Names.«Lists::Node<Ixon::MutConst>» h).1, x_stream,
        by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        he41, allocNil_rep _ _ h, by simpa using hs'⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    rcases Obs.«IxonDeserialize::get_mut_const_list».obs ev with
      ⟨m2, cs12, m43, ev14, -⟩ |
      ⟨m2, cs12, m70, cs80, x_mc, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, ev82, ev138, ev117, he164, hm174, he201, -⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨ext1, mc, n1, mcVal, sPtr, hok1, hmc_tup, hmcRep, hs1⟩ := get_mut_const_spec hs ev82
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hmc_tup
      rcases hmc_tup with ⟨rfl, rfl⟩
      obtain ⟨hsp, hm128⟩ := Deserialize.u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v119 m128
      obtain ⟨ext2, tailMs, n2, tailPtr, s2Ptr, hok2, htail_tup, htailRep, hs2⟩ :=
        ih (by omega) hs1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl⟩
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<Ixon::MutConst>» x_mc x_rest m105
      have consRep := allocCons_rep Obs.Names.«Lists::Node<Ixon::MutConst>»
        repMutConst_heapMono₂ (hmcRep.mono ext2) htailRep
      rw [he201, hm174]
      rw [show i + n1 + n2 = i + (n1 + n2) by omega] at hok2 hs2
      refine ⟨(ext1.trans ext2).trans ext3, #[mc] ++ tailMs, n1 + n2,
        (allocCons Obs.Names.«Lists::Node<Ixon::MutConst>» x_mc x_rest m105).1, x_s2, ?_,
        he164, by simpa using consRep, L1.Stream.mono ext3 hs2⟩
      rw [Ixon.Verify.BoundedConstant.getArray_succ]
      simp [bind, EStateM.bind, hok1, hok2, pure, EStateM.pure]

theorem get_constant_info_by_variant_spec {v : UInt64} (hv_lt : v.toNat < 256)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constant_info_by_variant"
      [.field ((v.toNat : Nat) : F), x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ci : Ixon.ConstantInfo) (n : Nat) (ciVal restPtr : SourceValue F),
      Ixon.Verify.Codec.Constant.getInfoFromTag ⟨Ixon.Constant.FLAG, v⟩
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ci { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [ciVal, restPtr] ∧
      RepConstantInfo h' ci ciVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  rcases Obs.«IxonDeserialize::get_constant_info_by_variant».obs ev with
    ⟨m16, cs26, x_defn, x_s, hv14, ev28, he54, he79, -⟩ |
    ⟨m87, cs97, x_recr, x_s, -, hv85, ev99, he125, he150, -⟩ |
    ⟨m158, cs168, x_axim, x_s, -, -, hv156, ev170, he196, he221, -⟩ |
    ⟨m229, cs239, x_quot, x_s, -, -, -, hv227, ev241, he267, he292, -⟩ |
    ⟨m300, cs310, x_prj, x_s, -, -, -, -, hv298, ev312, he338, he363, -⟩ |
    ⟨m371, cs381, x_prj, x_s, -, -, -, -, -, hv369, ev383, he409, he434, -⟩ |
    ⟨m442, cs452, x_prj, x_s, -, -, -, -, -, -, hv440, ev454, he480, he505, -⟩ |
    ⟨m513, cs523, x_prj, x_s, -, -, -, -, -, -, -, hv511, ev525, he551, he576, -⟩
  · injection hv14 with hf
    have hveq : v = 0 := UInt64.ext ((Deserialize.natCast_eq_zero_iff hv_lt).mp hf)
    subst hveq
    obtain ⟨ext1, d, n, dVal, sPtr, hok, htup, hrep, hs1⟩ := get_definition_spec hs ev28
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he79
    refine ⟨ext1, .defn d, n, _, x_s, ?_, he54, ⟨x_defn, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv85 with hf
    have hveq : v = 1 := UInt64.ext ((Deserialize.natCast_eq_one_iff hv_lt).mp hf)
    subst hveq
    obtain ⟨ext1, rc, n, rcVal, sPtr, hok, htup, hrep, hs1⟩ := get_recursor_spec hs ev99
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he150
    refine ⟨ext1, .recr rc, n, _, x_s, ?_, he125, ⟨x_recr, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv156 with hf
    have hveq : v = 2 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, a, n, aVal, sPtr, hok, htup, hrep, hs1⟩ := get_axiom_spec hs ev170
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he221
    refine ⟨ext1, .axio a, n, _, x_s, ?_, he196, ⟨x_axim, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv227 with hf
    have hveq : v = 3 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, q, n, qVal, sPtr, hok, htup, hrep, hs1⟩ := get_quotient_spec hs ev241
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he292
    refine ⟨ext1, .quot q, n, _, x_s, ?_, he267, ⟨x_quot, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv298 with hf
    have hveq : v = 4 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, p, n, pVal, sPtr, hok, htup, hrep, hs1⟩ := get_constructor_proj_spec hs ev312
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he363
    refine ⟨ext1, .cPrj p, n, _, x_s, ?_, he338, ⟨x_prj, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv369 with hf
    have hveq : v = 5 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, p, n, pVal, sPtr, hok, htup, hrep, hs1⟩ := get_recursor_proj_spec hs ev383
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he434
    refine ⟨ext1, .rPrj p, n, _, x_s, ?_, he409, ⟨x_prj, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv440 with hf
    have hveq : v = 6 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, p, n, pVal, sPtr, hok, htup, hrep, hs1⟩ := get_inductive_proj_spec hs ev454
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he505
    refine ⟨ext1, .iPrj p, n, _, x_s, ?_, he480, ⟨x_prj, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]
  · injection hv511 with hf
    have hveq : v = 7 := UInt64.ext ((Deserialize.natCast_eq_ofNat_iff hv_lt (by omega)).mp hf)
    subst hveq
    obtain ⟨ext1, p, n, pVal, sPtr, hok, htup, hrep, hs1⟩ := get_definition_proj_spec hs ev525
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he576
    refine ⟨ext1, .dPrj p, n, _, x_s, ?_, he551, ⟨x_prj, rfl, hrep⟩, hs1⟩
    simp [Ixon.Verify.Codec.Constant.getInfoFromTag, Ixon.Constant.FLAG, Ixon.Constant.FLAG_MUTS,
      Functor.map, EStateM.map, hok]

theorem get_constant_info_spec {t : Ixon.TagN} {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constant_info"
      [.field ((t.flag.toNat : Nat) : F), TagN.u64Value t.value.toNat, x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (ci : Ixon.ConstantInfo) (n : Nat) (ciVal restPtr : SourceValue F),
      Ixon.Verify.Codec.Constant.getInfoFromTag t { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok ci { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [ciVal, restPtr] ∧
      RepConstantInfo h' ci ciVal ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  rcases Obs.«IxonDeserialize::get_constant_info».obs ev with
    ⟨m16, cs26, x_mutuals, x_s, hv14, ev28, he62, he87, -⟩ |
    ⟨w106, x_sz1, x_sz2, x_sz3, x_sz4, x_sz5, x_sz6, x_sz7, v158, m161,
      x166, y167, m168, x174, y175, m176, x182, y183, m184, x190, y191, m192,
      x198, y199, m200, x206, y207, m208, cs217, cs231, cs245, cs259, cs273, cs287, cs301, cs322,
      v325, m328, cs336, v339,
      -, hv93, hv104, ev219, ev233, op213, ev247, op205, ev261, op197, ev275, op189,
      ev289, op181, ev303, op173, heq318, pr348, ev338, ev324, -⟩
  · injection hv14 with hf
    have hfl : t.flag = 12 :=
      UInt8.ext ((Deserialize.natCast_eq_ofNat_iff t.flag.toNat_lt (by omega)).mp hf)
    obtain ⟨ext1, ms, n, msPtr, sPtr, hok, htup, hrep, hs1⟩ :=
      get_mut_const_list_spec t.value.toNat t.value.toNat_lt hs ev28
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
    rcases htup with ⟨rfl, rfl⟩; subst he87
    refine ⟨ext1, .muts ms, n, _, x_s, ?_, he62, ⟨x_mutuals, rfl, hrep⟩, hs1⟩
    have hmut : (t.flag == Ixon.Constant.FLAG_MUTS) = true := by
      rw [hfl]; decide
    unfold Ixon.Verify.Codec.Constant.getInfoFromTag
    rw [ite_eq_left hmut]
    simpa [Ixon.Verify.Codec.ConstantTables.getMany_eq_getArray] using
      (show (EStateM.bind (Ixon.getArray Ixon.getMutConst t.value.toNat)
          (fun ms => EStateM.pure (Ixon.ConstantInfo.muts ms)))
          { idx := i, bytes := ⟨bytes.toArray⟩ } = _ by
        simp only [EStateM.bind, hok, EStateM.pure])
  · injection hv93 with hf
    have hfl : t.flag = 13 :=
      UInt8.ext ((Deserialize.natCast_eq_ofNat_iff t.flag.toNat_lt (by omega)).mp hf)
    have hsz_tup : TagN.u64Value t.value.toNat =
        .tuple [w106, x_sz1, x_sz2, x_sz3, x_sz4, x_sz5, x_sz6, x_sz7] := hv104
    dsimp only [TagN.u64Value] at hsz_tup
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hsz_tup
    rcases hsz_tup with ⟨hw0, hsz1, hsz2, hsz3, hsz4, hsz5, hsz6, hsz7⟩
    obtain ⟨hx206, hm208⟩ := Deserialize.u8ToField_refines ev219.erase
    obtain ⟨hy207, hm200⟩ := Deserialize.u8ToField_refines ev233.erase
    obtain ⟨hy199, hm192⟩ := Deserialize.u8ToField_refines ev247.erase
    obtain ⟨hy191, hm184⟩ := Deserialize.u8ToField_refines ev261.erase
    obtain ⟨hy183, hm176⟩ := Deserialize.u8ToField_refines ev275.erase
    obtain ⟨hy175, hm168⟩ := Deserialize.u8ToField_refines ev289.erase
    obtain ⟨hy167, hm161⟩ := Deserialize.u8ToField_refines ev303.erase
    subst m208 m200 m192 m184 m176 m168 m161
    rw [hx206, ← hsz1, hy207, ← hsz2, evalBinOp_add_natCast, Except.ok.injEq] at op213
    rw [← op213, hy199, ← hsz3, evalBinOp_add_natCast, Except.ok.injEq] at op205
    rw [← op205, hy191, ← hsz4, evalBinOp_add_natCast, Except.ok.injEq] at op197
    rw [← op197, hy183, ← hsz5, evalBinOp_add_natCast, Except.ok.injEq] at op189
    rw [← op189, hy175, ← hsz6, evalBinOp_add_natCast, Except.ok.injEq] at op181
    rw [← op181, hy167, ← hsz7, evalBinOp_add_natCast, Except.ok.injEq] at op173
    rw [← op173] at heq318
    set s1 := t.value.toNat / 256 % 256
    set s2 := t.value.toNat / 65536 % 256
    set s3 := t.value.toNat / 16777216 % 256
    set s4 := t.value.toNat / 4294967296 % 256
    set s5 := t.value.toNat / 1099511627776 % 256
    set s6 := t.value.toNat / 281474976710656 % 256
    set s7 := t.value.toNat / 72057594037927936 % 256
    have hhi0 : s1 + s2 + s3 + s4 + s5 + s6 + s7 = 0 := by
      injection heq318 with hsum
      have hval := congrArg ZMod.val hsum
      rw [Deserialize.zmod_val_natCast_of_lt (by omega)] at hval
      simpa using hval
    have hv_lt256 : t.value.toNat < 256 := by
      have hlt := t.value.toNat_lt
      omega
    dsimp only [TagN.u64Value] at pr348
    simp only [projectValue, Except.ok.injEq] at pr348
    obtain ⟨hv325, hm328⟩ := Deserialize.u8ToField_refines ev338.erase
    subst m328
    have hv325_eq : v325 = .field ((t.value.toNat : Nat) : F) := by
      rw [hv325, ← pr348, Nat.mod_eq_of_lt hv_lt256]
    rw [hv325_eq] at ev324
    obtain ⟨ext1, ci, n, ciVal, sPtr, hok, htup, hrep, hs1⟩ :=
      get_constant_info_by_variant_spec hv_lt256 hs ev324
    have htag_eq : t = ⟨Ixon.Constant.FLAG, t.value⟩ := by
      cases t with
      | mk fl vl =>
        dsimp only at hfl ⊢
        rw [hfl]
        rfl
    rw [htag_eq]
    exact ⟨ext1, ci, n, ciVal, sPtr, hok, htup, hrep, hs1⟩

/-! ## Side tables (`get_address_list`, `get_refs`, `get_univs`), `max_lvls`, and `get_constant` -/

theorem get_address_list_spec (count : Nat) (hcount : count < 18446744073709551616)
    {bytes : List UInt8} {i : Nat} {x_stream r : SourceValue F} {h h' : Heap F}
    {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_address_list"
      [x_stream, TagN.u64Value count] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (addrs : Array _root_.Address) (n : Nat) (listPtr restPtr : SourceValue F),
      addrs.size = count ∧
      Ixon.getArray (Ixon.Serialize.get : Ixon.GetM _root_.Address) count
        { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok addrs { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h' addrs.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  induction count generalizing i x_stream r h h' calls with
  | zero =>
    rcases Obs.«IxonDeserialize::get_address_list».obs ev with
      ⟨m2, cs12, m43, ev14, he41, hm51, he62, -⟩ |
      ⟨m2, cs12, m70, cs80, x_addr, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, -⟩
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      have ext := allocNil_extends Obs.Names.«Lists::Node<&[Field; 32]>» h
      have hs' := L1.Stream.mono ext hs
      rw [he62, hm51]
      refine ⟨ext, #[], 0, (allocNil Obs.Names.«Lists::Node<&[Field; 32]>» h).1, x_stream,
        rfl, by simp [Ixon.Verify.BoundedConstant.getArray_zero, pure, EStateM.pure],
        he41, allocNil_rep _ _ h, by simpa using hs'⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
  | succ count ih =>
    rcases Obs.«IxonDeserialize::get_address_list».obs ev with
      ⟨m2, cs12, m43, ev14, -⟩ |
      ⟨m2, cs12, m70, cs80, x_addr, x_s, m105, cs115, v119, m128, cs136, x_rest, x_s2, m166,
        ev14, ev82, ev138, ev117, he164, hm174, he201, -⟩
    · obtain ⟨hiz, _⟩ := Deserialize.u64IsZero_refines hcount ev14.erase; simp at hiz
    · obtain ⟨_, hm2⟩ := Deserialize.u64IsZero_refines hcount ev14.erase
      subst m2
      obtain ⟨ext1, hlen, addrPtr, sPtr, haddr_tup, haddrRep, hs1⟩ :=
        Deserialize.getAddress_refines hs ev82.erase
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at haddr_tup
      rcases haddr_tup with ⟨rfl, rfl⟩
      rw [List.drop_drop] at hs1
      have haddr_ok := getAddress_of_drop hlen
      obtain ⟨hsp, hm128⟩ := Deserialize.u64SaturatingPred_refines hcount ev138.erase
      simp only [Nat.add_sub_cancel] at hsp
      subst v119 m128
      obtain ⟨ext2, tailAddrs, n2, tailPtr, s2Ptr, hsz2, hok2, htail_tup, htailRep, hs2⟩ :=
        ih (by omega) hs1 ev117
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htail_tup
      rcases htail_tup with ⟨rfl, rfl⟩
      let headAddr := ixAddr (Deserialize.takeAddress (bytes.drop i) hlen)
      have hheadRep : RepAddrElem m70 headAddr x_addr :=
        ⟨Deserialize.takeAddress (bytes.drop i) hlen, haddrRep, rfl⟩
      have ext3 := allocCons_extends Obs.Names.«Lists::Node<&[Field; 32]>» x_addr x_rest m105
      have consRep := allocCons_rep Obs.Names.«Lists::Node<&[Field; 32]>»
        repAddrElem_heapMono₂ (S0.addr_mono ext2 hheadRep) htailRep
      rw [he201, hm174]
      rw [show i + 32 + n2 = i + (32 + n2) by omega] at hok2 hs2
      refine ⟨(ext1.trans ext2).trans ext3, #[headAddr] ++ tailAddrs, 32 + n2,
        (allocCons Obs.Names.«Lists::Node<&[Field; 32]>» x_addr x_rest m105).1, x_s2,
        by simp [hsz2]; omega, ?_, he164, by simpa using consRep, L1.Stream.mono ext3 hs2⟩
      rw [Ixon.Verify.BoundedConstant.getArray_succ]
      simp [bind, EStateM.bind, haddr_ok, hok2, pure, EStateM.pure]

theorem get_refs_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_refs" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (addrs : Array _root_.Address) (n1 n2 : Nat)
      (listPtr restPtr : SourceValue F),
      addrs.size = t.value.toNat ∧
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } ∧
      Ixon.getArray (Ixon.Serialize.get : Ixon.GetM _root_.Address) t.value.toNat
        { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
        .ok addrs { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h' addrs.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n1 + n2)) restPtr := by
  obtain ⟨m2, cs12, x_len, x_s, cs39, ev14, ev41, -⟩ := Obs.«IxonDeserialize::get_refs».obs ev
  obtain ⟨hm2, t, n1, sPtr, _, _, ht_ok, _, hs1, ht_tup⟩ := getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht_tup
  rcases ht_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨ext1, addrs, n2, listPtr, restPtr, hsz, hok2, htup2, hrep, hs2⟩ :=
    get_address_list_spec t.value.toNat t.value.toNat_lt hs1 ev41
  exact ⟨ext1, t, addrs, n1, n2, listPtr, restPtr, hsz, ht_ok, hok2, htup2, hrep, hs2⟩

theorem get_univs_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_univs" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (t : Ixon.TagN) (univs : Array Ixon.Univ) (n1 n2 : Nat)
      (listPtr restPtr : SourceValue F),
      univs.size = t.value.toNat ∧
      Ixon.getTagN 0 { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok t { idx := i + n1, bytes := ⟨bytes.toArray⟩ } ∧
      Ixon.getArray Ixon.getUniv t.value.toNat
        { idx := i + n1, bytes := ⟨bytes.toArray⟩ } =
        .ok univs { idx := i + n1 + n2, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [listPtr, restPtr] ∧
      RepList Deserialize.univListEnum Deserialize.RepUnivPtr h' univs.toList listPtr ∧
      L1.Stream h' (bytes.drop (i + n1 + n2)) restPtr := by
  obtain ⟨m2, cs12, x_len, x_s, cs39, ev14, ev41, -⟩ := Obs.«IxonDeserialize::get_univs».obs ev
  obtain ⟨hm2, t, n1, sPtr, _, _, ht_ok, _, hs1, ht_tup⟩ := getTagN0_progress hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at ht_tup
  rcases ht_tup with ⟨rfl, rfl⟩; subst m2
  obtain ⟨ext1, univList, n2, listPtr, restPtr, hok2, hlen, htup2, hrep, hs2⟩ :=
    Deserialize.getUnivList_refines_at t.value.toNat t.value.toNat_lt hs1 ev41.erase
  have harr := getUnivChildren_to_getArray t.value.toNat hok2
  exact ⟨ext1, t, univList.toArray, n1, n2, listPtr, restPtr,
    by simp [hlen], ht_ok, harr, htup2, by simpa using hrep, hs2⟩

private theorem repList_nil_of_load {enumName : String} {R : Heap F → α → SourceValue F → Prop}
    {h : Heap F} {xs : List α} {ptr : SourceValue F}
    (hrep : RepList enumName R h xs ptr)
    (hld : loadValue h ptr = .ok (.construct enumName "Nil" [])) :
    xs = [] := by
  cases hrep with
  | nil _ => rfl
  | @cons _ _ n _ _ cell _ _ =>
    have h1 : loadValue h (.ptr (.enum enumName) n) = .ok _ := by
      simp [loadValue, cell, bind, Except.bind, pure, Except.pure, Value.type]
    have heq := Except.ok.inj (h1.symm.trans hld)
    cases heq

private theorem array_eq_empty_of_toList_nil {α : Type} {a : Array α} (h : a.toList = []) :
    a = #[] := by
  cases a with
  | mk l =>
    dsimp only at h
    subst h
    rfl

theorem assert_prj_empty_tables_spec {ci : Ixon.ConstantInfo}
    {sharing : Array Ixon.Expr} {refs : Array _root_.Address}
    {univs : Array Ixon.Univ} {binders : Array Ixon.BinderBlock}
    {x_info x_sharing x_refs x_univs x_binders r : SourceValue F}
    {h h' : Heap F} {calls : List (Obs.Call F)}
    (hinfo : RepConstantInfo h ci x_info)
    (hsh : Deserialize.RepShareVec h sharing.toList x_sharing)
    (hrefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs.toList x_refs)
    (hunivs : RepList Deserialize.univListEnum Deserialize.RepUnivPtr h univs.toList x_univs)
    (hbinders : RepList Deserialize.binderBlockListEnum Deserialize.RepBinderBlock h
      binders.toList x_binders)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::assert_prj_empty_tables"
      [x_info, x_sharing, x_refs, x_univs, x_binders] h r h' calls) :
    h' = h ∧
    (match ci with
     | .dPrj _ | .iPrj _ | .cPrj _ | .rPrj _ =>
         sharing = #[] ∧ refs = #[] ∧ univs = #[] ∧ binders = #[]
     | _ => True) := by
  rcases Obs.«IxonDeserialize::assert_prj_empty_tables».obs ev with
    ⟨w17, hv15, ld33, ld48, ld63, ld78, -, he86, -⟩ |
    ⟨w95, -, hv93, ld111, ld126, ld141, ld156, -, he164, -⟩ |
    ⟨w173, -, -, hv171, ld189, ld204, ld219, ld234, -, he242, -⟩ |
    ⟨w251, -, -, -, hv249, ld267, ld282, ld297, ld312, -, he320, -⟩ |
    ⟨x_members, -, -, -, -, hv327, _, _, -, he371, -⟩ |
    ⟨x_members, w380, w381, -, -, -, -, hv327, _, -, he395, -⟩ |
    ⟨hne88, hne166, hne244, hne322, hne398, -, he405, -⟩
  · have empty4 : sharing = #[] ∧ refs = #[] ∧ univs = #[] ∧ binders = #[] :=
      ⟨array_eq_empty_of_toList_nil (repList_nil_of_load hsh ld33),
       array_eq_empty_of_toList_nil (repList_nil_of_load hrefs ld48),
       array_eq_empty_of_toList_nil (repList_nil_of_load hunivs ld63),
       array_eq_empty_of_toList_nil (repList_nil_of_load hbinders ld78)⟩
    refine ⟨he86, ?_⟩
    cases ci <;> first | exact empty4 | trivial
  · have empty4 : sharing = #[] ∧ refs = #[] ∧ univs = #[] ∧ binders = #[] :=
      ⟨array_eq_empty_of_toList_nil (repList_nil_of_load hsh ld111),
       array_eq_empty_of_toList_nil (repList_nil_of_load hrefs ld126),
       array_eq_empty_of_toList_nil (repList_nil_of_load hunivs ld141),
       array_eq_empty_of_toList_nil (repList_nil_of_load hbinders ld156)⟩
    refine ⟨he164, ?_⟩
    cases ci <;> first | exact empty4 | trivial
  · have empty4 : sharing = #[] ∧ refs = #[] ∧ univs = #[] ∧ binders = #[] :=
      ⟨array_eq_empty_of_toList_nil (repList_nil_of_load hsh ld189),
       array_eq_empty_of_toList_nil (repList_nil_of_load hrefs ld204),
       array_eq_empty_of_toList_nil (repList_nil_of_load hunivs ld219),
       array_eq_empty_of_toList_nil (repList_nil_of_load hbinders ld234)⟩
    refine ⟨he242, ?_⟩
    cases ci <;> first | exact empty4 | trivial
  · have empty4 : sharing = #[] ∧ refs = #[] ∧ univs = #[] ∧ binders = #[] :=
      ⟨array_eq_empty_of_toList_nil (repList_nil_of_load hsh ld267),
       array_eq_empty_of_toList_nil (repList_nil_of_load hrefs ld282),
       array_eq_empty_of_toList_nil (repList_nil_of_load hunivs ld297),
       array_eq_empty_of_toList_nil (repList_nil_of_load hbinders ld312)⟩
    refine ⟨he320, ?_⟩
    cases ci <;> first | exact empty4 | trivial
  · refine ⟨he371, ?_⟩
    cases ci with
    | dPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | iPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | cPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | rPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | _ => trivial
  · refine ⟨he395, ?_⟩
    cases ci with
    | dPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | iPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | cPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | rPrj p => obtain ⟨pv, hv, -⟩ := hinfo; rw [hv] at hv327; cases hv327
    | _ => trivial
  · refine ⟨he405, ?_⟩
    cases ci with
    | dPrj p => obtain ⟨pv, hv, -⟩ := hinfo; exact (hne88 [pv] rfl hv).elim
    | iPrj p => obtain ⟨pv, hv, -⟩ := hinfo; exact (hne166 [pv] rfl hv).elim
    | cPrj p => obtain ⟨pv, hv, -⟩ := hinfo; exact (hne244 [pv] rfl hv).elim
    | rPrj p => obtain ⟨pv, hv, -⟩ := hinfo; exact (hne322 [pv] rfl hv).elim
    | _ => trivial

/-- **Every observed derivation of `IxonDeserialize::get_constant` at reader offset `i`** refines
`Ixon.getConstant` at `i`, producing a `RepConstant` value with `ConstantWireFacts`. -/
theorem get_constant_spec {bytes : List UInt8} {i : Nat}
    {x_stream r : SourceValue F} {h h' : Heap F} {calls : List (Obs.Call F)}
    (hs : L1.Stream h (bytes.drop i) x_stream)
    (ev : Obs.ObsFn Obs.W "IxonDeserialize::get_constant" [x_stream] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (c : Ixon.Constant) (n : Nat) (cVal restPtr : SourceValue F),
      Ixon.getConstant { idx := i, bytes := ⟨bytes.toArray⟩ } =
        .ok c { idx := i + n, bytes := ⟨bytes.toArray⟩ } ∧
      r = .tuple [cVal, restPtr] ∧
      RepConstant h' c cVal ∧
      ConstantWireFacts c ∧
      L1.Stream h' (bytes.drop (i + n)) restPtr := by
  obtain ⟨m2, cs12, x_s, x_flag, x_size, m59, cs69, x_info, x_s2, m110, cs120, x_sharing, x_s3,
    m145, cs155, x_refs, x_s4, m180, cs190, x_univs, x_s5, m215, cs225, v229, m238, cs246,
    x_binders, x_s6, v270, m271, cs281,
    ev14, ev71, ev122, ev157, ev192, ev248, ev227, ev283, he328, he385, -⟩ :=
    Obs.«IxonDeserialize::get_constant».obs ev
  obtain ⟨hm2, tag4, n0, sPtr, htag4_ok, hs1, htag4_tup⟩ := TagN.getTagN4_refines_at hs ev14.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htag4_tup
  rcases htag4_tup with ⟨⟨rfl, rfl⟩, rfl⟩; subst m2
  obtain ⟨ext_info, ci, n1, ciVal, s2Ptr, hci_ok, hci_tup, hciRep, hs2⟩ :=
    get_constant_info_spec hs1 ev71
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hci_tup
  rcases hci_tup with ⟨rfl, rfl⟩
  rw [show i + n0 + n1 = i + (n0 + n1) by omega] at hci_ok hs2
  have hinfo_ok : Ixon.getConstantInfo { idx := i, bytes := ⟨bytes.toArray⟩ } =
      .ok ci { idx := i + (n0 + n1), bytes := ⟨bytes.toArray⟩ } := by
    rw [Ixon.Verify.Codec.Constant.getConstantInfo_eq]
    simp only [bind, EStateM.bind, htag4_ok, hci_ok]
  obtain ⟨ext_sh, shTag, n2a, n2b, shList, shPtr, s3Ptr, hshTag_ok, _, hshList_ok, hshLen,
    hsh_tup, hshRep, hs3⟩ := Deserialize.getSharing_refines_at hs2 ev122.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hsh_tup
  rcases hsh_tup with ⟨rfl, rfl⟩
  have hshArr_ok := getExprChildren_to_getArray shTag.value.toNat hshList_ok
  rw [show i + (n0 + n1) + n2a + n2b = i + (n0 + n1 + n2a + n2b) by omega] at hshArr_ok hs3
  obtain ⟨ext_refs, refsTag, refsArr, n3a, n3b, refsPtr, s4Ptr, hrefsSz, hrefsTag_ok, hrefsArr_ok,
    hrefs_tup, hrefsRep, hs4⟩ := get_refs_spec hs3 ev157
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hrefs_tup
  rcases hrefs_tup with ⟨rfl, rfl⟩
  rw [show i + (n0 + n1 + n2a + n2b) + n3a + n3b =
    i + (n0 + n1 + n2a + n2b + n3a + n3b) by omega] at hrefsArr_ok hs4
  obtain ⟨ext_univs, univsTag, univsArr, n4a, n4b, univsPtr, s5Ptr, hunivsSz, hunivsTag_ok,
    hunivsArr_ok, hunivs_tup, hunivsRep, hs5⟩ := get_univs_spec hs4 ev192
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hunivs_tup
  rcases hunivs_tup with ⟨rfl, rfl⟩
  rw [show i + (n0 + n1 + n2a + n2b + n3a + n3b) + n4a + n4b =
    i + (n0 + n1 + n2a + n2b + n3a + n3b + n4a + n4b) by omega] at hunivsArr_ok hs5
  have ext_max := ev248.heap_extends
  have hs5' := L1.Stream.mono ext_max hs5
  obtain ⟨ext_binders, bindersArr, n5, bindersPtr, s6Ptr, hbinders_ok, hbinders_tup,
    hbindersRep, hs6⟩ := Deserialize.getBinders_refines_at hs5' ev227.erase
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hbinders_tup
  rcases hbinders_tup with ⟨rfl, rfl⟩
  rw [show i + (n0 + n1 + n2a + n2b + n3a + n3b + n4a + n4b) + n5 =
    i + (n0 + n1 + n2a + n2b + n3a + n3b + n4a + n4b + n5) by omega] at hbinders_ok hs6
  have ext_after_info := (((ext_sh.trans ext_refs).trans ext_univs).trans ext_max).trans ext_binders
  have ext_after_sh := ((ext_refs.trans ext_univs).trans ext_max).trans ext_binders
  have ext_after_refs := (ext_univs.trans ext_max).trans ext_binders
  have ext_after_univs := ext_max.trans ext_binders
  have hciRep' := hciRep.mono ext_after_info
  have hshRep' : Deserialize.RepShareVec m215 shList.toArray.toList x_sharing := by
    simpa using hshRep.mono ext_after_sh
  have hrefsRep' := repList_heapMono₂ _ repAddrElem_heapMono₂ ext_after_refs hrefsRep
  have hunivsRep' := repList_heapMono₂ _ Deserialize.repUnivPtr_heapMono₂ ext_after_univs hunivsRep
  obtain ⟨hm271, hprj⟩ := assert_prj_empty_tables_spec
    hciRep' hshRep' hrefsRep' hunivsRep' hbindersRep ev283
  subst m271 he385
  refine ⟨ext_info.trans ext_after_info,
    ⟨ci, shList.toArray, refsArr, univsArr, bindersArr⟩,
    n0 + n1 + n2a + n2b + n3a + n3b + n4a + n4b + n5, _, x_s6, ?_, he328,
    ⟨x_info, x_sharing, x_refs, x_univs, x_binders, rfl,
      hciRep', hshRep', hrefsRep', hunivsRep', hbindersRep⟩,
    ⟨by simp [hshLen, shTag.value.toNat_lt],
     by rw [hrefsSz]; exact refsTag.value.toNat_lt,
     by rw [hunivsSz]; exact univsTag.value.toNat_lt,
     hprj⟩, hs6⟩
  unfold Ixon.getConstant Ixon.getConstantWithUnivs
  simp only [bind, EStateM.bind, hinfo_ok, hshTag_ok, hshArr_ok, hrefsTag_ok, hrefsArr_ok,
    hunivsTag_ok, hunivsArr_ok, hbinders_ok, pure, EStateM.pure]

/-! ## Top-level `Ingress::load_verified_constant` refinement -/

/-- **`Ingress::load_verified_constant` on a represented address (`S0.addr`)** hashes raw bytes
whose BLAKE3 digest is `addr`, decodes them to `c : Ixon.Constant` (`Ixon.deConstant = .ok c` and
`Ixon.deConstantExact = .ok c`), and returns a `RepConstant` value with `ConstantWireFacts c`. -/
theorem load_verified_constant_de {addr : _root_.Address} {ap r : SourceValue F}
    {h h' : Heap F} {calls : List (Obs.Call F)}
    (ha : S0.addr h ap addr)
    (ev : Obs.ObsFn Obs.W "Ingress::load_verified_constant" [ap] h r h' calls) :
    Heap.Extends h h' ∧
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = addr ∧
      Ixon.deConstant rawBytes = .ok c ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      RepConstant h' c r ∧
      ConstantWireFacts c := by
  obtain ⟨aVec, haRep, rfl⟩ := ha
  obtain ⟨bytes, inp, rest, m, cs', ext1, hst, hashed, hdigest, hget, hrest, -⟩ :=
    L1.load_verified_constant_addr haRep ev
  obtain ⟨ext2, c, n, cVal, restPtr, hok, htup, hcRep, hwf, hs_rest⟩ :=
    get_constant_spec (i := 0) (by simpa using hst) hget
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  rcases htup with ⟨rfl, rfl⟩
  simp only [Nat.zero_add] at hok hs_rest
  obtain ⟨hnil, -⟩ | ⟨_, _, _, _, hbad, -⟩ := L1.stream_inv hs_rest hrest
  · have hlen_le : bytes.length ≤ n := List.drop_eq_nil_iff.mp hnil
    have hsp := Ixon.Verify.ConstantBounds.getConstant_bound
      { idx := 0, bytes := ⟨bytes.toArray⟩ } { idx := n, bytes := ⟨bytes.toArray⟩ } c
      (Nat.zero_le _) hok
    have hn_le : n ≤ bytes.length := by
      have hw := hsp.within
      change n ≤ bytes.toArray.size at hw
      rw [List.size_toArray] at hw
      exact hw
    have hn_eq : n = (ByteArray.mk bytes.toArray).size := by
      change n = bytes.toArray.size
      rw [List.size_toArray]
      omega
    have hde : Ixon.deConstant ⟨bytes.toArray⟩ = .ok c := by
      unfold Ixon.deConstant Ixon.runGet
      change (match Ixon.getConstant { idx := 0, bytes := ⟨bytes.toArray⟩ } with
        | .ok x _ => Except.ok x
        | .error msg _ => Except.error msg) = .ok c
      rw [hok]
    have hdeExact : Ixon.deConstantExact ⟨bytes.toArray⟩ = .ok c := by
      unfold Ixon.deConstantExact Ixon.runGetExact
      change (match Ixon.getConstant { idx := 0, bytes := ⟨bytes.toArray⟩ } with
        | .ok x s' => if s'.idx == (ByteArray.mk bytes.toArray).size then .ok x else .error _
        | .error msg _ => .error msg) = .ok c
      rw [hok]
      simp [hn_eq]
    exact ⟨ext1.trans ext2, ⟨bytes.toArray⟩, c, hashed, hdigest, hde, hdeExact, hcRep, hwf⟩
  · cases hbad

end IxVM.Refinement.Claim
