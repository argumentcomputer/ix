import IxVMRefinement.Guard.Loads
import IxVMRefinement.Core.RawKeyed

/-! # Exact classifier load origins under a fixed global keying

Scoped loading supplies a physical raw root, and the actual raw universe operation instantiates
that root exactly. The original get_ci call and heap are retained for matching the serialized
canonical root. No equality of raw roots from unrelated loads is assumed here.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Decl (RawExprRep)

private theorem level_list_length {ps : List KLevel} {params r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [params] h r h' calls)
    (represented : RepKLevelList h ps params) : r = .field (ps.length : F) ∧ h' = h :=
  ProjAux.levels_length ev ⟨ps, represented, LvEqList.refl ps⟩

/-- A definition-value invocation supplies its exact physical raw value and arity, together
with the actual load and universe-substitution subcalls that produced the result. -/
theorem definition_value_keyed_raw_origin (rawKey : _root_.Address → KKey)
    [∀ a, Resolved (rawKey a)] {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : Bytes.Address} {ps : List KLevel} {ap params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (resolved : c.κ (ixAddr a) ≠ unresolvedKey) (parameters : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::definition_value" [ap, params] h r h' cs) :
    ∃ (cv : Ix.Kernel.ConstantVal .anon) (V R : KExpr) (hint : Ix.Kernel.ReducibilityHint)
      (ptr nl ty value flag hintPtr : SourceValue F) (loaded beforeInst : Heap F)
      (loadCalls instCalls : List (Call F)),
      c.env.find? (c.κ (ixAddr a)) = some (.defnInfo cv V hint) ∧
      ps.length = cv.levelParams.length ∧
      ObsFn W "Ingress::get_ci" [ap] h ptr loaded loadCalls ∧
      (⟨"Ingress::get_ci", [ap], h⟩ : Call F) ∈ cs ∧
      loadValue loaded ptr = .ok (.construct kciEnum "Defn" [nl, ty, value, flag, hintPtr]) ∧
      RawExprRep rawKey loaded 0 R value ∧ Heap.Extends loaded beforeInst ∧
      ObsFn W "KernelGuard::expr_inst_raw" [value, params] beforeInst r h' instCalls ∧
      (∀ cl ∈ loadCalls, cl ∈ cs) ∧ (∀ cl ∈ instCalls, cl ∈ cs) ∧
      RawExprRep rawKey h' 0 (R.instantiateLevelParams (List.range ps.length) ps) r := by
  match Obs.«KernelGuard::definition_value».obs ev with
  | .run (m2 := loaded) (p9 := ptr) (cs15 := loadCalls)
      (x_nl := nl) (w29 := ty) (x_value := value) (w30 := flag) (w31 := hintPtr)
      (m71 := beforeInst) (cs101 := instCalls) (ev17 := load) (ld11 := shape)
      (ev81 := length) (heq97 := arity) (ev103 := inst) (hc120 := events) .. =>
    have loadInside : ∀ cl ∈ loadCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have instInside : ∀ cl ∈ instCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have allowed : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [events]; simp)
    obtain ⟨ci, found, actual, loadedValue, represented⟩ :=
      get_ci_step c hc load ap a rfl allowed resolved (hg.sub loadInside) ha
    rw [shape] at loadedValue
    have same := Except.ok.inj loadedValue
    subst actual
    obtain ⟨cv, V, hint, rfl, valRep, bodyRep⟩ := CIRep.defn_inv represented
    obtain ⟨R, raw⟩ := RawExprRep.ofOpenTm_keyed rawKey (bodyRep 0 (fun _ => default))
    have psLoaded := parameters.mono load.heap_extends
    obtain ⟨lengthValue, _⟩ := level_list_length length psLoaded
    have psBound : ps.length < 549755813888 := by
      have bound := RomBound.bounded_length_lt hg.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [params], loaded⟩)
        (p := params) (by rw [events]; simp) (by simp) psLoaded
      simpa using bound
    have levelsBound : cv.levelParams.length < 4294967296 := valRep.2.1
    rw [lengthValue, valRep.1] at arity
    have arityExact : ps.length = cv.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj arity)
    exact ⟨cv, V, R, hint, ptr, nl, ty, value, flag, hintPtr, loaded, beforeInst,
      loadCalls, instCalls, found, arityExact, load, (by rw [events]; simp), shape, raw, length.heap_extends,
      inst, loadInside, instInside,
      (raw.mono length.heap_extends).instLevels
        (psLoaded.mono length.heap_extends) inst⟩

/-- Declared-type classification retains the actual root pointer and exact positional universe
substitution for every loaded constant kind. -/
theorem declared_type_keyed_raw_origin (rawKey : _root_.Address → KKey)
    [∀ a, Resolved (rawKey a)] {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {a : Bytes.Address} {ps : List KLevel} {ap params r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hg : CoreGood c cs) (ha : Bytes.RepAddressRef addrTy h a ap)
    (resolved : c.κ (ixAddr a) ≠ unresolvedKey) (parameters : RepKLevelList h ps params)
    (ev : ObsFn W "KernelGuard::declared_type" [ap, params] h r h' cs) :
    ∃ (ci : Ix.Kernel.ConstantInfo .anon) (R : KExpr)
      (ptr value typePtr : SourceValue F) (loaded beforeType beforeInst : Heap F)
      (loadCalls typeCalls instCalls : List (Call F)),
      c.env.find? (c.κ (ixAddr a)) = some ci ∧ ps.length = ci.toConstantVal.levelParams.length ∧
      ObsFn W "Ingress::get_ci" [ap] h ptr loaded loadCalls ∧
      (⟨"Ingress::get_ci", [ap], h⟩ : Call F) ∈ cs ∧ loadValue loaded ptr = .ok value ∧
      ObsFn W "KernelInfer::const_type_of" [value] beforeType typePtr beforeInst typeCalls ∧
      RawExprRep rawKey beforeInst 0 R typePtr ∧ Heap.Extends loaded beforeInst ∧
      ObsFn W "KernelGuard::expr_inst_raw" [typePtr, params] beforeInst r h' instCalls ∧
      (∀ cl ∈ loadCalls, cl ∈ cs) ∧ (∀ cl ∈ typeCalls, cl ∈ cs) ∧
      (∀ cl ∈ instCalls, cl ∈ cs) ∧
      RawExprRep rawKey h' 0 (R.instantiateLevelParams (List.range ps.length) ps) r := by
  match Obs.«KernelGuard::declared_type».obs ev with
  | .run (v1 := value) (m2 := loaded) (p9 := ptr) (cs15 := loadCalls)
      (cs68 := countCalls) (cs83 := instCalls) (v86 := typePtr) (m60 := beforeType)
      (m89 := beforeInst) (cs97 := typeCalls) (ev17 := load) (ld11 := shape)
      (ev50 := length) (ev70 := count) (heq79 := arity)
      (ev99 := getType) (ev85 := inst) (hc115 := events) .. =>
    have loadInside : ∀ cl ∈ loadCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have countInside : ∀ cl ∈ countCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have typeInside : ∀ cl ∈ typeCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have instInside : ∀ cl ∈ instCalls, cl ∈ cs := by intro cl member; rw [events]; simp [member]
    have allowed : c.allowed ⟨"Ingress::get_ci", [ap], h⟩ :=
      hg.allAllowed _ (by rw [events]; simp)
    obtain ⟨ci, found, actual, loadedValue, represented⟩ :=
      get_ci_step c hc load ap a rfl allowed resolved (hg.sub loadInside) ha
    rw [shape] at loadedValue
    have same := Except.ok.inj loadedValue
    subst actual
    have psLoaded := parameters.mono load.heap_extends
    obtain ⟨lengthValue, _⟩ := level_list_length length psLoaded
    have countSpec := Registry.induction c (scoped_steps c hc) (.infer .const_num_lvls)
      _ _ _ _ _ count
    obtain ⟨countValue, _⟩ := countSpec value ci rfl (hg.sub countInside)
      (represented.mono length.heap_extends)
    have psBound : ps.length < 549755813888 := by
      have bound := RomBound.bounded_length_lt hg.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [params], loaded⟩)
        (p := params) (by rw [events]; simp) (by simp) psLoaded
      simpa using bound
    obtain ⟨_, _, _, _, _, valRep⟩ := represented.head
    have levelsBound : ci.toConstantVal.levelParams.length < 4294967296 := valRep.2.1
    rw [lengthValue, countValue] at arity
    have arityExact : ps.length = ci.toConstantVal.levelParams.length :=
      (NatAux.natCast_inj (by omega) (by omega)).mp (NatAux.field_inj arity)
    have beforeExtension := length.heap_extends.trans count.heap_extends
    have typeSpec := Registry.induction c (scoped_steps c hc) (.infer .const_type_of)
      _ _ _ _ _ getType
    obtain ⟨typeRep, _⟩ := typeSpec value ci rfl (hg.sub typeInside)
      (represented.mono beforeExtension)
    obtain ⟨R, raw⟩ := RawExprRep.ofOpenTm_keyed rawKey (typeRep 0 (fun _ => default))
    have extension := beforeExtension.trans getType.heap_extends
    exact ⟨ci, R, ptr, value, typePtr, loaded, beforeType, beforeInst, loadCalls, typeCalls,
      instCalls, found, arityExact, load, (by rw [events]; simp), shape, getType, raw, extension, inst,
      loadInside, typeInside, instInside, raw.instLevels (psLoaded.mono extension) inst⟩

end IxVM.Refinement.Core.GuardData
