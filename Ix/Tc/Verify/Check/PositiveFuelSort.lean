import Ix.Tc.Verify.Check.BoundedPipelines
import Ix.Tc.Verify.RecursiveMethods.SortInference
import Ix.Tc.Verify.RecursiveMethods.ScopedSortInference
import Ix.Tc.Verify.ScopedSuffix.ClosedContext

/-!
# Positive-fuel bounded checker witness

This fixture instantiates the corrected C1A/K3 interfaces at recursion fuel
one.  Its method-call domain contains exactly one closed sort inference; its
finite result footprint contains that source and its successor-sort result.
The joint suffix model remains an explicit semantic parameter, but the call
schedule, syntax, reduction of collision freedom to two exact digest
inequalities, strong inference upgrade, and checker pipeline resources are
all concrete.
-/

namespace Ix.Tc.PositiveFuelSort

def sourceUniv : KUniv .anon := KUniv.mkZero
def resultUniv : KUniv .anon := KUniv.mkSucc sourceUniv
def source : KExpr .anon := KExpr.mkSort sourceUniv
def result : KExpr .anon := KExpr.mkSort resultUniv

/-- The two concrete expressions and their two universe roots are the entire
finite result/collision footprint. -/
def support : RunSupport where
  expr := fun candidate => candidate = source ∨ candidate = result
  exprFinite :=
    FiniteSupport.union (FiniteSupport.singleton source)
      (FiniteSupport.singleton result)
  univ := fun candidate => candidate = sourceUniv ∨ candidate = resultUniv
  univFinite :=
    FiniteSupport.union (FiniteSupport.singleton sourceUniv)
      (FiniteSupport.singleton resultUniv)

/-- The only cryptographic premise in the concrete fixture: the two exact
expression digests and the two exact universe digests do not collide.  It is
kept explicit because Lean's build-time evaluator cannot execute the Blake3
FFI; production parity can discharge these two byte comparisons separately. -/
structure AddressSeparation : Prop where
  expr : source.addr ≠ result.addr
  univ : sourceUniv.addr ≠ resultUniv.addr

/-- The concrete footprint satisfies both address-collision obligations.
The two cross cases are discharged by the exact `AddressSeparation` premises
for the actual Blake3 smart constructors. -/
theorem support_collisionFree
    (separation : AddressSeparation) : support.CollisionFree := by
  constructor
  · intro left hleft right hright haddr
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · rfl
    · exact False.elim (separation.expr haddr)
    · exact False.elim (separation.expr haddr.symm)
    · rfl
  · intro left hleft right hright haddr
    rcases hleft with rfl | rfl <;> rcases hright with rfl | rfl
    · rfl
    · exact False.elim (separation.univ haddr)
    · exact False.elim (separation.univ haddr.symm)
    · rfl

theorem source_supported : support source := Or.inl rfl

theorem result_supported : support result := Or.inr rfl

/-- Every expression in this deliberately small result footprint is a
syntactic sort, so `ensureSortDirect` never invokes WHNF. -/
theorem supported_is_sort {candidate : KExpr .anon}
    (hcandidate : support candidate) :
    ∃ u info, candidate = .sort u info := by
  rcases hcandidate with rfl | rfl
  · exact ⟨sourceUniv, source.info, by rfl⟩
  · exact ⟨resultUniv, result.info, by rfl⟩

/-- Both possible sort views have the exact finite universe-subterm support
required by the checker pipeline. -/
theorem sortResources : SortComponentResources support := by
  intro u info hsource
  rcases hsource with hsource | hresult
  · have heq : (.sort u info : KExpr .anon) = source := hsource
    change (.sort u info : KExpr .anon) = KExpr.mkSort sourceUniv at heq
    cases heq
    constructor
    · change 1 < UInt64.size
      decide
    · intro child hchild
      cases hchild
      exact Or.inl rfl
  · have heq : (.sort u info : KExpr .anon) = result := hresult
    change (.sort u info : KExpr .anon) = KExpr.mkSort resultUniv at heq
    cases heq
    constructor
    · change 2 < UInt64.size
      decide
    · intro child hchild
      cases hchild with
      | refl => exact Or.inr rfl
      | succ hchild =>
          cases hchild
          exact Or.inl rfl

/-- Closed sorts contain no declaration references, so the empty trusted
world supplies the exact run-scoped reference policy. -/
theorem trustedReferences :
    RecM.TrustedReferences VerifyWorld.empty support := by
  intro candidate id hcandidate href
  obtain ⟨u, info, hsort⟩ := supported_is_sort hcandidate
  subst candidate
  simp [KExpr.References] at href

/-- Empty Theory has no literal constants; the literal premise is therefore
vacuous.  Projection closure is definitionally empty as well. -/
def theory (uvars : Nat) :
    WhnfTheory RawProjRel.none VerifyWorld.empty uvars where
  literalWF := by
    intro literal hliteral
    cases literal <;>
      simp [VerifyWorld.empty, VerifyWorld.ofCatalog,
        Lean4Lean.VEnv.ContainsLits, Lean4Lean.VEnv.contains,
        Lean4Lean.VEnv.empty] at hliteral
  projections := RawProjRel.none_ok VerifyWorld.empty.venv uvars

/-! ## Concrete run-scoped suffix instance -/

/-- K2S's production suffix model for this closed fixture.  Unlike the
legacy theorems below, this value contains only the singleton normalized
context input reached by the run. -/
def scopedModel : ScopedKernelSuffixModel RawProjRel.none VerifyWorld.empty :=
  ClosedContextDigest.model RawProjRel.none VerifyWorld.empty 0

/-- A genuinely positive-fuel production state with empty semantic caches
and no local context. -/
def scopedInitialState : TcState .anon :=
  { TcState.ofEnvAnon ({} : KEnv .anon) with
    noAccel := true
    recFuel := 1
    fuelBudget := 1 }

theorem scopedInitialState_closed : ClosedContextState scopedInitialState := by
  constructor <;> rfl

theorem scopedInitialState_core :
    TcStateWF RawProjRel.none scopedInitialState VerifyWorld.empty := by
  refine ⟨TrustedCatalogRel.ofCatalog Catalog.empty, ?_, InternTable.WF.empty⟩
  exact LoadedAgrees.empty Catalog.empty

theorem scopedInitialState_kernel :
    KernelStateWF (kernelCacheSemantics scopedModel.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support scopedInitialState := by
  apply KernelStateWF.of_no_cache_entries scopedInitialState_core
  · constructor
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [scopedInitialState, TcState.ofEnvAnon] at haddr
    · intro candidate hcandidate
      obtain ⟨addr, haddr⟩ := hcandidate
      simp [scopedInitialState, TcState.ofEnvAnon] at haddr
  · rfl
  · intro entry hentry
    cases hentry <;>
      simp [scopedInitialState, TcState.ofEnvAnon] at *

theorem scopedInitialState_baseInv :
    WhnfStateInv .noAccel
      (kernelCacheSemantics scopedModel.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support scopedModel.keys.uvars []
      scopedInitialState := by
  refine ⟨scopedInitialState_kernel, ?_, rfl,
    Primitives.ofAnonAddrs_canonical⟩
  apply CtxRecon.empty <;> rfl

theorem scopedInitialState_inv :
    ScopedWhnfStateInv scopedModel .noAccel
      (kernelCacheSemantics scopedModel.keys RawProjRel.none)
      support [] scopedInitialState :=
  ⟨scopedInitialState_baseInv,
    ClosedContextDigest.model_stateInScope scopedInitialState_closed⟩

theorem source_translation :
    TrKExprS VerifyWorld.empty.venv scopedModel.keys.uvars
      VerifyWorld.empty.nameOf RawProjRel.none [] source (.sort .zero) := by
  unfold source sourceUniv
  exact .sort (by trivial)

/-- The public positive-fuel sort theorem consumes the concrete finite model
directly.  There is no global `KernelSuffixModel` premise or scoped-to-global
conversion anywhere in this statement. -/
theorem scopedPublicInference_wf (separation : AddressSeparation) :
    TcM.WF
      (ScopedWhnfStateInv scopedModel .noAccel
        (kernelCacheSemantics scopedModel.keys RawProjRel.none) support [])
      scopedInitialState (TcM.infer source)
      (fun inferred _ => support inferred ∧
        InferPost RawProjRel.none VerifyWorld.empty scopedModel.keys.uvars []
          (.sort .zero) inferred) := by
  exact
    (TcM.infer.sort_scoped_wf_fuel_one
      (initial := scopedInitialState) (model := scopedModel)
      (u := sourceUniv) (info := source.info)
      (Delta := []) (sourceV := .sort .zero)
      (by rfl) (support_collisionFree separation) source_supported
      result_supported (theory 0) trustedReferences source_translation)

def scopedInferKey : Address × Address := (source.addr, emptyCtxAddr)

theorem scopedInitialState_inferKey :
    TcM.inferKey source scopedInitialState =
      .ok scopedInferKey scopedInitialState := by
  simpa [scopedInferKey, TcM.inferKey_eq_whnfKey] using
    (TcM.whnfKey_closed (s := scopedInitialState) (source := source)
      (by rfl))

theorem scopedInitialState_inferMiss :
    scopedInitialState.env.inferCache[scopedInferKey]? = none := by
  simp [scopedInitialState, scopedInferKey, TcState.ofEnvAnon]

/-- An exact execution witness for the real public `TcM.infer` entry at
positive fuel.  The run takes the production context-key fast path, misses
the empty inference cache, interns the successor sort, writes the validated
cache entry, and finishes in the finite suffix state domain. -/
theorem scopedPublicInference_execution
    (separation : AddressSeparation) :
    ∃ after,
      TcM.infer source scopedInitialState = .ok result after ∧
      ScopedWhnfStateInv scopedModel .noAccel
        (kernelCacheSemantics scopedModel.keys RawProjRel.none) support []
        after ∧
      support result ∧
      InferPost RawProjRel.none VerifyWorld.empty scopedModel.keys.uvars []
        (.sort .zero) result := by
  obtain ⟨afterIntern, hintern, _hbaseAfter, _hframe⟩ :=
    TcM.intern_whnf_eval (support_collisionFree separation)
      result_supported scopedInitialState_baseInv
  have hbody :
      (RecM.inferUncached RecM.inferCall false source).run
          (Ix.Tc.methodsN (m := .anon) 1) scopedInitialState =
        .ok result afterIntern := by
    exact hintern
  have hshell := RecM.inferWith_fullMiss_success
    (inferRec := RecM.inferCall)
    (methods := Ix.Tc.methodsN (m := .anon) 1)
    (source := source) (ty := result) (key := scopedInferKey)
    (s := scopedInitialState) (sKey := scopedInitialState)
    (sBody := afterIntern) (by rfl) scopedInitialState_inferKey
    scopedInitialState_inferMiss hbody
  let after : TcState .anon :=
    { afterIntern with env := { afterIntern.env with
        inferCache := afterIntern.env.inferCache.insert scopedInferKey result } }
  have hrun : TcM.infer source scopedInitialState = .ok result after := by
    simpa [TcM.infer, TcM.runRec, RecM.infer, scopedInitialState, after]
      using hshell
  have hverified :=
    (scopedPublicInference_wf separation) scopedInitialState_inv
  rw [hrun] at hverified
  exact ⟨after, hrun, hverified.1, hverified.2⟩

/-- The exact depth-two schedule needed by a public body whose callback table
has recursion fuel one. -/
theorem scheduleAtFuelOne
    (separation : AddressSeparation)
    (model : KernelSuffixModel RawProjRel.none VerifyWorld.empty) :
    Methods.CallScheduleAt .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support model.keys.uvars
      (Methods.SortSchedule.calls source) 2 :=
  Methods.SortSchedule.two (support_collisionFree separation) source_supported
    result_supported (theory model.keys.uvars) trustedReferences

/-- Concrete C1A contract for the outer production body at fuel one.  Its
only admitted method call is inference of `source`. -/
theorem methodContractAtFuelOne
    (separation : AddressSeparation)
    (model : KernelSuffixModel RawProjRel.none VerifyWorld.empty) :
    Methods.WFAtOn .noAccel
      (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support model.keys.uvars
      (.singletonInfer source)
      (Methods.next (Ix.Tc.methodsN (m := .anon) 1)) := by
  simpa [Methods.SortSchedule.calls] using
    (scheduleAtFuelOne separation model).nextSelected

/-- Concrete strong K3 inference contract obtained from the bounded C1A
contract because sort pretranslation is already typed. -/
theorem fullInferenceAtFuelOne
    (separation : AddressSeparation)
    (model : KernelSuffixModel RawProjRel.none VerifyWorld.empty) :
    Methods.FullInferenceWFAtOn
      (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support model.keys.uvars
      (.singletonInfer source)
      (Methods.next (Ix.Tc.methodsN (m := .anon) 1)) :=
  Methods.FullInferenceWFAtOn.ofSingletonSort
    (methodContractAtFuelOne separation model)
    (Methods.next_preservesInferOnly _
      (Methods.methodsN_concrete_preservesInferOnly 1))

/-- Declaration-local K3 pipeline resources at fuel one.  The type pipeline
admits one sort inference and no WHNF/DefEq callback. -/
def pipelinesAtFuelOne
    (separation : AddressSeparation)
    (model : KernelSuffixModel RawProjRel.none VerifyWorld.empty) :
    StandalonePipelineResources
      (kernelCacheSemantics model.keys RawProjRel.none)
      RawProjRel.none VerifyWorld.empty support model.keys.uvars
      (.singletonInfer source) (Ix.Tc.methodsN (m := .anon) 1) :=
  StandalonePipelineResources.singletonSortAxiom
    (fullInferenceAtFuelOne separation model) sortResources supported_is_sort

def concreteAxiom : KConst .anon := .axio () () false 0 source

/-- The concrete sort axiom is covered by the positive-fuel K3 resources. -/
theorem pipelines_cover_concreteAxiom
    (separation : AddressSeparation)
    (model : KernelSuffixModel RawProjRel.none VerifyWorld.empty) :
    (pipelinesAtFuelOne separation model).Covers concreteAxiom :=
  .axiom rfl

end Ix.Tc.PositiveFuelSort
