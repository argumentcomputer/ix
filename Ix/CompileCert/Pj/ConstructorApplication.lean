import Ix.CompileCert.Pj.MinorConclusion
import Ix.CompileCert.Pj.RecGrading

namespace Ix.CompileCert.Pj

open Kernel.SetTheory Kernel.SetModel
open Ix.CompileCert (pushArguments)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

/-- Constructor lookup and arity come from the reader's checked installed
constructor. Its actual model value inhabits the rebuilt, instantiated type. -/
theorem MinorRd.constructor_typed (n : MinorRd) (np : Nat)
    (motives : List MotiveRd) (params : List (Kernel.Expr × Kernel.BinderMeta))
    (checked : n.CtorOk env np motives params)
    (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) :
    ∃ constructor T,
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      Kernel.Denotes strong.public.cval env φ ρ (n.ctorType np motives params) T ∧
      constructor ∈ˢ T := by
  have entry : ∃ cv cnp cnf,
      env.find? n.ctor = some (.ctorInfo cv cnp cnf) ∧
      n.ctorUs.length = cv.levelParams.length ∧
      cv.type.instantiateLevelParams cv.levelParams n.ctorUs =
        n.ctorType np motives params := by
    cases lookup : env.find? n.ctor with
    | none => simp [MinorRd.CtorOk, lookup] at checked
    | some ci =>
      cases ci <;> simp only [MinorRd.CtorOk, lookup] at checked
      case ctorInfo cv cnp cnf => exact ⟨cv, cnp, cnf, rfl, checked.2.2⟩
  obtain ⟨cv, cnp, cnf, lookup, arity, typeEq⟩ := entry
  have present := Kernel.Semantics.Env.find?_mem lookup
  have nameEq : cv.name = n.ctor := Kernel.Semantics.Env.find?_name lookup
  obtain ⟨T, typeRead, member⟩ := strong.public.mem (.ctorInfo cv cnp cnf) present
    (Kernel.Level.substFn φ cv.levelParams n.ctorUs) ρ
  change Kernel.Denotes strong.public.cval env
    (Kernel.Level.substFn φ cv.levelParams n.ctorUs) ρ cv.type T at typeRead
  have instantiated := Bridge.denotes_levels (Bridge.cvalLocal_of_strong strong)
    cv.levelParams n.ctorUs typeRead
  refine ⟨strong.public.cval n.ctor (Kernel.Level.substFn φ cv.levelParams n.ctorUs),
    T, (fun valuation => .const lookup arity), ?_, ?_⟩
  · simpa only [typeEq] using instantiated
  · change strong.public.cval cv.name (Kernel.Level.substFn φ cv.levelParams n.ctorUs)
      ∈ˢ T at member
    simpa only [nameEq] using member

/-- Applying the actual constructor to typed parameters and fields gives a
member of the reader's exact result type, with the original index expressions. -/
theorem MinorRd.constructor_applied (n : MinorRd) (np : Nat)
    (motives : List MotiveRd) (paramBinders : List (Kernel.Expr × Kernel.BinderMeta))
    (checked : n.CtorOk env np motives paramBinders)
    (paramMetasLength : n.paramMetas.length = paramBinders.length)
    (strong : Ix.CompileCert.StrongInstalledModel V env)
    (φ : Kernel.Name → Nat) (ρ : Nat → V) (params fields : List V)
    (paramsTyped : TeleTyped strong.public.cval env φ ρ (paramBinders.map Prod.fst) params)
    (fieldsTyped : TeleTyped strong.public.cval env φ (pushArguments ρ params)
      ((n.fieldTys np motives).map Prod.fst) fields) :
    ∃ constructor B,
      (∀ valuation, Kernel.Denotes strong.public.cval env φ valuation
        (.const n.ctor n.ctorUs) constructor) ∧
      Kernel.Denotes strong.public.cval env φ (pushArguments ρ (params ++ fields))
        (Kernel.Expr.mkAppN
          (.const (motives.getD n.motive default).ind (motives.getD n.motive default).indUs)
          (bvarsAt np n.fields.length ++ n.resIdx)) B ∧
      (params ++ fields).foldl app constructor ∈ˢ B := by
  obtain ⟨constructor, T, constructorRead, typeRead, member⟩ :=
    n.constructor_typed np motives paramBinders checked strong φ ρ
  have typed : TeleTyped strong.public.cval env φ ρ
      ((zipMetas (paramBinders.map Prod.fst) n.paramMetas).map Prod.fst) params := by
    rw [zipMetas_types _ _ (by simpa only [List.length_map] using paramMetasLength)]
    exact paramsTyped
  obtain ⟨U, fieldsRead, appliedParams⟩ := teleTyped_apply
    (bs := zipMetas (paramBinders.map Prod.fst) n.paramMetas)
    (by simpa only [MinorRd.ctorType] using typeRead) member typed
  obtain ⟨B, resultRead, appliedFields⟩ :=
    teleTyped_apply fieldsRead appliedParams fieldsTyped
  refine ⟨constructor, B, constructorRead, ?_, ?_⟩
  · simpa only [Ix.CompileCert.pushArguments_append] using resultRead
  · simpa only [List.foldl_append] using appliedFields

/-- Minor field metadata changes binder regimes, while its domain list is
exactly the constructor's dependent fields weakened past the motive segment. -/
theorem MinorRd.fieldBinders_types (n : MinorRd) (np nm : Nat)
    (motives : List MotiveRd) (length : n.fieldMetas.length = n.fields.length) :
    (zipMetas ((n.fieldTys np motives).mapIdx
      (fun a p => p.1.liftLooseBVars nm a)) n.fieldMetas).map Prod.fst =
      liftTypes nm 0 ((n.fieldTys np motives).map Prod.fst) := by
  rw [zipMetas_types _ _ (by
    simpa only [List.length_mapIdx, fieldTys_length] using length), liftTypes_eq_mapIdx]
  ext1 i
  simp [Option.map_map, Function.comp_def]

/-- Typed values of the actual minor's field binders are typed constructor
fields after removing the inserted motives; no closedness restriction is used. -/
theorem MinorRd.fields_unlift (n : MinorRd) (np nm : Nat)
    (sourceMotives : List MotiveRd) (ρ : Nat → V) (motives fields : List V)
    (motiveLength : motives.length = nm)
    (metaLength : n.fieldMetas.length = n.fields.length)
    (typed : TeleTyped cval env φ (pushArguments ρ motives)
      ((zipMetas ((n.fieldTys np sourceMotives).mapIdx
        (fun a p => p.1.liftLooseBVars nm a)) n.fieldMetas).map Prod.fst) fields) :
    TeleTyped cval env φ ρ ((n.fieldTys np sourceMotives).map Prod.fst) fields := by
  apply TeleTyped.unlift (valuationLift_prefix ρ motives)
  simpa only [n.fieldBinders_types np nm sourceMotives metaLength, motiveLength] using typed

end Ix.CompileCert.Pj
