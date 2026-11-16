import IxVMRefinement.Decl.NativeFront

/-! # Scoped core facts at the native former stage

A fresh former preserves the base core facts. Its actual native capabilities obtain their
arity evidence from the checked former telescope; global eta-table assumptions are unnecessary.
-/

namespace IxVM.Refinement.Decl

open IxVM.Refinement.Core
open Ix.Kernel (ConstantVal ConstantInfo)

private theorem coreEnvFacts_consInd {c : Ctx} {cv : ConstantVal .anon}
    {caps : Ix.Kernel.IndCaps .anon}
    (facts : CoreEnvFacts c) (fresh : c.env.find? cv.name = none)
    (keyShape : cv.name.isProjFnShape = false)
    (stageStore : Ix.Kernel.Open.StoreInv ⟨.indInfo cv caps :: c.env.consts⟩) :
    CoreEnvFacts { c with env := ⟨.indInfo cv caps :: c.env.consts⟩ } := by
  let staged : Ix.Kernel.Env .anon := ⟨.indInfo cv caps :: c.env.consts⟩
  have extended : Ix.Kernel.EnvExt c.env staged :=
    envExt_cons_nonProj fresh (ne_projTableName_of_isProjFnShape_false keyShape)
  have oldRec : ∀ {name : KKey} {value : ConstantVal .anon} {major params : Nat}
      {rules : List (Ix.Kernel.RecRule .anon)},
      staged.find? name = some (.recInfo value major params rules) →
        c.env.find? name = some (.recInfo value major params rules) := by
    intro name value major params rules found
    change (Ix.Kernel.Env.mk (.indInfo cv caps :: c.env.consts)).find? name = _ at found
    rw [Ix.Kernel.Env.find?_cons] at found
    split at found
    · cases found
    · exact found
  have oldCtor : ∀ {name : KKey} {value : ConstantVal .anon} {params fields : Nat},
      staged.find? name = some (.ctorInfo value params fields) →
        c.env.find? name = some (.ctorInfo value params fields) := by
    intro name value params fields found
    change (Ix.Kernel.Env.mk (.indInfo cv caps :: c.env.consts)).find? name = _ at found
    rw [Ix.Kernel.Env.find?_cons] at found
    split at found
    · cases found
    · exact found
  refine {
    tableWf := facts.tableWf
    storeClosed := stageStore.storeClosed
    thmTyped := Ix.Kernel.Model.thmTyped_step_noThm extended facts.thmTyped
      (Ix.Kernel.Model.NewSat.cons (fun _ _ equal => nomatch equal))
    natLit := fun hn hz hs => extended.natLitSupported_mono (facts.natLit hn hz hs)
    strLit := fun hs => extended.strLitSupported_mono (facts.strLit hs)
    natOps := fun role force operation => extended.natOpStored_mono (facts.natOps role force operation)
    natAdd := fun force => extended.opt_mono (p := Ix.Kernel.Rules.natAddTyOk) (facts.natAdd force) rfl
    eqStored := ?_
    recRules := ?_
    recPlain := ?_
    store := stageStore
    recMajorRecord := ?_
    ruleCtorHead := ?_
    quotBasis := ?_
    recEta := ?_
    recArity := fun _ _ _ _ _ found rule member => stageStore.recArity found member
    ruleCtorArity := fun _ _ _ _ _ found rule member _ _ _ constructor =>
      stageStore.ruleCtor_arity found member constructor
    tableCtorArity := fun _ _ _ found _ _ _ constructor => stageStore.tableCtor_arity found constructor
    familyArity := fun _ _ _ found => stageStore.familyArity found }
  · intro force
    obtain ⟨value, found⟩ := facts.eqStored force
    exact ⟨value, extended.find found⟩
  · intro name value major params rules found
    obtain ⟨nodup, firing, projections⟩ := facts.recRules name value major params rules (oldRec found)
    refine ⟨nodup, ?_, projections⟩
    intro rule member
    obtain ⟨fire, constructor, fields, stored⟩ := firing rule member
    exact ⟨fire, constructor, fields, extended.find stored⟩
  · intro name value major params rules rule constructor numParams numFields found member fire stored
    exact facts.recPlain name value major params rules rule constructor numParams numFields
      (oldRec found) member fire (oldCtor stored)
  · intro name value major params rules parent levels found nonempty head
    exact facts.recMajorRecord name value major params rules parent levels (oldRec found) nonempty head
  · intro name value major params rules rule constructor numParams numFields former levels found member stored head
    exact facts.ruleCtorHead name value major params rules rule constructor numParams numFields former levels
      (oldRec found) member (oldCtor stored) head
  · intro force value member
    exact extended.find (facts.quotBasis force value member)
  · intro name value major params rule found
    have old := oldRec found
    exact (facts.recEta name value major params rule old).trans
      (Ix.Kernel.Model.recRuleEtaOf_stable facts.store extended.find old (by simp) name)

/-- Stage the actual native capabilities using the checked former telescope, while preserving
all base scoped-core environment facts without a global eta invariant. -/
theorem coreEnvFacts_consNativeCapsAt {c : Ctx} {cv : ConstantVal .anon}
    {p : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    {binders : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr}
    (facts : CoreEnvFacts c) (fresh : c.env.find? cv.name = none)
    (keyShape : cv.name.isProjFnShape = false)
    (typeShape : cv.type.hasFvar = false ∧ cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve c.env = true ∧ cv.type.looseBVarsBounded 0 = true)
    (telescope : cv.type.stripPis (p.nP + p.nIdx) = some (binders, body)) :
    CoreEnvFacts { c with env := ⟨.indInfo cv (Ix.Kernel.nativeCapsAt p isRec) :: c.env.consts⟩ } :=
  coreEnvFacts_consInd facts fresh keyShape
    (storeInv_consNativeCapsAt facts.store fresh typeShape telescope)

end IxVM.Refinement.Decl
