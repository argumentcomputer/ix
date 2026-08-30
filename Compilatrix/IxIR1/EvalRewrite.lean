import Compilatrix.IxIR1.EvalIso

/-!
# Evaluator refinement under an abstract declaration environment

An owner-sensitive optimization changes stored function bodies while leaving
the calling convention stable.  This module isolates the recursive evaluator
argument needed to lift such a local body theorem through direct calls,
`callSelf`, PAP application, and arbitrary surrounding code.

The abstraction is deliberately semantic.  It does not require a particular
declaration map implementation or a syntactic rewrite function: each source
function lookup supplies a target function with the same arity and result
world, plus a local successful-run refinement in the source context.  The
common fuel induction below is therefore reusable by every body optimizer and
by the old-keyed logical environment that precedes content readdressing.
-/

namespace Compilatrix.IxIR1.Sim

open Compilatrix.Ixon (Address)

/-- Local semantic obligation for one rewritten function body.  Both runs use
the source declaration context; the general evaluator traversal is responsible
for replacing recursive callees afterward. -/
def FunctionBodyRefines (ctx : Ctx) (source target : FnDef) : Prop :=
  ∀ {fuel : Nat} {store : Store} {environment : List RVal}
      {sourceOut : Store × RVal}
      (base : HeapHistoryIso store store),
    environment.length = source.arity →
    RValsIso base.locRel environment environment →
    runCode ctx fuel source store environment source.body = .ok sourceOut →
    ∃ targetOut,
      runCode ctx fuel target store environment target.body = .ok targetOut ∧
        RunHistoryIso base sourceOut targetOut

/-- The non-recursive obligation supplied by a body optimizer.  The rewritten
body still runs under the source current frame; `FunctionBodyRefines.ofStatic`
below closes the recursive `callSelf` fixed point and installs `target` as the
dynamic frame. -/
def StaticFunctionBodyRefines (ctx : Ctx) (source target : FnDef) : Prop :=
  ∀ {fuel : Nat} {store : Store} {environment : List RVal}
      {sourceOut : Store × RVal}
      (base : HeapHistoryIso store store),
    environment.length = source.arity →
    RValsIso base.locRel environment environment →
    runCode ctx fuel source store environment source.body = .ok sourceOut →
    ∃ targetOut,
      runCode ctx fuel source store environment target.body = .ok targetOut ∧
        RunHistoryIso base sourceOut targetOut

/-- One-way logical relation between evaluator declaration environments.
Extra target declarations are harmless: only successful source lookups need a
matching target. -/
structure AbstractEnvironment (before after : Ctx) : Prop where
  oracle_eq : after.oracle = before.oracle
  extern : ∀ {address : Address} {arity : Nat},
    before.decls address = some (.extern arity) →
      after.decls address = some (.extern arity)
  function : ∀ {address : Address} {source : FnDef},
    before.decls address = some (.fn source) →
      ∃ target : FnDef,
        after.decls address = some (.fn target) ∧
          target.arity = source.arity ∧
          target.result = source.result ∧
          FunctionBodyRefines before source target

namespace AbstractEnvironment

theorem declaration {before after : Ctx}
    (environment : AbstractEnvironment before after)
    {address : Address} {source : Decl}
    (hsource : before.decls address = some source) :
    ∃ target,
      after.decls address = some target ∧
        declArity target = declArity source := by
  cases source with
  | extern arity =>
      exact ⟨.extern arity, environment.extern hsource, rfl⟩
  | fn source =>
      obtain ⟨target, htarget, harity, _, _⟩ :=
        environment.function hsource
      refine ⟨.fn target, htarget, ?_⟩
      change target.arity = source.arity
      exact harity

end AbstractEnvironment

private structure DropCtxEqAt (before after : Ctx) (fuel : Nat) : Prop where
  dropVal : ∀ (store : Store) (value : RVal),
    dropVal after fuel store value = dropVal before fuel store value
  dropMany : ∀ (store : Store) (values : List RVal),
    dropMany after fuel store values = dropMany before fuel store values
  dropUVal : ∀ (store : Store) (value : RVal),
    dropUVal after fuel store value = dropUVal before fuel store value
  dropManyU : ∀ (store : Store) (values : List RVal),
    dropManyU after fuel store values = dropManyU before fuel store values

private theorem dropCtxEqAt (before after : Ctx) :
    ∀ fuel, DropCtxEqAt before after fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [dropVal, dropMany, dropUVal, dropManyU]
  | succ fuel smaller =>
      constructor
      · intro store value
        cases value with
        | lit literal => simp [dropVal]
        | erased => simp [dropVal]
        | loc location =>
            simp only [dropVal]
            cases hbox : store.get? location with
            | none => simp
            | some box =>
                simp only
                cases hworld : box.world with
                | unique => simp
                | shared =>
                    simp only
                    by_cases hone : box.rc == 1
                    · simp only [hone, if_true]
                      cases hnode : box.node with
                      | ctorN identity fields =>
                          simpa [hnode] using smaller.dropMany
                            (store.rcTick.kill location) fields.toList
                      | papN function arity arguments =>
                          simpa [hnode] using smaller.dropMany
                            (store.rcTick.kill location) arguments.toList
                    · simp [hone]
      · intro store values
        cases values with
        | nil => simp [dropMany]
        | cons value rest =>
            simp only [dropMany]
            rw [smaller.dropVal store value]
            cases hdrop : dropVal before fuel store value with
            | error error => rfl
            | ok next => exact smaller.dropMany next rest
      · intro store value
        cases value with
        | lit literal => simp [dropUVal]
        | erased => simp [dropUVal]
        | loc location =>
            simp only [dropUVal]
            cases hbox : store.get? location with
            | none => simp
            | some box =>
                simp only
                cases hworld : box.world with
                | shared => simp
                | unique =>
                    simp only
                    cases hnode : box.node with
                    | ctorN identity fields =>
                        simpa [hnode] using smaller.dropManyU
                          (store.kill location) fields.toList
                    | papN function arity arguments => simp
      · intro store values
        cases values with
        | nil => simp [dropManyU]
        | cons value rest =>
            simp only [dropManyU]
            rw [smaller.dropUVal store value]
            cases hdrop : dropUVal before fuel store value with
            | error error => rfl
            | ok next => exact smaller.dropManyU next rest

/-- The context-changing part of the evaluator theorem.  Entry stores and
values are literally shared; `base` supplies the self-history needed when a
body rewrite removes allocations and later locations drift. -/
private structure EvalRewriteAt (before after : Ctx) (fuel : Nat) : Prop where
  runCode : ∀ (current : FnDef) (store : Store)
      (base : HeapHistoryIso store store) (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (input : Code) (sourceOut : Store × RVal),
      runCode before fuel current store environment input = .ok sourceOut →
      ∃ targetOut,
        runCode after fuel current store environment input = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut
  runOp : ∀ (current : FnDef) (store : Store)
      (base : HeapHistoryIso store store) (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (operation : Op) (sourceOut : Store × RVal),
      runOp before fuel current store environment operation = .ok sourceOut →
      ∃ targetOut,
        runOp after fuel current store environment operation = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut
  invoke : ∀ (function : Address) (arguments : List RVal) (store : Store)
      (base : HeapHistoryIso store store),
    RValsIso base.locRel arguments arguments →
    ∀ (sourceOut : Store × RVal),
      IxIR1.invoke before fuel function arguments store = .ok sourceOut →
      ∃ targetOut,
        IxIR1.invoke after fuel function arguments store = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut
  applyGo : ∀ (store : Store) (base : HeapHistoryIso store store)
      (function : RVal) (arguments : List RVal),
    RValIso base.locRel function function →
    RValsIso base.locRel arguments arguments →
    ∀ (sourceOut : Store × RVal),
      IxIR1.applyGo before fuel store function arguments = .ok sourceOut →
      ∃ targetOut,
        IxIR1.applyGo after fuel store function arguments = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut

private theorem selfRight_extends_compose
    {left right : Store} (heap : HeapHistoryIso left right) :
    heap.Extends (heap.trans (heap.symm.trans heap)) := by
  intro leftLoc rightLoc hrel
  exact ⟨rightLoc, hrel, leftLoc, hrel, hrel⟩

private theorem selfLeft_compose_extends
    {store : Store} (base : HeapHistoryIso store store) :
    base.Extends ((base.trans base.symm).trans base) := by
  intro leftLoc rightLoc hrel
  exact ⟨leftLoc, ⟨rightLoc, hrel, hrel⟩, hrel⟩

private theorem runCode_crossOfSame
    {before after : Ctx} {fuel : Nat}
    (same : EvalRewriteAt before after fuel)
    {current : FnDef} {left right : Store}
    (heap : HeapHistoryIso left right)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {input : Code} {sourceOut : Store × RVal}
    (hrun : runCode before fuel current left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode after fuel current right rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut := by
  obtain ⟨middleOut, hmiddle, hsourceMiddle⟩ :=
    runCode_historyIso heap henvironments hrun
  let self := heap.symm.trans heap
  have hselfEnvironment : RValsIso self.locRel
      rightEnvironment rightEnvironment := by
    exact henvironments.symm.trans henvironments
  obtain ⟨targetOut, htarget, hmiddleTarget⟩ :=
    same.runCode current right self rightEnvironment hselfEnvironment input
      middleOut hmiddle
  exact ⟨targetOut, htarget,
    RunHistoryIso.weaken (selfRight_extends_compose heap)
      (hsourceMiddle.trans hmiddleTarget)⟩

private theorem applyGo_crossOfSame
    {before after : Ctx} {fuel : Nat}
    (same : EvalRewriteAt before after fuel)
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftFunction rightFunction : RVal}
    {leftArguments rightArguments : List RVal}
    (hfunction : RValIso heap.locRel leftFunction rightFunction)
    (harguments : RValsIso heap.locRel leftArguments rightArguments)
    {sourceOut : Store × RVal}
    (hrun : IxIR1.applyGo before fuel left leftFunction leftArguments =
      .ok sourceOut) :
    ∃ targetOut,
      IxIR1.applyGo after fuel right rightFunction rightArguments =
          .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut := by
  obtain ⟨middleOut, hmiddle, hsourceMiddle⟩ :=
    applyGo_historyIso heap hfunction harguments hrun
  let self := heap.symm.trans heap
  have hselfFunction : RValIso self.locRel rightFunction rightFunction :=
    hfunction.symm.trans hfunction
  have hselfArguments : RValsIso self.locRel
      rightArguments rightArguments := harguments.symm.trans harguments
  obtain ⟨targetOut, htarget, hmiddleTarget⟩ :=
    same.applyGo right self rightFunction rightArguments hselfFunction
      hselfArguments middleOut hmiddle
  exact ⟨targetOut, htarget,
    RunHistoryIso.weaken (selfRight_extends_compose heap)
      (hsourceMiddle.trans hmiddleTarget)⟩

private theorem resolveAtom_selfIso
    {rel : Nat → Nat → Prop} {environment : List RVal}
    (henvironment : RValsIso rel environment environment)
    {atom : Atom} {value : RVal}
    (hresolve : resolveAtom environment atom = .ok value) :
    RValIso rel value value := by
  obtain ⟨rightValue, hright, hvalue⟩ :=
    resolveAtom_historyIso henvironment hresolve
  have heq : rightValue = value := Except.ok.inj (hright.symm.trans hresolve)
  subst rightValue
  exact hvalue

private theorem resolveAtoms_selfIso
    {rel : Nat → Nat → Prop} {environment : List RVal}
    (henvironment : RValsIso rel environment environment)
    {atoms : Array Atom} {values : List RVal}
    (hresolve : resolveAtoms environment atoms = .ok values) :
    RValsIso rel values values := by
  obtain ⟨rightValues, hright, hvalues⟩ :=
    resolveAtoms_historyIso henvironment hresolve
  have heq : rightValues = values := Except.ok.inj (hright.symm.trans hresolve)
  subst rightValues
  exact hvalues

/-! ## Closing a rewritten current-frame fixed point -/

private structure CurrentFrameRefinesAt (ctx : Ctx)
    (source target : FnDef) (fuel : Nat) : Prop where
  runCode : ∀ (store : Store) (base : HeapHistoryIso store store)
      (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (input : Code) (sourceOut : Store × RVal),
      runCode ctx fuel source store environment input = .ok sourceOut →
      ∃ targetOut,
        runCode ctx fuel target store environment input = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut
  runOp : ∀ (store : Store) (base : HeapHistoryIso store store)
      (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (operation : Op) (sourceOut : Store × RVal),
      runOp ctx fuel source store environment operation = .ok sourceOut →
      ∃ targetOut,
        runOp ctx fuel target store environment operation = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut

private theorem runCode_currentFrameCrossOfSame
    {ctx : Ctx} {source target : FnDef} {fuel : Nat}
    (same : CurrentFrameRefinesAt ctx source target fuel)
    {left right : Store} (heap : HeapHistoryIso left right)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {input : Code} {sourceOut : Store × RVal}
    (hrun : runCode ctx fuel source left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode ctx fuel target right rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut := by
  obtain ⟨middleOut, hmiddle, hsourceMiddle⟩ :=
    runCode_historyIso heap henvironments hrun
  let self := heap.symm.trans heap
  have hselfEnvironment : RValsIso self.locRel
      rightEnvironment rightEnvironment :=
    henvironments.symm.trans henvironments
  obtain ⟨targetOut, htarget, hmiddleTarget⟩ :=
    same.runCode right self rightEnvironment hselfEnvironment input middleOut
      hmiddle
  exact ⟨targetOut, htarget,
    RunHistoryIso.weaken (selfRight_extends_compose heap)
      (hsourceMiddle.trans hmiddleTarget)⟩

private theorem runCode_currentFrameCaseStep
    {ctx : Ctx} {source target : FnDef} {fuel : Nat}
    (smaller : CurrentFrameRefinesAt ctx source target fuel)
    (store : Store) (base : HeapHistoryIso store store)
    (environment : List RVal)
    (henvironment : RValsIso base.locRel environment environment)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt)
    (sourceOut : Store × RVal)
    (hrun : runCode ctx (fuel + 1) source store environment
      (.case scrutinee peelNat alternatives) = .ok sourceOut) :
    ∃ targetOut,
      runCode ctx (fuel + 1) target store environment
          (.case scrutinee peelNat alternatives) = .ok targetOut ∧
        RunHistoryIso base sourceOut targetOut := by
  rw [runCode.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error =>
      rw [hscrutinee] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok value =>
      rw [hscrutinee] at hrun
      simp only [bind, Except.bind] at hrun ⊢
      have hvalue : RValIso base.locRel value value :=
        resolveAtom_selfIso henvironment hscrutinee
      cases value with
      | erased => simp at hrun
      | lit literal =>
          cases literal with
          | str value => simp at hrun
          | nat value =>
              cases peelNat with
              | false => simp at hrun
              | true =>
                  cases value with
                  | zero =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          simp only [hfind] at hrun ⊢
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  exact smaller.runCode store base environment
                                    henvironment body sourceOut hrun
                              | succ fields => simp at hrun
                  | succ value =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          simp only [hfind] at hrun ⊢
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp at hrun
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      exact smaller.runCode store base
                                        (.lit (.nat value) :: environment)
                                        (.cons .lit henvironment) body
                                        sourceOut hrun
                                  | succ fields => simp at hrun
      | loc location =>
          cases hbox : store.get? location with
          | none => simp [hbox] at hrun
          | some box =>
              simp only [hbox] at hrun ⊢
              cases hnode : box.node with
              | papN function arity arguments => simp [hnode] at hrun
              | ctorN identity fields =>
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == identity.cidx) with
                  | none => simp [hnode, hfind] at hrun
                  | some alternative =>
                      simp only [hfind] at hrun ⊢
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hcount : fields.size = fieldCount
                          · simp [hnode, hfind, hcount] at hrun ⊢
                            cases hvalue with
                            | @loc _ _ hrel =>
                                obtain ⟨rightBox, hrightBox, hboxIso⟩ :=
                                  base.boxes hrel hbox
                                have hrightBoxEq : rightBox = box := by
                                  exact Option.some.inj
                                    (hrightBox.symm.trans hbox)
                                subst rightBox
                                have hfields : RValsIso base.locRel
                                    fields.toList fields.toList := by
                                  have hnodeIso : NodeIso base.locRel
                                      box.node box.node := hboxIso.node
                                  rw [hnode] at hnodeIso
                                  cases hnodeIso with
                                  | ctor hfields => exact hfields
                                have hbranch : RValsIso base.locRel
                                    (fields.toList.reverse ++ environment)
                                    (fields.toList.reverse ++ environment) :=
                                  hfields.reverse.append henvironment
                                obtain ⟨targetOut, htarget, hiso⟩ :=
                                  smaller.runCode store base
                                    (fields.toList.reverse ++ environment)
                                    hbranch body sourceOut hrun
                                rcases targetOut with
                                  ⟨targetStore, targetValue⟩
                                exact ⟨targetStore, targetValue,
                                  htarget, hiso⟩
                          · simp [hnode, hfind, hcount] at hrun

private theorem runCode_currentFrameStep
    {ctx : Ctx} {source target : FnDef} {fuel : Nat}
    (smaller : CurrentFrameRefinesAt ctx source target fuel) :
    ∀ (store : Store) (base : HeapHistoryIso store store)
      (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (input : Code) (sourceOut : Store × RVal),
      runCode ctx (fuel + 1) source store environment input = .ok sourceOut →
      ∃ targetOut,
        runCode ctx (fuel + 1) target store environment input = .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro store base environment henvironment input sourceOut hrun
  cases input with
  | ret atom =>
      simpa [runCode] using
        (runCode_historyIso base henvironment hrun)
  | case scrutinee peelNat alternatives =>
      exact runCode_currentFrameCaseStep smaller store base environment
        henvironment scrutinee peelNat alternatives sourceOut hrun
  | letOp operation rest =>
      rw [runCode.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hoperation : runOp ctx fuel source store environment operation with
      | error error =>
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok operationOut =>
          rcases operationOut with ⟨middle, sourceValue⟩
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          obtain ⟨targetOperationOut, htargetOperation,
              operationHeap, hbaseOperation, hvalue⟩ :=
            smaller.runOp store base environment henvironment operation
              (middle, sourceValue) hoperation
          rcases targetOperationOut with ⟨targetMiddle, targetValue⟩
          have hrestEnvironment : RValsIso operationHeap.locRel
              (sourceValue :: environment) (targetValue :: environment) :=
            .cons hvalue (hbaseOperation.rvals henvironment)
          obtain ⟨targetOut, htargetRest, hrestIso⟩ :=
            runCode_currentFrameCrossOfSame smaller operationHeap
              hrestEnvironment hrun
          refine ⟨targetOut, ?_,
            RunHistoryIso.weaken hbaseOperation hrestIso⟩
          rw [htargetOperation]
          simp only [bind, Except.bind]
          exact htargetRest

private theorem runOp_currentFrameStep
    {ctx : Ctx} {source target : FnDef}
    (bodyRewrite : StaticFunctionBodyRefines ctx source target)
    (harity : target.arity = source.arity)
    (hresult : target.result = source.result)
    {fuel : Nat} (smaller : CurrentFrameRefinesAt ctx source target fuel) :
    ∀ (store : Store) (base : HeapHistoryIso store store)
      (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (operation : Op) (sourceOut : Store × RVal),
      runOp ctx (fuel + 1) source store environment operation = .ok sourceOut →
      ∃ targetOut,
        runOp ctx (fuel + 1) target store environment operation =
            .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro store base environment henvironment operation sourceOut hrun
  cases operation with
  | pure atom =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | alloc world identity arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | reuse targetAtom identity arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | free targetAtom =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | dup targetAtom =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | drop targetAtom =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | dropU targetAtom =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | fetch targetAtom field =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | call function arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | papp function arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | apply function arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | extern function arguments =>
      simpa [runOp] using (runOp_historyIso base henvironment hrun)
  | callSelf arguments =>
      rw [runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases harguments : resolveAtoms environment arguments with
      | error error =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok argumentValues =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          have hargumentValues : RValsIso base.locRel
              argumentValues argumentValues :=
            resolveAtoms_selfIso henvironment harguments
          by_cases hsourceArity : argumentValues.length = source.arity
          · have htargetArity : argumentValues.length = target.arity := by
              rw [harity]
              exact hsourceArity
            simp [hsourceArity] at hrun
            cases hbody : runCode ctx fuel source store
                argumentValues.reverse source.body with
            | error error =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok bodyOut =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                have hout := (checkResultWorld_ok hrun).1
                subst sourceOut
                let self := base.trans base.symm
                have hselfArguments : RValsIso self.locRel
                    argumentValues.reverse argumentValues.reverse :=
                  (hargumentValues.trans hargumentValues.symm).reverse
                obtain ⟨localOut, hlocalRun, hlocalIso⟩ :=
                  bodyRewrite self (by simpa using hsourceArity)
                    hselfArguments hbody
                obtain ⟨targetOut, htargetBody, hframeIso⟩ :=
                  smaller.runCode store base argumentValues.reverse
                    hargumentValues.reverse target.body localOut hlocalRun
                have hbodyIso : RunHistoryIso base bodyOut targetOut :=
                  RunHistoryIso.weaken (selfLeft_compose_extends base)
                    (hlocalIso.trans hframeIso)
                rcases bodyOut with ⟨bodyStore, bodyValue⟩
                rcases targetOut with ⟨targetStore, targetValue⟩
                obtain ⟨finalHeap, hbaseFinal, hvalue⟩ := hbodyIso
                have htargetWorld := checkResultWorld_historyIso finalHeap
                  hvalue source.result hrun
                refine ⟨(targetStore, targetValue), ?_, finalHeap,
                  hbaseFinal, hvalue⟩
                simp [htargetArity, htargetBody, hresult]
                simpa only [bind, Except.bind] using htargetWorld
          · have htargetDifferent : argumentValues.length ≠ target.arity := by
              intro heq
              exact hsourceArity (heq.trans harity)
            simp [hsourceArity, htargetDifferent] at hrun

private theorem currentFrameRefinesAt
    {ctx : Ctx} {source target : FnDef}
    (bodyRewrite : StaticFunctionBodyRefines ctx source target)
    (harity : target.arity = source.arity)
    (hresult : target.result = source.result) :
    ∀ fuel, CurrentFrameRefinesAt ctx source target fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [runCode, runOp] at *
  | succ fuel smaller =>
      exact ⟨runCode_currentFrameStep smaller,
        runOp_currentFrameStep bodyRewrite harity hresult smaller⟩

/-- A pass-local body rewrite closes to a genuine function refinement once
the calling convention is stable. -/
theorem FunctionBodyRefines.ofStatic
    {ctx : Ctx} {source target : FnDef}
    (bodyRewrite : StaticFunctionBodyRefines ctx source target)
    (harity : target.arity = source.arity)
    (hresult : target.result = source.result) :
    FunctionBodyRefines ctx source target := by
  intro fuel store environment sourceOut base hlength henvironment hrun
  let self := base.trans base.symm
  have hselfEnvironment : RValsIso self.locRel environment environment :=
    henvironment.trans henvironment.symm
  obtain ⟨localOut, hlocalRun, hlocalIso⟩ :=
    bodyRewrite self hlength hselfEnvironment hrun
  obtain ⟨targetOut, htargetRun, hframeIso⟩ :=
    (currentFrameRefinesAt bodyRewrite harity hresult fuel).runCode store base
      environment henvironment target.body localOut hlocalRun
  exact ⟨targetOut, htargetRun,
    RunHistoryIso.weaken (selfLeft_compose_extends base)
      (hlocalIso.trans hframeIso)⟩

/-- The same fixed-point closure lifted through arbitrary related entry heaps
and environments. -/
theorem runCode_currentFrame_refines
    {ctx : Ctx} {source target : FnDef}
    (bodyRewrite : StaticFunctionBodyRefines ctx source target)
    (harity : target.arity = source.arity)
    (hresult : target.result = source.result)
    {left right : Store} {fuel : Nat}
    {leftEnvironment rightEnvironment : List RVal}
    {input : Code} {sourceOut : Store × RVal}
    (heap : HeapHistoryIso left right)
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    (hrun : runCode ctx fuel source left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode ctx fuel target right rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  runCode_currentFrameCrossOfSame
    (currentFrameRefinesAt bodyRewrite harity hresult fuel) heap henvironments
      hrun

private theorem runCode_caseRewriteAt
    {before after : Ctx} {fuel : Nat}
    (smaller : EvalRewriteAt before after fuel)
    (current : FnDef) (store : Store)
    (base : HeapHistoryIso store store) (environment : List RVal)
    (henvironment : RValsIso base.locRel environment environment)
    (scrutinee : Atom) (peelNat : Bool) (alternatives : Array Alt)
    (sourceOut : Store × RVal)
    (hrun : runCode before (fuel + 1) current store environment
      (.case scrutinee peelNat alternatives) = .ok sourceOut) :
    ∃ targetOut,
      runCode after (fuel + 1) current store environment
          (.case scrutinee peelNat alternatives) = .ok targetOut ∧
        RunHistoryIso base sourceOut targetOut := by
  rw [runCode.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hscrutinee : resolveAtom environment scrutinee with
  | error error =>
      rw [hscrutinee] at hrun
      simp only [bind, Except.bind] at hrun
      contradiction
  | ok value =>
      rw [hscrutinee] at hrun
      simp only [bind, Except.bind] at hrun ⊢
      have hvalue := resolveAtom_selfIso henvironment hscrutinee
      cases value with
      | erased => simp at hrun
      | lit literal =>
          cases literal with
          | str value => simp at hrun
          | nat value =>
              cases peelNat with
              | false => simp at hrun
              | true =>
                  cases value with
                  | zero =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 0) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          simp only [hfind] at hrun ⊢
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero =>
                                  exact smaller.runCode current store base
                                    environment henvironment body sourceOut
                                    hrun
                              | succ fields => simp at hrun
                  | succ value =>
                      cases hfind : alternatives.find?
                          (fun alternative => alternative.cidx == 1) with
                      | none => simp [hfind] at hrun
                      | some alternative =>
                          simp only [hfind] at hrun ⊢
                          cases alternative with
                          | mk cidx fields body =>
                              cases fields with
                              | zero => simp at hrun
                              | succ fields =>
                                  cases fields with
                                  | zero =>
                                      exact smaller.runCode current store base
                                        (.lit (.nat value) :: environment)
                                        (.cons .lit henvironment) body
                                        sourceOut hrun
                                  | succ fields => simp at hrun
      | loc location =>
          cases hbox : store.get? location with
          | none => simp [hbox] at hrun
          | some box =>
              simp only [hbox] at hrun ⊢
              cases hnode : box.node with
              | papN function arity arguments =>
                  simp [hnode] at hrun
              | ctorN identity fields =>
                  cases hfind : alternatives.find?
                      (fun alternative => alternative.cidx == identity.cidx) with
                  | none => simp [hnode, hfind] at hrun
                  | some alternative =>
                      simp only [hfind] at hrun ⊢
                      cases alternative with
                      | mk cidx fieldCount body =>
                          by_cases hcount : fields.size = fieldCount
                          · simp [hnode, hfind, hcount] at hrun ⊢
                            cases hvalue with
                            | @loc _ _ hrel =>
                                obtain ⟨rightBox, hrightBox, hboxIso⟩ :=
                                  base.boxes hrel hbox
                                have hrightBoxEq : rightBox = box := by
                                  exact Option.some.inj
                                    (hrightBox.symm.trans hbox)
                                subst rightBox
                                have hfields : RValsIso base.locRel
                                    fields.toList fields.toList := by
                                  have hnodeIso : NodeIso base.locRel
                                      box.node box.node := hboxIso.node
                                  rw [hnode] at hnodeIso
                                  cases hnodeIso with
                                  | ctor hfields => exact hfields
                                have hfold : RValsIso base.locRel
                                    (fields.toList.reverse ++ environment)
                                    (fields.toList.reverse ++ environment) :=
                                  hfields.reverse.append henvironment
                                obtain ⟨targetOut, htarget, hiso⟩ :=
                                  smaller.runCode current store base
                                    (fields.toList.reverse ++ environment)
                                    hfold body sourceOut hrun
                                rcases targetOut with
                                  ⟨targetStore, targetValue⟩
                                exact ⟨targetStore, targetValue,
                                  htarget, hiso⟩
                          · simp [hnode, hfind, hcount] at hrun

private theorem runCode_rewriteStep
    {before after : Ctx} {fuel : Nat}
    (smaller : EvalRewriteAt before after fuel) :
    ∀ (current : FnDef) (store : Store)
      (base : HeapHistoryIso store store) (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (input : Code) (sourceOut : Store × RVal),
      runCode before (fuel + 1) current store environment input =
          .ok sourceOut →
      ∃ targetOut,
        runCode after (fuel + 1) current store environment input =
            .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro current store base environment henvironment input sourceOut hrun
  cases input with
  | ret atom =>
      simpa [runCode] using
        (runCode_historyIso base henvironment hrun)
  | case scrutinee peelNat alternatives =>
      exact runCode_caseRewriteAt smaller current store base environment
        henvironment scrutinee peelNat alternatives sourceOut hrun
  | letOp operation rest =>
      rw [runCode.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hoperation : runOp before fuel current store environment
          operation with
      | error error =>
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok operationOut =>
          rcases operationOut with ⟨middle, sourceValue⟩
          rw [hoperation] at hrun
          simp only [bind, Except.bind] at hrun
          obtain ⟨targetOperationOut, htargetOperation,
              operationHeap, hbaseOperation, hvalue⟩ :=
            smaller.runOp current store base environment henvironment
              operation (middle, sourceValue) hoperation
          rcases targetOperationOut with ⟨targetMiddle, targetValue⟩
          have hrestEnvironment : RValsIso operationHeap.locRel
              (sourceValue :: environment) (targetValue :: environment) :=
            .cons hvalue (hbaseOperation.rvals henvironment)
          obtain ⟨targetOut, htargetRest, hrestIso⟩ :=
            runCode_crossOfSame smaller operationHeap hrestEnvironment hrun
          refine ⟨targetOut, ?_,
            RunHistoryIso.weaken hbaseOperation hrestIso⟩
          rw [htargetOperation]
          simp only [bind, Except.bind]
          exact htargetRest

private theorem runOp_rewriteStep
    {before after : Ctx} (abstract : AbstractEnvironment before after)
    {fuel : Nat} (smaller : EvalRewriteAt before after fuel) :
    ∀ (current : FnDef) (store : Store)
      (base : HeapHistoryIso store store) (environment : List RVal),
    RValsIso base.locRel environment environment →
    ∀ (operation : Op) (sourceOut : Store × RVal),
      runOp before (fuel + 1) current store environment operation =
          .ok sourceOut →
      ∃ targetOut,
        runOp after (fuel + 1) current store environment operation =
            .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro current store base values hvalues operation sourceOut hrun
  have hsourceRun := hrun
  let drops := dropCtxEqAt before after fuel
  cases operation with
  | pure atom =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | alloc world identity arguments =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | reuse target identity arguments =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | free target =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | dup target =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | drop target =>
      simpa [runOp, drops.dropVal] using
        (runOp_historyIso base hvalues hrun)
  | dropU target =>
      simpa [runOp, drops.dropUVal] using
        (runOp_historyIso base hvalues hrun)
  | fetch target field =>
      simpa [runOp] using (runOp_historyIso base hvalues hrun)
  | call function arguments =>
      rw [runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases harguments : resolveAtoms values arguments with
      | error error =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok arguments =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          exact smaller.invoke function arguments store base
            (resolveAtoms_selfIso hvalues harguments) sourceOut hrun
  | callSelf arguments =>
      rw [runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases harguments : resolveAtoms values arguments with
      | error error =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok arguments =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          have hargumentValues := resolveAtoms_selfIso hvalues harguments
          by_cases harity : arguments.length = current.arity
          · simp [harity] at hrun
            cases hbody : runCode before fuel current store arguments.reverse
                current.body with
            | error error =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok bodyOut =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                have hout := (checkResultWorld_ok hrun).1
                subst sourceOut
                obtain ⟨targetBodyOut, htargetBody, bodyHeap,
                    hbaseBody, hbodyValue⟩ :=
                  smaller.runCode current store base arguments.reverse
                    hargumentValues.reverse current.body bodyOut hbody
                rcases bodyOut with ⟨bodyStore, bodyValue⟩
                rcases targetBodyOut with
                  ⟨targetBodyStore, targetBodyValue⟩
                have htargetWorld := checkResultWorld_historyIso bodyHeap
                  hbodyValue current.result hrun
                refine ⟨(targetBodyStore, targetBodyValue), ?_, bodyHeap,
                  hbaseBody, hbodyValue⟩
                simp [harity, htargetBody]
                simpa only [bind, Except.bind] using htargetWorld
          · have harityBool : (arguments.length != current.arity) = true := by
              simpa using harity
            simp [harityBool] at hrun
  | papp function atoms =>
      rw [runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases harguments : resolveAtoms values atoms with
      | error error =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok arguments =>
          rw [harguments] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          cases hdeclaration : before.decls function with
          | none => simp [hdeclaration] at hrun
          | some declaration =>
              obtain ⟨targetDeclaration, htargetDeclaration, harity⟩ :=
                abstract.declaration hdeclaration
              simp only [hdeclaration] at hrun
              simp only [htargetDeclaration]
              by_cases hless : arguments.length < declArity declaration
              · have htargetLess :
                    arguments.length < declArity targetDeclaration := by
                  rw [harity]
                  exact hless
                obtain ⟨selfOut, hselfRun, hiso⟩ :=
                  runOp_historyIso base hvalues hsourceRun
                have hout : selfOut = sourceOut :=
                  Except.ok.inj (hselfRun.symm.trans hsourceRun)
                subst selfOut
                refine ⟨sourceOut, ?_, hiso⟩
                simp only [hless, if_true, Except.ok.injEq] at hrun
                simpa [harity, hless] using
                  congrArg (fun output =>
                    (Except.ok output : Except Err (Store × RVal))) hrun
              · simp [hless] at hrun
  | apply function arguments =>
      rw [runOp.eq_def] at hrun ⊢
      dsimp only at hrun ⊢
      cases hfunction : resolveAtom values function with
      | error error =>
          rw [hfunction] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok functionValue =>
          rw [hfunction] at hrun
          simp only [bind, Except.bind] at hrun ⊢
          cases harguments : resolveAtoms values arguments with
          | error error =>
              rw [harguments] at hrun
              simp only [bind, Except.bind] at hrun
              contradiction
          | ok argumentValues =>
              rw [harguments] at hrun
              simp only [bind, Except.bind] at hrun ⊢
              exact smaller.applyGo store base functionValue argumentValues
                (resolveAtom_selfIso hvalues hfunction)
                (resolveAtoms_selfIso hvalues harguments) sourceOut hrun
  | extern function arguments =>
      simpa [runOp, callScalarOracle, abstract.oracle_eq] using
        (runOp_historyIso base hvalues hrun)

private theorem invoke_rewriteStep
    {before after : Ctx} (abstract : AbstractEnvironment before after)
    {fuel : Nat} (smaller : EvalRewriteAt before after fuel) :
    ∀ (function : Address) (arguments : List RVal) (store : Store)
      (base : HeapHistoryIso store store),
    RValsIso base.locRel arguments arguments →
    ∀ (sourceOut : Store × RVal),
      IxIR1.invoke before (fuel + 1) function arguments store =
          .ok sourceOut →
      ∃ targetOut,
        IxIR1.invoke after (fuel + 1) function arguments store =
            .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro function arguments store base harguments sourceOut hrun
  have hsourceRun := hrun
  rw [IxIR1.invoke.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases hdeclaration : before.decls function with
  | none => simp [hdeclaration] at hrun
  | some declaration =>
      cases declaration with
      | extern arity =>
          have htargetDeclaration := abstract.extern hdeclaration
          simp only [hdeclaration] at hrun
          simp only [htargetDeclaration]
          obtain ⟨selfOut, hselfRun, hiso⟩ :=
            invoke_historyIso base harguments hsourceRun
          have hout : selfOut = sourceOut :=
            Except.ok.inj (hselfRun.symm.trans hsourceRun)
          subst selfOut
          refine ⟨sourceOut, ?_, hiso⟩
          simpa [callScalarOracle, abstract.oracle_eq] using hrun
      | fn source =>
          obtain ⟨target, htargetDeclaration, harity, hresult,
              hbodyRefines⟩ := abstract.function hdeclaration
          simp only [hdeclaration] at hrun
          simp only [htargetDeclaration]
          by_cases hsame : arguments.length = source.arity
          · have htargetSame : arguments.length = target.arity := by
              rw [harity]
              exact hsame
            simp [hsame] at hrun
            cases hbody : runCode before fuel source store arguments.reverse
                source.body with
            | error error =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                contradiction
            | ok bodyOut =>
                rw [hbody] at hrun
                simp only [bind, Except.bind] at hrun
                have hout := (checkResultWorld_ok hrun).1
                subst sourceOut
                let self := base.trans base.symm
                have hselfArguments : RValsIso self.locRel
                    arguments.reverse arguments.reverse := by
                  exact (harguments.trans harguments.symm).reverse
                obtain ⟨localOut, hlocalRun, hlocalIso⟩ :=
                  hbodyRefines self (by simpa using hsame)
                    hselfArguments hbody
                obtain ⟨targetOut, htargetBody, hctxIso⟩ :=
                  smaller.runCode target store base arguments.reverse
                    harguments.reverse target.body localOut hlocalRun
                have hbodyIso : RunHistoryIso base bodyOut targetOut :=
                  RunHistoryIso.weaken (selfLeft_compose_extends base)
                    (hlocalIso.trans hctxIso)
                rcases bodyOut with ⟨bodyStore, bodyValue⟩
                rcases targetOut with ⟨targetStore, targetValue⟩
                obtain ⟨finalHeap, hbaseFinal, hvalue⟩ := hbodyIso
                have htargetWorld := checkResultWorld_historyIso finalHeap
                  hvalue source.result hrun
                refine ⟨(targetStore, targetValue), ?_, finalHeap,
                  hbaseFinal, hvalue⟩
                simp [htargetSame, htargetBody, hresult]
                simpa only [bind, Except.bind] using htargetWorld
          · have htargetDifferent : arguments.length ≠ target.arity := by
              intro heq
              exact hsame (heq.trans harity)
            simp [hsame] at hrun

private theorem applyGo_rewriteStep
    {before after : Ctx} {fuel : Nat}
    (smaller : EvalRewriteAt before after fuel) :
    ∀ (store : Store) (base : HeapHistoryIso store store)
      (function : RVal) (arguments : List RVal),
    RValIso base.locRel function function →
    RValsIso base.locRel arguments arguments →
    ∀ (sourceOut : Store × RVal),
      IxIR1.applyGo before (fuel + 1) store function arguments =
          .ok sourceOut →
      ∃ targetOut,
        IxIR1.applyGo after (fuel + 1) store function arguments =
            .ok targetOut ∧
          RunHistoryIso base sourceOut targetOut := by
  intro store base function arguments hfunction harguments sourceOut hrun
  have hsourceRun := hrun
  let drops := dropCtxEqAt before after fuel
  rw [IxIR1.applyGo.eq_def] at hrun ⊢
  dsimp only at hrun ⊢
  cases function with
  | lit literal => simp at hrun
  | erased =>
      cases hdrop : dropMany before fuel store arguments with
      | error error =>
          rw [hdrop] at hrun
          simp only [bind, Except.bind] at hrun
          contradiction
      | ok next =>
          rw [hdrop] at hrun
          simp only [bind, Except.bind, Except.ok.injEq] at hrun
          subst sourceOut
          rw [drops.dropMany store arguments, hdrop]
          obtain ⟨selfOut, hselfRun, hiso⟩ :=
            applyGo_historyIso base hfunction harguments hsourceRun
          have hselfOut : selfOut = (next, .erased) :=
            Except.ok.inj (hselfRun.symm.trans hsourceRun)
          subst selfOut
          exact ⟨(next, .erased), rfl, hiso⟩
  | loc location =>
      cases hbox : store.get? location with
      | none => simp [hbox] at hrun
      | some box =>
          simp only [hbox] at hrun ⊢
          cases hnode : box.node with
          | ctorN identity fields => simp [hnode] at hrun
          | papN called arity captured =>
              rw [hnode] at hrun
              dsimp only at hrun ⊢
              cases hfunction with
              | @loc _ _ hrel =>
                  obtain ⟨rightBox, hrightBox, hboxIso⟩ :=
                    base.boxes hrel hbox
                  have hrightBoxEq : rightBox = box := by
                    exact Option.some.inj (hrightBox.symm.trans hbox)
                  subst rightBox
                  have hcaptured : RValsIso base.locRel
                      captured.toList captured.toList := by
                    have hnodeIso : NodeIso base.locRel box.node box.node :=
                      hboxIso.node
                    rw [hnode] at hnodeIso
                    cases hnodeIso with
                    | pap hcaptured => exact hcaptured
                  cases hdup : dupVals store captured.toList with
                  | error error =>
                      rw [hdup] at hrun
                      simp only [bind, Except.bind] at hrun
                      contradiction
                  | ok duplicated =>
                      rw [hdup] at hrun
                      simp only [bind, Except.bind] at hrun ⊢
                      obtain ⟨duplicatedRight, hrightDup, duplicateHeap,
                          hbaseDuplicate⟩ :=
                        dupVals_historyIso base hcaptured hdup
                      have hduplicated : duplicatedRight = duplicated :=
                        Except.ok.inj (hrightDup.symm.trans hdup)
                      subst duplicatedRight
                      rw [drops.dropVal duplicated (.loc location)]
                      cases hdrop : dropVal before fuel duplicated
                          (.loc location) with
                      | error error =>
                          rw [hdrop] at hrun
                          simp only [bind, Except.bind] at hrun
                          contradiction
                      | ok ready =>
                          rw [hdrop] at hrun
                          simp only [bind, Except.bind] at hrun ⊢
                          obtain ⟨readyRight, hrightDrop, readyHeap,
                              hduplicateReady⟩ :=
                            dropVal_historyIso duplicateHeap
                              (hbaseDuplicate.rval (.loc hrel)) hdrop
                          have hready : readyRight = ready :=
                            Except.ok.inj (hrightDrop.symm.trans hdrop)
                          subst readyRight
                          let hbaseReady : base.Extends readyHeap :=
                            hbaseDuplicate.trans hduplicateReady
                          let total := captured.toList ++ arguments
                          have htotal : RValsIso readyHeap.locRel total total :=
                            (hbaseReady.rvals hcaptured).append
                              (hbaseReady.rvals harguments)
                          by_cases hunder : total.length < arity
                          · have hunderRaw :
                                (captured.toList ++ arguments).length <
                                  arity := by
                              simpa [total] using hunder
                            have hunderSize :
                                captured.size + arguments.length < arity := by
                              simpa [total] using hunder
                            simp only [hunderRaw, if_true,
                              Except.ok.injEq] at hrun
                            subst sourceOut
                            let next := readyHeap.alloc (world := .shared)
                              (leftNode := .papN called arity total.toArray)
                              (rightNode := .papN called arity total.toArray)
                              (.pap (by simpa [total] using htotal))
                            have hreadyNext : readyHeap.Extends next := by
                              intro leftLoc rightLoc hknown
                              exact .inr hknown
                            have hfresh : RValIso next.locRel
                                (.loc ready.nodes.size)
                                (.loc ready.nodes.size) := by
                              exact .loc (.inl ⟨rfl, rfl⟩)
                            let allocated := ready.allocNode .shared
                              (.papN called arity total.toArray)
                            refine ⟨(allocated.1, .loc allocated.2), ?_, next,
                              hbaseReady.trans hreadyNext, ?_⟩
                            · simpa [total, allocated, hunderSize]
                            · simpa [allocated, Store.allocNode] using hfresh
                          · by_cases hexact : total.length = arity
                            · have hunderRaw :
                                  ¬(captured.toList ++ arguments).length <
                                    arity := by
                                simpa [total] using hunder
                              have hexactRaw :
                                  (captured.toList ++ arguments).length =
                                    arity := by
                                simpa [total] using hexact
                              simp [hunderRaw, hexactRaw] at hrun
                              obtain ⟨targetOut, htargetInvoke, hiso⟩ :=
                                smaller.invoke called total ready readyHeap
                                  htotal sourceOut (by simpa [total] using hrun)
                              refine ⟨targetOut, ?_,
                                RunHistoryIso.weaken hbaseReady hiso⟩
                              simpa [total, hunderRaw, hexactRaw] using
                                htargetInvoke
                            · have hunderRaw :
                                  ¬(captured.toList ++ arguments).length <
                                    arity := by
                                simpa [total] using hunder
                              have hexactRaw :
                                  (captured.toList ++ arguments).length ≠
                                    arity := by
                                simpa [total] using hexact
                              have hunderSize :
                                  ¬captured.size + arguments.length <
                                    arity := by
                                simpa [total] using hunder
                              have hexactSize :
                                  captured.size + arguments.length ≠
                                    arity := by
                                simpa [total] using hexact
                              simp [hunderSize, hexactSize] at hrun
                              cases hinvoke : IxIR1.invoke before fuel called
                                  (total.take arity) ready with
                              | error error =>
                                  rw [hinvoke] at hrun
                                  simp only [bind, Except.bind] at hrun
                                  contradiction
                              | ok calledOut =>
                                  rcases calledOut with
                                    ⟨calledStore, calledValue⟩
                                  rw [hinvoke] at hrun
                                  simp only [bind, Except.bind] at hrun
                                  obtain ⟨targetCalledOut, htargetInvoke,
                                      callHeap, hreadyCall, hcalledValue⟩ :=
                                    smaller.invoke called (total.take arity)
                                      ready readyHeap (htotal.take arity)
                                      (calledStore, calledValue) hinvoke
                                  rcases targetCalledOut with
                                    ⟨targetCalledStore, targetCalledValue⟩
                                  obtain ⟨targetOut, htargetApply, hiso⟩ :=
                                    applyGo_crossOfSame smaller callHeap
                                      hcalledValue
                                      (hreadyCall.rvals (htotal.drop arity))
                                      (by simpa [total] using hrun)
                                  refine ⟨targetOut, ?_,
                                    RunHistoryIso.weaken
                                      (hbaseReady.trans hreadyCall) hiso⟩
                                  simp [hunderSize, hexactSize]
                                  rw [htargetInvoke]
                                  simp only [bind, Except.bind]
                                  exact htargetApply

private theorem evalRewriteAt {before after : Ctx}
    (abstract : AbstractEnvironment before after) :
    ∀ fuel, EvalRewriteAt before after fuel := by
  intro fuel
  induction fuel with
  | zero =>
      constructor <;> intros <;>
        simp [runCode, runOp, IxIR1.invoke, IxIR1.applyGo] at *
  | succ fuel smaller =>
      exact ⟨runCode_rewriteStep smaller,
        runOp_rewriteStep abstract smaller,
        invoke_rewriteStep abstract smaller,
        applyGo_rewriteStep smaller⟩

/-- A successful run in the source context is reproduced in any abstractly
related target environment.  The theorem accepts arbitrary related entry
stores and environments; no closure or canonical-location assumption is
required. -/
theorem runCode_abstractEnvironment
    {before after : Ctx} (abstract : AbstractEnvironment before after)
    {fuel : Nat} {current : FnDef} {left right : Store}
    (heap : HeapHistoryIso left right)
    {leftEnvironment rightEnvironment : List RVal}
    (henvironments : RValsIso heap.locRel
      leftEnvironment rightEnvironment)
    {input : Code} {sourceOut : Store × RVal}
    (hrun : runCode before fuel current left leftEnvironment input =
      .ok sourceOut) :
    ∃ targetOut,
      runCode after fuel current right rightEnvironment input = .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  runCode_crossOfSame (evalRewriteAt abstract fuel) heap henvironments hrun

/-- Dynamic application form of `runCode_abstractEnvironment`. -/
theorem applyGo_abstractEnvironment
    {before after : Ctx} (abstract : AbstractEnvironment before after)
    {fuel : Nat} {left right : Store}
    (heap : HeapHistoryIso left right)
    {leftFunction rightFunction : RVal}
    {leftArguments rightArguments : List RVal}
    (hfunction : RValIso heap.locRel leftFunction rightFunction)
    (harguments : RValsIso heap.locRel leftArguments rightArguments)
    {sourceOut : Store × RVal}
    (hrun : IxIR1.applyGo before fuel left leftFunction leftArguments =
      .ok sourceOut) :
    ∃ targetOut,
      IxIR1.applyGo after fuel right rightFunction rightArguments =
          .ok targetOut ∧
        RunHistoryIso heap sourceOut targetOut :=
  applyGo_crossOfSame (evalRewriteAt abstract fuel) heap hfunction harguments
    hrun

end Compilatrix.IxIR1.Sim
