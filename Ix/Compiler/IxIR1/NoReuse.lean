import Ix.Compiler.IxIR1.Reclamation
import Ix.Compiler.IxIR1.LowerStateSim

/-!
# Syntactic and dynamic absence of IxIR₁ reuse

`Reclamation.AllocationOrderInvariant` is a semantic trace invariant.  This
module supplies its compiler-facing premise: the current IxIR₀→IxIR₁
lowerer never emits `Op.reuse`, and execution of a closed reuse-free program
therefore leaves the fresh store's reuse counter at zero.
-/

namespace Ix.Compiler.IxIR1.NoReuse

open Ix.Compiler.IxIR1
open Ix.Compiler.IxIR1.Lower

private theorem bindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem bindErr {error α β : Type} (err : error)
    (next : α → Except error β) :
    ((Except.error err : Except error α) >>= next) = .error err := rfl

/-- The one instruction excluded by the current append-only lowerer. -/
def OpNoReuse : Op → Prop
  | .reuse .. => False
  | _ => True

mutual

/-- Every operation and every recursively nested alternative is reuse-free. -/
def CodeNoReuse : Code → Prop
  | .ret _ => True
  | .letOp op rest => OpNoReuse op ∧ CodeNoReuse rest
  | .case _ _ alternatives =>
      ∀ alternative ∈ alternatives, AltNoReuse alternative

def AltNoReuse : Alt → Prop
  | .mk _ _ body => CodeNoReuse body

end

/-- Every callable function body in the runtime environment is reuse-free. -/
def CtxNoReuse (ctx : Ctx) : Prop :=
  ∀ {address definition},
    ctx.decls address = some (.fn definition) → CodeNoReuse definition.body

/-! ## Executable reflection

The compiler proves reuse-freedom before content addressing, but the final
artifact may content-deduplicate declarations.  These small structural checks
let downstream attachment boundaries validate the exact emitted syntax and
reflect the result back into the propositions consumed by simulation. -/

/-- Executable counterpart of `OpNoReuse`. -/
def checkOp : Op → Bool
  | .reuse .. => false
  | _ => true

mutual

/-- Executable counterpart of `CodeNoReuse`. -/
def checkCode : Code → Bool
  | .ret _ => true
  | .letOp operation rest => checkOp operation && checkCode rest
  | .case _ _ alternatives => checkAlternatives alternatives.toList

/-- Executable counterpart of `AltNoReuse`. -/
def checkAlt : Alt → Bool
  | .mk _ _ body => checkCode body

/-- Structural list walk used beneath case-alternative arrays. -/
def checkAlternatives : List Alt → Bool
  | [] => true
  | head :: tail => checkAlt head && checkAlternatives tail

end

theorem checkOp_eq_true_iff (operation : Op) :
    checkOp operation = true ↔ OpNoReuse operation := by
  cases operation <;> simp [checkOp, OpNoReuse]

/-- The executable recursive syntax walk decides exactly `CodeNoReuse`. -/
theorem checkCode_eq_true_iff (code : Code) :
    checkCode code = true ↔ CodeNoReuse code := by
  apply Code.rec
    (motive_1 := fun operation =>
      checkOp operation = true ↔ OpNoReuse operation)
    (motive_2 := fun alternative =>
      checkAlt alternative = true ↔ AltNoReuse alternative)
    (motive_3 := fun code =>
      checkCode code = true ↔ CodeNoReuse code)
    (motive_4 := fun alternatives =>
      checkAlternatives alternatives.toList = true ↔
        ∀ alternative ∈ alternatives, AltNoReuse alternative)
    (motive_5 := fun alternatives =>
      checkAlternatives alternatives = true ↔
        ∀ alternative ∈ alternatives, AltNoReuse alternative)
    (pure := by intros; simp [checkOp, OpNoReuse])
    (alloc := by intros; simp [checkOp, OpNoReuse])
    (reuse := by intros; simp [checkOp, OpNoReuse])
    (free := by intros; simp [checkOp, OpNoReuse])
    (dup := by intros; simp [checkOp, OpNoReuse])
    (drop := by intros; simp [checkOp, OpNoReuse])
    (dropU := by intros; simp [checkOp, OpNoReuse])
    (fetch := by intros; simp [checkOp, OpNoReuse])
    (call := by intros; simp [checkOp, OpNoReuse])
    (callSelf := by intros; simp [checkOp, OpNoReuse])
    (papp := by intros; simp [checkOp, OpNoReuse])
    (apply := by intros; simp [checkOp, OpNoReuse])
    (extern := by intros; simp [checkOp, OpNoReuse])
    (mk := by
      intro cidx fields body hbody
      simpa [checkAlt, AltNoReuse] using hbody)
    (ret := by intros; simp [checkCode, CodeNoReuse])
    (letOp := by
      intro operation rest hoperation hrest
      simp [checkCode, CodeNoReuse, hoperation, hrest])
    (case := by
      intro scrutinee peelNat alternatives halternatives
      simpa [checkCode, CodeNoReuse] using halternatives)
    (by
      intro alternatives halternatives
      simpa using halternatives)
    (by simp [checkAlternatives])
    (by
      intro head tail hhead htail
      simp [checkAlternatives, hhead, htail])
    code

/-- A difference-list emitter preserves reuse-free continuations. -/
def EmitNoReuse (emit : Emit) : Prop :=
  ∀ code, CodeNoReuse code → CodeNoReuse (emit code)

theorem emitNoReuse_id : EmitNoReuse (_root_.id : Emit) := by
  intro code hcode
  exact hcode

theorem emitNoReuse_emitOp {op : Op} (hop : OpNoReuse op) :
    EmitNoReuse (emitOp op) := by
  intro code hcode
  simpa [emitOp, CodeNoReuse] using And.intro hop hcode

theorem emitNoReuse_comp {first second : Emit}
    (hfirst : EmitNoReuse first) (hsecond : EmitNoReuse second) :
    EmitNoReuse (first ∘ second) := by
  intro code hcode
  exact hfirst (second code) (hsecond code hcode)

/-- Retaining pap captures changes only RC state. -/
theorem dupVals_reuses {store store' : Store} {values : List RVal}
    (heval : dupVals store values = .ok store') :
    store'.reuses = store.reuses := by
  induction values generalizing store with
  | nil =>
    change (.ok store : Except Err Store) = .ok store' at heval
    injection heval with hstore
    subst store'
    rfl
  | cons head tail ih =>
    cases head with
    | lit literal =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih heval
    | erased =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      exact ih heval
    | loc location =>
      simp only [Ix.Compiler.IxIR1.dupVals, List.foldlM_cons] at heval
      cases hget : store.get? location with
      | none => simp [hget, bindErr] at heval
      | some box =>
        cases box with
        | mk world rc node =>
          cases world with
          | unique => simp [hget, bindErr] at heval
          | shared =>
            simp only [hget] at heval
            have htail := ih heval
            simpa [Sim.incRcStore, Store.setBox, Store.rcTick] using htail

private def DropReusesAt (fuel : Nat) : Prop :=
  (∀ ctx store value store',
    dropVal ctx fuel store value = .ok store' →
      store'.reuses = store.reuses) ∧
  (∀ ctx store values store',
    dropMany ctx fuel store values = .ok store' →
      store'.reuses = store.reuses) ∧
  (∀ ctx store value store',
    dropUVal ctx fuel store value = .ok store' →
      store'.reuses = store.reuses) ∧
  (∀ ctx store values store',
    dropManyU ctx fuel store values = .ok store' →
      store'.reuses = store.reuses)

private theorem dropReusesAt : ∀ fuel, DropReusesAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx store value store' heval
      rw [dropVal.eq_def] at heval
      simp at heval
    · intro ctx store values store' heval
      rw [dropMany.eq_def] at heval
      simp at heval
    · intro ctx store value store' heval
      rw [dropUVal.eq_def] at heval
      simp at heval
    · intro ctx store values store' heval
      rw [dropManyU.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihVal, ihMany, ihUVal, ihUMany⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx store value store' heval
      cases value with
      | lit literal =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | erased =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | loc location =>
        rw [dropVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? location with
        | none => simp [hget] at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at heval
            | shared =>
              dsimp only at heval
              by_cases hrc : rc = 1
              · subst rc
                have hbeq : ((1 : Nat) == 1) = true := by decide
                rw [hbeq] at heval
                cases node with
                | ctorN cid fields =>
                  have htail := ihMany _ _ _ _ heval
                  simpa [Store.rcTick, Store.kill] using htail
                | papN address arity args =>
                  have htail := ihMany _ _ _ _ heval
                  simpa [Store.rcTick, Store.kill] using htail
              · have hbeq : (rc == 1) = false := by simp [hrc]
                rw [hbeq] at heval
                injection heval with hstore
                subst store'
                simp [Store.rcTick, Store.setBox]
    · intro ctx store values store' heval
      cases values with
      | nil =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | cons value values =>
        rw [dropMany.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropVal ctx fuel store value with
        | error err => rw [hfirst, bindErr] at heval; contradiction
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact (ihMany _ _ _ _ heval).trans (ihVal _ _ _ _ hfirst)
    · intro ctx store value store' heval
      cases value with
      | lit literal =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | erased =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | loc location =>
        rw [dropUVal.eq_def] at heval
        dsimp only at heval
        cases hget : store.get? location with
        | none => simp [hget] at heval
        | some box =>
          rw [hget] at heval
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at heval
            | unique =>
              cases node with
              | ctorN cid fields =>
                have htail := ihUMany _ _ _ _ heval
                simpa [Store.kill] using htail
              | papN address arity args => simp at heval
    · intro ctx store values store' heval
      cases values with
      | nil =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        injection heval with hstore
        subst store'
        rfl
      | cons value values =>
        rw [dropManyU.eq_def] at heval
        dsimp only at heval
        cases hfirst : dropUVal ctx fuel store value with
        | error err => rw [hfirst, bindErr] at heval; contradiction
        | ok middle =>
          rw [hfirst, bindOk] at heval
          exact (ihUMany _ _ _ _ heval).trans (ihUVal _ _ _ _ hfirst)

theorem dropVal_reuses {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} (heval : dropVal ctx fuel store value = .ok store') :
    store'.reuses = store.reuses :=
  (dropReusesAt fuel).1 ctx store value store' heval

theorem dropMany_reuses {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal}
    (heval : dropMany ctx fuel store values = .ok store') :
    store'.reuses = store.reuses :=
  (dropReusesAt fuel).2.1 ctx store values store' heval

theorem dropUVal_reuses {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {value : RVal} (heval : dropUVal ctx fuel store value = .ok store') :
    store'.reuses = store.reuses :=
  (dropReusesAt fuel).2.2.1 ctx store value store' heval

theorem dropManyU_reuses {ctx : Ctx} {fuel : Nat} {store store' : Store}
    {values : List RVal}
    (heval : dropManyU ctx fuel store values = .ok store') :
    store'.reuses = store.reuses :=
  (dropReusesAt fuel).2.2.2 ctx store values store' heval

private def EvalReusesAt (fuel : Nat) : Prop :=
  (∀ ctx cur store env code store' value,
    CtxNoReuse ctx → CodeNoReuse cur.body → CodeNoReuse code →
    runCode ctx fuel cur store env code = .ok (store', value) →
      store'.reuses = store.reuses) ∧
  (∀ ctx cur store env op store' value,
    CtxNoReuse ctx → CodeNoReuse cur.body → OpNoReuse op →
    runOp ctx fuel cur store env op = .ok (store', value) →
      store'.reuses = store.reuses) ∧
  (∀ ctx address args store store' value,
    CtxNoReuse ctx →
    invoke ctx fuel address args store = .ok (store', value) →
      store'.reuses = store.reuses) ∧
  (∀ ctx store function args store' value,
    CtxNoReuse ctx →
    applyGo ctx fuel store function args = .ok (store', value) →
      store'.reuses = store.reuses)

/-- Successful execution of reuse-free code in a reuse-free declaration
environment preserves the reuse counter exactly. -/
private theorem evalReusesAt : ∀ fuel, EvalReusesAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value hctx hcur hcode heval
      rw [runCode.eq_def] at heval
      simp at heval
    · intro ctx cur store env op store' value hctx hcur hop heval
      rw [runOp.eq_def] at heval
      simp at heval
    · intro ctx address args store store' value hctx heval
      rw [invoke.eq_def] at heval
      simp at heval
    · intro ctx store function args store' value hctx heval
      rw [applyGo.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value hctx hcur hcode heval
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          rfl
      | letOp op rest =>
        simp only [CodeNoReuse] at hcode
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hopEval : runOp ctx fuel cur store env op with
        | error err => rw [hopEval, bindErr] at heval; contradiction
        | ok result =>
          rcases result with ⟨middle, opValue⟩
          rw [hopEval, bindOk] at heval
          exact (ihCode _ _ _ _ _ _ _ hctx hcur hcode.2 heval).trans
            (ihOp _ _ _ _ _ _ _ hctx hcur hcode.1 hopEval)
      | case scrut peelNat alternatives =>
        simp only [CodeNoReuse] at hcode
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hscrut : resolveAtom env scrut with
        | error err => rw [hscrut, bindErr] at heval; contradiction
        | ok scrutValue =>
          rw [hscrut, bindOk] at heval
          cases scrutValue with
          | loc location =>
            dsimp only at heval
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity captured => simp at heval
                | ctorN cid fields =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == cid.cidx) with
                  | none => simp [halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at heval
                        exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo heval
                      · simp [halt, hsize] at heval
          | lit literal =>
            cases literal with
            | str string => simp at heval
            | nat n =>
              cases hpeel : peelNat with
              | false => simp [hpeel] at heval
              | true =>
                cases n with
                | zero =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == 0) with
                  | none => simp [hpeel, halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at heval
                        exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo heval
                      | succ fieldCount => simp [hpeel, halt] at heval
                | succ n =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == 1) with
                  | none => simp [hpeel, halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases fieldCount with
                      | zero => simp [hpeel, halt] at heval
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at heval
                          exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo heval
                        | succ fieldCount => simp [hpeel, halt] at heval
          | erased => simp at heval
    · intro ctx cur store env op store' value hctx hcur hop heval
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          rfl
      | alloc world cid atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          simp [Store.allocNode]
      | reuse target cid atoms =>
        simp [OpNoReuse] at hop
      | free target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | shared => simp at heval
                | unique =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  simp [Store.kill]
      | dup target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | unique => simp at heval
                | shared =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  simp [Store.setBox, Store.rcTick]
      | drop target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | loc location =>
            dsimp only at heval
            cases hdrop : dropVal ctx fuel store (.loc location) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact dropVal_reuses hdrop
      | dropU target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
          | loc location =>
            dsimp only at heval
            cases hdrop : dropUVal ctx fuel store (.loc location) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact dropUVal_reuses hdrop
      | fetch target field =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity captured => simp at heval
                | ctorN cid fields =>
                  cases hfield : fields[field]? with
                  | none => simp [hfield] at heval
                  | some result =>
                    simp only [hfield] at heval
                    have hpair := Except.ok.inj heval
                    cases hpair
                    rfl
      | call address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          exact ihInvoke _ _ _ _ _ _ hctx heval
      | callSelf atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hbody : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err => rw [hbody, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hbody, bindOk] at heval
              obtain ⟨hresult, _⟩ := Sim.checkResultWorld_ok heval
              cases hresult
              exact ihCode _ _ _ _ _ _ _ hctx hcur hcur hbody
          · simp [harity] at heval
      | papp address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases hdecl : ctx.decls address with
          | none => simp [hdecl] at heval
          | some declaration =>
            simp only [hdecl] at heval
            by_cases hlength : values.length < declArity declaration
            · simp only [hlength, if_true] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              simp [Store.allocNode]
            · simp [hlength] at heval
      | apply function atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hfunction : resolveAtom env function with
        | error err => rw [hfunction, bindErr] at heval; contradiction
        | ok functionValue =>
          rw [hfunction, bindOk] at heval
          cases hargs : resolveAtoms env atoms with
          | error err => rw [hargs, bindErr] at heval; contradiction
          | ok values =>
            rw [hargs, bindOk] at heval
            exact ihApply _ _ _ _ _ _ hctx heval
      | extern address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases hcall : callScalarOracle ctx address values with
          | error err => rw [hcall, bindErr] at heval; contradiction
          | ok result =>
            rw [hcall, bindOk] at heval
            have hpair := Except.ok.inj heval
            cases hpair
            rfl
    · intro ctx address args store store' value hctx heval
      rw [invoke.eq_def] at heval
      dsimp only at heval
      cases hdecl : ctx.decls address with
      | none => simp [hdecl] at heval
      | some declaration =>
        simp only [hdecl] at heval
        cases declaration with
        | extern arity =>
          cases harity : args.length != arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hcall : callScalarOracle ctx address args with
            | error err => simp [hcall] at heval
            | ok result =>
              simp only [hcall] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              rfl
          · simp [harity] at heval
        | fn definition =>
          cases harity : args.length != definition.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hbody : runCode ctx fuel definition store args.reverse
                definition.body with
            | error err => rw [hbody, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hbody, bindOk] at heval
              obtain ⟨hresult, _⟩ := Sim.checkResultWorld_ok heval
              cases hresult
              have hbodyNo := hctx hdecl
              exact ihCode _ _ _ _ _ _ _ hctx hbodyNo hbodyNo hbody
          · simp [harity] at heval
    · intro ctx store function args store' value hctx heval
      rw [applyGo.eq_def] at heval
      dsimp only at heval
      cases function with
      | lit literal => simp at heval
      | erased =>
        cases hdrop : dropMany ctx fuel store args with
        | error err => rw [hdrop, bindErr] at heval; contradiction
        | ok dropped =>
          rw [hdrop, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact dropMany_reuses hdrop
      | loc location =>
        cases hbox : store.get? location with
        | none => simp [hbox] at heval
        | some box =>
          simp only [hbox] at heval
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields => simp at heval
            | papN address arity captured =>
              dsimp only at heval
              cases hdup : dupVals store captured.toList with
              | error err => rw [hdup, bindErr] at heval; contradiction
              | ok retained =>
                rw [hdup, bindOk] at heval
                cases hdrop : dropVal ctx fuel retained (.loc location) with
                | error err => rw [hdrop, bindErr] at heval; contradiction
                | ok ready =>
                  rw [hdrop, bindOk] at heval
                  have hdupReuse := dupVals_reuses hdup
                  have hdropReuse := dropVal_reuses hdrop
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder, if_true] at heval
                    have hpair := Except.ok.inj heval
                    cases hpair
                    simpa [Store.allocNode] using
                      hdropReuse.trans hdupReuse
                  · simp only [hunder, if_false] at heval
                    by_cases hexact :
                        (captured.toList ++ args).length = arity
                    · simp only [hexact, beq_self_eq_true, if_true]
                        at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some declaration =>
                        cases hpapsafe : declPapSafe declaration with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          exact (ihInvoke _ _ _ _ _ _ hctx heval).trans
                            (hdropReuse.trans hdupReuse)
                    · have hbeq :
                          ((captured.toList ++ args).length == arity) =
                            false := by
                        exact beq_eq_false_iff_ne.mpr hexact
                      simp only [hbeq, Bool.false_eq_true, if_false] at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some declaration =>
                        cases hpapsafe : declPapSafe declaration with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at heval
                            contradiction
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at heval
                            exact (ihApply _ _ _ _ _ _ hctx heval).trans
                              ((ihInvoke _ _ _ _ _ _ hctx hinvoke).trans
                                (hdropReuse.trans hdupReuse))

private def EvalPAPsUnderAt (fuel : Nat) : Prop :=
  (∀ ctx cur store env code store' value,
    CtxNoReuse ctx → CodeNoReuse cur.body → CodeNoReuse code →
    Reclamation.PAPsUnder store →
    runCode ctx fuel cur store env code = .ok (store', value) →
      Reclamation.PAPsUnder store') ∧
  (∀ ctx cur store env op store' value,
    CtxNoReuse ctx → CodeNoReuse cur.body → OpNoReuse op →
    Reclamation.PAPsUnder store →
    runOp ctx fuel cur store env op = .ok (store', value) →
      Reclamation.PAPsUnder store') ∧
  (∀ ctx address args store store' value,
    CtxNoReuse ctx → Reclamation.PAPsUnder store →
    invoke ctx fuel address args store = .ok (store', value) →
      Reclamation.PAPsUnder store') ∧
  (∀ ctx store function args store' value,
    CtxNoReuse ctx → Reclamation.PAPsUnder store →
    applyGo ctx fuel store function args = .ok (store', value) →
      Reclamation.PAPsUnder store')

/-- Reuse-free execution preserves the strict under-saturation of every
live PAP.  The induction follows dynamic calls and application chains; its
only PAP-producing branches are guarded by the evaluator's strict length
tests. -/
private theorem evalPAPsUnderAt : ∀ fuel, EvalPAPsUnderAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value hctx hcur hcode hpaps heval
      rw [runCode.eq_def] at heval
      simp at heval
    · intro ctx cur store env op store' value hctx hcur hop hpaps heval
      rw [runOp.eq_def] at heval
      simp at heval
    · intro ctx address args store store' value hctx hpaps heval
      rw [invoke.eq_def] at heval
      simp at heval
    · intro ctx store function args store' value hctx hpaps heval
      rw [applyGo.eq_def] at heval
      simp at heval
  | succ fuel ih =>
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code store' value hctx hcur hcode hpaps heval
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact hpaps
      | letOp op rest =>
        simp only [CodeNoReuse] at hcode
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hopEval : runOp ctx fuel cur store env op with
        | error err => rw [hopEval, bindErr] at heval; contradiction
        | ok result =>
          rcases result with ⟨middle, opValue⟩
          rw [hopEval, bindOk] at heval
          exact ihCode _ _ _ _ _ _ _ hctx hcur hcode.2
            (ihOp _ _ _ _ _ _ _ hctx hcur hcode.1 hpaps hopEval) heval
      | case scrut peelNat alternatives =>
        simp only [CodeNoReuse] at hcode
        rw [runCode.eq_def] at heval
        dsimp only at heval
        cases hscrut : resolveAtom env scrut with
        | error err => rw [hscrut, bindErr] at heval; contradiction
        | ok scrutValue =>
          rw [hscrut, bindOk] at heval
          cases scrutValue with
          | loc location =>
            dsimp only at heval
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity captured => simp at heval
                | ctorN cid fields =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == cid.cidx) with
                  | none => simp [halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at heval
                        exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo hpaps
                          heval
                      · simp [halt, hsize] at heval
          | lit literal =>
            cases literal with
            | str string => simp at heval
            | nat n =>
              cases hpeel : peelNat with
              | false => simp [hpeel] at heval
              | true =>
                cases n with
                | zero =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == 0) with
                  | none => simp [hpeel, halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at heval
                        exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo hpaps
                          heval
                      | succ fieldCount => simp [hpeel, halt] at heval
                | succ n =>
                  cases halt : alternatives.find?
                      (fun alternative => alternative.cidx == 1) with
                  | none => simp [hpeel, halt] at heval
                  | some alternative =>
                    have haltNo := hcode alternative
                      (Array.mem_of_find?_eq_some halt)
                    cases alternative with
                    | mk cidx fieldCount body =>
                      simp only [AltNoReuse] at haltNo
                      cases fieldCount with
                      | zero => simp [hpeel, halt] at heval
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at heval
                          exact ihCode _ _ _ _ _ _ _ hctx hcur haltNo hpaps
                            heval
                        | succ fieldCount => simp [hpeel, halt] at heval
          | erased => simp at heval
    · intro ctx cur store env op store' value hctx hcur hop hpaps heval
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hresolve : resolveAtom env atom with
        | error err => rw [hresolve, bindErr] at heval; contradiction
        | ok result =>
          rw [hresolve, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact hpaps
      | alloc world cid atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact hpaps.allocCtor world cid values.toArray
      | reuse target cid atoms =>
        simp [OpNoReuse] at hop
      | free target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | shared => simp at heval
                | unique =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  exact hpaps.kill hbox
      | dup target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases world with
                | unique => simp at heval
                | shared =>
                  have hpair := Except.ok.inj heval
                  cases hpair
                  simpa [Sim.incRcStore] using hpaps.incRcStore hbox
      | drop target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | loc location =>
            dsimp only at heval
            cases hdrop : dropVal ctx fuel store (.loc location) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact hpaps.dropVal hdrop
      | dropU target =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | erased =>
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
          | loc location =>
            dsimp only at heval
            cases hdrop : dropUVal ctx fuel store (.loc location) with
            | error err => rw [hdrop, bindErr] at heval; contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact hpaps.dropUVal hdrop
      | fetch target field =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases htarget : resolveAtom env target with
        | error err => rw [htarget, bindErr] at heval; contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at heval
          cases targetValue with
          | lit literal => simp at heval
          | erased => simp at heval
          | loc location =>
            cases hbox : store.get? location with
            | none => simp [hbox] at heval
            | some box =>
              simp only [hbox] at heval
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity captured => simp at heval
                | ctorN cid fields =>
                  cases hfield : fields[field]? with
                  | none => simp [hfield] at heval
                  | some result =>
                    simp only [hfield] at heval
                    have hpair := Except.ok.inj heval
                    cases hpair
                    exact hpaps
      | call address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          exact ihInvoke _ _ _ _ _ _ hctx hpaps heval
      | callSelf atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hbody : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err => rw [hbody, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hbody, bindOk] at heval
              obtain ⟨hresult, _⟩ := Sim.checkResultWorld_ok heval
              cases hresult
              exact ihCode _ _ _ _ _ _ _ hctx hcur hcur hpaps hbody
          · simp [harity] at heval
      | papp address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases hdecl : ctx.decls address with
          | none => simp [hdecl] at heval
          | some declaration =>
            simp only [hdecl] at heval
            by_cases hlength : values.length < declArity declaration
            · simp only [hlength, if_true] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact hpaps.allocPap .shared address (declArity declaration)
                values.toArray (by simpa using hlength)
            · simp [hlength] at heval
      | apply function atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hfunction : resolveAtom env function with
        | error err => rw [hfunction, bindErr] at heval; contradiction
        | ok functionValue =>
          rw [hfunction, bindOk] at heval
          cases hargs : resolveAtoms env atoms with
          | error err => rw [hargs, bindErr] at heval; contradiction
          | ok values =>
            rw [hargs, bindOk] at heval
            exact ihApply _ _ _ _ _ _ hctx hpaps heval
      | extern address atoms =>
        rw [runOp.eq_def] at heval
        dsimp only at heval
        cases hargs : resolveAtoms env atoms with
        | error err => rw [hargs, bindErr] at heval; contradiction
        | ok values =>
          rw [hargs, bindOk] at heval
          cases hcall : callScalarOracle ctx address values with
          | error err => rw [hcall, bindErr] at heval; contradiction
          | ok result =>
            rw [hcall, bindOk] at heval
            have hpair := Except.ok.inj heval
            cases hpair
            exact hpaps
    · intro ctx address args store store' value hctx hpaps heval
      rw [invoke.eq_def] at heval
      dsimp only at heval
      cases hdecl : ctx.decls address with
      | none => simp [hdecl] at heval
      | some declaration =>
        simp only [hdecl] at heval
        cases declaration with
        | extern arity =>
          cases harity : args.length != arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hcall : callScalarOracle ctx address args with
            | error err => simp [hcall] at heval
            | ok result =>
              simp only [hcall] at heval
              have hpair := Except.ok.inj heval
              cases hpair
              exact hpaps
          · simp [harity] at heval
        | fn definition =>
          cases harity : args.length != definition.arity
          · simp only [harity, Bool.false_eq_true, if_false] at heval
            cases hbody : runCode ctx fuel definition store args.reverse
                definition.body with
            | error err => rw [hbody, bindErr] at heval; contradiction
            | ok result =>
              rcases result with ⟨bodyStore, bodyValue⟩
              rw [hbody, bindOk] at heval
              obtain ⟨hresult, _⟩ := Sim.checkResultWorld_ok heval
              cases hresult
              have hbodyNo := hctx hdecl
              exact ihCode _ _ _ _ _ _ _ hctx hbodyNo hbodyNo hpaps hbody
          · simp [harity] at heval
    · intro ctx store function args store' value hctx hpaps heval
      rw [applyGo.eq_def] at heval
      dsimp only at heval
      cases function with
      | lit literal => simp at heval
      | erased =>
        cases hdrop : dropMany ctx fuel store args with
        | error err => rw [hdrop, bindErr] at heval; contradiction
        | ok dropped =>
          rw [hdrop, bindOk] at heval
          have hpair := Except.ok.inj heval
          cases hpair
          exact hpaps.dropMany hdrop
      | loc location =>
        cases hbox : store.get? location with
        | none => simp [hbox] at heval
        | some box =>
          simp only [hbox] at heval
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields => simp at heval
            | papN address arity captured =>
              dsimp only at heval
              cases hdup : dupVals store captured.toList with
              | error err => rw [hdup, bindErr] at heval; contradiction
              | ok retained =>
                rw [hdup, bindOk] at heval
                cases hdrop : dropVal ctx fuel retained (.loc location) with
                | error err => rw [hdrop, bindErr] at heval; contradiction
                | ok ready =>
                  rw [hdrop, bindOk] at heval
                  have hready := (hpaps.dupVals hdup).dropVal hdrop
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder, if_true] at heval
                    have hpair := Except.ok.inj heval
                    cases hpair
                    exact hready.allocPap .shared address arity
                      (captured.toList ++ args).toArray
                      (by simpa using hunder)
                  · simp only [hunder, if_false] at heval
                    by_cases hexact :
                        (captured.toList ++ args).length = arity
                    · simp only [hexact, beq_self_eq_true, if_true]
                        at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some declaration =>
                        cases hpapsafe : declPapSafe declaration with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          exact ihInvoke _ _ _ _ _ _ hctx hready heval
                    · have hbeq :
                          ((captured.toList ++ args).length == arity) =
                            false := by
                        exact beq_eq_false_iff_ne.mpr hexact
                      simp only [hbeq, Bool.false_eq_true, if_false] at heval
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at heval
                      | some declaration =>
                        cases hpapsafe : declPapSafe declaration with
                        | false => simp [hdecl, hpapsafe] at heval
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at heval
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at heval
                            contradiction
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at heval
                            exact ihApply _ _ _ _ _ _ hctx
                              (ihInvoke _ _ _ _ _ _ hctx hready hinvoke)
                              heval

/-- Reuse-free source code preserves strict PAP under-saturation. -/
theorem runCode_papsUnder {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {code : Code} {value : RVal}
    (hctx : CtxNoReuse ctx) (hcur : CodeNoReuse cur.body)
    (hcode : CodeNoReuse code) (hpaps : Reclamation.PAPsUnder store)
    (heval : runCode ctx fuel cur store env code = .ok (store', value)) :
    Reclamation.PAPsUnder store' :=
  (evalPAPsUnderAt fuel).1 ctx cur store env code store' value
    hctx hcur hcode hpaps heval

/-- Operation-level PAP-shape preservation for a reuse-free instruction. -/
theorem runOp_papsUnder {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {op : Op} {value : RVal}
    (hctx : CtxNoReuse ctx) (hcur : CodeNoReuse cur.body)
    (hop : OpNoReuse op) (hpaps : Reclamation.PAPsUnder store)
    (heval : runOp ctx fuel cur store env op = .ok (store', value)) :
    Reclamation.PAPsUnder store' :=
  (evalPAPsUnderAt fuel).2.1 ctx cur store env op store' value
    hctx hcur hop hpaps heval

/-- Declared invocation preserves PAP shape in a reuse-free context. -/
theorem invoke_papsUnder {ctx : Ctx} {fuel : Nat}
    {address : Ixon.Address} {args : List RVal} {store store' : Store}
    {value : RVal} (hctx : CtxNoReuse ctx)
    (hpaps : Reclamation.PAPsUnder store)
    (heval : invoke ctx fuel address args store = .ok (store', value)) :
    Reclamation.PAPsUnder store' :=
  (evalPAPsUnderAt fuel).2.2.1 ctx address args store store' value hctx hpaps
    heval

/-- Higher-order application preserves PAP shape across all redispatches. -/
theorem applyGo_papsUnder {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {function : RVal} {args : List RVal}
    {value : RVal} (hctx : CtxNoReuse ctx)
    (hpaps : Reclamation.PAPsUnder store)
    (heval : applyGo ctx fuel store function args = .ok (store', value)) :
    Reclamation.PAPsUnder store' :=
  (evalPAPsUnderAt fuel).2.2.2 ctx store function args store' value hctx
    hpaps heval

theorem runCode_reuses_eq {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {code : Code} {value : RVal}
    (hctx : CtxNoReuse ctx) (hcur : CodeNoReuse cur.body)
    (hcode : CodeNoReuse code)
    (heval : runCode ctx fuel cur store env code = .ok (store', value)) :
    store'.reuses = store.reuses :=
  (evalReusesAt fuel).1 ctx cur store env code store' value
    hctx hcur hcode heval

/-- The operation-level projection of reuse-free execution.  Exporting this
alongside `runCode_reuses_eq` lets later compositional simulations preserve
append-only heap invariants one instruction at a time. -/
theorem runOp_reuses_eq {ctx : Ctx} {fuel : Nat} {cur : FnDef}
    {store store' : Store} {env : List RVal} {op : Op} {value : RVal}
    (hctx : CtxNoReuse ctx) (hcur : CodeNoReuse cur.body)
    (hop : OpNoReuse op)
    (heval : runOp ctx fuel cur store env op = .ok (store', value)) :
    store'.reuses = store.reuses :=
  (evalReusesAt fuel).2.1 ctx cur store env op store' value
    hctx hcur hop heval

/-- Declared invocation preserves the reuse counter whenever every callable
body in the runtime context is reuse-free. -/
theorem invoke_reuses_eq {ctx : Ctx} {fuel : Nat}
    {address : Ixon.Address} {args : List RVal} {store store' : Store}
    {value : RVal} (hctx : CtxNoReuse ctx)
    (heval : invoke ctx fuel address args store = .ok (store', value)) :
    store'.reuses = store.reuses :=
  (evalReusesAt fuel).2.2.1 ctx address args store store' value hctx heval

/-- Higher-order application preserves the reuse counter in a reuse-free
runtime context, including every PAP branch and dynamically selected callee. -/
theorem applyGo_reuses_eq {ctx : Ctx} {fuel : Nat}
    {store store' : Store} {function : RVal} {args : List RVal}
    {value : RVal} (hctx : CtxNoReuse ctx)
    (heval : applyGo ctx fuel store function args = .ok (store', value)) :
    store'.reuses = store.reuses :=
  (evalReusesAt fuel).2.2.2 ctx store function args store' value hctx heval

/-- A successful fresh execution of a reuse-free closed program executes no
in-place reuse, so its counter remains definitionally zero. -/
theorem runMain_reuses_eq_zero {ctx : Ctx} {fuel : Nat} {code : Code}
    {store : Store} {value : RVal} (hctx : CtxNoReuse ctx)
    (hcode : CodeNoReuse code)
    (heval : runMain ctx code fuel = .ok (store, value)) :
    store.reuses = 0 := by
  exact (evalReusesAt fuel).1 ctx ⟨0, .shared, false, code⟩ ({} : Store) []
    code store value hctx hcode hcode heval

/-- The exact counter equation contributed by the current lowerer. -/
def ReuseFreeCostSpec (observation : LowerSim.CostObservation) : Prop :=
  observation.reuses = 0

/-- The current lowerer's general counter contract: no in-place reuse and no
more completed frees than allocations. -/
def CurrentLowererCostSpec (observation : LowerSim.CostObservation) : Prop :=
  ReuseFreeCostSpec observation ∧
    LowerSim.AllocationFreeCostSpec observation

/-- Reuse-free syntax and declarations expose their dynamic counter equation
through the generic target-only cost interface. -/
theorem runCostInvariant_of_noReuse {ctx : Ctx} {code : Code}
    (hctx : CtxNoReuse ctx) (hcode : CodeNoReuse code) :
    LowerSim.RunCostInvariant ctx code ReuseFreeCostSpec := by
  intro targetFuel targetStore targetValue hrun
  exact runMain_reuses_eq_zero hctx hcode hrun

/-- Reuse-free syntax combines its compiler-specific zero-reuse equation
with the evaluator's general allocation/free balance. -/
theorem runCostInvariant_of_noReuse_with_allocationFree
    {ctx : Ctx} {code : Code}
    (hctx : CtxNoReuse ctx) (hcode : CodeNoReuse code) :
    LowerSim.RunCostInvariant ctx code CurrentLowererCostSpec := by
  intro targetFuel targetStore targetValue hrun
  exact ⟨runMain_reuses_eq_zero hctx hcode hrun,
    Ix.Compiler.IxIR1.Reclamation.runMain_frees_le_allocs hrun⟩

/-! ## Compiler syntax -/

def DeclNoReuse : Decl → Prop
  | .fn definition => CodeNoReuse definition.body
  | .extern _ => True

def DeclListNoReuse (declarations : List (Ixon.Address × Decl)) : Prop :=
  ∀ declaration ∈ declarations, DeclNoReuse declaration.2

/-- Executable reuse-freedom check for one declaration. -/
def checkDecl : Decl → Bool
  | .fn definition => checkCode definition.body
  | .extern _ => true

/-- Executable reuse-freedom check for a finite declaration environment. -/
def checkDeclarations (declarations : List (Ixon.Address × Decl)) : Bool :=
  declarations.all fun declaration => checkDecl declaration.2

theorem checkDecl_eq_true_iff (declaration : Decl) :
    checkDecl declaration = true ↔ DeclNoReuse declaration := by
  cases declaration with
  | fn definition =>
      exact checkCode_eq_true_iff definition.body
  | extern arity =>
      simp [checkDecl, DeclNoReuse]

/-- The finite declaration check reflects exactly into `DeclListNoReuse`. -/
theorem checkDeclarations_eq_true_iff
    (declarations : List (Ixon.Address × Decl)) :
    checkDeclarations declarations = true ↔
      DeclListNoReuse declarations := by
  simp only [checkDeclarations, List.all_eq_true, DeclListNoReuse]
  constructor
  · intro checked declaration member
    exact (checkDecl_eq_true_iff declaration.2).mp
      (checked declaration member)
  · intro noReuse declaration member
    exact (checkDecl_eq_true_iff declaration.2).mpr
      (noReuse declaration member)

def StateNoReuse (state : LowSt) : Prop :=
  DeclListNoReuse state.extra

theorem StateNoReuse.empty : StateNoReuse ({} : LowSt) := by
  simp [StateNoReuse, DeclListNoReuse]

/-- A compiler action preserves the reuse-free generated-declaration
invariant along every successful state transition. -/
def PreservesStateNoReuse {α : Type} (action : LowerM α) : Prop :=
  ∀ {initial final result},
    StateNoReuse initial →
    action.run initial = .ok result final →
    StateNoReuse final

private theorem stateBindRun_ok_inv {error state α β : Type}
    {action : EStateM error state α} {next : α → EStateM error state β}
    {initial final : state} {result : β}
    (hrun : (action >>= next).run initial = .ok result final) :
    ∃ value middle,
      action.run initial = .ok value middle ∧
      (next value).run middle = .ok result final := by
  change
    (match action.run initial with
      | .ok value nextState => (next value).run nextState
      | .error err nextState => .error err nextState) =
      .ok result final at hrun
  cases haction : action.run initial with
  | ok value middle =>
    rw [haction] at hrun
    exact ⟨value, middle, rfl, hrun⟩
  | error err middle =>
    rw [haction] at hrun
    contradiction

private theorem stateThrowRun_not_ok {error state α : Type}
    {err : error} {initial final : state} {result : α}
    (hrun : (throw err : EStateM error state α).run initial =
      .ok result final) : False := by
  change EStateM.Result.error err initial = .ok result final at hrun
  contradiction

private theorem stateMapRun_ok_inv {α β : Type} {action : LowerM α}
    {map : α → β} {initial final : LowSt} {result : β}
    (hrun : (map <$> action).run initial = .ok result final) :
    ∃ value, action.run initial = .ok value final ∧ map value = result := by
  have hbind : (action >>= fun value => pure (map value)).run initial =
      .ok result final := by
    simpa only [bind_pure_comp] using hrun
  obtain ⟨value, middle, haction, hpure⟩ := stateBindRun_ok_inv hbind
  have hresult : map value = result ∧ middle = final := by
    simpa using hpure
  cases hresult.2
  exact ⟨value, haction, hresult.1⟩

theorem PreservesStateNoReuse.pure {α : Type} (value : α) :
    PreservesStateNoReuse (pure value : LowerM α) := by
  intro initial final result hinitial hrun
  have hpure : value = result ∧ initial = final := by
    simpa using hrun
  rw [← hpure.2]
  exact hinitial

theorem PreservesStateNoReuse.throw {α : Type} (message : String) :
    PreservesStateNoReuse (throw message : LowerM α) := by
  intro initial final result hinitial hrun
  exact (stateThrowRun_not_ok hrun).elim

theorem PreservesStateNoReuse.throwBind {α β : Type} (message : String)
    (next : α → LowerM β) :
    PreservesStateNoReuse
      ((EStateM.throw message : LowerM α) >>= next) := by
  intro initial final result hinitial hrun
  change EStateM.Result.error message initial = .ok result final at hrun
  contradiction

theorem PreservesStateNoReuse.get :
    PreservesStateNoReuse (get : LowerM LowSt) := by
  intro initial final result hinitial hrun
  change EStateM.Result.ok initial initial = .ok result final at hrun
  injection hrun with _ hstate
  subst final
  exact hinitial

theorem PreservesStateNoReuse.bind {α β : Type}
    {action : LowerM α} {next : α → LowerM β}
    (haction : PreservesStateNoReuse action)
    (hnext : ∀ value, PreservesStateNoReuse (next value)) :
    PreservesStateNoReuse (action >>= next) := by
  intro initial final result hinitial hrun
  obtain ⟨value, middle, hfirst, hsecond⟩ :=
    stateBindRun_ok_inv hrun
  exact hnext value (haction hinitial hfirst) hsecond

theorem PreservesStateNoReuse.map {α β : Type} {action : LowerM α}
    (haction : PreservesStateNoReuse action) (map : α → β) :
    PreservesStateNoReuse (map <$> action) := by
  have hbind : PreservesStateNoReuse
      (action >>= fun value => (Pure.pure (map value) : LowerM β)) :=
    PreservesStateNoReuse.bind haction
      (fun value => PreservesStateNoReuse.pure (map value))
  intro initial final result hinitial hrun
  apply hbind hinitial
  simpa only [bind_pure_comp] using hrun

theorem PreservesStateNoReuse.listMapM {α β : Type}
    (action : α → LowerM β)
    (haction : ∀ value, PreservesStateNoReuse (action value)) :
    ∀ values : List α, PreservesStateNoReuse (values.mapM action)
  | [] => by
      simpa using (PreservesStateNoReuse.pure ([] : List β))
  | value :: rest => by
      rw [List.mapM_cons]
      apply PreservesStateNoReuse.bind (haction value)
      intro head
      apply PreservesStateNoReuse.bind
        (PreservesStateNoReuse.listMapM action haction rest)
      intro tail
      exact PreservesStateNoReuse.pure (head :: tail)

theorem PreservesStateNoReuse.listFilterMapM {α β : Type}
    (action : α → LowerM (Option β))
    (haction : ∀ value, PreservesStateNoReuse (action value)) :
    ∀ values : List α, PreservesStateNoReuse (values.filterMapM action)
  | [] => by
      simpa using (PreservesStateNoReuse.pure ([] : List β))
  | value :: rest => by
      rw [List.filterMapM_cons]
      apply PreservesStateNoReuse.bind (haction value)
      intro head
      cases head with
      | none =>
        exact PreservesStateNoReuse.listFilterMapM action haction rest
      | some head =>
        apply PreservesStateNoReuse.bind
          (PreservesStateNoReuse.listFilterMapM action haction rest)
        intro tail
        exact PreservesStateNoReuse.pure (head :: tail)

theorem StateNoReuse.prepend {state : LowSt}
    {item : Ixon.Address × Decl} (hitem : DeclNoReuse item.2)
    (hstate : StateNoReuse state) :
    StateNoReuse { state with extra := item :: state.extra } := by
  intro declaration hmember
  rw [List.mem_cons] at hmember
  cases hmember with
  | inl hhead =>
    subst declaration
    exact hitem
  | inr htail => exact hstate declaration htail

theorem ctorWrapperDecl_noReuse (source : Ixon.Address)
    (tag arity : Nat) :
    DeclNoReuse (ctorWrapperDecl source tag arity) := by
  simp [ctorWrapperDecl, DeclNoReuse, CodeNoReuse, OpNoReuse]

theorem freshAddr_preservesStateNoReuse :
    PreservesStateNoReuse freshAddr := by
  intro initial final result hinitial hrun
  change EStateM.Result.ok (synthAddr initial.fresh)
      { initial with fresh := initial.fresh + 1 } =
    .ok result final at hrun
  have hstate : { initial with fresh := initial.fresh + 1 } = final :=
    congrArg
      (fun outcome : EStateM.Result String LowSt Ixon.Address =>
        match outcome with
        | .ok _ state | .error _ state => state) hrun
  subst final
  exact hinitial

theorem pushExtra_preservesStateNoReuse
    (item : Ixon.Address × Decl) (hitem : DeclNoReuse item.2) :
    PreservesStateNoReuse (pushExtra item) := by
  intro initial final result hinitial hrun
  simp [pushExtra] at hrun
  subst final
  exact hinitial.prepend hitem

theorem wrapperFor_preservesStateNoReuse (source : Ixon.Address)
    (tag arity : Nat) :
    PreservesStateNoReuse (wrapperFor source tag arity) := by
  intro initial final result hinitial hrun
  cases hcached : initial.wrappers.find?
      (·.matches source tag arity) with
  | none =>
    simp [wrapperFor, hcached] at hrun
    have hstate :
        { initial with
            fresh := initial.fresh + 1
            wrappers :=
              ⟨source, tag, arity, synthAddr initial.fresh⟩ ::
                initial.wrappers
            extra :=
              (synthAddr initial.fresh,
                ctorWrapperDecl source tag arity) :: initial.extra } =
          final := by
      exact congrArg
        (fun outcome : EStateM.Result String LowSt Ixon.Address =>
          match outcome with
          | .ok _ state | .error _ state => state) hrun
    subst final
    exact hinitial.prepend (ctorWrapperDecl_noReuse source tag arity)
  | some memo =>
    simp [wrapperFor, hcached] at hrun
    obtain ⟨_, hstate⟩ := hrun
    subst final
    exact hinitial

theorem releaseSlots_emitNoReuse (input : VEnv) :
    ∀ {drops output emit state finalState},
      (releaseSlots input drops).run state = .ok (output, emit) finalState →
      EmitNoReuse emit := by
  intro drops output emit state finalState hrun
  exact releaseSlots_run_core
    (Result := fun _ _ _ resultEmit => EmitNoReuse resultEmit)
    (hnil := fun _ => emitNoReuse_id)
    (haffine := by
      intro entry abs rest initial final tailEmit htail
      exact emitNoReuse_comp
        (emitNoReuse_emitOp
          (op := .dropU (.var (initial.rel abs)))
          (by simp [OpNoReuse]))
        htail)
    (hmany := by
      intro entry abs rest initial final tailEmit htail
      exact emitNoReuse_comp
        (emitNoReuse_emitOp
          (op := .drop (.var (initial.rel abs)))
          (by simp [OpNoReuse]))
        htail)
    hrun

theorem applyRecursorFieldRetains_emitNoReuse (input : VEnv)
    (retains : List RecursorFieldRetain) :
    EmitNoReuse (applyRecursorFieldRetains input retains).2 := by
  induction retains generalizing input with
  | nil => exact emitNoReuse_id
  | cons retain rest ih =>
    simp only [applyRecursorFieldRetains]
    exact emitNoReuse_comp
      (emitNoReuse_emitOp (op := .dup (.var (input.rel retain.fieldAbs)))
        (by simp [OpNoReuse]))
      (ih _)

theorem releaseAll_emitNoReuse (input : VEnv) (values : List AVal) :
    EmitNoReuse (releaseAll input values).2 := by
  exact releaseAll_traverse_core
    (Result := fun _ _ _ emit => EmitNoReuse emit)
    (hnil := fun _ => emitNoReuse_id)
    (hconst := fun htail => htail)
    (hslot := by
      intro initial abs rest output tailEmit htail
      exact emitNoReuse_comp
        (emitNoReuse_emitOp (op := .drop (.var (initial.rel abs)))
          (by simp [OpNoReuse]))
        htail)
    input values

theorem lowerCapture_emitNoReuse {expr : IxIR0.Expr} {input output : VEnv}
    {index : Nat} {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hrun : (lowerCapture expr input index).run state =
      .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  cases hentry : input.entries[index]? with
  | none =>
    exact (stateThrowRun_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (stateThrowRun_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (stateThrowRun_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Ixon.Owned.unique == Ixon.Owned.unique) = true :=
            by decide
          exact (stateThrowRun_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Ixon.Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses index expr
          · have hemit : emit = emitOp (.dup (.var
                ((input.setEntry index
                  (.slot abs (remaining - countUses index expr) uses true)).rel
                    abs))) := by
              have hpure := congrArg
                (fun result : EStateM.Result String LowSt
                    (VEnv × Emit × AVal) =>
                  match result with
                  | .ok result _ => result.2.1
                  | .error _ _ => (_root_.id : Emit)) hrun
              simpa [lowerCapture, hentry, huniqueEq, hmore] using hpure.symm
            subst emit
            exact emitNoReuse_emitOp
              (op := .dup (.var
                ((input.setEntry index
                  (.slot abs (remaining - countUses index expr) uses true)).rel
                    abs))) (by simp [OpNoReuse])
          · by_cases hequal : remaining = countUses index expr
            · have hemit : emit = (_root_.id : Emit) := by
                have hpure := congrArg
                  (fun result : EStateM.Result String LowSt
                      (VEnv × Emit × AVal) =>
                    match result with
                    | .ok result _ => result.2.1
                    | .error _ _ => (_root_.id : Emit)) hrun
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hpure.symm
              subst emit
              exact emitNoReuse_id
            · exact (stateThrowRun_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_emitNoReuse (expr : IxIR0.Expr) :
    ∀ {input captures state finalState output emit values},
      (lowerCaptures expr input captures).run state =
        .ok (output, emit, values) finalState →
      EmitNoReuse emit := by
  intro input captures state finalState output emit values hrun
  apply lowerCaptures_run_core
    (Result := fun _ _ _ emit _ => EmitNoReuse emit)
    (e := expr) (hrun := hrun)
  · intro input
    exact emitNoReuse_id
  · intro index rest input middle output headEmit tailEmit headValue
      tailValues state middleState hhead htail
    exact emitNoReuse_comp (lowerCapture_emitNoReuse hhead) htail

def LowerENoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Ixon.Owned} {expr : IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit}
      {value : AVal},
    (lowerE src fuel input world expr).run state =
      .ok (output, emit, value) finalState →
    EmitNoReuse emit

def LowerBorrowNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal} {release : Bool},
    (lowerBorrow src fuel input expr).run state =
      .ok (output, emit, value, release) finalState →
    EmitNoReuse emit

def LowerSpineNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {world : Ixon.Owned} {head : IxIR0.Expr}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerSpine src fuel input world head args).run state =
      .ok (output, emit, value) finalState →
    EmitNoReuse emit

def KnownCallNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {build : Array Atom → Op} {count : Nat}
      {argWorlds : List Ixon.Owned} {resultWorld : Ixon.Owned}
      {args : List IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (∀ atoms, OpNoReuse (build atoms)) →
    (knownCall src fuel input build count argWorlds resultWorld args).run
        state = .ok (output, emit, value) finalState →
    EmitNoReuse emit

def LowerArgsNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {args : List (IxIR0.Expr × Ixon.Owned)}
      {state finalState : LowSt} {output : VEnv} {emit : Emit}
      {values : List AVal},
    (lowerArgs src fuel input args).run state =
      .ok (output, emit, values) finalState →
    EmitNoReuse emit

def ApplyRestNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {resultWorld : Ixon.Owned} {pre : Emit}
      {function : AVal} {args : List IxIR0.Expr}
      {state finalState : LowSt} {output : VEnv} {emit : Emit}
      {value : AVal},
    EmitNoReuse pre →
    (applyRest src fuel input resultWorld pre function args).run state =
      .ok (output, emit, value) finalState →
    EmitNoReuse emit

def LowerLamNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {expr : IxIR0.Expr} {state finalState : LowSt}
      {output : VEnv} {emit : Emit} {value : AVal},
    (lowerLam src fuel input expr).run state =
      .ok (output, emit, value) finalState →
    EmitNoReuse emit

def LowerFnBodyNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ {input : VEnv} {drops : List SlotDrop} {world : Ixon.Owned}
      {body : IxIR0.Expr} {state finalState : LowSt} {code : Code},
    (lowerFnBody src fuel input drops world body).run state =
      .ok code finalState →
    CodeNoReuse code

structure LowerNoReuseCluster (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerENoReuse src fuel
  borrow : LowerBorrowNoReuse src fuel
  spine : LowerSpineNoReuse src fuel
  knownCall : KnownCallNoReuse src fuel
  args : LowerArgsNoReuse src fuel
  applyRest : ApplyRestNoReuse src fuel
  lam : LowerLamNoReuse src fuel
  fnBody : LowerFnBodyNoReuse src fuel

private theorem lowerNoReuse_zero (src : IxIR0.Env) :
    LowerNoReuseCluster src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr state finalState output emit value hrun
    exact (stateThrowRun_not_ok (by simpa [lowerE] using hrun)).elim
  · intro input expr state finalState output emit value release hrun
    exact (stateThrowRun_not_ok (by simpa [lowerBorrow] using hrun)).elim
  · intro input world head args state finalState output emit value hrun
    exact (stateThrowRun_not_ok (by simpa [lowerSpine] using hrun)).elim
  · intro input build count argWorlds resultWorld args state finalState
      output emit value hbuild hrun
    exact (stateThrowRun_not_ok (by simpa [knownCall] using hrun)).elim
  · intro input args state finalState output emit values hrun
    exact (stateThrowRun_not_ok (by simpa [lowerArgs] using hrun)).elim
  · intro input resultWorld pre function args state finalState output emit
      value hpre hrun
    exact (stateThrowRun_not_ok (by simpa [applyRest] using hrun)).elim
  · intro input expr state finalState output emit value hrun
    exact (stateThrowRun_not_ok (by simpa [lowerLam] using hrun)).elim
  · intro input drops world body state finalState code hrun
    exact (stateThrowRun_not_ok (by simpa [lowerFnBody] using hrun)).elim

private theorem lowerArgsNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel) (hargs : LowerArgsNoReuse src fuel) :
    LowerArgsNoReuse src (fuel + 1) := by
  intro input args state finalState output emit values hrun
  cases args with
  | nil =>
    have hpure :
        (input, (_root_.id : Emit), []) = (output, emit, values) ∧
          state = finalState := by
      simpa [lowerArgs] using hrun
    cases hpure.1
    exact emitNoReuse_id
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs] at hrun
    obtain ⟨headResult, middleState, hhead, hafterHead⟩ :=
      stateBindRun_ok_inv hrun
    rcases headResult with ⟨middle, headEmit, headValue⟩
    obtain ⟨tailResult, tailState, htail, hpure⟩ :=
      stateBindRun_ok_inv hafterHead
    rcases tailResult with ⟨actualOutput, tailEmit, tailValues⟩
    have hemit : headEmit ∘ tailEmit = emit := by
      simpa using congrArg
        (fun result : EStateM.Result String LowSt
            (VEnv × Emit × List AVal) =>
          match result with
          | .ok result _ => result.2.1
          | .error _ _ => (_root_.id : Emit)) hpure
    subst emit
    exact emitNoReuse_comp (hexpr hhead) (hargs htail)

private theorem applyRestNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsNoReuse src fuel) :
    ApplyRestNoReuse src (fuel + 1) := by
  intro input resultWorld pre function args state finalState output emit value
    hpre hrun
  cases function with
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest] at hrun
      obtain ⟨argsResult, argsState, hargsRun, hpure⟩ :=
        stateBindRun_ok_inv hrun
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hemit :
          pre ∘ argsEmit ∘ (releaseAll middle values).2 = emit := by
        simpa using congrArg
          (fun result : EStateM.Result String LowSt
              (VEnv × Emit × AVal) =>
            match result with
            | .ok result _ => result.2.1
            | .error _ _ => (_root_.id : Emit)) hpure
      subst emit
      have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
      have hprefix : EmitNoReuse (pre ∘ argsEmit) :=
        emitNoReuse_comp (first := pre) (second := argsEmit) hpre hargsNo
      exact emitNoReuse_comp
        (first := pre ∘ argsEmit)
        (second := (releaseAll middle values).2) hprefix
        (releaseAll_emitNoReuse middle values)
    | var relative =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ :=
        stateBindRun_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpure⟩ :=
        stateBindRun_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hemit : pre ∘ argsEmit ∘ emitOp (.apply
          ((AVal.constA (.var relative)).toAtom middle)
          (values.map (·.toAtom middle)).toArray) = emit := by
        simpa using congrArg
          (fun result : EStateM.Result String LowSt
              (VEnv × Emit × AVal) =>
            match result with
            | .ok result _ => result.2.1
            | .error _ _ => (_root_.id : Emit)) hpure
      subst emit
      have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
      have hprefix : EmitNoReuse (pre ∘ argsEmit) :=
        emitNoReuse_comp (first := pre) (second := argsEmit) hpre hargsNo
      exact emitNoReuse_comp
        (first := pre ∘ argsEmit)
        (second := emitOp (.apply
          ((AVal.constA (.var relative)).toAtom middle)
          (values.map (·.toAtom middle)).toArray)) hprefix
        (emitNoReuse_emitOp (by simp [OpNoReuse]))
    | lit literal =>
      simp only [applyRest] at hrun
      obtain ⟨_, checkedState, _, hafterCheck⟩ :=
        stateBindRun_ok_inv hrun
      obtain ⟨argsResult, argsState, hargsRun, hpure⟩ :=
        stateBindRun_ok_inv hafterCheck
      rcases argsResult with ⟨middle, argsEmit, values⟩
      have hemit : pre ∘ argsEmit ∘ emitOp (.apply
          ((AVal.constA (.lit literal)).toAtom middle)
          (values.map (·.toAtom middle)).toArray) = emit := by
        simpa using congrArg
          (fun result : EStateM.Result String LowSt
              (VEnv × Emit × AVal) =>
            match result with
            | .ok result _ => result.2.1
            | .error _ _ => (_root_.id : Emit)) hpure
      subst emit
      have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
      have hprefix : EmitNoReuse (pre ∘ argsEmit) :=
        emitNoReuse_comp (first := pre) (second := argsEmit) hpre hargsNo
      exact emitNoReuse_comp
        (first := pre ∘ argsEmit)
        (second := emitOp (.apply
          ((AVal.constA (.lit literal)).toAtom middle)
          (values.map (·.toAtom middle)).toArray)) hprefix
        (emitNoReuse_emitOp (by simp [OpNoReuse]))
  | slotA abs =>
    simp only [applyRest] at hrun
    obtain ⟨_, checkedState, _, hafterCheck⟩ :=
      stateBindRun_ok_inv hrun
    obtain ⟨argsResult, argsState, hargsRun, hpure⟩ :=
      stateBindRun_ok_inv hafterCheck
    rcases argsResult with ⟨middle, argsEmit, values⟩
    have hemit : pre ∘ argsEmit ∘ emitOp (.apply
        ((AVal.slotA abs).toAtom middle)
        (values.map (·.toAtom middle)).toArray) = emit := by
      simpa using congrArg
        (fun result : EStateM.Result String LowSt
            (VEnv × Emit × AVal) =>
          match result with
          | .ok result _ => result.2.1
          | .error _ _ => (_root_.id : Emit)) hpure
    subst emit
    have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
    have hprefix : EmitNoReuse (pre ∘ argsEmit) :=
      emitNoReuse_comp (first := pre) (second := argsEmit) hpre hargsNo
    exact emitNoReuse_comp
      (first := pre ∘ argsEmit)
      (second := emitOp (.apply ((AVal.slotA abs).toAtom middle)
        (values.map (·.toAtom middle)).toArray)) hprefix
      (emitNoReuse_emitOp (by simp [OpNoReuse]))

private theorem knownCallNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsNoReuse src fuel)
    (hrest : ApplyRestNoReuse src fuel) :
    KnownCallNoReuse src (fuel + 1) := by
  intro input build count argWorlds resultWorld args state finalState output
    emit value hbuild hrun
  simp only [knownCall] at hrun
  obtain ⟨argsResult, argsState, hargsRun, hafterArgs⟩ :=
    stateBindRun_ok_inv hrun
  rcases argsResult with ⟨middle, argsEmit, values⟩
  by_cases hterminal : args.length ≤ count
  · have hpure :
        (middle.bump,
          argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray),
          AVal.slotA middle.depth) = (output, emit, value) ∧
          argsState = finalState := by
      simpa [hterminal] using hafterArgs
    have hemit : argsEmit ∘ emitOp
        (build (values.map (·.toAtom middle)).toArray) = emit :=
      congrArg (fun result : VEnv × Emit × AVal => result.2.1) hpure.1
    subst emit
    have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
    exact emitNoReuse_comp (first := argsEmit)
      (second := emitOp
        (build (values.map (·.toAtom middle)).toArray)) hargsNo
      (emitNoReuse_emitOp (hbuild _))
  · have hrestRun :
        (applyRest src fuel middle.bump resultWorld
          (argsEmit ∘ emitOp
            (build (values.map (·.toAtom middle)).toArray))
          (.slotA middle.depth)
          (args.drop count)).run argsState =
            .ok (output, emit, value) finalState := by
      simpa [hterminal] using hafterArgs
    have hargsNo : EmitNoReuse argsEmit := hargs hargsRun
    have hpre : EmitNoReuse (argsEmit ∘ emitOp
        (build (values.map (·.toAtom middle)).toArray)) :=
      emitNoReuse_comp (first := argsEmit)
        (second := emitOp
          (build (values.map (·.toAtom middle)).toArray)) hargsNo
        (emitNoReuse_emitOp (hbuild _))
    exact hrest hpre hrestRun

private theorem lowerBorrow_dynamicNoReuse {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel)
    {input output : VEnv} {expr : IxIR0.Expr}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    {release : Bool}
    {finish : (VEnv × Emit × AVal) → (VEnv × Emit × AVal × Bool)}
    (hrun : (finish <$> lowerE src fuel input .shared expr).run state =
      .ok (output, emit, value, release) finalState)
    (hfinish : ∀ result, (finish result).2.1 = result.2.1) :
    EmitNoReuse emit := by
  obtain ⟨exprResult, hexprRun, hvalue⟩ := stateMapRun_ok_inv hrun
  rcases exprResult with ⟨middle, middleEmit, middleValue⟩
  have hemit : middleEmit = emit :=
    calc
      middleEmit = (finish (middle, middleEmit, middleValue)).2.1 :=
        (hfinish (middle, middleEmit, middleValue)).symm
      _ = emit := congrArg
        (fun result : VEnv × Emit × AVal × Bool => result.2.1)
        hvalue
  subst emit
  exact hexpr hexprRun

private theorem lowerBorrowVarNoReuse {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {index : Nat} {state finalState : LowSt}
    {emit : Emit} {value : AVal} {release : Bool}
    (hrun : (lowerBorrow src (fuel + 1) input (.var index)).run state =
      .ok (output, emit, value, release) finalState) :
    EmitNoReuse emit := by
  cases hentry : input.entries[index]? with
  | none =>
    exact (stateThrowRun_not_ok (by
      simpa [lowerBorrow, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (stateThrowRun_not_ok (by
        simpa [lowerBorrow, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (stateThrowRun_not_ok (by
          simpa [lowerBorrow, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq : (Ixon.Owned.unique == Ixon.Owned.unique) = true :=
            by decide
          exact (stateThrowRun_not_ok (by
            simpa [lowerBorrow, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Ixon.Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          cases remaining with
          | zero =>
            exact (stateThrowRun_not_ok (by
              simpa [lowerBorrow, hentry, huniqueEq] using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry index (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs, true) =
                      (output, emit, value, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, huniqueEq] using hrun
              have hemit : (_root_.id : Emit) = emit :=
                congrArg
                  (fun result : VEnv × Emit × AVal × Bool =>
                    result.2.1) hpure.1
              rw [← hemit]
              exact emitNoReuse_id
            | succ remaining =>
              have hpure :
                  (input.setEntry index
                      (.slot abs (remaining + 1) uses true),
                    (_root_.id : Emit), AVal.slotA abs, false) =
                      (output, emit, value, release) ∧
                    state = finalState := by
                simpa [lowerBorrow, hentry, huniqueEq] using hrun
              have hemit : (_root_.id : Emit) = emit :=
                congrArg
                  (fun result : VEnv × Emit × AVal × Bool =>
                    result.2.1) hpure.1
              rw [← hemit]
              exact emitNoReuse_id

private theorem lowerBorrowNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel) :
    LowerBorrowNoReuse src (fuel + 1) := by
  intro input expr state finalState output emit value release hrun
  cases expr with
  | var index => exact lowerBorrowVarNoReuse hrun
  | ref address =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | app function argument =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | lam uses body =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | letE uses bound body =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | proj index source =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | lit literal =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)
  | erased =>
    exact lowerBorrow_dynamicNoReuse hexpr
      (by simpa [lowerBorrow] using hrun) (fun _ => rfl)

private theorem lowerEApplyRestNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel)
    (hrest : ApplyRestNoReuse src fuel)
    {input output : VEnv} {world : Ixon.Owned} {head : IxIR0.Expr}
    {args : List IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (do
      let (middle, headEmit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel middle world headEmit function args).run state =
        .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  obtain ⟨headResult, middleState, hhead, htail⟩ :=
    stateBindRun_ok_inv hrun
  rcases headResult with ⟨middle, headEmit, function⟩
  exact hrest (hexpr hhead) htail

private theorem lowerSpineNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel)
    (hspine : LowerSpineNoReuse src fuel)
    (hknown : KnownCallNoReuse src fuel)
    (hrest : ApplyRestNoReuse src fuel) :
    LowerSpineNoReuse src (fuel + 1) := by
  intro input world head args state finalState output emit value hrun
  have hsuEq : (Ixon.Owned.shared == Ixon.Owned.unique) = false := by
    decide
  cases head with
  | app function argument =>
    exact hspine (by simpa [lowerSpine] using hrun)
  | erased =>
    exact hrest emitNoReuse_id (by simpa [lowerSpine] using hrun)
  | var index =>
    simp only [lowerSpine] at hrun
    cases hentry : input.entries[index]? with
    | none =>
      exact lowerEApplyRestNoReuse hexpr hrest (by
        simpa [hentry] using hrun)
    | some entry =>
      cases entry with
      | slot abs remaining uses held =>
        exact lowerEApplyRestNoReuse hexpr hrest (by
          simpa [hentry] using hrun)
      | recSelf arity =>
        by_cases hunder : args.length < arity
        · exact (stateThrowRun_not_ok (by
            simpa [hentry, hunder] using hrun)).elim
        · obtain ⟨_, checkedState, _, hknownRun⟩ :=
            stateBindRun_ok_inv (by simpa [hentry, hunder] using hrun)
          exact hknown (by intro atoms; simp [OpNoReuse]) hknownRun
  | ref address =>
    simp only [lowerSpine] at hrun
    cases hsource : src address with
    | none =>
      exact (stateThrowRun_not_ok (by
        simpa [hsource] using hrun)).elim
    | some declaration =>
      cases declaration with
      | defn result body =>
        by_cases hunder : args.length < lamArity body
        · cases world with
          | unique =>
            exact (stateThrowRun_not_ok (by
              simpa [hsource, hunder] using hrun)).elim
          | shared =>
            cases result with
            | unique =>
              exact (stateThrowRun_not_ok (by
                simpa [hsource, hunder] using hrun)).elim
            | shared =>
              cases hp : papSafe body with
              | false =>
                exact (stateThrowRun_not_ok (by
                  simpa [hsource, hunder, hp, hsuEq] using hrun)).elim
              | true =>
                exact hknown
                  (build := fun atoms => .papp address atoms)
                  (by intro atoms; simp [OpNoReuse]) (by
                  simpa [hsource, hunder, hp, hsuEq] using hrun)
        · obtain ⟨_, checkedState, _, hknownRun⟩ :=
            stateBindRun_ok_inv (by
              simpa [hsource, hunder] using hrun)
          exact hknown (by intro atoms; simp [OpNoReuse]) hknownRun
      | ctor tag arity =>
        by_cases hunder : args.length < arity
        · cases world with
          | unique =>
            exact (stateThrowRun_not_ok (by
              simpa [hsource, hunder] using hrun)).elim
          | shared =>
            obtain ⟨wrapper, wrapperState, _, hknownRun⟩ :=
              stateBindRun_ok_inv (by
                simpa [hsource, hunder] using hrun)
            exact hknown (by intro atoms; simp [OpNoReuse]) hknownRun
        · exact hknown
            (build := fun atoms => .alloc world (ctorIdOf address tag) atoms)
            (by intro atoms; simp [OpNoReuse]) (by
            simpa [hsource, hunder] using hrun)
      | recursor numArgs natLit rules =>
        by_cases hunder : args.length < numArgs + 1
        · cases world with
          | unique =>
            exact (stateThrowRun_not_ok (by
              simpa [hsource, hunder] using hrun)).elim
          | shared =>
            exact hknown
              (build := fun atoms => .papp address atoms)
              (by intro atoms; simp [OpNoReuse]) (by
              simpa [hsource, hunder] using hrun)
        · obtain ⟨_, checkedState, _, hknownRun⟩ :=
            stateBindRun_ok_inv (by
              simpa [hsource, hunder] using hrun)
          exact hknown (by intro atoms; simp [OpNoReuse]) hknownRun
      | extern arity =>
        by_cases hunder : args.length < arity
        · cases world with
          | unique =>
            exact (stateThrowRun_not_ok (by
              simpa [hsource, hunder] using hrun)).elim
          | shared =>
            exact hknown
              (build := fun atoms => .papp address atoms)
              (by intro atoms; simp [OpNoReuse]) (by
              simpa [hsource, hunder] using hrun)
        · exact hknown
            (build := fun atoms => .extern address atoms)
            (by intro atoms; simp [OpNoReuse]) (by
            simpa [hsource, hunder] using hrun)
  | lam uses body =>
    exact lowerEApplyRestNoReuse hexpr hrest (by
      simpa [lowerSpine] using hrun)
  | letE uses bound body =>
    exact lowerEApplyRestNoReuse hexpr hrest (by
      simpa [lowerSpine] using hrun)
  | proj index source =>
    exact lowerEApplyRestNoReuse hexpr hrest (by
      simpa [lowerSpine] using hrun)
  | lit literal =>
    exact lowerEApplyRestNoReuse hexpr hrest (by
      simpa [lowerSpine] using hrun)

private theorem lowerEVarNoReuse {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {world : Ixon.Owned} {index : Nat}
    {state finalState : LowSt} {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.var index)).run state =
      .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  have hssNe : (Ixon.Owned.shared != Ixon.Owned.shared) = false := by
    decide
  have huuNe : (Ixon.Owned.unique != Ixon.Owned.unique) = false := by
    decide
  have hsuNe : (Ixon.Owned.shared != Ixon.Owned.unique) = true := by
    decide
  have husNe : (Ixon.Owned.unique != Ixon.Owned.shared) = true := by
    decide
  have hsuEq : (Ixon.Owned.shared == Ixon.Owned.unique) = false := by
    decide
  have huuEq : (Ixon.Owned.unique == Ixon.Owned.unique) = true := by
    decide
  cases hentry : input.entries[index]? with
  | none =>
    exact (stateThrowRun_not_ok (by
      simpa [lowerE, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (stateThrowRun_not_ok (by
        simpa [lowerE, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (stateThrowRun_not_ok (by
          simpa [lowerE, hentry] using hrun)).elim
      | true =>
        by_cases hworld : worldOfUses uses = world
        · subst world
          have hsame :
              (worldOfUses uses != worldOfUses uses) = false := by
            cases uses <;> decide
          cases remaining with
          | zero =>
            exact (stateThrowRun_not_ok (by
              simpa [lowerE, hentry, hsame] using hrun)).elim
          | succ remaining =>
            cases remaining with
            | zero =>
              have hpure :
                  (input.setEntry index (.slot abs 0 uses false),
                    (_root_.id : Emit), AVal.slotA abs) =
                      (output, emit, value) ∧ state = finalState := by
                simpa [lowerE, hentry, hsame] using hrun
              have hemit : (_root_.id : Emit) = emit :=
                congrArg
                  (fun result : VEnv × Emit × AVal => result.2.1)
                  hpure.1
              rw [← hemit]
              exact emitNoReuse_id
            | succ remaining =>
              cases uses with
              | erased =>
                have hpure :
                    let input' := input.setEntry index
                      (.slot abs (Nat.succ remaining) .erased true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) =
                        (output, emit, value) ∧ state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, hsuEq,
                    hssNe, huuNe, hsuNe, husNe, huuEq] using hrun
                dsimp only at hpure
                have hemit :
                    emitOp (.dup (.var
                      ((input.setEntry index
                        (.slot abs (Nat.succ remaining) .erased true)).rel
                          abs))) = emit := by
                  simpa using congrArg
                    (fun result : VEnv × Emit × AVal => result.2.1)
                    hpure.1
                rw [← hemit]
                exact emitNoReuse_emitOp (by simp [OpNoReuse])
              | linear =>
                exact (stateThrowRun_not_ok (by
                  simpa [lowerE, hentry, worldOfUses, hsame, huuEq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq] using hrun)).elim
              | affine =>
                exact (stateThrowRun_not_ok (by
                  simpa [lowerE, hentry, worldOfUses, hsame, huuEq,
                    hssNe, huuNe, hsuNe, husNe, hsuEq] using hrun)).elim
              | many =>
                have hpure :
                    let input' := input.setEntry index
                      (.slot abs (Nat.succ remaining) .many true)
                    (input'.bump,
                      emitOp (.dup (.var (input'.rel abs))),
                      AVal.slotA input'.depth) =
                        (output, emit, value) ∧ state = finalState := by
                  simpa [lowerE, hentry, worldOfUses, hsame, hsuEq,
                    hssNe, huuNe, hsuNe, husNe, huuEq] using hrun
                dsimp only at hpure
                have hemit :
                    emitOp (.dup (.var
                      ((input.setEntry index
                        (.slot abs (Nat.succ remaining) .many true)).rel
                          abs))) = emit := by
                  simpa using congrArg
                    (fun result : VEnv × Emit × AVal => result.2.1)
                    hpure.1
                rw [← hemit]
                exact emitNoReuse_emitOp (by simp [OpNoReuse])
        · have hdiff : (worldOfUses uses != world) = true := by
            cases uses <;> cases world <;>
              simp_all [worldOfUses] <;> decide
          cases uses <;> cases world
          all_goals
            try { exact (hworld (by rfl)).elim }
          all_goals
            exact (stateThrowRun_not_ok (by
              simpa [lowerE, hentry, worldOfUses, hdiff, hssNe, huuNe,
                hsuNe, husNe, hsuEq, huuEq] using hrun)).elim

private theorem pureTripleRun_emitNoReuse
    {expectedOutput output : VEnv} {expectedEmit emit : Emit}
    {expectedValue value : AVal} {state finalState : LowSt}
    (hexpected : EmitNoReuse expectedEmit)
    (hrun : (pure (expectedOutput, expectedEmit, expectedValue) :
        LowerM (VEnv × Emit × AVal)).run state =
      .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  have hpure :
      (expectedOutput, expectedEmit, expectedValue) =
          (output, emit, value) ∧ state = finalState := by
    simpa using hrun
  have hemit : expectedEmit = emit :=
    congrArg (fun result : VEnv × Emit × AVal => result.2.1) hpure.1
  rw [← hemit]
  exact hexpected

private theorem lowerERefNoReuse {src : IxIR0.Env} {fuel : Nat}
    {input output : VEnv} {world : Ixon.Owned}
    {address : Ixon.Address} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world (.ref address)).run state =
      .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  have hsuEq : (Ixon.Owned.shared == Ixon.Owned.unique) = false := by
    decide
  cases hsource : src address with
  | none =>
    exact (stateThrowRun_not_ok (by
      simpa [lowerE, hsource] using hrun)).elim
  | some declaration =>
    cases declaration with
    | defn result body =>
      cases harity : lamArity body with
      | zero =>
        obtain ⟨unitValue, _, hvalue⟩ :=
          stateMapRun_ok_inv (by
            simpa [lowerE, hsource, harity] using hrun)
        cases unitValue
        have hemit : emitOp (.call address #[]) = emit :=
          congrArg (fun result : VEnv × Emit × AVal => result.2.1)
            hvalue
        rw [← hemit]
        exact emitNoReuse_emitOp (by simp [OpNoReuse])
      | succ arity =>
        cases world with
        | unique =>
          exact (stateThrowRun_not_ok (by
            simpa [lowerE, hsource, harity] using hrun)).elim
        | shared =>
          cases result with
          | unique =>
            exact (stateThrowRun_not_ok (by
              simpa [lowerE, hsource, harity] using hrun)).elim
          | shared =>
            cases hp : papSafe body with
            | false =>
              exact (stateThrowRun_not_ok (by
                simpa [lowerE, hsource, harity, hp, hsuEq]
                  using hrun)).elim
            | true =>
              exact pureTripleRun_emitNoReuse
                (emitNoReuse_emitOp (op := .papp address #[])
                  (by simp [OpNoReuse])) (by
                    simpa [lowerE, hsource, harity, hp, hsuEq]
                      using hrun)
    | ctor tag arity =>
      cases arity with
      | zero =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_emitOp
            (op := .alloc world (ctorIdOf address tag) #[])
            (by simp [OpNoReuse])) (by
              simpa [lowerE, hsource] using hrun)
      | succ arity =>
        cases world with
        | unique =>
          exact (stateThrowRun_not_ok (by
            simpa [lowerE, hsource] using hrun)).elim
        | shared =>
          obtain ⟨wrapper, _, hvalue⟩ :=
            stateMapRun_ok_inv (by
              simpa [lowerE, hsource] using hrun)
          have hemit : emitOp (.papp wrapper #[]) = emit :=
            congrArg (fun result : VEnv × Emit × AVal => result.2.1)
              hvalue
          rw [← hemit]
          exact emitNoReuse_emitOp (by simp [OpNoReuse])
    | recursor numArgs natLit rules =>
      cases world with
      | unique =>
        exact (stateThrowRun_not_ok (by
          simpa [lowerE, hsource] using hrun)).elim
      | shared =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_emitOp (op := .papp address #[])
            (by simp [OpNoReuse])) (by
              simpa [lowerE, hsource] using hrun)
    | extern arity =>
      cases arity with
      | zero =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_emitOp (op := .extern address #[])
            (by simp [OpNoReuse])) (by
              simpa [lowerE, hsource] using hrun)
      | succ arity =>
        cases world with
        | unique =>
          exact (stateThrowRun_not_ok (by
            simpa [lowerE, hsource] using hrun)).elim
        | shared =>
          exact pureTripleRun_emitNoReuse
            (emitNoReuse_emitOp (op := .papp address #[])
              (by simp [OpNoReuse])) (by
                simpa [lowerE, hsource] using hrun)

private theorem lowerELetNoReuse {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel)
    {input output : VEnv} {world : Ixon.Owned} {uses : Ixon.Uses}
    {bound body : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.letE uses bound body)).run state =
        .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  obtain ⟨boundResult, boundState, hbound, hafterBound⟩ :=
    stateBindRun_ok_inv (by simpa [lowerE] using hrun)
  rcases boundResult with ⟨middle, boundEmit, boundValue⟩
  have hboundNo : EmitNoReuse boundEmit := hexpr hbound
  cases boundValue with
  | slotA abs =>
    by_cases hzero : countUses 0 body = 0
    · cases uses with
      | erased =>
        obtain ⟨_, _, hthrow, _⟩ := stateBindRun_ok_inv (by
          simpa [hzero] using hafterBound)
        exact (stateThrowRun_not_ok hthrow).elim
      | linear =>
        obtain ⟨_, _, hthrow, _⟩ := stateBindRun_ok_inv (by
          simpa [hzero] using hafterBound)
        exact (stateThrowRun_not_ok hthrow).elim
      | affine =>
        obtain ⟨bodyResult, hbody, hvalue⟩ :=
          stateMapRun_ok_inv (by simpa [hzero] using hafterBound)
        rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
        have hemit :
            boundEmit ∘ emitOp (.dropU (.var (middle.rel abs))) ∘
              bodyEmit = emit := by
          exact congrArg
            (fun result : VEnv × Emit × AVal => result.2.1) hvalue
        rw [← hemit]
        exact emitNoReuse_comp (first := boundEmit)
          (second := emitOp (.dropU (.var (middle.rel abs))) ∘ bodyEmit)
          hboundNo
          (emitNoReuse_comp
            (emitNoReuse_emitOp (by simp [OpNoReuse]))
            (hexpr hbody))
      | many =>
        obtain ⟨bodyResult, hbody, hvalue⟩ :=
          stateMapRun_ok_inv (by simpa [hzero] using hafterBound)
        rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
        have hemit :
            boundEmit ∘ emitOp (.drop (.var (middle.rel abs))) ∘
              bodyEmit = emit := by
          exact congrArg
            (fun result : VEnv × Emit × AVal => result.2.1) hvalue
        rw [← hemit]
        exact emitNoReuse_comp (first := boundEmit)
          (second := emitOp (.drop (.var (middle.rel abs))) ∘ bodyEmit)
          hboundNo
          (emitNoReuse_comp
            (emitNoReuse_emitOp (by simp [OpNoReuse]))
            (hexpr hbody))
    · obtain ⟨bodyResult, hbody, hvalue⟩ :=
        stateMapRun_ok_inv (by simpa [hzero] using hafterBound)
      rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
      have hemit : boundEmit ∘ bodyEmit = emit := by
        exact congrArg
          (fun result : VEnv × Emit × AVal => result.2.1) hvalue
      rw [← hemit]
      exact emitNoReuse_comp hboundNo (hexpr hbody)
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · obtain ⟨bodyResult, hbody, hvalue⟩ :=
        stateMapRun_ok_inv (by simpa [hzero] using hafterBound)
      rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
      have hemit :
          boundEmit ∘ emitOp (.pure atom) ∘ bodyEmit = emit := by
        exact congrArg
          (fun result : VEnv × Emit × AVal => result.2.1) hvalue
      rw [← hemit]
      exact emitNoReuse_comp (first := boundEmit)
        (second := emitOp (.pure atom) ∘ bodyEmit) hboundNo
        (emitNoReuse_comp
          (emitNoReuse_emitOp (by simp [OpNoReuse]))
          (hexpr hbody))
    · obtain ⟨bodyResult, hbody, hvalue⟩ :=
        stateMapRun_ok_inv (by simpa [hzero] using hafterBound)
      rcases bodyResult with ⟨bodyOutput, bodyEmit, bodyValue⟩
      have hemit :
          boundEmit ∘ emitOp (.pure atom) ∘ bodyEmit = emit := by
        exact congrArg
          (fun result : VEnv × Emit × AVal => result.2.1) hvalue
      rw [← hemit]
      exact emitNoReuse_comp (first := boundEmit)
        (second := emitOp (.pure atom) ∘ bodyEmit) hboundNo
        (emitNoReuse_comp
          (emitNoReuse_emitOp (by simp [OpNoReuse]))
          (hexpr hbody))

private theorem lowerEProjNoReuse {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowNoReuse src fuel)
    {input output : VEnv} {world : Ixon.Owned} {index : Nat}
    {source : IxIR0.Expr} {state finalState : LowSt}
    {emit : Emit} {value : AVal}
    (hrun : (lowerE src (fuel + 1) input world
      (.proj index source)).run state =
        .ok (output, emit, value) finalState) :
    EmitNoReuse emit := by
  cases world with
  | unique =>
    simp [lowerE] at hrun
  | shared =>
    obtain ⟨borrowResult, borrowState, hborrowRun, hafterBorrow⟩ :=
      stateBindRun_ok_inv (by simpa [lowerE] using hrun)
    rcases borrowResult with ⟨middle, borrowEmit, borrowed, release⟩
    have hborrowNo : EmitNoReuse borrowEmit := hborrow hborrowRun
    cases borrowed with
    | constA atom =>
      cases atom with
      | erased =>
        exact pureTripleRun_emitNoReuse hborrowNo (by
          simpa using hafterBorrow)
      | var relative =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_comp hborrowNo
            (emitNoReuse_emitOp
              (op := .fetch (.var relative) index)
              (by simp [OpNoReuse]))) (by
              simpa using hafterBorrow)
      | lit literal =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_comp hborrowNo
            (emitNoReuse_emitOp
              (op := .fetch (.lit literal) index)
              (by simp [OpNoReuse]))) (by
              simpa using hafterBorrow)
    | slotA abs =>
      cases release with
      | false =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_comp (first := borrowEmit)
            (second := emitOp (.fetch (.var (middle.rel abs)) index) ∘
              emitOp (.dup (.var (middle.bump.rel middle.depth))))
            hborrowNo
            (emitNoReuse_comp
              (emitNoReuse_emitOp (by simp [OpNoReuse]))
              (emitNoReuse_emitOp (by simp [OpNoReuse])))) (by
                simpa using hafterBorrow)
      | true =>
        exact pureTripleRun_emitNoReuse
          (emitNoReuse_comp (first := borrowEmit)
            (second := emitOp (.fetch (.var (middle.rel abs)) index) ∘
              emitOp (.dup (.var (middle.bump.rel middle.depth))) ∘
              emitOp (.drop (.var (middle.bump.bump.rel abs))))
            hborrowNo
            (emitNoReuse_comp
              (emitNoReuse_emitOp (by simp [OpNoReuse]))
              (emitNoReuse_comp
                (emitNoReuse_emitOp (by simp [OpNoReuse]))
                (emitNoReuse_emitOp (by simp [OpNoReuse]))))) (by
                  simpa using hafterBorrow)

private theorem lowerENoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel)
    (hspine : LowerSpineNoReuse src fuel)
    (hborrow : LowerBorrowNoReuse src fuel)
    (hlam : LowerLamNoReuse src fuel) :
    LowerENoReuse src (fuel + 1) := by
  intro input world expr state finalState output emit value hrun
  cases expr with
  | var index => exact lowerEVarNoReuse hrun
  | ref address => exact lowerERefNoReuse hrun
  | lit literal =>
    exact pureTripleRun_emitNoReuse emitNoReuse_id (by
      simpa [lowerE] using hrun)
  | erased =>
    exact pureTripleRun_emitNoReuse emitNoReuse_id (by
      simpa [lowerE] using hrun)
  | lam uses body =>
    cases world with
    | unique =>
      have hthrow :
          (throw
            "function values live in the shared world (one-shot closures deferred)" :
            LowerM (VEnv × Emit × AVal)).run state =
              .ok (output, emit, value) finalState := by
        simpa [lowerE] using hrun
      exact (stateThrowRun_not_ok hthrow).elim
    | shared =>
      exact hlam (by simpa [lowerE] using hrun)
  | letE uses bound body => exact lowerELetNoReuse hexpr hrun
  | app function argument =>
    exact hspine (by simpa [lowerE] using hrun)
  | proj index source => exact lowerEProjNoReuse hborrow hrun

private theorem lowerLamNoReuse_succ {src : IxIR0.Env} {fuel : Nat} :
    LowerLamNoReuse src (fuel + 1) := by
  intro input expr state finalState output emit value hrun
  apply LowerSim.lowerLam_run_core
    (Result := fun _ _ emit _ => EmitNoReuse emit)
    (hrun := hrun)
  intro _bodyFuel captureOutput captureEmit captureValues _captureState
    fnAddress _addressState _code _bodyState _hfuel _hp hcaptureRun
    _hfreshRun _hbodyRun
  exact emitNoReuse_comp
    (first := captureEmit)
    (second := emitOp (.papp fnAddress
      (captureValues.map (·.toAtom captureOutput)).toArray))
    (lowerCaptures_emitNoReuse expr hcaptureRun)
    (emitNoReuse_emitOp (by simp [OpNoReuse]))

private theorem lowerFnBodyNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerENoReuse src fuel) :
    LowerFnBodyNoReuse src (fuel + 1) := by
  intro input drops world body state finalState code hrun
  simp only [lowerFnBody] at hrun
  obtain ⟨releaseResult, releaseState, hrelease, hafterRelease⟩ :=
    stateBindRun_ok_inv hrun
  rcases releaseResult with ⟨middle, releaseEmit⟩
  obtain ⟨bodyResult, bodyState, hbody, hpure⟩ :=
    stateBindRun_ok_inv hafterRelease
  rcases bodyResult with ⟨output, emit, value⟩
  have hcode :
      (releaseEmit ∘ emit) (.ret (value.toAtom output)) = code := by
    simpa using congrArg
      (fun result : EStateM.Result String LowSt Code =>
        match result with
        | .ok result _ => result
        | .error _ _ => .ret .erased) hpure
  rw [← hcode]
  apply emitNoReuse_comp (releaseSlots_emitNoReuse input hrelease)
    (hexpr hbody)
  simp [CodeNoReuse]

private theorem lowerNoReuse_succ {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerNoReuseCluster src fuel) :
    LowerNoReuseCluster src (fuel + 1) :=
  { expr := lowerENoReuse_succ hprev.expr hprev.spine hprev.borrow hprev.lam
    borrow := lowerBorrowNoReuse_succ hprev.expr
    spine := lowerSpineNoReuse_succ hprev.expr hprev.spine
      hprev.knownCall hprev.applyRest
    knownCall := knownCallNoReuse_succ hprev.args hprev.applyRest
    args := lowerArgsNoReuse_succ hprev.expr hprev.args
    applyRest := applyRestNoReuse_succ hprev.args
    lam := lowerLamNoReuse_succ
    fnBody := lowerFnBodyNoReuse_succ hprev.expr }

/-- Every successful mutually recursive expression-lowering action emits no
`reuse`, at every compiler fuel. -/
theorem lowerNoReuse (src : IxIR0.Env) :
    ∀ fuel, LowerNoReuseCluster src fuel := by
  intro fuel
  induction fuel with
  | zero => exact lowerNoReuse_zero src
  | succ fuel ih =>
    simpa [Nat.succ_eq_add_one] using lowerNoReuse_succ ih

/-- Closing a successfully lowered function body with `ret` produces
reuse-free target code. -/
theorem lowerFnBody_noReuse {src : IxIR0.Env} {fuel : Nat}
    {input : VEnv} {drops : List SlotDrop} {world : Ixon.Owned}
    {body : IxIR0.Expr} {state finalState : LowSt} {code : Code}
    (hrun : (lowerFnBody src fuel input drops world body).run state =
      .ok code finalState) :
    CodeNoReuse code :=
  (lowerNoReuse src fuel).fnBody hrun

/-! ## Generated-declaration state -/

theorem requireResultWorld_preservesStateNoReuse
    (actual demand : Ixon.Owned) :
    PreservesStateNoReuse (requireResultWorld actual demand) := by
  cases actual <;> cases demand <;>
    simp [requireResultWorld] <;>
    first
    | exact PreservesStateNoReuse.pure _
    | exact PreservesStateNoReuse.throw _

theorem releaseSlots_preservesStateNoReuse (input : VEnv) :
    ∀ drops : List SlotDrop,
      PreservesStateNoReuse (releaseSlots input drops) := by
  exact releaseSlots_action_core
    (ActionProperty := fun {α : Type} (action : LowerM α) =>
      PreservesStateNoReuse action)
    (hpure := fun value => PreservesStateNoReuse.pure value)
    (hbind := fun haction hnext =>
      PreservesStateNoReuse.bind haction hnext)
    (hthrowBind := fun message next =>
      PreservesStateNoReuse.throwBind message next)
    input

theorem lowerCapture_preservesStateNoReuse (expr : IxIR0.Expr)
    (input : VEnv) (index : Nat) :
    PreservesStateNoReuse (lowerCapture expr input index) := by
  intro state finalState result hstate hrun
  cases hentry : input.entries[index]? with
  | none =>
    exact (stateThrowRun_not_ok (by
      simpa [lowerCapture, hentry] using hrun)).elim
  | some entry =>
    cases entry with
    | recSelf arity =>
      exact (stateThrowRun_not_ok (by
        simpa [lowerCapture, hentry] using hrun)).elim
    | slot abs remaining uses held =>
      cases held with
      | false =>
        exact (stateThrowRun_not_ok (by
          simpa [lowerCapture, hentry] using hrun)).elim
      | true =>
        by_cases hunique : worldOfUses uses = .unique
        · have huuEq :
              (Ixon.Owned.unique == Ixon.Owned.unique) = true := by
            decide
          exact (stateThrowRun_not_ok (by
            simpa [lowerCapture, hentry, hunique, huuEq] using hrun)).elim
        · have huniqueEq :
              (worldOfUses uses == Ixon.Owned.unique) = false := by
            cases uses <;> simp_all [worldOfUses] <;> decide
          by_cases hmore : remaining > countUses index expr
          · have hfinal : state = finalState := by
              have hfull :
                  ((input.setEntry index
                      (.slot abs (remaining - countUses index expr)
                        uses true)).bump,
                    emitOp (.dup (.var
                      ((input.setEntry index
                        (.slot abs (remaining - countUses index expr)
                          uses true)).rel abs))),
                    AVal.slotA
                      (input.setEntry index
                        (.slot abs (remaining - countUses index expr)
                          uses true)).depth) = result ∧
                    state = finalState := by
                simpa [lowerCapture, hentry, huniqueEq, hmore] using hrun
              exact hfull.2
            subst finalState
            exact hstate
          · by_cases hequal : remaining = countUses index expr
            · have hfinal : state = finalState := by
                have hfull :
                    (input.setEntry index (.slot abs 0 uses false),
                      (_root_.id : Emit), AVal.slotA abs) = result ∧
                      state = finalState := by
                  simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                    using hrun
                exact hfull.2
              subst finalState
              exact hstate
            · exact (stateThrowRun_not_ok (by
                simpa [lowerCapture, hentry, huniqueEq, hmore, hequal]
                  using hrun)).elim

theorem lowerCaptures_preservesStateNoReuse (expr : IxIR0.Expr) :
    ∀ (input : VEnv) (captures : List Nat),
      PreservesStateNoReuse (lowerCaptures expr input captures) := by
  exact lowerCaptures_action_core
    (e := expr)
    (ActionProperty := fun {α : Type} (action : LowerM α) =>
      PreservesStateNoReuse action)
    (hpure := fun value => PreservesStateNoReuse.pure value)
    (hbind := fun haction hnext =>
      PreservesStateNoReuse.bind haction hnext)
    (hcapture := lowerCapture_preservesStateNoReuse expr)

def LowerEPreservesStateNoReuse (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input world expr,
    PreservesStateNoReuse (lowerE src fuel input world expr)

def LowerBorrowPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input expr,
    PreservesStateNoReuse (lowerBorrow src fuel input expr)

def LowerSpinePreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input world head args,
    PreservesStateNoReuse (lowerSpine src fuel input world head args)

def KnownCallPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input build count argWorlds resultWorld args,
    PreservesStateNoReuse
      (knownCall src fuel input build count argWorlds resultWorld args)

def LowerArgsPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input args,
    PreservesStateNoReuse (lowerArgs src fuel input args)

def ApplyRestPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input resultWorld pre function args,
    PreservesStateNoReuse
      (applyRest src fuel input resultWorld pre function args)

def LowerLamPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input expr,
    PreservesStateNoReuse (lowerLam src fuel input expr)

def LowerFnBodyPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) : Prop :=
  ∀ input drops world body,
    PreservesStateNoReuse (lowerFnBody src fuel input drops world body)

structure LowerStateNoReuseCluster
    (src : IxIR0.Env) (fuel : Nat) : Prop where
  expr : LowerEPreservesStateNoReuse src fuel
  borrow : LowerBorrowPreservesStateNoReuse src fuel
  spine : LowerSpinePreservesStateNoReuse src fuel
  knownCall : KnownCallPreservesStateNoReuse src fuel
  args : LowerArgsPreservesStateNoReuse src fuel
  applyRest : ApplyRestPreservesStateNoReuse src fuel
  lam : LowerLamPreservesStateNoReuse src fuel
  fnBody : LowerFnBodyPreservesStateNoReuse src fuel

private theorem lowerStateNoReuse_zero (src : IxIR0.Env) :
    LowerStateNoReuseCluster src 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro input world expr
    simp only [lowerE]
    exact PreservesStateNoReuse.throw _
  · intro input expr
    simp only [lowerBorrow]
    exact PreservesStateNoReuse.throw _
  · intro input world head args
    simp only [lowerSpine]
    exact PreservesStateNoReuse.throw _
  · intro input build count argWorlds resultWorld args
    simp only [knownCall]
    exact PreservesStateNoReuse.throw _
  · intro input args
    simp only [lowerArgs]
    exact PreservesStateNoReuse.throw _
  · intro input resultWorld pre function args
    simp only [applyRest]
    exact PreservesStateNoReuse.throw _
  · intro input expr
    simp only [lowerLam]
    exact PreservesStateNoReuse.throw _
  · intro input drops world body
    simp only [lowerFnBody]
    exact PreservesStateNoReuse.throw _

private theorem lowerFnBodyPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel) :
    LowerFnBodyPreservesStateNoReuse src (fuel + 1) := by
  intro input drops world body
  simp only [lowerFnBody]
  apply PreservesStateNoReuse.bind
    (releaseSlots_preservesStateNoReuse input drops)
  intro releaseResult
  rcases releaseResult with ⟨middle, releaseEmit⟩
  apply PreservesStateNoReuse.bind (hexpr middle world body)
  intro bodyResult
  rcases bodyResult with ⟨output, bodyEmit, value⟩
  exact PreservesStateNoReuse.pure
    (releaseEmit (bodyEmit (.ret (value.toAtom output))))

private theorem lowerLamPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hfnBody : LowerFnBodyPreservesStateNoReuse src fuel) :
    LowerLamPreservesStateNoReuse src (fuel + 1) := by
  intro input expr initial finalState result hinitial hrun
  rcases result with ⟨output, emit, value⟩
  apply LowerSim.lowerLam_run_core
    (Result := fun finalState _ _ _ => StateNoReuse finalState)
    (hrun := hrun)
  intro bodyFuel _captureOutput _captureEmit _captureValues captureState
    _fnAddress addressState code bodyState hfuel _hp hcaptureRun
    hfreshRun hbodyRun
  have hbodyFuel : bodyFuel = fuel := by
    exact Nat.add_right_cancel hfuel
  subst bodyFuel
  have hcaptureState :=
    lowerCaptures_preservesStateNoReuse expr input _ hinitial hcaptureRun
  have haddressState :=
    freshAddr_preservesStateNoReuse hcaptureState hfreshRun
  have hbodyState := hfnBody _ _ _ _ haddressState hbodyRun
  have hcode : CodeNoReuse code := lowerFnBody_noReuse hbodyRun
  exact hbodyState.prepend hcode

private theorem lowerArgsPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (hargs : LowerArgsPreservesStateNoReuse src fuel) :
    LowerArgsPreservesStateNoReuse src (fuel + 1) := by
  intro input args
  cases args with
  | nil =>
    simp only [lowerArgs]
    exact PreservesStateNoReuse.pure _
  | cons head rest =>
    rcases head with ⟨expr, world⟩
    simp only [lowerArgs]
    apply PreservesStateNoReuse.bind (hexpr input world expr)
    intro headResult
    rcases headResult with ⟨middle, headEmit, value⟩
    apply PreservesStateNoReuse.bind (hargs middle rest)
    intro tailResult
    rcases tailResult with ⟨output, tailEmit, values⟩
    exact PreservesStateNoReuse.pure
      (output, headEmit ∘ tailEmit, value :: values)

private theorem applyRestPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesStateNoReuse src fuel) :
    ApplyRestPreservesStateNoReuse src (fuel + 1) := by
  intro input resultWorld pre function args
  cases function with
  | slotA abs =>
    simp only [applyRest]
    apply PreservesStateNoReuse.bind
      (requireResultWorld_preservesStateNoReuse .shared resultWorld)
    intro unitValue
    cases unitValue
    apply PreservesStateNoReuse.bind
      (hargs input (args.map (fun arg => (arg, Ixon.Owned.shared))))
    intro argsResult
    rcases argsResult with ⟨output, argsEmit, values⟩
    exact PreservesStateNoReuse.pure
      (output.bump,
        pre ∘ argsEmit ∘ emitOp (.apply
          ((AVal.slotA abs).toAtom output)
          (values.map (·.toAtom output)).toArray),
        AVal.slotA output.depth)
  | constA atom =>
    cases atom with
    | erased =>
      simp only [applyRest]
      apply PreservesStateNoReuse.bind
        (hargs input (args.map (fun arg => (arg, Ixon.Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact PreservesStateNoReuse.pure
        ((releaseAll output values).1,
          pre ∘ argsEmit ∘ (releaseAll output values).2,
          AVal.constA .erased)
    | var relative =>
      simp only [applyRest]
      apply PreservesStateNoReuse.bind
        (requireResultWorld_preservesStateNoReuse .shared resultWorld)
      intro unitValue
      cases unitValue
      apply PreservesStateNoReuse.bind
        (hargs input (args.map (fun arg => (arg, Ixon.Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact PreservesStateNoReuse.pure
        (output.bump,
          pre ∘ argsEmit ∘ emitOp (.apply
            ((AVal.constA (.var relative)).toAtom output)
            (values.map (·.toAtom output)).toArray),
          AVal.slotA output.depth)
    | lit literal =>
      simp only [applyRest]
      apply PreservesStateNoReuse.bind
        (requireResultWorld_preservesStateNoReuse .shared resultWorld)
      intro unitValue
      cases unitValue
      apply PreservesStateNoReuse.bind
        (hargs input (args.map (fun arg => (arg, Ixon.Owned.shared))))
      intro argsResult
      rcases argsResult with ⟨output, argsEmit, values⟩
      exact PreservesStateNoReuse.pure
        (output.bump,
          pre ∘ argsEmit ∘ emitOp (.apply
            ((AVal.constA (.lit literal)).toAtom output)
            (values.map (·.toAtom output)).toArray),
          AVal.slotA output.depth)

private theorem knownCallPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hargs : LowerArgsPreservesStateNoReuse src fuel)
    (hrest : ApplyRestPreservesStateNoReuse src fuel) :
    KnownCallPreservesStateNoReuse src (fuel + 1) := by
  intro input build count argWorlds resultWorld args
  simp only [knownCall]
  apply PreservesStateNoReuse.bind
    (hargs input ((args.take count).zip (padWorlds argWorlds count)))
  intro argsResult
  rcases argsResult with ⟨output, argsEmit, values⟩
  by_cases hterminal : args.length ≤ count
  · simp only [if_pos hterminal]
    exact PreservesStateNoReuse.pure
      (output.bump,
        argsEmit ∘ emitOp
          (build (values.map (·.toAtom output)).toArray),
        AVal.slotA output.depth)
  · simp only [if_neg hterminal]
    exact hrest output.bump resultWorld
      (argsEmit ∘ emitOp
        (build (values.map (·.toAtom output)).toArray))
      (.slotA output.depth) (args.drop count)

private theorem lowerBorrowVarPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv) (index : Nat) :
    PreservesStateNoReuse
      (lowerBorrow src (fuel + 1) input (.var index)) := by
  simp only [lowerBorrow]
  cases hentry : input.entries[index]? with
  | none => exact PreservesStateNoReuse.throw _
  | some entry =>
    cases entry with
    | recSelf arity => exact PreservesStateNoReuse.throw _
    | slot abs remaining uses held =>
      cases held with
      | false => exact PreservesStateNoReuse.throw _
      | true =>
        cases uses with
        | linear => exact PreservesStateNoReuse.throw _
        | affine => exact PreservesStateNoReuse.throw _
        | erased =>
          cases remaining with
          | zero => exact PreservesStateNoReuse.throw _
          | succ remaining =>
            cases remaining with
            | zero => exact PreservesStateNoReuse.pure _
            | succ remaining => exact PreservesStateNoReuse.pure _
        | many =>
          cases remaining with
          | zero => exact PreservesStateNoReuse.throw _
          | succ remaining =>
            cases remaining with
            | zero => exact PreservesStateNoReuse.pure _
            | succ remaining => exact PreservesStateNoReuse.pure _

private theorem lowerBorrowDynamicPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    {input : VEnv} {expr : IxIR0.Expr} :
    PreservesStateNoReuse (do
      let (output, emit, value) ←
        lowerE src fuel input .shared expr
      let release :=
        match value with | .slotA _ => true | .constA _ => false
      pure (output, emit, value, release)) := by
  apply PreservesStateNoReuse.bind (hexpr input .shared expr)
  intro exprResult
  rcases exprResult with ⟨output, emit, value⟩
  exact PreservesStateNoReuse.pure
    (output, emit, value,
      match value with | .slotA _ => true | .constA _ => false)

private theorem lowerBorrowPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel) :
    LowerBorrowPreservesStateNoReuse src (fuel + 1) := by
  intro input expr
  cases expr with
  | var index =>
    exact (lowerBorrowVarPreservesStateNoReuse src fuel input index)
  | ref address =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | app function argument =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | lam uses body =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | letE uses value body =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | proj index value =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | lit literal =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr
  | erased =>
    simp only [lowerBorrow]
    exact lowerBorrowDynamicPreservesStateNoReuse hexpr

private theorem lowerEVarPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv)
    (world : Ixon.Owned) (index : Nat) :
    PreservesStateNoReuse
      (lowerE src (fuel + 1) input world (.var index)) := by
  simp only [lowerE]
  cases hentry : input.entries[index]? with
  | none => exact PreservesStateNoReuse.throw _
  | some entry =>
    cases entry with
    | recSelf arity => exact PreservesStateNoReuse.throw _
    | slot abs remaining uses held =>
      cases held with
      | false => exact PreservesStateNoReuse.throw _
      | true =>
        cases remaining with
        | zero =>
          cases uses <;> cases world <;>
            first
            | exact PreservesStateNoReuse.pure _
            | exact PreservesStateNoReuse.throw _
        | succ remaining =>
          cases remaining with
          | zero =>
            cases uses <;> cases world <;>
              first
              | exact PreservesStateNoReuse.pure _
              | exact PreservesStateNoReuse.throw _
          | succ remaining =>
            cases uses <;> cases world <;>
              first
              | exact PreservesStateNoReuse.pure _
              | exact PreservesStateNoReuse.throw _

private theorem lowerERefPreservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) (input : VEnv)
    (world : Ixon.Owned) (address : Ixon.Address) :
    PreservesStateNoReuse
      (lowerE src (fuel + 1) input world (.ref address)) := by
  simp only [lowerE]
  cases hsource : src address with
  | none =>
    simp only
    exact PreservesStateNoReuse.throw _
  | some declaration =>
    cases declaration with
    | defn result body =>
      simp only
      cases harity : lamArity body with
      | zero =>
        apply PreservesStateNoReuse.bind
          (requireResultWorld_preservesStateNoReuse result world)
        intro unitValue
        cases unitValue
        exact PreservesStateNoReuse.pure _
      | succ arity =>
        cases result <;> cases world <;> cases hp : papSafe body <;>
          first
          | exact PreservesStateNoReuse.pure _
          | exact PreservesStateNoReuse.throw _
    | ctor tag arity =>
      simp only
      cases arity with
      | zero => exact PreservesStateNoReuse.pure _
      | succ arity =>
        cases world with
        | unique => exact PreservesStateNoReuse.throw _
        | shared =>
          apply PreservesStateNoReuse.bind
            (wrapperFor_preservesStateNoReuse address tag (arity + 1))
          intro wrapper
          exact PreservesStateNoReuse.pure _
    | recursor numArgs natLit rules =>
      simp only
      cases world <;> first
        | exact PreservesStateNoReuse.pure _
        | exact PreservesStateNoReuse.throw _
    | extern arity =>
      simp only
      cases arity with
      | zero => exact PreservesStateNoReuse.pure _
      | succ arity =>
        cases world <;> first
          | exact PreservesStateNoReuse.pure _
          | exact PreservesStateNoReuse.throw _

private theorem lowerELamPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hlam : LowerLamPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (uses : Ixon.Uses)
    (body : IxIR0.Expr) :
    PreservesStateNoReuse
      (lowerE src (fuel + 1) input world (.lam uses body)) := by
  cases world with
  | unique =>
    simp only [lowerE]
    exact PreservesStateNoReuse.throw _
  | shared =>
    have hsuEq :
        (Ixon.Owned.shared == Ixon.Owned.unique) = false := by
      decide
    intro initial final result hinitial hrun
    exact hlam input (.lam uses body) hinitial (by
      simpa only [lowerE, hsuEq, Bool.false_eq_true, if_false] using hrun)

private theorem lowerEProjPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hborrow : LowerBorrowPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (index : Nat)
    (source : IxIR0.Expr) :
    PreservesStateNoReuse
      (lowerE src (fuel + 1) input world (.proj index source)) := by
  cases world with
  | unique =>
    simp only [lowerE]
    exact PreservesStateNoReuse.throw _
  | shared =>
    simp only [lowerE]
    apply PreservesStateNoReuse.bind (hborrow input source)
    intro borrowResult
    rcases borrowResult with ⟨output, emit, value, release⟩
    cases value with
    | slotA abs =>
      cases release <;> exact PreservesStateNoReuse.pure _
    | constA atom =>
      cases atom <;> exact PreservesStateNoReuse.pure _

private theorem lowerELetPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (uses : Ixon.Uses)
    (value body : IxIR0.Expr) :
    PreservesStateNoReuse
      (lowerE src (fuel + 1) input world (.letE uses value body)) := by
  simp only [lowerE]
  apply PreservesStateNoReuse.bind
    (hexpr input (worldOfUses uses) value)
  intro valueResult
  rcases valueResult with ⟨middle, valueEmit, boundValue⟩
  cases boundValue with
  | slotA abs =>
    by_cases hzero : countUses 0 body = 0
    · simp only [hzero, beq_self_eq_true, if_true]
      cases uses with
      | erased => exact PreservesStateNoReuse.throwBind _ _
      | linear => exact PreservesStateNoReuse.throwBind _ _
      | affine =>
        apply PreservesStateNoReuse.bind
          (PreservesStateNoReuse.pure _)
        intro releaseEmit
        apply PreservesStateNoReuse.bind (hexpr _ world body)
        intro bodyResult
        rcases bodyResult with ⟨output, bodyEmit, result⟩
        exact PreservesStateNoReuse.pure
          (output.pop, valueEmit ∘ releaseEmit ∘ bodyEmit, result)
      | many =>
        apply PreservesStateNoReuse.bind
          (PreservesStateNoReuse.pure _)
        intro releaseEmit
        apply PreservesStateNoReuse.bind (hexpr _ world body)
        intro bodyResult
        rcases bodyResult with ⟨output, bodyEmit, result⟩
        exact PreservesStateNoReuse.pure
          (output.pop, valueEmit ∘ releaseEmit ∘ bodyEmit, result)
    · simp [hzero]
      apply PreservesStateNoReuse.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact PreservesStateNoReuse.pure
        (output.pop, valueEmit ∘ bodyEmit, result)
  | constA atom =>
    by_cases hzero : countUses 0 body = 0
    · simp only [hzero, beq_self_eq_true, if_true]
      apply PreservesStateNoReuse.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact PreservesStateNoReuse.pure
        (output.pop,
          valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit, result)
    · simp [hzero]
      apply PreservesStateNoReuse.bind (hexpr _ world body)
      intro bodyResult
      rcases bodyResult with ⟨output, bodyEmit, result⟩
      exact PreservesStateNoReuse.pure
        (output.pop,
          valueEmit ∘ emitOp (.pure atom) ∘ bodyEmit, result)

private theorem lowerEPreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (hspine : LowerSpinePreservesStateNoReuse src fuel)
    (hborrow : LowerBorrowPreservesStateNoReuse src fuel)
    (hlam : LowerLamPreservesStateNoReuse src fuel) :
    LowerEPreservesStateNoReuse src (fuel + 1) := by
  intro input world expr
  cases expr with
  | var index =>
    exact (lowerEVarPreservesStateNoReuse src fuel input world index)
  | ref address =>
    exact (lowerERefPreservesStateNoReuse src fuel input world address)
  | lit literal =>
    simp only [lowerE]
    exact PreservesStateNoReuse.pure _
  | erased =>
    simp only [lowerE]
    exact PreservesStateNoReuse.pure _
  | lam uses body =>
    exact (lowerELamPreservesStateNoReuse hlam input world uses body)
  | letE uses value body =>
    exact (lowerELetPreservesStateNoReuse
      hexpr input world uses value body)
  | app function argument =>
    simp only [lowerE]
    exact hspine input world function [argument]
  | proj index source =>
    exact (lowerEProjPreservesStateNoReuse
      hborrow input world index source)

private theorem lowerSpineDynamicPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (hrest : ApplyRestPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (head : IxIR0.Expr)
    (args : List IxIR0.Expr) :
    PreservesStateNoReuse (do
      let (output, emit, function) ←
        lowerE src fuel input .shared head
      applyRest src fuel output world emit function args) := by
  apply PreservesStateNoReuse.bind (hexpr input .shared head)
  intro headResult
  rcases headResult with ⟨output, emit, function⟩
  exact hrest output world emit function args

private theorem lowerSpineVarPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (hknown : KnownCallPreservesStateNoReuse src fuel)
    (hrest : ApplyRestPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (index : Nat)
    (args : List IxIR0.Expr) :
    PreservesStateNoReuse
      (lowerSpine src (fuel + 1) input world (.var index) args) := by
  simp only [lowerSpine]
  cases hentry : input.entries[index]? with
  | none =>
    simp only
    exact lowerSpineDynamicPreservesStateNoReuse
      hexpr hrest input world (.var index) args
  | some entry =>
    cases entry with
    | slot abs remaining uses held =>
      simp only
      exact lowerSpineDynamicPreservesStateNoReuse
        hexpr hrest input world (.var index) args
    | recSelf arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        exact PreservesStateNoReuse.throw _
      · simp only [if_neg hunder]
        apply PreservesStateNoReuse.bind
          (requireResultWorld_preservesStateNoReuse .shared world)
        intro unitValue
        cases unitValue
        exact hknown input (.callSelf ·) arity
          (List.replicate arity .shared) world args

private theorem lowerSpineRefPreservesStateNoReuse
    {src : IxIR0.Env} {fuel : Nat}
    (hknown : KnownCallPreservesStateNoReuse src fuel)
    (input : VEnv) (world : Ixon.Owned) (address : Ixon.Address)
    (args : List IxIR0.Expr) :
    PreservesStateNoReuse
      (lowerSpine src (fuel + 1) input world (.ref address) args) := by
  simp only [lowerSpine]
  cases hsource : src address with
  | none =>
    simp only
    exact PreservesStateNoReuse.throw _
  | some declaration =>
    cases declaration with
    | defn result body =>
      simp only
      by_cases hunder : args.length < lamArity body
      · simp only [if_pos hunder]
        cases world with
        | unique => exact PreservesStateNoReuse.throw _
        | shared =>
          cases result with
          | unique => exact PreservesStateNoReuse.throw _
          | shared =>
            cases hp : papSafe body with
            | false => exact PreservesStateNoReuse.throw _
            | true =>
              exact hknown input (.papp address ·) args.length
                (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        apply PreservesStateNoReuse.bind
          (requireResultWorld_preservesStateNoReuse result
            (if args.length == lamArity body then world else .shared))
        intro unitValue
        cases unitValue
        exact hknown input (.call address ·) (lamArity body)
          ((lamUses body).map worldOfUses) world args
    | ctor tag arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        cases world with
        | unique => exact PreservesStateNoReuse.throw _
        | shared =>
          apply PreservesStateNoReuse.bind
            (wrapperFor_preservesStateNoReuse address tag arity)
          intro wrapper
          exact hknown input (.papp wrapper ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        exact hknown input (.alloc world (ctorIdOf address tag) ·) arity
          (List.replicate arity world) world args
    | recursor numArgs natLit rules =>
      simp only
      by_cases hunder : args.length < numArgs + 1
      · simp only [if_pos hunder]
        cases world with
        | unique => exact PreservesStateNoReuse.throw _
        | shared =>
          exact hknown input (.papp address ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        apply PreservesStateNoReuse.bind
          (requireResultWorld_preservesStateNoReuse .shared world)
        intro unitValue
        cases unitValue
        exact hknown input (.call address ·) (numArgs + 1)
          (List.replicate (numArgs + 1) .shared) world args
    | extern arity =>
      simp only
      by_cases hunder : args.length < arity
      · simp only [if_pos hunder]
        cases world with
        | unique => exact PreservesStateNoReuse.throw _
        | shared =>
          exact hknown input (.papp address ·) args.length
            (List.replicate args.length .shared) .shared args
      · simp only [if_neg hunder]
        exact hknown input (.extern address ·) arity
          (List.replicate arity .shared) world args

private theorem lowerSpinePreservesStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hexpr : LowerEPreservesStateNoReuse src fuel)
    (hspine : LowerSpinePreservesStateNoReuse src fuel)
    (hknown : KnownCallPreservesStateNoReuse src fuel)
    (hrest : ApplyRestPreservesStateNoReuse src fuel) :
    LowerSpinePreservesStateNoReuse src (fuel + 1) := by
  intro input world head args
  cases head with
  | app function argument =>
    simp only [lowerSpine]
    exact hspine input world function (argument :: args)
  | erased =>
    simp only [lowerSpine]
    exact hrest input world (_root_.id : Emit) (.constA .erased) args
  | var index =>
    exact (lowerSpineVarPreservesStateNoReuse
      hexpr hknown hrest input world index args)
  | ref address =>
    exact (lowerSpineRefPreservesStateNoReuse
      hknown input world address args)
  | lam uses body =>
    simp only [lowerSpine]
    exact lowerSpineDynamicPreservesStateNoReuse
      hexpr hrest input world (.lam uses body) args
  | letE uses value body =>
    simp only [lowerSpine]
    exact lowerSpineDynamicPreservesStateNoReuse
      hexpr hrest input world (.letE uses value body) args
  | proj index source =>
    simp only [lowerSpine]
    exact lowerSpineDynamicPreservesStateNoReuse
      hexpr hrest input world (.proj index source) args
  | lit literal =>
    simp only [lowerSpine]
    exact lowerSpineDynamicPreservesStateNoReuse
      hexpr hrest input world (.lit literal) args

private theorem lowerStateNoReuse_succ
    {src : IxIR0.Env} {fuel : Nat}
    (hprev : LowerStateNoReuseCluster src fuel) :
    LowerStateNoReuseCluster src (fuel + 1) :=
  { expr := lowerEPreservesStateNoReuse_succ
      hprev.expr hprev.spine hprev.borrow hprev.lam
    borrow := lowerBorrowPreservesStateNoReuse_succ hprev.expr
    spine := lowerSpinePreservesStateNoReuse_succ
      hprev.expr hprev.spine hprev.knownCall hprev.applyRest
    knownCall := knownCallPreservesStateNoReuse_succ
      hprev.args hprev.applyRest
    args := lowerArgsPreservesStateNoReuse_succ hprev.expr hprev.args
    applyRest := applyRestPreservesStateNoReuse_succ hprev.args
    lam := lowerLamPreservesStateNoReuse_succ hprev.fnBody
    fnBody := lowerFnBodyPreservesStateNoReuse_succ hprev.expr }

/-- Every lowering-cluster action preserves reuse-freedom of the accumulated
generated declarations. -/
theorem lowerStateNoReuse (src : IxIR0.Env) :
    ∀ fuel, LowerStateNoReuseCluster src fuel := by
  intro fuel
  induction fuel with
  | zero => exact lowerStateNoReuse_zero src
  | succ fuel ih =>
    simpa [Nat.succ_eq_add_one] using lowerStateNoReuse_succ ih

private theorem fieldRetainPlan_emitNoReuse
    {input output : VEnv} {retains : List RecursorFieldRetain}
    {emit : Emit}
    (hplan : LowerSim.FieldRetainPlan input retains output emit) :
    EmitNoReuse emit := by
  induction hplan with
  | nil => exact emitNoReuse_id
  | retain hentry tail ih =>
    exact emitNoReuse_comp
      (emitNoReuse_emitOp (by simp [OpNoReuse])) ih

private theorem releasePlan_emitNoReuse
    {input output : VEnv} {drops : List SlotDrop} {emit : Emit}
    (hplan : LowerSim.ReleasePlan input drops output emit) :
    EmitNoReuse emit := by
  induction hplan with
  | nil => exact emitNoReuse_id
  | many hentry tail ih =>
    exact emitNoReuse_comp
      (emitNoReuse_emitOp (by simp [OpNoReuse])) ih
  | affine hentry tail ih =>
    exact emitNoReuse_comp
      (emitNoReuse_emitOp (by simp [OpNoReuse])) ih

/-- Every successfully generated recursor alternative is reuse-free. -/
theorem lowerRecursorRule_noReuse
    {src : IxIR0.Env} {fuel numArgs : Nat}
    {rule : IxIR0.RecRule} {tag : Nat}
    {state finalState : LowSt} {alternative : Alt}
    (hrun : (lowerRecursorRule src fuel numArgs (rule, tag)).run state =
      .ok alternative finalState) :
    AltNoReuse alternative := by
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      output, bodyEmit, value, hfield, hparameter, hbody, hshape⟩ :=
    LowerSim.lowerRecursorRule_run_plan_inv hrun
  subst alternative
  simp only [AltNoReuse]
  exact fieldRetainPlan_emitNoReuse hfield _
    ((emitNoReuse_emitOp (op := .drop (.var (fieldOutput.rel numArgs)))
        (by simp [OpNoReuse])) _
      (releasePlan_emitNoReuse hparameter _
        (((lowerNoReuse src fuel).expr hbody) _
          (by simp [CodeNoReuse]))))

theorem lowerRecursorRule_preservesStateNoReuse
    (src : IxIR0.Env) (fuel numArgs : Nat)
    (item : IxIR0.RecRule × Nat) :
    PreservesStateNoReuse (lowerRecursorRule src fuel numArgs item) := by
  intro initial finalState alternative hinitial hrun
  rcases item with ⟨rule, tag⟩
  obtain ⟨fieldOutput, fieldEmit, rhsInput, parameterEmit,
      output, bodyEmit, value, hfield, hparameter, hbody, hshape⟩ :=
    LowerSim.lowerRecursorRule_run_plan_inv hrun
  exact (lowerStateNoReuse src fuel).expr rhsInput .shared rule.rhs
    hinitial hbody

private theorem listMapM_altNoReuse {α : Type}
    (action : α → LowerM Alt)
    (haction : ∀ item {initial finalState alternative},
      (action item).run initial = .ok alternative finalState →
      AltNoReuse alternative) :
    ∀ (items : List α) {initial finalState : LowSt}
        {alternatives : List Alt},
      (items.mapM action).run initial = .ok alternatives finalState →
      ∀ alternative ∈ alternatives, AltNoReuse alternative := by
  intro items
  induction items with
  | nil =>
    intro initial finalState alternatives hrun alternative hmember
    have hpure : ([] : List Alt) = alternatives ∧
        initial = finalState := by
      simpa using hrun
    rw [← hpure.1] at hmember
    simp at hmember
  | cons head tail ih =>
    intro initial finalState alternatives hrun alternative hmember
    simp only [List.mapM_cons] at hrun
    obtain ⟨headAlt, middle, hhead, hafterHead⟩ :=
      stateBindRun_ok_inv hrun
    obtain ⟨tailAlts, tailState, htail, hpure⟩ :=
      stateBindRun_ok_inv hafterHead
    have hresult : headAlt :: tailAlts = alternatives ∧
        tailState = finalState := by
      simpa using hpure
    rw [← hresult.1] at hmember
    simp only [List.mem_cons] at hmember
    cases hmember with
    | inl hselected =>
      subst alternative
      exact haction head hhead
    | inr hselected => exact ih htail alternative hselected

theorem lowerRecursor_preservesStateNoReuse
    (src : IxIR0.Env) (fuel numArgs : Nat) (natLit : Bool)
    (rules : Array IxIR0.RecRule) :
    PreservesStateNoReuse
      (lowerRecursor src fuel numArgs natLit rules) := by
  simp only [lowerRecursor]
  apply PreservesStateNoReuse.bind
    (PreservesStateNoReuse.listMapM
      (lowerRecursorRule src fuel numArgs)
      (lowerRecursorRule_preservesStateNoReuse src fuel numArgs)
      rules.toList.zipIdx)
  intro alternatives
  exact PreservesStateNoReuse.pure
    (⟨numArgs + 1, .shared, true,
      .case (.var 0) natLit alternatives.toArray⟩ : FnDef)

/-- A successfully lowered recursor has reuse-free alternatives. -/
theorem lowerRecursor_noReuse
    {src : IxIR0.Env} {fuel numArgs : Nat} {natLit : Bool}
    {rules : Array IxIR0.RecRule} {state finalState : LowSt}
    {definition : FnDef}
    (hrun : (lowerRecursor src fuel numArgs natLit rules).run state =
      .ok definition finalState) :
    CodeNoReuse definition.body := by
  obtain ⟨alternatives, halts, hdefinition⟩ := stateMapRun_ok_inv (by
    simpa [lowerRecursor] using hrun)
  have hall := listMapM_altNoReuse
    (lowerRecursorRule src fuel numArgs)
    (fun item _ _ _ hrun => lowerRecursorRule_noReuse hrun)
    rules.toList.zipIdx halts
  cases hdefinition
  simp only [CodeNoReuse]
  intro alternative hmember
  exact hall alternative (by simpa using hmember)

def OptionDeclNoReuse : Option (Ixon.Address × Decl) → Prop
  | none => True
  | some item => DeclNoReuse item.2

theorem lowerDecl_preservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat) :
    ∀ item, PreservesStateNoReuse (lowerDecl src fuel item)
  | (address, .defn result body) => by
      simp only [lowerDecl]
      apply PreservesStateNoReuse.bind
        ((lowerStateNoReuse src fuel).fnBody _ _ result _)
      intro code
      exact PreservesStateNoReuse.pure
        (some (address, Decl.fn ⟨lamArity body, result,
          result == .shared && papSafe body, code⟩))
  | (_, .ctor tag arity) => by
      simp only [lowerDecl]
      exact PreservesStateNoReuse.pure
        (none : Option (Ixon.Address × Decl))
  | (address, .recursor numArgs natLit rules) => by
      simp only [lowerDecl]
      apply PreservesStateNoReuse.bind
        (lowerRecursor_preservesStateNoReuse
          src fuel numArgs natLit rules)
      intro definition
      exact PreservesStateNoReuse.pure
        (some (address, Decl.fn definition))
  | (address, .extern arity) => by
      simp only [lowerDecl]
      exact PreservesStateNoReuse.pure
        (some (address, Decl.extern arity))

/-- Every optional base declaration returned by `lowerDecl` is reuse-free. -/
theorem lowerDecl_noReuse
    {src : IxIR0.Env} {fuel : Nat}
    {item : Ixon.Address × IxIR0.Decl} {state finalState : LowSt}
    {output : Option (Ixon.Address × Decl)}
    (hrun : (lowerDecl src fuel item).run state =
      .ok output finalState) :
    OptionDeclNoReuse output := by
  rcases item with ⟨address, declaration⟩
  cases declaration with
  | defn result body =>
    obtain ⟨code, hbody, houtput⟩ := stateMapRun_ok_inv (by
      simpa [lowerDecl] using hrun)
    cases houtput
    exact lowerFnBody_noReuse hbody
  | ctor tag arity =>
    have hpure : none = output ∧ state = finalState := by
      simpa [lowerDecl] using hrun
    rw [← hpure.1]
    simp [OptionDeclNoReuse]
  | recursor numArgs natLit rules =>
    obtain ⟨definition, hrecursor, houtput⟩ := stateMapRun_ok_inv (by
      simpa [lowerDecl] using hrun)
    cases houtput
    exact lowerRecursor_noReuse hrecursor
  | extern arity =>
    have hpure : some (address, Decl.extern arity) = output ∧
        state = finalState := by
      simpa [lowerDecl] using hrun
    rw [← hpure.1]
    simp [OptionDeclNoReuse, DeclNoReuse]

theorem DeclListNoReuse.append
    {left right : List (Ixon.Address × Decl)}
    (hleft : DeclListNoReuse left)
    (hright : DeclListNoReuse right) :
    DeclListNoReuse (left ++ right) := by
  intro declaration hmember
  rw [List.mem_append] at hmember
  cases hmember with
  | inl hleftMember => exact hleft declaration hleftMember
  | inr hrightMember => exact hright declaration hrightMember

private theorem listFilterMapM_declNoReuse {α : Type}
    (action : α → LowerM (Option (Ixon.Address × Decl)))
    (haction : ∀ item {initial finalState output},
      (action item).run initial = .ok output finalState →
      OptionDeclNoReuse output) :
    ∀ (items : List α) {initial finalState : LowSt}
        {declarations : List (Ixon.Address × Decl)},
      (items.filterMapM action).run initial =
        .ok declarations finalState →
      DeclListNoReuse declarations := by
  intro items
  induction items with
  | nil =>
    intro initial finalState declarations hrun
    have hpure : ([] : List (Ixon.Address × Decl)) = declarations ∧
        initial = finalState := by
      simpa using hrun
    intro declaration hmember
    rw [← hpure.1] at hmember
    simp at hmember
  | cons head tail ih =>
    intro initial finalState declarations hrun
    rw [List.filterMapM_cons] at hrun
    obtain ⟨headOutput, middle, hhead, hafterHead⟩ :=
      stateBindRun_ok_inv hrun
    have hheadNo := haction head hhead
    cases headOutput with
    | none =>
      exact ih (by simpa only using hafterHead)
    | some headDeclaration =>
      obtain ⟨tailDeclarations, tailState, htail, hpure⟩ :=
        stateBindRun_ok_inv hafterHead
      have hresult : headDeclaration :: tailDeclarations = declarations ∧
          tailState = finalState := by
        simpa [Function.comp_def] using hpure
      intro declaration hmember
      rw [← hresult.1] at hmember
      simp only [List.mem_cons] at hmember
      cases hmember with
      | inl hselected =>
        subst declaration
        exact hheadNo
      | inr hselected => exact ih htail declaration hselected

theorem lowerDecls_preservesStateNoReuse
    (src : IxIR0.Env) (fuel : Nat)
    (declarations : List (Ixon.Address × IxIR0.Decl)) :
    PreservesStateNoReuse
      (declarations.filterMapM (lowerDecl src fuel)) :=
  PreservesStateNoReuse.listFilterMapM (lowerDecl src fuel)
    (lowerDecl_preservesStateNoReuse src fuel) declarations

theorem lowerDecls_noReuse
    {src : IxIR0.Env} {fuel : Nat}
    {inputs : List (Ixon.Address × IxIR0.Decl)}
    {state finalState : LowSt}
    {declarations : List (Ixon.Address × Decl)}
    (hrun : (inputs.filterMapM (lowerDecl src fuel)).run state =
      .ok declarations finalState) :
    DeclListNoReuse declarations :=
  listFilterMapM_declNoReuse (lowerDecl src fuel)
    (fun _item _ _ _ hrun => lowerDecl_noReuse hrun) inputs hrun

/-- Every declaration and the closed main body returned by a successful
whole-program lowering run are reuse-free; the final generated state carries
the same invariant. -/
theorem lowerAllAction_noReuse
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {fuel : Nat}
    {targetDeclarations : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt}
    (hrun : (lowerAllAction declarations main mainWorld fuel).run {} =
      .ok (targetDeclarations, mainCode) finalState) :
    DeclListNoReuse targetDeclarations ∧
      CodeNoReuse mainCode ∧ StateNoReuse finalState := by
  let src := IxIR0.Env.ofList declarations
  simp only [lowerAllAction] at hrun
  obtain ⟨base, baseState, hbase, hafterBase⟩ :=
    stateBindRun_ok_inv hrun
  obtain ⟨compiledMain, mainState, hmain, hafterMain⟩ :=
    stateBindRun_ok_inv hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    stateBindRun_ok_inv hafterMain
  have hgetState : mainState = observed ∧ mainState = getState := by
    simpa using hget
  have hresult :
      (base ++ observed.extra, compiledMain) =
          (targetDeclarations, mainCode) ∧
        getState = finalState := by
    simpa using hpure
  have hbaseNo : DeclListNoReuse base := by
    apply lowerDecls_noReuse hbase
  have hbaseState : StateNoReuse baseState := by
    apply lowerDecls_preservesStateNoReuse src fuel declarations
      StateNoReuse.empty
    simpa [src] using hbase
  have hmainNo : CodeNoReuse compiledMain := lowerFnBody_noReuse hmain
  have hmainState : StateNoReuse mainState :=
    (lowerStateNoReuse src fuel).fnBody ⟨[], 0⟩ [] mainWorld main
      hbaseState hmain
  have hdeclsEq : base ++ mainState.extra = targetDeclarations := by
    rw [hgetState.1]
    exact congrArg Prod.fst hresult.1
  have hmainEq : compiledMain = mainCode :=
    congrArg Prod.snd hresult.1
  have hfinalEq : mainState = finalState :=
    hgetState.2.trans hresult.2
  refine ⟨?_, ?_, ?_⟩
  · rw [← hdeclsEq]
    exact hbaseNo.append hmainState
  · rwa [← hmainEq]
  · rwa [← hfinalEq]

private theorem envOfList_some_mem
    {entries : List (Ixon.Address × Decl)} {address : Ixon.Address}
    {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    (address, declaration) ∈ entries := by
  unfold Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ :=
    Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Ixon.Address × Decl => entry.1 == address) hfind
  have haddress : entryAddress = address :=
    Ixon.Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

/-- A declaration-list environment is reuse-free whenever every declaration
in the backing list is reuse-free. -/
theorem ctxOfList_noReuse
    {declarations : List (Ixon.Address × Decl)}
    {oracle : Ixon.Address → List RVal → Option RVal}
    (hdeclarations : DeclListNoReuse declarations) :
    CtxNoReuse
      ({ decls := Env.ofList declarations, oracle := oracle } : Ctx) := by
  intro address definition hlookup
  exact hdeclarations (address, .fn definition)
    (envOfList_some_mem hlookup)

/-- The exact declaration-list context returned by a successful whole pass is
reuse-free, including every lifted body and constructor wrapper accumulated in
the final compiler state. -/
theorem lowerAllAction_ctxNoReuse
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {targetDeclarations : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {ctx : Ctx}
    (hlower :
      (lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (targetDeclarations, mainCode) finalState)
    (hdecls : ctx.decls = Env.ofList targetDeclarations) :
    CtxNoReuse ctx := by
  have houtput := lowerAllAction_noReuse hlower
  intro address definition hlookup
  rw [hdecls] at hlookup
  exact houtput.1 (address, .fn definition)
    (envOfList_some_mem hlookup)

/-- The actual whole-pass output instantiates `CostRefinement` with the exact
equation `reuses = 0`.  The source run and value graph remain semantically
relevant to the interface but are intentionally absent from the counter
proof. -/
theorem lowerAllAction_reuseCostRefinement
    {sourceCtx : IxIR0.Ctx} {funRel : Sim.FunctionRel}
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {targetDeclarations : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {ctx : Ctx}
    (hlower :
      (lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (targetDeclarations, mainCode) finalState)
    (hdecls : ctx.decls = Env.ofList targetDeclarations) :
    LowerSim.CostRefinement sourceCtx ctx main mainCode funRel
      (fun _ observation => ReuseFreeCostSpec observation) := by
  apply LowerSim.RunCostInvariant.costRefinement
  exact runCostInvariant_of_noReuse
    (lowerAllAction_ctxNoReuse hlower hdecls)
    (lowerAllAction_noReuse hlower).2.1

/-- The whole-pass output satisfies the current lowerer's combined counter
contract: `reuses = 0 ∧ frees ≤ allocs`. -/
theorem lowerAllAction_costRefinement
    {sourceCtx : IxIR0.Ctx} {funRel : Sim.FunctionRel}
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {targetDeclarations : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {ctx : Ctx}
    (hlower :
      (lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (targetDeclarations, mainCode) finalState)
    (hdecls : ctx.decls = Env.ofList targetDeclarations) :
    LowerSim.CostRefinement sourceCtx ctx main mainCode funRel
      (fun _ observation => CurrentLowererCostSpec observation) := by
  apply LowerSim.RunCostInvariant.costRefinement
  exact runCostInvariant_of_noReuse_with_allocationFree
    (lowerAllAction_ctxNoReuse hlower hdecls)
    (lowerAllAction_noReuse hlower).2.1

/-- The actual transient lowerer satisfies `LowerSim.Reclamation`: every
successful compiled-main execution can release its result and reach a store
with no live nodes. -/
theorem lowerAllAction_reclamation
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {targetDeclarations : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {ctx : Ctx}
    (hlower :
      (lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (targetDeclarations, mainCode) finalState)
    (hdecls : ctx.decls = Env.ofList targetDeclarations)
    (hrepresented : LowerSim.ExtraRepresented ctx finalState)
    (hcontracts :
      LowerSim.CompilerContracts (IxIR0.Env.ofList declarations) ctx) :
    LowerSim.Reclamation ctx mainCode mainWorld := by
  have houtput := lowerAllAction_noReuse hlower
  have hctx : CtxNoReuse ctx :=
    lowerAllAction_ctxNoReuse hlower hdecls
  apply LowerSim.reclamation_of_run_ownership_and_zero_reuses
  · intro runFuel store value hrun
    exact LowerSim.lowerAllAction_main_owned hlower hrepresented hcontracts
      hrun
  · intro runFuel store value hrun
    exact runMain_reuses_eq_zero hctx houtput.2.1 hrun

end Ix.Compiler.IxIR1.NoReuse
