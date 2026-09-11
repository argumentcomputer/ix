import Ix.Compiler.Fuel
import Ix.Compiler.IxIR1.Eval

/-!
# Fuel monotonicity for the IxIR₁ evaluator

Successful state-passing evaluation is stable under raising fuel for all
eight mutually recursive evaluator functions. Every reached non-fuel error
is stable as well. These are the target-side composition principles needed
by progress and settlement proofs: independently constructed observations
can be raised to one common fuel without changing their result.
-/

namespace Ix.Compiler.IxIR1

private theorem bindOk {error α β : Type} (value : α)
    (next : α → Except error β) :
    (Except.ok value >>= next) = next value := rfl

private theorem bindErr {error α β : Type} (err : error)
    (next : α → Except error β) :
    ((Except.error err : Except error α) >>= next) = .error err := rfl

private def MonoAt (fuel : Nat) : Prop :=
  (∀ ctx cur store env code out,
    runCode ctx fuel cur store env code = .ok out →
      runCode ctx (fuel + 1) cur store env code = .ok out) ∧
  (∀ ctx cur store env op out,
    runOp ctx fuel cur store env op = .ok out →
      runOp ctx (fuel + 1) cur store env op = .ok out) ∧
  (∀ ctx address args store out,
    invoke ctx fuel address args store = .ok out →
      invoke ctx (fuel + 1) address args store = .ok out) ∧
  (∀ ctx store function args out,
    applyGo ctx fuel store function args = .ok out →
      applyGo ctx (fuel + 1) store function args = .ok out) ∧
  (∀ ctx store value out,
    dropVal ctx fuel store value = .ok out →
      dropVal ctx (fuel + 1) store value = .ok out) ∧
  (∀ ctx store values out,
    dropMany ctx fuel store values = .ok out →
      dropMany ctx (fuel + 1) store values = .ok out) ∧
  (∀ ctx store value out,
    dropUVal ctx fuel store value = .ok out →
      dropUVal ctx (fuel + 1) store value = .ok out) ∧
  (∀ ctx store values out,
    dropManyU ctx fuel store values = .ok out →
      dropManyU ctx (fuel + 1) store values = .ok out)

private theorem monoAt : ∀ fuel, MonoAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code out h
      rw [runCode.eq_def] at h
      simp at h
    · intro ctx cur store env op out h
      rw [runOp.eq_def] at h
      simp at h
    · intro ctx address args store out h
      rw [invoke.eq_def] at h
      simp at h
    · intro ctx store function args out h
      rw [applyGo.eq_def] at h
      simp at h
    · intro ctx store value out h
      rw [dropVal.eq_def] at h
      simp at h
    · intro ctx store values out h
      rw [dropMany.eq_def] at h
      simp at h
    · intro ctx store value out h
      rw [dropUVal.eq_def] at h
      simp at h
    · intro ctx store values out h
      rw [dropManyU.eq_def] at h
      simp at h
  | succ fuel ih =>
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply, ihDrop, ihDropMany,
      ihDropU, ihDropManyU⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code out h
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | letOp op rest =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hop : runOp ctx fuel cur store env op with
        | error err =>
          rw [hop, bindErr] at h
          contradiction
        | ok opOut =>
          rcases opOut with ⟨middle, value⟩
          rw [hop, bindOk] at h
          rw [ihOp _ _ _ _ _ _ hop, bindOk]
          exact ihCode _ _ _ _ _ _ h
      | case scrut peelNat alts =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hscrut : resolveAtom env scrut with
        | error err =>
          rw [hscrut, bindErr] at h
          contradiction
        | ok scrutValue =>
          rw [hscrut, bindOk] at h
          rw [bindOk]
          cases scrutValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hbox : store.get? loc with
            | none => simp [hbox] at h
            | some box =>
              simp only [hbox] at h ⊢
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => simp at h
                | ctorN cid fields =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == cid.cidx) with
                  | none => simp [halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at h ⊢
                        exact ihCode _ _ _ _ _ _ h
                      · simp [halt, hsize] at h
          | lit literal =>
            cases literal with
            | str string => simp at h
            | nat value =>
              cases hpeel : peelNat with
              | false => simp [hpeel] at h
              | true =>
                cases value with
                | zero =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == 0) with
                  | none => simp [hpeel, halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at h ⊢
                        exact ihCode _ _ _ _ _ _ h
                      | succ fieldCount => simp [hpeel, halt] at h
                | succ value =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == 1) with
                  | none => simp [hpeel, halt] at h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero => simp [hpeel, halt] at h
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at h ⊢
                          exact ihCode _ _ _ _ _ _ h
                        | succ fieldCount => simp [hpeel, halt] at h
          | erased => simp at h
    · intro ctx cur store env op out h
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | alloc world cid args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | reuse target cid args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | free target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | dup target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | drop target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases htarget : resolveAtom env target with
        | error err =>
          rw [htarget, bindErr] at h
          contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          rw [bindOk]
          cases targetValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hdrop : dropVal ctx fuel store (.loc loc) with
            | error err =>
              rw [hdrop, bindErr] at h
              contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at h
              rw [ihDrop _ _ _ _ hdrop, bindOk]
              exact h
          | lit literal => exact h
          | erased => exact h
      | dropU target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases htarget : resolveAtom env target with
        | error err =>
          rw [htarget, bindErr] at h
          contradiction
        | ok targetValue =>
          rw [htarget, bindOk] at h
          rw [bindOk]
          cases targetValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hdrop : dropUVal ctx fuel store (.loc loc) with
            | error err =>
              rw [hdrop, bindErr] at h
              contradiction
            | ok dropped =>
              rw [hdrop, bindOk] at h
              rw [ihDropU _ _ _ _ hdrop, bindOk]
              exact h
          | lit literal => exact h
          | erased => exact h
      | fetch target field =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | call address args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hargs : resolveAtoms env args with
        | error err =>
          rw [hargs, bindErr] at h
          contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          rw [bindOk]
          exact ihInvoke _ _ _ _ _ h
      | callSelf args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hargs : resolveAtoms env args with
        | error err =>
          rw [hargs, bindErr] at h
          contradiction
        | ok values =>
          rw [hargs, bindOk] at h
          rw [bindOk]
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h ⊢
            cases hcode : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err =>
              rw [hcode, bindErr] at h
              contradiction
            | ok result =>
              rw [hcode, bindOk] at h
              rw [ihCode _ _ _ _ _ _ hcode, bindOk]
              exact h
          · simp [harity] at h
      | papp address args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | apply function args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hfunction : resolveAtom env function with
        | error err =>
          rw [hfunction, bindErr] at h
          contradiction
        | ok functionValue =>
          rw [hfunction, bindOk] at h
          rw [bindOk]
          cases hargs : resolveAtoms env args with
          | error err =>
            rw [hargs, bindErr] at h
            contradiction
          | ok values =>
            rw [hargs, bindOk] at h
            rw [bindOk]
            exact ihApply _ _ _ _ _ h
      | extern address args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
    · intro ctx address args store out h
      rw [invoke.eq_def] at h ⊢
      dsimp only at h ⊢
      cases hdecl : ctx.decls address with
      | none => simp [hdecl] at h
      | some decl =>
        simp only [hdecl] at h ⊢
        cases decl with
        | extern arity => exact h
        | fn d =>
          dsimp only at h ⊢
          cases harity : args.length != d.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h ⊢
            cases hcode : runCode ctx fuel d store args.reverse d.body with
            | error err =>
              rw [hcode, bindErr] at h
              contradiction
            | ok result =>
              rw [hcode, bindOk] at h
              rw [ihCode _ _ _ _ _ _ hcode, bindOk]
              exact h
          · simp [harity] at h
    · intro ctx store function args out h
      rw [applyGo.eq_def] at h ⊢
      dsimp only at h ⊢
      cases function with
      | lit literal => simp at h
      | erased =>
        cases hdrop : dropMany ctx fuel store args with
        | error err =>
          rw [hdrop, bindErr] at h
          contradiction
        | ok dropped =>
          rw [hdrop, bindOk] at h
          rw [ihDropMany _ _ _ _ hdrop, bindOk]
          exact h
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields => simp at h
            | papN address arity captured =>
              dsimp only at h ⊢
              cases hdup : dupVals store captured.toList with
              | error err =>
                rw [hdup, bindErr] at h
                contradiction
              | ok duplicated =>
                rw [hdup, bindOk] at h
                rw [bindOk]
                cases hdrop : dropVal ctx fuel duplicated (.loc loc) with
                | error err =>
                  rw [hdrop, bindErr] at h
                  contradiction
                | ok ready =>
                  rw [hdrop, bindOk] at h
                  rw [ihDrop _ _ _ _ hdrop, bindOk]
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder] at h ⊢
                    exact h
                  · simp only [hunder] at h ⊢
                    cases hexact :
                        (captured.toList ++ args).length == arity
                    · simp only [hexact, Bool.false_eq_true,
                        if_false] at h ⊢
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h ⊢
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at h
                            contradiction
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at h
                            rw [ihInvoke _ _ _ _ _ hinvoke, bindOk]
                            exact ihApply _ _ _ _ _ h
                    · simp only [hexact, if_true] at h ⊢
                      cases hdecl : ctx.decls address with
                      | none => simp [hdecl] at h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false => simp [hdecl, hpapsafe] at h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h ⊢
                          exact ihInvoke _ _ _ _ _ h
    · intro ctx store value out h
      rw [dropVal.eq_def] at h ⊢
      dsimp only at h ⊢
      cases value with
      | lit literal => exact h
      | erased => exact h
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases world with
            | unique => simp at h
            | shared =>
              cases hrc : rc == 1
              · simp only [hrc, Bool.false_eq_true, if_false] at h ⊢
                exact h
              · simp only [hrc, if_true] at h ⊢
                cases node with
                | ctorN cid fields =>
                  exact ihDropMany _ _ _ _ h
                | papN address arity args =>
                  exact ihDropMany _ _ _ _ h
    · intro ctx store values out h
      rw [dropMany.eq_def] at h ⊢
      dsimp only at h ⊢
      cases values with
      | nil => exact h
      | cons value rest =>
        dsimp only at h ⊢
        cases hdrop : dropVal ctx fuel store value with
        | error err =>
          rw [hdrop, bindErr] at h
          contradiction
        | ok middle =>
          rw [hdrop, bindOk] at h
          rw [ihDrop _ _ _ _ hdrop, bindOk]
          exact ihDropMany _ _ _ _ h
    · intro ctx store value out h
      rw [dropUVal.eq_def] at h ⊢
      dsimp only at h ⊢
      cases value with
      | lit literal => exact h
      | erased => exact h
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp [hbox] at h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases world with
            | shared => simp at h
            | unique =>
              cases node with
              | papN address arity args => simp at h
              | ctorN cid fields =>
                exact ihDropManyU _ _ _ _ h
    · intro ctx store values out h
      rw [dropManyU.eq_def] at h ⊢
      dsimp only at h ⊢
      cases values with
      | nil => exact h
      | cons value rest =>
        dsimp only at h ⊢
        cases hdrop : dropUVal ctx fuel store value with
        | error err =>
          rw [hdrop, bindErr] at h
          contradiction
        | ok middle =>
          rw [hdrop, bindOk] at h
          rw [ihDropU _ _ _ _ hdrop, bindOk]
          exact ihDropManyU _ _ _ _ h

/-! ## Persistence of terminal evaluator errors -/

/-- Any reached non-fuel error is stable when one unit of evaluator fuel is
added.  The mutual proof covers stuck, memory, and closed-world failures that
may surface through calls, higher-order application, or recursive release. -/
private def ErrorMonoAt (fuel : Nat) (error : Err) : Prop :=
  (∀ ctx cur store env code,
    runCode ctx fuel cur store env code = .error (error) →
      runCode ctx (fuel + 1) cur store env code = .error (error)) ∧
  (∀ ctx cur store env op,
    runOp ctx fuel cur store env op = .error (error) →
      runOp ctx (fuel + 1) cur store env op = .error (error)) ∧
  (∀ ctx address args store,
    invoke ctx fuel address args store = .error (error) →
      invoke ctx (fuel + 1) address args store = .error (error)) ∧
  (∀ ctx store function args,
    applyGo ctx fuel store function args = .error (error) →
      applyGo ctx (fuel + 1) store function args = .error (error)) ∧
  (∀ ctx store value,
    dropVal ctx fuel store value = .error (error) →
      dropVal ctx (fuel + 1) store value = .error (error)) ∧
  (∀ ctx store values,
    dropMany ctx fuel store values = .error (error) →
      dropMany ctx (fuel + 1) store values = .error (error)) ∧
  (∀ ctx store value,
    dropUVal ctx fuel store value = .error (error) →
      dropUVal ctx (fuel + 1) store value = .error (error)) ∧
  (∀ ctx store values,
    dropManyU ctx fuel store values = .error (error) →
      dropManyU ctx (fuel + 1) store values = .error (error))

private theorem errorMonoAt : ∀ fuel error, error ≠ .fuel → ErrorMonoAt fuel error := by
  intro fuel
  induction fuel with
  | zero =>
    intro error hnonfuel
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code h
      rw [runCode.eq_def] at h
      simp_all
    · intro ctx cur store env op h
      rw [runOp.eq_def] at h
      simp_all
    · intro ctx address args store h
      rw [invoke.eq_def] at h
      simp_all
    · intro ctx store function args h
      rw [applyGo.eq_def] at h
      simp_all
    · intro ctx store value h
      rw [dropVal.eq_def] at h
      simp_all
    · intro ctx store values h
      rw [dropMany.eq_def] at h
      simp_all
    · intro ctx store value h
      rw [dropUVal.eq_def] at h
      simp_all
    · intro ctx store values h
      rw [dropManyU.eq_def] at h
      simp_all
  | succ fuel ih =>
    intro error hnonfuel
    obtain ⟨ihCode, ihOp, ihInvoke, ihApply, ihDrop, ihDropMany,
      ihDropU, ihDropManyU⟩ := ih error hnonfuel
    obtain ⟨monoCode, monoOp, monoInvoke, monoApply, monoDrop,
      monoDropMany, monoDropU, monoDropManyU⟩ := monoAt fuel
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx cur store env code h
      cases code with
      | ret atom =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        exact h
      | letOp op rest =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hop : runOp ctx fuel cur store env op with
        | error err =>
          rw [hop, bindErr] at h
          have herr : err = error := Except.error.inj h
          subst err
          rw [ihOp _ _ _ _ _ hop, bindErr]
        | ok opOut =>
          rcases opOut with ⟨middle, value⟩
          rw [hop, bindOk] at h
          rw [monoOp _ _ _ _ _ _ hop, bindOk]
          exact ihCode _ _ _ _ _ h
      | case scrut peelNat alts =>
        rw [runCode.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hscrut : resolveAtom env scrut with
        | error err =>
          rw [hscrut, bindErr] at h
          rw [bindErr]
          exact h
        | ok scrutValue =>
          rw [hscrut, bindOk] at h
          rw [bindOk]
          cases scrutValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hbox : store.get? loc with
            | none => simp only [hbox] at h ⊢; exact h
            | some box =>
              simp only [hbox] at h ⊢
              cases box with
              | mk world rc node =>
                cases node with
                | papN address arity args => exact h
                | ctorN cid fields =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == cid.cidx) with
                  | none => simp only [halt] at h ⊢; exact h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases hsize : fields.size != fieldCount
                      · simp only [halt, hsize, Bool.false_eq_true,
                          if_false] at h ⊢
                        exact ihCode _ _ _ _ _ h
                      · simp only [halt, hsize, if_true] at h ⊢
                        exact h
          | lit literal =>
            cases literal with
            | str string => exact h
            | nat value =>
              cases hpeel : peelNat with
              | false => simp only [hpeel] at h ⊢; exact h
              | true =>
                cases value with
                | zero =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == 0) with
                  | none => simp only [hpeel, halt] at h ⊢; exact h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at h ⊢
                        exact ihCode _ _ _ _ _ h
                      | succ fieldCount =>
                        simp only [hpeel, halt] at h ⊢
                        exact h
                | succ value =>
                  cases halt : alts.find?
                      (fun alt => alt.cidx == 1) with
                  | none => simp only [hpeel, halt] at h ⊢; exact h
                  | some alt =>
                    cases alt with
                    | mk cidx fieldCount body =>
                      cases fieldCount with
                      | zero =>
                        simp only [hpeel, halt] at h ⊢
                        exact h
                      | succ fieldCount =>
                        cases fieldCount with
                        | zero =>
                          simp only [hpeel, halt] at h ⊢
                          exact ihCode _ _ _ _ _ h
                        | succ fieldCount =>
                          simp only [hpeel, halt] at h ⊢
                          exact h
          | erased => exact h
    · intro ctx cur store env op h
      cases op with
      | pure atom =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | alloc world cid args =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | reuse target cid args =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | free target =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | dup target =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | drop target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases htarget : resolveAtom env target with
        | error err =>
          rw [htarget, bindErr] at h
          rw [bindErr]
          exact h
        | ok targetValue =>
          rw [htarget, bindOk] at h
          rw [bindOk]
          cases targetValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hdrop : dropVal ctx fuel store (.loc loc) with
            | error err =>
              rw [hdrop, bindErr] at h
              have herr : err = error := Except.error.inj h
              subst err
              rw [ihDrop _ _ _ hdrop, bindErr]
            | ok dropped =>
              rw [hdrop, bindOk] at h
              contradiction
          | lit literal => exact h
          | erased => exact h
      | dropU target =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases htarget : resolveAtom env target with
        | error err =>
          rw [htarget, bindErr] at h
          rw [bindErr]
          exact h
        | ok targetValue =>
          rw [htarget, bindOk] at h
          rw [bindOk]
          cases targetValue with
          | loc loc =>
            dsimp only at h ⊢
            cases hdrop : dropUVal ctx fuel store (.loc loc) with
            | error err =>
              rw [hdrop, bindErr] at h
              have herr : err = error := Except.error.inj h
              subst err
              rw [ihDropU _ _ _ hdrop, bindErr]
            | ok dropped =>
              rw [hdrop, bindOk] at h
              contradiction
          | lit literal => exact h
          | erased => exact h
      | fetch target field =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | call address args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hargs : resolveAtoms env args with
        | error err =>
          rw [hargs, bindErr] at h
          rw [bindErr]
          exact h
        | ok values =>
          rw [hargs, bindOk] at h
          rw [bindOk]
          exact ihInvoke _ _ _ _ h
      | callSelf args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hargs : resolveAtoms env args with
        | error err =>
          rw [hargs, bindErr] at h
          rw [bindErr]
          exact h
        | ok values =>
          rw [hargs, bindOk] at h
          rw [bindOk]
          cases harity : values.length != cur.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h ⊢
            cases hcode : runCode ctx fuel cur store values.reverse
                cur.body with
            | error err =>
              rw [hcode, bindErr] at h
              have herr : err = error := Except.error.inj h
              subst err
              rw [ihCode _ _ _ _ _ hcode, bindErr]
            | ok result =>
              rw [hcode, bindOk] at h
              rw [monoCode _ _ _ _ _ _ hcode, bindOk]
              exact h
          · simp only [harity, if_true] at h ⊢
            exact h
      | papp address args =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | apply function args =>
        rw [runOp.eq_def] at h ⊢
        dsimp only at h ⊢
        cases hfunction : resolveAtom env function with
        | error err =>
          rw [hfunction, bindErr] at h
          rw [bindErr]
          exact h
        | ok functionValue =>
          rw [hfunction, bindOk] at h
          rw [bindOk]
          cases hargs : resolveAtoms env args with
          | error err =>
            rw [hargs, bindErr] at h
            rw [bindErr]
            exact h
          | ok values =>
            rw [hargs, bindOk] at h
            rw [bindOk]
            exact ihApply _ _ _ _ h
      | extern address args =>
        rw [runOp.eq_def] at h ⊢; dsimp only at h ⊢; exact h
    · intro ctx address args store h
      rw [invoke.eq_def] at h ⊢
      dsimp only at h ⊢
      cases hdecl : ctx.decls address with
      | none => simp only [hdecl] at h ⊢; exact h
      | some decl =>
        simp only [hdecl] at h ⊢
        cases decl with
        | extern arity => exact h
        | fn d =>
          dsimp only at h ⊢
          cases harity : args.length != d.arity
          · simp only [harity, Bool.false_eq_true, if_false] at h ⊢
            cases hcode : runCode ctx fuel d store args.reverse d.body with
            | error err =>
              rw [hcode, bindErr] at h
              have herr : err = error := Except.error.inj h
              subst err
              rw [ihCode _ _ _ _ _ hcode, bindErr]
            | ok result =>
              rw [hcode, bindOk] at h
              rw [monoCode _ _ _ _ _ _ hcode, bindOk]
              exact h
          · simp only [harity, if_true] at h ⊢
            exact h
    · intro ctx store function args h
      rw [applyGo.eq_def] at h ⊢
      dsimp only at h ⊢
      cases function with
      | lit literal => exact h
      | erased =>
        cases hdrop : dropMany ctx fuel store args with
        | error err =>
          rw [hdrop, bindErr] at h
          have herr : err = error := Except.error.inj h
          subst err
          rw [ihDropMany _ _ _ hdrop, bindErr]
        | ok dropped =>
          rw [hdrop, bindOk] at h
          contradiction
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp only [hbox] at h ⊢; exact h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases node with
            | ctorN cid fields => exact h
            | papN address arity captured =>
              dsimp only at h ⊢
              cases hdup : dupVals store captured.toList with
              | error err =>
                rw [hdup, bindErr] at h
                rw [bindErr]
                exact h
              | ok duplicated =>
                rw [hdup, bindOk] at h
                rw [bindOk]
                cases hdrop : dropVal ctx fuel duplicated (.loc loc) with
                | error err =>
                  rw [hdrop, bindErr] at h
                  have herr : err = error := Except.error.inj h
                  subst err
                  rw [ihDrop _ _ _ hdrop, bindErr]
                | ok ready =>
                  rw [hdrop, bindOk] at h
                  rw [monoDrop _ _ _ _ hdrop, bindOk]
                  by_cases hunder :
                      (captured.toList ++ args).length < arity
                  · simp only [hunder] at h ⊢
                    exact h
                  · simp only [hunder] at h ⊢
                    cases hexact :
                        (captured.toList ++ args).length == arity
                    · simp only [hexact, Bool.false_eq_true,
                        if_false] at h ⊢
                      cases hdecl : ctx.decls address with
                      | none => simp only [hdecl] at h ⊢; exact h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false =>
                          simp only [hdecl, hpapsafe,
                            Bool.false_eq_true, if_false] at h ⊢
                          exact h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h ⊢
                          cases hinvoke : invoke ctx fuel address
                              ((captured.toList ++ args).take arity) ready with
                          | error err =>
                            rw [hinvoke, bindErr] at h
                            have herr : err = error := Except.error.inj h
                            subst err
                            rw [ihInvoke _ _ _ _ hinvoke, bindErr]
                          | ok called =>
                            rcases called with ⟨calledStore, calledValue⟩
                            rw [hinvoke, bindOk] at h
                            rw [monoInvoke _ _ _ _ _ hinvoke, bindOk]
                            exact ihApply _ _ _ _ h
                    · simp only [hexact, if_true] at h ⊢
                      cases hdecl : ctx.decls address with
                      | none => simp only [hdecl] at h ⊢; exact h
                      | some decl =>
                        cases hpapsafe : declPapSafe decl with
                        | false =>
                          simp only [hdecl, hpapsafe,
                            Bool.false_eq_true, if_false] at h ⊢
                          exact h
                        | true =>
                          simp only [hdecl, hpapsafe, if_true] at h ⊢
                          exact ihInvoke _ _ _ _ h
    · intro ctx store value h
      rw [dropVal.eq_def] at h ⊢
      dsimp only at h ⊢
      cases value with
      | lit literal => exact h
      | erased => exact h
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp only [hbox] at h ⊢; exact h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases world with
            | unique => exact h
            | shared =>
              cases hrc : rc == 1
              · simp only [hrc, Bool.false_eq_true, if_false] at h ⊢
                exact h
              · simp only [hrc, if_true] at h ⊢
                cases node with
                | ctorN cid fields =>
                  exact ihDropMany _ _ _ h
                | papN address arity args =>
                  exact ihDropMany _ _ _ h
    · intro ctx store values h
      rw [dropMany.eq_def] at h ⊢
      dsimp only at h ⊢
      cases values with
      | nil => exact h
      | cons value rest =>
        dsimp only at h ⊢
        cases hdrop : dropVal ctx fuel store value with
        | error err =>
          rw [hdrop, bindErr] at h
          have herr : err = error := Except.error.inj h
          subst err
          rw [ihDrop _ _ _ hdrop, bindErr]
        | ok middle =>
          rw [hdrop, bindOk] at h
          rw [monoDrop _ _ _ _ hdrop, bindOk]
          exact ihDropMany _ _ _ h
    · intro ctx store value h
      rw [dropUVal.eq_def] at h ⊢
      dsimp only at h ⊢
      cases value with
      | lit literal => exact h
      | erased => exact h
      | loc loc =>
        dsimp only at h ⊢
        cases hbox : store.get? loc with
        | none => simp only [hbox] at h ⊢; exact h
        | some box =>
          simp only [hbox] at h ⊢
          cases box with
          | mk world rc node =>
            cases world with
            | shared => exact h
            | unique =>
              cases node with
              | papN address arity args => exact h
              | ctorN cid fields =>
                exact ihDropManyU _ _ _ h
    · intro ctx store values h
      rw [dropManyU.eq_def] at h ⊢
      dsimp only at h ⊢
      cases values with
      | nil => exact h
      | cons value rest =>
        dsimp only at h ⊢
        cases hdrop : dropUVal ctx fuel store value with
        | error err =>
          rw [hdrop, bindErr] at h
          have herr : err = error := Except.error.inj h
          subst err
          rw [ihDropU _ _ _ hdrop, bindErr]
        | ok middle =>
          rw [hdrop, bindOk] at h
          rw [monoDropU _ _ _ _ hdrop, bindOk]
          exact ihDropManyU _ _ _ h
/-- Successful code execution is stable under raising fuel. -/
theorem runCode_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {code : Code}
    {out : Store × RVal} (hle : fuel ≤ larger)
    (hrun : runCode ctx fuel cur store env code = .ok out) :
    runCode ctx larger cur store env code = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).1 _ _ _ _ _ _ h) hle hrun

/-- Every reached non-fuel code error persists when fuel is raised. -/
theorem runCode_error_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {code : Code} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : runCode ctx fuel cur store env code = .error error) :
    runCode ctx larger cur store env code = .error error := by
  exact fuel_mono_of_succ
    (fun current h => (errorMonoAt current error hne).1 _ _ _ _ _ h)
    hle hrun

/-- A dynamic memory error in code execution persists when fuel is raised.
Fuel may reveal more execution, but it cannot repair an already-reached
memory-discipline failure. -/
theorem runCode_mem_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {code : Code} {message : String}
    (hle : fuel ≤ larger)
    (hrun : runCode ctx fuel cur store env code = .error (.mem message)) :
    runCode ctx larger cur store env code = .error (.mem message) :=
  runCode_error_mono hle (by simp) hrun

/-- Successful primitive-operation execution is stable under raising fuel. -/
theorem runOp_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {op : Op}
    {out : Store × RVal} (hle : fuel ≤ larger)
    (hrun : runOp ctx fuel cur store env op = .ok out) :
    runOp ctx larger cur store env op = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.1 _ _ _ _ _ _ h) hle hrun

/-- Every reached non-fuel primitive-operation error persists when fuel is
raised. -/
theorem runOp_error_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {op : Op} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : runOp ctx fuel cur store env op = .error error) :
    runOp ctx larger cur store env op = .error error := by
  exact fuel_mono_of_succ
    (fun current h => (errorMonoAt current error hne).2.1 _ _ _ _ _ h)
    hle hrun

theorem runOp_mem_mono {ctx : Ctx} {fuel larger : Nat} {cur : FnDef}
    {store : Store} {env : List RVal} {op : Op} {message : String}
    (hle : fuel ≤ larger)
    (hrun : runOp ctx fuel cur store env op = .error (.mem message)) :
    runOp ctx larger cur store env op = .error (.mem message) :=
  runOp_error_mono hle (by simp) hrun

/-- Successful known invocation is stable under raising fuel. -/
theorem invoke_mono {ctx : Ctx} {fuel larger : Nat}
    {address : Ixon.Address}
    {args : List RVal} {store : Store} {out : Store × RVal}
    (hle : fuel ≤ larger)
    (hrun : invoke ctx fuel address args store = .ok out) :
    invoke ctx larger address args store = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.1 _ _ _ _ _ h) hle hrun

theorem invoke_error_mono {ctx : Ctx} {fuel larger : Nat}
    {address : Ixon.Address} {args : List RVal} {store : Store}
    {error : Err} (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : invoke ctx fuel address args store = .error error) :
    invoke ctx larger address args store = .error error := by
  exact fuel_mono_of_succ
    (fun current h => (errorMonoAt current error hne).2.2.1 _ _ _ _ h)
    hle hrun

/-- Successful higher-order application is stable under raising fuel. -/
theorem applyGo_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {function : RVal} {args : List RVal} {out : Store × RVal}
    (hle : fuel ≤ larger)
    (hrun : applyGo ctx fuel store function args = .ok out) :
    applyGo ctx larger store function args = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.2.1 _ _ _ _ _ h) hle hrun

theorem applyGo_error_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {function : RVal} {args : List RVal} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : applyGo ctx fuel store function args = .error error) :
    applyGo ctx larger store function args = .error error := by
  exact fuel_mono_of_succ
    (fun current h =>
      (errorMonoAt current error hne).2.2.2.1 _ _ _ _ h)
    hle hrun

/-- Successful shared deep drop is stable under raising fuel. -/
theorem dropVal_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {value : RVal} {out : Store} (hle : fuel ≤ larger)
    (hrun : dropVal ctx fuel store value = .ok out) :
    dropVal ctx larger store value = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.2.2.1 _ _ _ _ h) hle hrun

theorem dropVal_error_mono {ctx : Ctx} {fuel larger : Nat}
    {store : Store} {value : RVal} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : dropVal ctx fuel store value = .error error) :
    dropVal ctx larger store value = .error error := by
  exact fuel_mono_of_succ
    (fun current h =>
      (errorMonoAt current error hne).2.2.2.2.1 _ _ _ h)
    hle hrun

theorem dropMany_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {values : List RVal} {out : Store} (hle : fuel ≤ larger)
    (hrun : dropMany ctx fuel store values = .ok out) :
    dropMany ctx larger store values = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.2.2.2.1 _ _ _ _ h) hle hrun

theorem dropMany_error_mono {ctx : Ctx} {fuel larger : Nat}
    {store : Store} {values : List RVal} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : dropMany ctx fuel store values = .error error) :
    dropMany ctx larger store values = .error error := by
  exact fuel_mono_of_succ
    (fun current h =>
      (errorMonoAt current error hne).2.2.2.2.2.1 _ _ _ h)
    hle hrun

/-- Successful unique deep free is stable under raising fuel. -/
theorem dropUVal_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {value : RVal} {out : Store} (hle : fuel ≤ larger)
    (hrun : dropUVal ctx fuel store value = .ok out) :
    dropUVal ctx larger store value = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.2.2.2.2.1 _ _ _ _ h) hle hrun

theorem dropUVal_error_mono {ctx : Ctx} {fuel larger : Nat}
    {store : Store} {value : RVal} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : dropUVal ctx fuel store value = .error error) :
    dropUVal ctx larger store value = .error error := by
  exact fuel_mono_of_succ
    (fun current h =>
      (errorMonoAt current error hne).2.2.2.2.2.2.1 _ _ _ h)
    hle hrun

theorem dropManyU_mono {ctx : Ctx} {fuel larger : Nat} {store : Store}
    {values : List RVal} {out : Store} (hle : fuel ≤ larger)
    (hrun : dropManyU ctx fuel store values = .ok out) :
    dropManyU ctx larger store values = .ok out := by
  exact fuel_mono_of_succ
    (fun current h => (monoAt current).2.2.2.2.2.2.2 _ _ _ _ h) hle hrun

theorem dropManyU_error_mono {ctx : Ctx} {fuel larger : Nat}
    {store : Store} {values : List RVal} {error : Err}
    (hle : fuel ≤ larger) (hne : error ≠ .fuel)
    (hrun : dropManyU ctx fuel store values = .error error) :
    dropManyU ctx larger store values = .error error := by
  exact fuel_mono_of_succ
    (fun current h =>
      (errorMonoAt current error hne).2.2.2.2.2.2.2 _ _ _ h)
    hle hrun

/-- Top-level specialization of `runCode_mono`. -/
theorem runMain_mono {ctx : Ctx} {code : Code} {fuel larger : Nat}
    {out : Store × RVal} (hle : fuel ≤ larger)
    (hrun : runMain ctx code fuel = .ok out) :
    runMain ctx code larger = .ok out :=
  runCode_mono hle hrun

/-- Top-level specialization of `runCode_error_mono`. -/
theorem runMain_error_mono {ctx : Ctx} {code : Code}
    {fuel larger : Nat} {error : Err} (hle : fuel ≤ larger)
    (hne : error ≠ .fuel)
    (hrun : runMain ctx code fuel = .error error) :
    runMain ctx code larger = .error error :=
  runCode_error_mono hle hne hrun

/-- Reached ordinary stuckness persists when evaluator fuel is raised. -/
theorem runMain_stuck_mono {ctx : Ctx} {code : Code}
    {fuel larger : Nat} {message : String} (hle : fuel ≤ larger)
    (hrun : runMain ctx code fuel = .error (.stuck message)) :
    runMain ctx code larger = .error (.stuck message) :=
  runMain_error_mono hle (by simp) hrun

/-- A reached closed-world lookup failure persists when fuel is raised. -/
theorem runMain_unknownRef_mono {ctx : Ctx} {code : Code}
    {fuel larger : Nat} {address : Ixon.Address} (hle : fuel ≤ larger)
    (hrun : runMain ctx code fuel = .error (.unknownRef address)) :
    runMain ctx code larger = .error (.unknownRef address) :=
  runMain_error_mono hle (by simp) hrun

/-- Top-level specialization of `runCode_mem_mono`. -/
theorem runMain_mem_mono {ctx : Ctx} {code : Code}
    {fuel larger : Nat} {message : String} (hle : fuel ≤ larger)
    (hrun : runMain ctx code fuel = .error (.mem message)) :
    runMain ctx code larger = .error (.mem message) :=
  runCode_mem_mono hle hrun

end Ix.Compiler.IxIR1
