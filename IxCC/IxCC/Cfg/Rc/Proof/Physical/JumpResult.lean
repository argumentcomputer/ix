import IxCC.Cfg.Rc.Proof.Native.CodeRecursion
import IxCC.Cfg.Rc.Proof.Physical.JumpEntry
import IxCC.Cfg.Rc.Proof.Physical.Admission
import IxCC.Cfg.Rc.Proof.Native.HeapHistory
import IxCC.Own.Plain.Proof.Owned.Joins
import IxCC.Fir.Proof.Unfold

/-! A jump over the typing context: the captured-token step. No action prefix and no heap change:
the checker took the arguments' tokens and one token of each variable the target captures, and
found none left (`closed`), so the join body's tokens count exactly what the jumping path held
(`jump_body_refs`); the native edge moves the arguments into the join block's parameters
(`jump_entry`). -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Native IxCC.Rt.Rc
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own IxCC.Own.Rc
open IxCC.Own.Plain (Ctx JCtx checkCode)

section
variable {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
  {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} {functions : List Lir.Func}
  {main clock : Nat} {sourceJoins : List Fir.JEntry}

/-- **A jump**: the body is any Own code that erases to the source entry's (the one the checker
typed at the declaration). -/
theorem jump_result (admission : CodeAdmission F bodies P config pairs functions)
    (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k)
    {j : Fir.JoinId} {args : List Fir.Arg}
    (next : ∀ entry rest, Fir.lookupJ j sourceJoins = some (entry, rest) → entry.charged = false →
      ∀ body : Own.Plain.Code, Own.Plain.eraseCode body = entry.body →
        PhysicalCode F P config pairs main clock (entry.after rest) body) :
    PhysicalCode F P config pairs main clock sourceJoins (.jmp j args) := by
  intro H addresses external live Γ Δ sourceEnv ownedEnv roots lex ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    sourceLookup before heap
  show ResultAt _ _ _ _ _ _ _ _ _ _ _ _ _ (Fir.eval F clock sourceEnv sourceJoins (.jmp j args))
  rw [Fir.eval_jmp]
  obtain ⟨captured, Γ₁, Γ₂, hΔ, h1, h2, h3⟩ := Own.Plain.checkCode_jmp before.typed
  cases found : Fir.lookupJ j sourceJoins with
  | none => simp only [Sem.Result.ofOption, Sem.Result.bind]; trivial
  | some pair =>
    obtain ⟨entry, rest⟩ := pair
    simp only [Sem.Result.ofOption, Sem.Result.bind_ok]
    obtain ⟨vs, ws, eo, resto, ownArgs, sourceArgs, lengths, ownedLookup, params, charged, body⟩ :=
      Own.Plain.jump_body_refs before.owned hΔ h1 h2 h3 found
    simp only [sourceArgs, Sem.Result.bind_ok]
    by_cases length : ws.length = entry.params.length
    · obtain ⟨Δb, Γb, lexd, lexb, owned', state, typed, erased, scope, refs⟩ := body length
      have sourceRange : source.fn < F.size := by
        obtain ⟨_, _, _, _, _, _, _, _, range, _⟩ := before.layout
        exact range
      have programSize : P.base.size = F.size :=
        generate_size (checkProgram_parts (checkScopedProgram_parts admission.scopedProgram).1).2
      have nativeRange : source.fn < P.base.size := by simpa only [programSize] using sourceRange
      have arity : vs.length = eo.params.length := by rw [params, lengths]; exact length
      have realParams : ∀ fd, P.base.fun? source.fn = some fd →
          ∀ (label : Nat) (block : Cfg.Block), fd.blocks[label]? = some block →
            ∀ x ∈ block.params.map Prod.fst, x < sourceFunction.vars :=
        fun fd fdLookup label block blockLookup =>
          checked_block_params admission.scopedProgram sourceRange sourceLookup fdLookup blockLookup
      rcases jump_entry admission.consuming before.layout ownedLookup ownArgs arity before.frame
          nativeRange realParams before.running memory context callers with entered | failure
      · obtain ⟨after, final, cost, afterLayout, afterFrame, trace, costBound, running, sameFn,
          fused⟩ := entered
        have activation : Activation F P pairs
            (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main) H addresses
            external (lexd ++ entry.params) Γb Δb (Fir.bindAll entry.env entry.params ws)
            (Own.bindAll eo.env eo.params vs) owned' lexb (entry.after rest) (eo.after resto)
            eo.body sourceFunction.vars function after final :=
          ⟨state, typed, afterLayout, afterFrame, by rw [erased]; exact scope, running, fused⟩
        have heap' : HeapState P pairs H addresses memory external owned' context base bump limit
            regionBytes slots lists :=
          ⟨by rw [← holdRoots_sameRefs refs]; exact heap.ready, heap.ordered, heap.compatible,
            heap.extent⟩
        have lookupAfter : F.fun? after.fn = some sourceFunction := by
          simpa only [sameFn] using sourceLookup
        have preserved : Own.Plain.ExternalPreserved H H external := fun _ _ _ h => h
        have history : HeapHistory H.size addresses H.size addresses :=
          ⟨Nat.le_refl _, fun _ _ => rfl⟩
        simp only [Fir.jumpTo, if_pos length]
        rw [← erased]
        cases isCharged : entry.charged with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ResultAt.prefix trace preserved history (by omega)
            (next entry rest found isCharged eo.body erased H addresses external
              (lexd ++ entry.params) Γb Δb _ _ owned' lexb _ sourceFunction function after final
              memory context base bump limit regionBytes slots lists callers lookupAfter activation
              heap')
        | true =>
          simp only [↓reduceIte]
          apply ResultAt.charge trace
            (by simpa only [charged, isCharged, Bool.toNat_true] using costBound) preserved history
          intro k clockEq
          exact smaller k (by omega) (entry.after rest) eo.body H addresses external
            (lexd ++ entry.params) Γb Δb _ _ owned' lexb _ sourceFunction function after final
            memory context base bump limit regionBytes slots lists callers lookupAfter activation
            heap'
      · exact ResultAt.of_fails failure
    · simp only [Fir.jumpTo, if_neg length]
      trivial

end

end IxCC.Cfg.Rc.Native.Spec
