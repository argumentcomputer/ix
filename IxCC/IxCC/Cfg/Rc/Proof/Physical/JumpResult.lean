import IxCC.Cfg.Rc.Proof.Physical.JumpActivation
import IxCC.Cfg.Rc.Proof.Native.CodeRecursion

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native.Spec
open IxCC.Cfg.Rc.Proof.Physical.Bridge IxCC.Rt.Rc.Procs IxCC.Own.Rc

/-- Free jumps use the structural body continuation; charged jumps use only
the smaller-clock claim. Copy/drop and edge costs are taken from the actual
physical trace, including cleanup performed before a zero-clock timeout. -/
theorem jump_result {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkScopedProgram F bodies P = true)
    {config : Rt.Config} {pairs : List (Nat × Cfg.Fun)} (consuming : consumeAll P = .ok pairs)
    {main clock : Nat} (smaller : ∀ k, k < clock → PhysicalAtClock F P config pairs main k)
    {sourceJoins : List Fir.JEntry} {j : Fir.JoinId} {args : List Fir.Arg}
    (next : ∀ entry rest, Fir.lookupJ j sourceJoins = some (entry, rest) → entry.charged = false →
      PhysicalCode F P config pairs main clock (entry.after rest) entry.body) :
    PhysicalCode F P config pairs main clock sourceJoins (.jmp j args) := by
  intro H addresses external live sourceEnv ownedEnv roots joins ownedJoins sourceFunction
    function source target memory context base bump limit regionBytes slots lists callers
    imm sourceLookup before heap
  rw [Fir.eval_jmp]
  cases found : Fir.lookupJ j sourceJoins with
  | none => simp only [found, Sem.Result.ofOption, Sem.Result.bind]; trivial
  | some pair =>
    obtain ⟨entry, rest⟩ := pair
    simp only [found, Sem.Result.ofOption, Sem.Result.bind_ok]
    cases evaluated : Fir.evalArgs sourceEnv args with
    | none => simp only [evaluated, Sem.Result.ofOption, Sem.Result.bind]; trivial
    | some logical =>
      simp only [evaluated, Sem.Result.ofOption, Sem.Result.bind_ok]
      by_cases length : logical.length = entry.params.length
      · have argsLength : args.length = entry.params.length :=
          (Fir.evalArgs_length sourceEnv evaluated).symm.trans length
        have empty : holdRoots external [] = external := by funext location; simp [holdRoots, refsIn]
        have framed : Activation F P pairs (Public.Spec.sourceStage P (Public.Spec.rawSource config P pairs) main)
            H addresses (holdRoots external []) live sourceEnv ownedEnv roots joins sourceJoins ownedJoins
            (.jmp j args) sourceFunction.vars function source target imm := by simpa only [empty] using before
        have initial : HeapState P pairs H addresses memory external (roots ++ [])
            context base bump limit regionBytes slots lists := by simpa only [List.append_nil] using heap
        rcases jump_activation checked consuming (Public.Spec.rawSource config P pairs) main framed
            sourceLookup found argsLength initial callers with success | failure
        · obtain ⟨captured, older, ownedEntry, ownedRest, fields, actualLogical, kept, H', memory', slots', lists',
            after, final, cost, ownedLookup, capturedLookup, params, charged, ownedArgs, sourceArgs,
            activation, heapAfter, trace, costBound, size, sameFn, heldPreserved, externalPreserved⟩ := success
          have equal : actualLogical = logical := Option.some.inj (sourceArgs.symm.trans evaluated)
          subst actualLogical
          simp only [empty, List.append_nil] at activation heapAfter
          have preserved : Own.Plain.ExternalPreserved H H' external := by
            intro root value externalRoot den
            change H'.value? root = some value
            rw [← externalPreserved root externalRoot]
            exact den
          have history : HeapHistory H.size addresses H'.size addresses :=
            ⟨by omega, fun _ _ => rfl⟩
          have lookupAfter : F.fun? after.fn = some sourceFunction := by simpa only [sameFn] using sourceLookup
          simp only [Fir.jumpTo, if_pos length]
          cases isCharged : entry.charged with
          | false =>
            simp only [isCharged, Bool.false_eq_true, ↓reduceIte]
            exact ResultAt.prefix trace preserved history (by omega)
              (next entry rest found isCharged _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ callers
                lookupAfter activation heapAfter)
          | true =>
            simp only [isCharged, ↓reduceIte]
            apply ResultAt.charge trace (by simpa only [isCharged, Bool.toNat_true] using costBound) preserved history
            intro k clockEq
            exact (smaller k (by omega)).code (entry.after rest) entry.body
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ callers lookupAfter activation heapAfter
        · exact ResultAt.of_fails failure
      · simp only [Fir.jumpTo, if_neg length]
        trivial


end IxCC.Cfg.Rc.Native.Spec
