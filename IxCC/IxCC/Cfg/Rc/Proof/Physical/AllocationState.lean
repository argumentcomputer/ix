import IxCC.Cfg.Rc.Proof.Physical.AllocationCopies
import IxCC.Own.Plain.Proof.ValidRoots

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Own IxCC.Own.Rc IxCC.Cfg.Rc.Proof.Physical.Bridge

/-- Restore the complete canonical State at the exact copied/published heap,
including saved join denotations, lexical capture views and scope. The actual
copy-prefix result identifies the intermediate heap; it is not a simulation
premise. Physical increment traces independently establish or fail that prefix. -/
theorem allocation_state_after
    {functions : Own.Plain.Signatures} {H copied : Heap} {external : Nat → Nat}
    {fields held roots : List RVal} {live : List Fir.Var} {imm : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    {joins : Own.Plain.Joins} {Jf : List Fir.JEntry} {Jo : List Own.Plain.JEntry}
    (before : Own.Plain.State functions H (holdRoots external held) live ρf ρo roots joins Jf Jo imm)
    (tables : Own.Tables) (ctor : Fir.CtorInfo) (args : List Fir.Arg) (x : Fir.Var)
    (fresh : x ∉ live) (scope : args.all (Own.Plain.argIn live) = true)
    (arguments : Own.evalArgs ρo args = some fields) (arity : fields.length = ctor.arity)
    (positive : 0 < ctor.arity)
    (copies : Own.Plain.evalActions ρo H (Own.Plain.copies (Own.Plain.heapArgs imm args)) = .ok copied) :
    ∃ sourceValues, Fir.evalArgs ρf args = some sourceValues ∧
      let allocated := copied.alloc .rc {ctor, fields}
      Own.Plain.evalRhs tables ρo copied (.ctor ctor args) = .ok allocated ∧
      Own.Plain.State functions allocated.2 (holdRoots external held) (live ++ [x])
        (ρf.insert x (.ctor ctor sourceValues)) (ρo.insert x allocated.1)
        (roots ++ [allocated.1]) joins Jf Jo imm ∧
      (∀ value logical, Own.Proof.Den H value logical → Own.Proof.Den allocated.2 value logical) := by
  obtain ⟨actualFields, _, actualHeap, fieldArgs, _, copyEffect, copiedTokens, preserved⟩ :=
    allocation_copy_tokens (Tokens.ofState before) args scope before.immOk
  have sameFields : actualFields = fields := Option.some.inj (fieldArgs.symm.trans arguments)
  subst actualFields
  have sameHeap : actualHeap = copied := Sem.Result.ok.inj (copyEffect.symm.trans copies)
  subst actualHeap
  obtain ⟨sourceValues, sourceArgs, effect, afterTokens, preservesDen⟩ :=
    allocation_tokens copiedTokens tables ctor args x fresh scope arguments arity positive
  have oldDen : ∀ value logical, Own.Proof.Den H value logical →
      Own.Proof.Den (copied.alloc .rc {ctor, fields}).2 value logical := by
    intro value logical den
    apply preservesDen value logical
    change copied.value? value = some logical
    rw [← preserved value]
    exact den
  have resultDen : Own.Proof.Den (copied.alloc .rc {ctor, fields}).2
      (copied.alloc .rc {ctor, fields}).1 (.ctor ctor sourceValues) := by
    obtain ⟨value, logical, ownLookup, sourceLookup, den⟩ := afterTokens.den x (by simp)
    rw [Src.NatMap.get?_insert_self] at ownLookup sourceLookup
    cases ownLookup
    cases sourceLookup
    exact den
  exact ⟨sourceValues, sourceArgs, effect,
    before.bind_den x fresh resultDen afterTokens.balance oldDen, oldDen⟩


end IxCC.Cfg.Rc.Native
