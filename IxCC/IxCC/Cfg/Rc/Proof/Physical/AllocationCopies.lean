import IxCC.Cfg.Rc.Proof.Physical.AllocationTokens

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Own IxCC.Own.Rc IxCC.Cfg.Rc.Proof.Physical.Bridge

/-- The real canonical constructor-copy prefix produces exactly one carried
token per argument occurrence. Repeated variables remain repeated fields;
immediates participate in the argument list without changing heap counts. -/
theorem allocation_copy_tokens
    {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held live ρf ρo roots)
    (args : List Fir.Arg) (scope : args.all (Own.Plain.argIn live) = true) :
    ∃ fields sourceValues copied,
      Own.evalArgs ρo args = some fields ∧
      Fir.evalArgs ρf args = some sourceValues ∧
      Own.Plain.evalActions ρo H (Own.Plain.copies args) = .ok copied ∧
      Tokens copied external (fields ++ held) live ρf ρo roots ∧
      (∀ root, H.value? root = copied.value? root) := by
  obtain ⟨fields, sourceValues, arguments, sourceArgs, _⟩ :=
    Own.Plain.args_den before.den args scope
  obtain ⟨copied, actions, balance, preserved⟩ :=
    Own.Plain.copies_sound ρo H args before.balance
      (Own.Plain.argsOwned_of_scope before.den before.exactRoots scope) arguments
  refine ⟨fields, sourceValues, copied, arguments, sourceArgs, actions,
    ⟨before.den.transport before.exactRoots (fun root _ => preserved root),
      before.exactRoots, ?_, before.distinct⟩, preserved⟩
  intro location
  have counted := balance location
  simp only [holdRoots, refsIn_append] at counted ⊢
  omega


end IxCC.Cfg.Rc.Native
