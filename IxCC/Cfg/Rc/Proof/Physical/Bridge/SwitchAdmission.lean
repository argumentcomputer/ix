import IxCC.Cfg.Rc.Proof.Physical.Bridge.CtorDispatch
import IxCC.Cfg.Rc.Proof.Native.Pipeline

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt IxCC.Rt.Proof
open IxCC.Cfg.Rc IxCC.Cfg.Rc.Native.Spec

/-- Read the actual source-block switch check from native admission. Runtime
helper function IDs changed by tablesOf do not affect constructor dispatch. -/
theorem admitted_switch_checks {P : Program} (pairs : List (Nat × Cfg.Fun))
    (accepted : Rt.checkSwitches P.base = .ok ())
    {f label x : Nat} {function : Cfg.Fun} {block : Cfg.Block}
    (functionLookup : P.base.fun? f = some function)
    (blockLookup : function.blocks[label]? = some block)
    {alts : List (Key.CtorKey × Cfg.Edge)} {default : Option Cfg.Edge}
    (terminator : block.term = .switch x alts default) :
    pinsApart (tablesOf P pairs).known = true ∧
      switchOk (tablesOf P pairs) alts default = true := by
  have checked := checkSwitches_ok accepted
  simp only [switchesOk, Bool.and_eq_true, List.all_eq_true] at checked
  have selected := checked.2 _ (Src.NatMap.mem_toList functionLookup)
    block (List.mem_of_getElem? blockLookup)
  simp only [blockSwitchOk, terminator] at selected
  have distinct : ∀ alternatives, testsDistinct (tablesOf P pairs) alternatives =
      testsDistinct (Rt.Lower.tables P.base) alternatives := by
    intro alternatives
    induction alternatives with
    | nil => rfl
    | cons head tail ih =>
      simp only [testsDistinct, ih]
      rfl
  refine ⟨checked.1, ?_⟩
  have natural : ∀ key, natAlt (tablesOf P pairs) key =
      natAlt (Rt.Lower.tables P.base) key := fun _ => rfl
  simpa only [switchOk, distinct, natural] using selected


end IxCC.Cfg.Rc.Proof.Physical.Bridge
