import Compilatrix.Cfg.Rc.Proof.Physical.Bridge.Tokens
import Compilatrix.Rt.Rc.Proof.IncrementCases

/-! Copying a live variable adds a carried argument token, not another
lexical binding. The live variable list stays distinct. Physical count room
is decided from the represented header bound, not assumed at the interface. -/
set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Proof.Physical.Bridge
open Compilatrix Compilatrix.Own Compilatrix.Own.Rc
open Compilatrix.Rt.Rc.Procs

theorem increment_tokens {H : Heap} {external : Nat → Nat} {held carry roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var} {value : RVal}
    (before : Tokens H external (carry ++ held) live ρf ρo roots)
    (member : x ∈ live) (lookup : ρo.get? x = some value) :
    ∃ H', Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external ((value :: carry) ++ held) live ρf ρo roots ∧
      ∀ root, H.value? root = H'.value? root := by
  obtain ⟨H', action, balance, values⟩ := Own.Plain.evalAction_inc_owned lookup before.balance
    (before.exactRoots.member member lookup)
  refine ⟨H', action, ⟨before.den.transport before.exactRoots (fun root _ => values root),
    before.exactRoots, ?_, before.distinct⟩, values⟩
  intro location
  have counted := balance location
  simp only [Balance, holdRoots, refsIn_append, refsIn, List.cons_append] at counted ⊢
  omega

theorem increment_entry_tokens
    {H : Heap} {external : Nat → Nat} {held carry roots : List RVal}
    {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env} {x : Fir.Var} {value : RVal}
    (before : Tokens H external (carry ++ held) live ρf ρo roots)
    (member : x ∈ live) (lookup : ρo.get? x = some value)
    {addresses : AddressMap} {mem : X86.Memory} {context base bump limit : Lir.Word}
    {slots : List Slot} {lists : Nat → List Lir.Word}
    (idle : ReleaseInvariant H addresses mem (holdRoots external (roots ++ carry ++ held)) none []
      context base bump limit slots lists)
    {word : Lir.Word} (represented : valueWord addresses value = some word) :
    ∃ H', Own.Plain.evalAction ρo H (.inc x 1) = .ok H' ∧
      Tokens H' external ((value :: carry) ++ held) live ρf ρo roots ∧
      (∀ root, H.value? root = H'.value? root) ∧
      ((∃ mem', ReleaseInvariant H' addresses mem'
          (holdRoots external (roots ++ (value :: carry) ++ held)) none []
          context base bump limit slots lists ∧
          Lir.eval incProgram 0 [word] mem context = .ok ([], mem')) ∨
        Lir.eval incProgram 0 [word] mem context = .resource .heap) := by
  obtain ⟨H', action, tokens, values⟩ := increment_tokens before member lookup
  refine ⟨H', action, tokens, values, ?_⟩
  have rebase : (fun location => holdRoots external (roots ++ carry ++ held) location + refsIn location [value]) =
      holdRoots external (roots ++ (value :: carry) ++ held) := by
    funext location
    simp only [holdRoots, refsIn_append, refsIn, List.cons_append]
    omega
  by_cases isLocation : ∃ location, value = .loc location
  · obtain ⟨location, rfl⟩ := isLocation
    obtain ⟨refs, body, cell, _⟩ := balance_pending_live before.balance
      (before.exactRoots.member member lookup)
    have placement : addresses location = some word := represented
    obtain ⟨_, address, mapped, physical⟩ := idle.live.cell location refs .dyn body cell
    by_cases room : refs < Rt.Rc.maxCount
    · obtain ⟨incremented, restored, result⟩ := increment_entry_complete idle cell placement room
      have actionPhysical : Own.Plain.evalAction ρo H (.inc x 1) =
          .ok (setCell H location (.live (refs+1) .dyn body)) := by
        simp [Own.Plain.evalAction, lookup, incremented, Sem.Result.ofOption]
      have equal := Sem.Result.ok.inj (actionPhysical.symm.trans action)
      rw [equal, rebase] at restored
      exact .inl ⟨_, restored, result⟩
    · have maxed : refs = Rt.Rc.maxCount := by have bounded := physical.bounded; omega
      subst refs
      exact .inr (increment_max_failure idle cell placement)
  · have immediate : ∀ location, value ≠ .loc location := fun location equal =>
      isLocation ⟨location, equal⟩
    obtain ⟨incremented, restored, result⟩ := increment_immediate_entry idle immediate word represented
    have actionPhysical : Own.Plain.evalAction ρo H (.inc x 1) = .ok H := by
      simp [Own.Plain.evalAction, lookup, incremented, Sem.Result.ofOption]
    have equal := Sem.Result.ok.inj (actionPhysical.symm.trans action)
    rw [equal, rebase] at restored
    exact .inl ⟨mem, restored, result⟩



end Compilatrix.Cfg.Rc.Proof.Physical.Bridge
