import Compilatrix.Cfg.Rc.Proof.Physical.CopyPrefix

set_option autoImplicit false
namespace Compilatrix.Cfg.Rc.Native
open Compilatrix.Cfg.Rc.Proof.Physical.Bridge Compilatrix.Own Compilatrix.Own.Rc

/-- Temporarily hold a retained lexical root while traversing later drop
markers. This changes only token accounting, not environments or heap. -/
theorem Tokens.hold_head {H : Heap} {external : Nat → Nat} {held roots : List RVal}
    {x : Fir.Var} {live : List Fir.Var} {ρf : Fir.Env} {ρo : Own.Env}
    (before : Tokens H external held (x :: live) ρf ρo roots) :
    ∃ value remaining, ρo.get? x = some value ∧ roots = value :: remaining ∧
      Tokens H external (value :: held) live ρf ρo remaining := by
  obtain ⟨value, remaining, lookup, tailRoots, equal⟩ := Own.Plain.envRoots_cons before.exactRoots
  refine ⟨value, remaining, lookup, equal,
    ⟨fun y hy => before.den y (by simp [hy]), tailRoots, ?_, before.distinct.tail⟩⟩
  intro location
  have balance := before.balance location
  rw [equal] at balance
  simp only [holdRoots, refsIn] at balance ⊢
  omega

/-- Restore a held root to its original lexical binding after the suffix
retains its denotation. No new reference count is created by this operation. -/
theorem Tokens.restore_head {H : Heap} {external : Nat → Nat}
    {value : RVal} {held roots : List RVal} {x : Fir.Var} {live : List Fir.Var}
    {ρf : Fir.Env} {ρo : Own.Env} {logical : Fir.Val}
    (before : Tokens H external (value :: held) live ρf ρo roots)
    (own : ρo.get? x = some value) (source : ρf.get? x = some logical)
    (den : Own.Proof.Den H value logical) (fresh : x ∉ live) :
    Tokens H external held (x :: live) ρf ρo (value :: roots) := by
  refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨fresh, before.distinct⟩⟩
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨value, logical, own, source, den⟩
    · exact before.den y hy
  · change Own.evalArgs ρo ((x :: live).map Fir.Arg.var) = some (value :: roots)
    have tail : Own.evalArgs ρo (live.map Fir.Arg.var) = some roots := before.exactRoots
    simp [Own.evalArgs, Own.evalArg, own, tail]
  · intro location
    have balance := before.balance location
    simp only [holdRoots, refsIn] at balance ⊢
    omega



end Compilatrix.Cfg.Rc.Native
