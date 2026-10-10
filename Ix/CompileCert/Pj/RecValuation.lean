import Ix.CompileCert.Pj.RecRead

/-! Consecutive argument segments under the actual caller valuation, using
the public telescope valuation laws. -/

namespace Ix.CompileCert.Pj

open Ix.CompileCert (pushArguments DenotesSpine)

universe u

variable {V : Type u} [Kernel.SetTheory V]
  {cval : Kernel.Name → (Kernel.Name → Nat) → V}
  {env : Kernel.Env} {φ : Kernel.Name → Nat}

theorem bvarsAt_zero (count : Nat) :
    bvarsAt count 0 = Ix.CompileCert.argumentVariables count := by
  simp only [bvarsAt, Ix.CompileCert.argumentVariables, Nat.zero_add]

/-- Later binders shift the selected argument segment but do not change
its values or reverse its outermost-first order. -/
theorem denotesSpine_bvarsAt (ρ : Nat → V) (arguments later : List V) :
    DenotesSpine cval env φ (pushArguments ρ (arguments ++ later))
      (bvarsAt arguments.length later.length) arguments := by
  apply DenotesSpine.of_get (by simp [bvarsAt])
  intro index inside
  have bound : index < arguments.length := by simpa [bvarsAt] using inside
  simp only [bvarsAt, List.getElem_map, List.getElem_range]
  have position : later.length + arguments.length - 1 - index =
      later.length + (arguments.length - 1 - index) := by omega
  have value : pushArguments ρ (arguments ++ later)
      (later.length + arguments.length - 1 - index) = arguments[index] := by
    rw [Ix.CompileCert.pushArguments_append, position,
      Ix.CompileCert.pushArguments_above,
      Ix.CompileCert.pushArguments_get arguments ρ index bound]
  rw [← value]
  exact .bvar

/-- The same reading with an explicit earlier parameter segment. -/
theorem denotesSpine_bvarsAt_middle (ρ : Nat → V)
    (earlier arguments later : List V) :
    DenotesSpine cval env φ (pushArguments ρ (earlier ++ arguments ++ later))
      (bvarsAt arguments.length later.length) arguments := by
  simpa only [List.append_assoc, Ix.CompileCert.pushArguments_append] using
    (denotesSpine_bvarsAt (cval := cval) (env := env) (φ := φ)
      (pushArguments ρ earlier) arguments later)

end Ix.CompileCert.Pj
