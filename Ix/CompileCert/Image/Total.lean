import Ix.CompileCert.Image.Dom

/-!
# M7 L2a-syn: totality of the image construction on `Dom` (L2a-1)

Nothing below assumes the block non-nested: `Dom` is the construction's own checks, whatever the block.

* `imageOfP_total` (**L2a-1**): on `Dom`, the image construction at the table-free core with its
  constant fuel `defaultFuel = 2^16` succeeds: the core returns the checking development's result
  on every call (`devRefines_dom`), so it returns the checking construction's image
  (`imageOfW_of_refines`);
* `imageOf_total_of`: the same for the executable, given that the tabled development agrees with
  the core where the core succeeds (X1's R-1);
* `blockView_expansion_total`: in the compiler, every auxiliary of a changed block gets its
  expansion (its image on `Dom`, Lean's value for a definition or theorem) or a decline naming it.

These assume nothing beyond `Dom` and, for the executable, that agreement.
-/

namespace Ix.CompileCert.Img

open Ix (Name Level Expr ConstantInfo InductiveVal RecursorVal)
open Ix.Compile.Image (GenM GenState freshName Local telescope LCtx Elim LeanMinor ImageSpec
  GenOptions Image)
open Ix.CompileCert.Conv

/-- **L2a-1: totality on `Dom`.** For a Lean recursor `r` in `Dom` (the construction's analyses
succeed and every development it makes is in the fuel classes), the image construction at X1's
core development, with its constant fuel `2^16`, succeeds. -/
theorem imageOfP_total {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec}
    {r : Name} (hdom : Dom opts const? spec r) :
    ∃ img, imageOfP opts const? spec r = .ok img := by
  unfold Dom at hdom
  cases h : imageOfW domDev opts const? spec r with
  | error e => rw [h] at hdom; cases hdom
  | ok img => exact ⟨img, imageOfW_of_refines devRefines_dom h⟩

/-- **L2a-1 for the executable**, given X1's refactor R-1 in the direction it needs: the tabled
development returns the core's result wherever the core succeeds. -/
theorem imageOf_total_of
    (hR1s : ∀ xs vs e r, substFVarsP xs vs e = .ok r → Ix.Compile.Image.substFVars xs vs e = .ok r)
    (hR1i : ∀ f args r, instantiateP f args = .ok r → Ix.Compile.Image.instantiate f args = .ok r)
    {opts : GenOptions} {const? : Name → Option ConstantInfo} {spec : ImageSpec} {r : Name}
    (hdom : Dom opts const? spec r) :
    ∃ img, Ix.Compile.Image.imageOf opts const? spec r = .ok img := by
  rw [imageOf_eq]
  unfold Dom at hdom
  cases h : imageOfW domDev opts const? spec r with
  | error e => rw [h] at hdom; cases hdom
  | ok img => exact ⟨img, imageOfW_of_refines (devRefines_dom.trans (D3 := execDev) ⟨hR1s, hR1i⟩) h⟩

/-- **Totality in the compiler** (Pass 3's view of a changed block, `BlockView.expansion`): every
auxiliary `a` gets its expansion — its image when it is a Lean recursor in `Dom`, Lean's value when
it is a definition or a theorem — or a decline naming it, when it is neither. Given R-1 as in
`imageOf_total_of`. -/
theorem blockView_expansion_total
    (hR1s : ∀ xs vs e r, substFVarsP xs vs e = .ok r → Ix.Compile.Image.substFVars xs vs e = .ok r)
    (hR1i : ∀ f args r, instantiateP f args = .ok r → Ix.Compile.Image.instantiate f args = .ok r)
    (inp : Ix.Compile.Pass.ViewInput) (v : Ix.Compile.Pass.BlockView) (a : Name)
    (hdom : ∀ rv, inp.const? a = some (.recInfo rv) → Dom {} (v.const? inp) v.spec a) :
    (∃ x, v.expansion inp a = .ok x) ∨
      v.expansion inp a = .error s!"Pass 3: {a.pretty} has no image (not a recursor or definition)" := by
  unfold Ix.Compile.Pass.BlockView.expansion
  split
  · rename_i rv hrv
    obtain ⟨img, himg⟩ := imageOf_total_of hR1s hR1i (hdom rv hrv)
    left
    unfold Ix.Compile.Pass.BlockView.image
    rw [himg]
    exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · left; exact ⟨_, rfl⟩
  · right; rfl

end Ix.CompileCert.Img
