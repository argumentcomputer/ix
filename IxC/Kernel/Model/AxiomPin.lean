module

import IxC.Kernel.Semantics.DeclRun
public import IxC.Kernel.Model.AxiomMem

public section

/-!
# The pin tier, at the validated-annotation currency (task #161,
ENDGAME A part 2)

`DeclAxiomR`'s branches at the P invariant: the tolerated skip and the two
standard axioms.

## What a branch owes

`harvestAxiom` (`Interp/HarvestP.lean`) is the wrapper: the *type*
side is harvested from `ConstantValR`'s own run (`accepted_reads` is a
theorem since part 1, so nothing is routed), and what the branch must
supply is the leaf `A` with

* `hAerase`/`hAclosed`/`hAparams` — syntactic, from the branch key and
  the `EnvModel` fields;
* `hAok`/`hAvalid` — free at a `BConst` or `acval` leaf (`WellDenoted`'s
  and `AnnotValid`'s `.const`/`.prf` clauses are `True`, and an
  `acval` leaf carries both as invariant fields);
* `hmemA` — **the semantic content**: `interp` of the leaf inhabits
  `interp` of the *stored* type's `denoteMeta` reading.

## THE WALL, named: the stored type's reading is not the pin's

`hmemA` speaks about the reading of `type'`, the *stored* annotated
type.  Every branch key knows the type only through `matchesPin`,
which compares `erasePw` — so the pin fixes the stored
type **up to binder names and binder `pw` data**.

At v1 that costs nothing: `denote` reads neither, so
`denote_matchesPin` (`Verify/Denote/Inst.lean:422`) turns a pin hit
into an equality of denotations and every consumer computes on the
pin.  **At the P currency the analogue is FALSE**, and not marginally:
`denoteMeta`'s binder clauses read `pwBit φ mb.pw`, and `erasePw`
normalizes every datum to `.never`, whose bit is `1`.  So
`denoteMeta (e.erasePw) = denoteMeta e` fails at the very first Prop-codomain
binder, and with it any `denoteP_erasePw`/`denoteP_pinEq`/
`denoteP_matchesPin` chain stated the v1 way.  This is the erasePw
RULING's own point 2, met: the P tier must take the bits from the
front door's recorded run, never from the match verdict.

Concretely, what each remaining branch needs is:

> **`pwBitsAgree`**: at `μ.verifiedChecks`, for each binder of the stored
> type, `pwBit φ` of the stored datum equals `pwBit φ` of the pin's
> generated datum.

and the route is fixed by the ruling: `ConstantValR`'s run conjunct
(H1) gives `inferTypeCore μ env F 0 type' = .ok stype`; inverting it
through `inferTypeCore_forall_inv` once per binder yields the
validation conjunct `Level.zeronessOf v = mb.pw`, hence
(`pwBit_zeronessOf`) `pwBit φ mb.pw = 0 ↔ Level.eval φ v = 0`;
the pin's datum is that same zero-ness *by construction*, so the two
bits agree **once `Level.eval φ v` is known**.

And that last step is the content that is not yet in the tree: `v` is
`ensureSort` of the inferred type of the *opened body*, so knowing it
means executing the checker's inference symbolically along the pinned
telescope (for `propext`: that `a = b` infers to `Prop`, from the
stored `Eq`'s own pinned type).  The telescope collapse makes it one
fact per pin rather than one per binder — `imax x y = 0 ↔ y = 0`, so
every binder of a chain carries the innermost codomain's bit — but it
is one genuine symbolic-inference lemma per pinned family.

That lemma is `AxiomBitsP`'s, and the two standard axioms' memberships
are `AxiomMemP`'s, so `axiomStd` below closes the branch that record
named.  Read the ENDGAME C seal for what the memberships actually cost:
the *companions'* bits are not reachable by any bit lemma, and two of
the three obstructions that follow from that were removed
(`pi_sort_bit_ne_zero`, the vacuous minor) rather than assumed.

## What lands here

* **the tolerated skip** — `axiomSkip`: the environment does not
  move, so the P invariant is the one already held;
* **the two standard axioms** — `axiomStd`, both halves, on
  `AxiomBitsP`'s bits and `AxiomMemP`'s memberships.

Those are all of `DeclAxiomRun`'s branches: since `ALPHA-COLLAPSE.md` §8.2
the certified theory is Lean with its three standard axioms, and the
compiler-trust axioms (`Lean.trustCompiler`, `Lean.ofReduceNat`,
`Lean.ofReduceBool`), with the `ReduceOps` law their memberships needed,
are gone.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel

open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env md} {F : Nat}

/-! ## The tolerated skip -/

/-- **The tolerated-axiom skip.**  `DeclAxiomR`'s skip branch stores
nothing (`env₂ = env`), so there is no leaf, no extension and no
crossing: the P invariant at the successor environment *is* the one
held at the prefix. -/
theorem axiomSkip (mp : EnvModelM V μ env) :
    Nonempty (EnvModelM V μ env) := ⟨mp⟩

/-! ## The two standard axioms

`DeclAxiomR`'s first branch, both halves.  The bits come from
`AxiomBitsP` (the axiom's *own* recorded run) and the memberships from
`AxiomMemP`; the v1 extension is `extendAxiomS` at the **named**
witness, which `StdAxiomKey.lean`'s `propextKeyS_mem`/`choiceKeyS_mem`
now expose — the lesson (first met at the retired `Lean.trustCompiler`
branch) that the key's `∃` is
one currency too coarse for a P leaf, generalized. -/

/-- **The standard-axiom branch, discharged.**  The leaf is the layer's
own constant in both halves, so every syntactic obligation is `rfl` or
a `const` clause, and the whole content is the membership. -/
theorem axiomStd (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {cv : ConstantVal md} {type' : Expr md}
    (hcv : ConstantValRun μ F env cv type')
    (hok : Ix.Kernel.stdAxiomOk env ⟨cv.name, cv.levelParams, type'⟩
      = true) :
    Nonempty (EnvModelM V μ
      ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩) := by
  have hcv' := hcv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr,
    hrunT⟩ := hcv'
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hfresh : env.find? cv.name = none :=
    Option.isNone_iff_eq_none.mp hfind
  obtain ⟨stype, usort, hst, hens⟩ := hrunT
  have hwfc : Ix.Kernel.EnvWF ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ ::
      env.consts⟩ := by
    refine Ix.Kernel.EnvWF.cons mp.base2.wf
      ⟨htf', htp, Expr.constsResolve_mono htr, hbt', ?_, ?_, ?_, ?_⟩
    · intro cv2 value2 hint2 heq; exact nomatch heq
    · intro cv2 mI rP rules heq; exact nomatch heq
    · intro tbl heq; exact nomatch heq
    · intro cv2 caps heq; exact nomatch heq
  by_cases hn : cv.name = propextName
  · refine harvestAxiom (V := V) hμ mp hcv
      (A := fun _ => .const .propext []) (fun _ => trivial)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => by simp)
      (fun _ _ => by simp) ?_
    intro ψ ta hta ρ
    exact propext_mem hμ mp hok hn hst ψ ta hta ρ
  · by_cases hn2 : cv.name = choiceName
    · -- the pin fixes the axiom's one level parameter, so both the v1
      -- witness and the P leaf read only `ψ uN`
      have huN : ∀ ψ₁ ψ₂ : LevelParam → Nat,
          (∀ p ∈ cv.levelParams, ψ₁ p = ψ₂ p) → ψ₁ uN = ψ₂ uN := by
        intro ψ₁ ψ₂ hp
        obtain ⟨-, -, -, hApin⟩ := nonempty_shapes hok hn2
        have hlpA : cv.levelParams = choiceA.levelParams :=
          (matchesPin_invT hApin).2
        refine hp uN ?_
        rw [hlpA, show choiceA.levelParams = [uN] from rfl]
        exact List.Mem.head _
      refine harvestAxiom (V := V) hμ mp hcv
        (A := fun ψ => .const .choice [ψ uN])
        (fun _ => trivial)
        (fun _ _ => rfl)
        (fun ψ₁ ψ₂ hp => by
          show AnnotTerm.const .choice [ψ₁ uN] = AnnotTerm.const .choice [ψ₂ uN]
          rw [huN ψ₁ ψ₂ hp])
        (fun _ _ => by simp) (fun _ _ => by simp) ?_
      intro ψ ta hta ρ
      exact choice_mem hμ mp hok hn2 hst ψ ta hta ρ
    · exfalso
      unfold Ix.Kernel.stdAxiomOk at hok
      rw [show (⟨cv.name, cv.levelParams, type'⟩ : ConstantVal md).name
        = cv.name from rfl] at hok
      rw [if_neg hn, if_neg hn2] at hok
      exact nomatch hok

end Ix.Kernel.Model
