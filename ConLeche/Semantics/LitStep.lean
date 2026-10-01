module

public import ConLeche.Semantics.Canon

@[expose] public section

/-!
# `CheckStep2`, the literal clauses — Tier B (the transposition batch)

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161:
`natLit_factsAV` is the module's only theorem, it mentions no `EnvS`,
no fuel and no mode — a pure `interp`/`WellDenoted` statement about a
`natLitAV` spine, as the note below already observes — and both lanes'
numeral clauses consume it.  Path and module name changed; the Lean
namespace, the statement and the proof are verbatim.)*

`Sound/Lit.lean`'s numeral facts onto `piR`/`WellDenoted`/`interp` and
`denoteAnnot`'s own numeral spine (`natLitAV`, from `Interp/BasisType.lean`
— the same former `denoteAnnot`'s `.lit natVal` clause emits).

**This is transposition, not new argument**, which is what
`interp_closed` (seal 2 of step 3) bought: the block touches the
interpretation through `interp_app`, `interp_bvar`, `interp_sort`,
`interp_pi` and `interp_closed`, and all five now have `interp`
analogues.

The numeral induction is stated over the two head facts as **explicit
arguments** rather than re-deriving them from the environment.  That is
deliberate: the head facts are a `mem_type2` chain over the stored
`Nat`/`Nat.zero`/`Nat.succ` shapes — the *same* chain for every numeral
— and factoring them out keeps the induction free of the literal
guards' inversion plumbing, exactly as v1 factors `natHeads_facts` out
of `natLit_facts`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The numeral facts.**  Every `denoteAnnot` numeral is truthful and
inhabits the stored `Nat`'s interpretation — by induction on the
numeral, from the zero's membership and the successor's `piR`
membership.

`Nat → Nat` sits at result sort `1`, so the successor's product is in
the **graph regime** and `app_mem_piR_pos` applies with no fibre
premise; the app slot's kind-`0` component is vacuous for the same
reason.  v1 needed `app_mem_piC` plus the collapse's side conditions
here. -/
theorem natLit_factsAV {ρ : Nat → V} {za sa natA : AnnotTerm}
    (hokz : WellDenoted V ρ za) (hoks : WellDenoted V ρ sa)
    (hz : interp V ρ za ∈ˢ interp V ρ natA)
    (hsucc : interp V ρ sa
      ∈ˢ piR 1 (interp V ρ natA) fun _ => interp V ρ natA) :
    ∀ n : Nat,
      WellDenoted V ρ (natLitAV za sa n) ∧
        interp V ρ (natLitAV za sa n) ∈ˢ interp V ρ natA := by
  intro n
  induction n with
  | zero => exact ⟨hokz, hz⟩
  | succ n ih =>
    obtain ⟨ihA, ihm⟩ := ih
    refine ⟨?_, ?_⟩
    · show WellDenoted V ρ (.app sa (natLitAV za sa n))
      rw [WellDenoted_app]
      exact ⟨hoks, ihA, 1, _, _, hsucc, ihm,
        fun h => absurd h Nat.one_ne_zero⟩
    · show interp V ρ (.app sa (natLitAV za sa n)) ∈ˢ _
      rw [interp_app]
      exact app_mem_piR_pos Nat.one_ne_zero hsucc ihm

/-! ## Re-pointed to `Claims2A` (seal 6)

**`natLit_factsAV` needed no repair, and that is a fact about the
amendment rather than about this file.**  All four repairs are about
*fuel*: R1 and R3 move the annotation's fuel, R2 grades a reduction, R4
restricts the modes.  `natLit_factsAV` mentions no fuel, no `denoteAnnot`
and no mode — it is a pure `interp`/`WellDenoted` statement about a
`natLitAV` spine — so it is amendment-neutral by construction.

*Rule: a lemma stated in the interpretation alone survives every
repair to the claim family, because every defect this campaign found
lives in the indexing between the run and the annotation.  The literal
blocks were transposed to `interp` early, and that is why they cost
nothing here.*

What did have to be re-pointed is the **clause** built on top, below.
-/

open ConLeche (CheckMode Env Expr Name inferTypeCore inferBody
  natLitSupported)

variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The `Nat`-literal clause lives in `InferQ.lean`

A version of `infer_natLit_claim2A` was written here in parallel with
the inference quarter's, with the same conclusion but four explicit
membership premises where theirs bundles one routed `NatHeads2`.
Theirs is strictly stronger — it derives the returned type's
annotation from the support guard instead of taking it as a
hypothesis — and it is the one the quarter's assembly calls, so this
copy is deleted rather than renamed.

Third instance of the same integration finding: parallel quarters
converge on the same helper *names* as well as the same content, and
the collision surfaces at the fold rather than at authoring.

## Generation four costs this file nothing

`Claims2C` hoists every `WellDenoted` above the `∀ ρ` and makes
`InferClaims2C` deliver the *returned type's* grading too.
`natLit_factsAV` states both of its conclusions at a single, arbitrary
`ρ` with no `Sat` in sight, so hoisting it is `fun ρ hρ => …` and the
statement does not move — the same reason seal 6's four repairs passed
through it.  The returned type is `.const Nat []`, whose grading is
`annotOk2_of_denote2_const` (`Steps/Dispatch.lean`) from
`EnvModel.acval_wellDenoted`, so the new conjunct is free at the numeral clause as
well; the clause itself lives in `Steps/InferQ.lean` and is the
inference quarter's to re-point. -/


end ConLeche.Semantics
