module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.Univ
public import ConLeche.Semantics.BasisOk

@[expose] public section

/-!
# The second soundness's per-former skeleton (task #151, arc step 4)

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161: the
per-former rows are stated over `WellDenoted`/`interp`/`Sat` and nothing
else — that is the module's own design rule — so they carry no
environment, and BOTH lanes' inference quarters close their rows with
them.  Its `Annot/EnvModel` import was transitive cover (`Sat`, now
`SetBase/Sat`).  Path and module name changed; namespaces, statements
and proofs verbatim.)*


The case statements of the `interp` soundness, one per `AnnotTerm`
former, each stated over **exactly the facts the frozen Claims2
interface carries** and nothing else.  Hypothesis-first per the
`CheckStepR` precedent: a case that needs a fact the interface lacks is
a finding, not a hypothesis to invent.

## What a case is

The assembly architecture rules out re-signing the 44-case mutual
induction: the soundness is **per-step graded lemmas on `AnnotTerm`**,
composed along the bridge claims, with annotations following the run
rather than crossing a bare `Red`.  So each case here takes the
subterms' two facts — hereditary truthfulness (`WellDenoted`) and
membership — and produces the node's, in the shape the run-level claim
will thread.

Two conventions, both forced:

* **membership is stated at the annotated type**, never at a bare
  value, because the node's type is what the next case consumes;
* **the binder cases take their numeral's justification as a
  hypothesis**, not the numeral alone.  The numeral is in the term
  (`denoteAnnot` computes it); what a case needs is what the numeral is
  *worth* semantically, and that is the sort fact — supplier
  `HasSort.mem_univ` (`Annot/Kinding.lean`), which is where every
  binder row's `hcod`/`hdom` premise below comes from.

## The λ row's freedom, recorded where it is used

`sound_lam` has **no** empty-domain side condition, and needs no
validity metatheorem: `lamR_mem`'s premise is a `∀ x ∈ˢ ⟦A⟧`, which at
`⟦A⟧ = ∅` is vacuous, and so is the kind-`0` fibre condition.  The
numeral still matters — `lamR 0 ∅ F = pt` and `lamR 1 ∅ F = ∅` are
different values — but it comes from the *term*, and no semantic fact
about it is required to close the case.  This is why `ValidInfer`'s
refutation (`Annot/Validity.lean`) does not block the consumer lane.

## What the app row owes to the slot amendment

`sound_app` closes at **both** kinds, and `app_mem_of_slot` closes from
the invariant *alone*.  Before the app clause gained its kind-`0` fibre
component (the consumer seal) neither did: `app_mem_piR`'s `hB0` had no
supplier, and the truth-value route gives only that the fibre is
inhabited.  The amendment is what makes the app row a theorem rather
than a residue.

## The `const` row, closed

It was deferred at the first seal for a supplier reason, not a proof
reason: `BConst.type` yields a `Term` and `denoteAnnot` maps
`Expr → AnnotTerm`, so a built-in's *annotated* type could not be written
at all, and there was no `interp` analogue of `ConstOk.lean`'s
capstone.  Migration step 2 supplied both — `BConst.typeAV`
(`Interp/BasisType.lean`, with `typeAV_erase` for faithfulness) and
`bval_mem_type` (`Interp/BasisOk.lean`, all eighteen constants) — so
`sound_const` is now two facts wide and the skeleton covers **ten
formers of ten**.

Worth keeping: the row consumes *nothing* from the interface.  A
built-in is a closed leaf, so it needs no context, no valuation and no
hereditary premise — which is why it could be the last row written and
still cost one line.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable (V : Type w) [SetTheory V]

/-! ## The leaf rows -/

/-- **`sort`.**  Interface facts: none.  The universe tower's own
membership; the annotated type of `.sort u` is `.sort (u + 1)`. -/
theorem sound_sort (ρ : Nat → V) (u : Nat) :
    WellDenoted V ρ (.sort u) ∧
      interp V ρ (.sort u) ∈ˢ interp V ρ (.sort (u + 1)) := by
  refine ⟨by simp, ?_⟩
  rw [interp_sort, interp_sort]
  exact univ_mem_univ u

/-- **`bvar`.**  Interface fact: the annotated context's satisfaction
(`Sat`), which is the context currency the graded soundness threads. -/
theorem sound_bvar {Δa : List AnnotTerm} {ρ : Nat → V} {i : Nat}
    {Aa : AnnotTerm} (hΔ : Sat V Δa ρ) (hi : Δa[i]? = some Aa) :
    WellDenoted V ρ (.bvar i) ∧
      ρ i ∈ˢ interp V (fun j => ρ (j + i + 1)) Aa := by
  exact ⟨by simp, hΔ i Aa hi⟩

/-! ## The binder rows -/

/-- **`pi`.**  Interface facts: the domain's membership at its own
numeral `u`, the codomain's at `v` under the binder, and the two
hereditary halves.  The formation law is the `imax` rule *exactly*
(`piR_mem_univ`), so the annotated type is `.sort (ConLeche.Term.imax u v)`
on the nose — no "may land lower" slack. -/
theorem sound_pi {u v : Nat} {ρ : Nat → V} {Aa Ba : AnnotTerm}
    (hokA : WellDenoted V ρ Aa)
    (hokB : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) Ba)
    (hA : interp V ρ Aa ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univ v : V)) :
    WellDenoted V ρ (.pi u v Aa Ba) ∧
      interp V ρ (.pi u v Aa Ba)
        ∈ˢ interp V ρ (.sort (ConLeche.Term.imax u v)) := by
  refine ⟨by rw [WellDenoted_pi]; exact ⟨hokA, hokB⟩, ?_⟩
  rw [interp_pi, interp_sort]
  exact piR_mem_univ hA hB

/-- **`lam`.**  Interface facts: the body's membership in the codomain
under the binder, the codomain's kind-`0` fibre condition (the
numeral's worth, from `HasSort.mem_univ`), and the two hereditary
halves.  **No empty-domain side condition** — see the module
docstring.  The `Π`'s domain numeral `u` is free: `interp`'s `pi`
clause discards it (only the codomain sort dispatches), so the row
holds at every annotation of the domain. -/
theorem sound_lam {u v : Nat} {ρ : Nat → V} {Aa ba Ba : AnnotTerm}
    (hokA : WellDenoted V ρ Aa)
    (hokb : ∀ x, x ∈ˢ interp V ρ Aa → WellDenoted V (cons x ρ) ba)
    (hb : ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) ba ∈ˢ interp V (cons x ρ) Ba)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.lam v Aa ba) ∧
      interp V ρ (.lam v Aa ba)
        ∈ˢ interp V ρ (.pi u v Aa Ba) := by
  refine ⟨?_, ?_⟩
  · rw [WellDenoted_lam]
    exact ⟨hokA, hokb, fun x => interp V (cons x ρ) Ba, hb, hcod⟩
  · rw [interp_lam, interp_pi]
    exact lamR_mem hb

/-! ## The application row -/

/-- **`app`.**  Interface facts: the function's membership at an
*annotated* `Π`, the argument's in its domain, and the `Π`'s kind-`0`
fibre condition.  Closes at **both** kinds — the kind-`0` premise is
exactly `app_mem_piR`'s, and its supplier is the `Π`'s own numeral. -/
theorem sound_app {u v : Nat} {ρ : Nat → V} {fa aa Aa Ba : AnnotTerm}
    (hokf : WellDenoted V ρ fa) (hoka : WellDenoted V ρ aa)
    (hf : interp V ρ fa ∈ˢ interp V ρ (.pi u v Aa Ba))
    (ha : interp V ρ aa ∈ˢ interp V ρ Aa)
    (hcod : v = 0 → ∀ x, x ∈ˢ interp V ρ Aa →
      interp V (cons x ρ) Ba ∈ˢ (univZero : V)) :
    WellDenoted V ρ (.app fa aa) ∧
      interp V ρ (.app fa aa) ∈ˢ interp V ρ (Ba.inst aa) := by
  refine ⟨WellDenoted_app_of V hokf hoka hf ha hcod, ?_⟩
  rw [interp_pi] at hf
  rw [interp_app, interp_inst0]
  exact app_mem_piR hf ha hcod

/-- **The amendment's payoff, isolated**: the application's membership
follows from the *invariant alone*, at every kind.  Before the app
clause carried its kind-`0` fibre component this was false — the slot
gave no handle on `B`, and an inhabited `piR 0 A B` says only that the
fibre is inhabited, never that its inhabitant is `pt`. -/
theorem app_mem_of_slot {ρ : Nat → V} {fa aa : AnnotTerm}
    (hok : WellDenoted V ρ (.app fa aa)) :
    ∃ B : V → V,
      interp V ρ (.app fa aa) ∈ˢ B (interp V ρ aa) := by
  rw [WellDenoted_app] at hok
  obtain ⟨-, -, v, A, B, hf, ha, hz⟩ := hok
  exact ⟨B, by rw [interp_app]; exact app_mem_piR hf ha hz⟩

/-! ## The `const` row -/

/-- **`const`.**  Interface facts: the basis capstone
(`bval_mem_type`) and nothing else — a built-in is a closed leaf, so
its row needs no context, no valuation and no hereditary premise.  With
this the skeleton covers **ten formers of ten**. -/
theorem sound_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) :
    WellDenoted V ρ (.const c us) ∧
      interp V ρ (.const c us)
        ∈ˢ interp V ρ (BConst.typeAV c us) :=
  ⟨by simp, bval_mem_type V c us ρ⟩

/-! ## The remaining structural rows -/


/-! ## The projection rows

The `Σ`-eliminations, general in the fibre family (`Interp/Value.lean`
states them for the `bval` tower's `fun x => app B x`; the invariant's
proj clause carries a meta-level `Bf`, so the two below are the
general forms `mem_sigma_elim` supports directly). -/

/-- First projection: a member of a `Σ` has its first component in the
base. -/
theorem sfst_mem_gen {u v : Nat} {A p : V} {Bf : V → V}
    (hA : A ∈ˢ (univ u : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A Bf) : sfst p ∈ˢ A := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · have hu : u = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_left u v)
    rw [h0 hw, sfst_pt]
    exact (mem_univ_zero (hu ▸ hA) ha) ▸ ha
  · rw [hne hw, sfst_spair]; exact ha

/-- Second projection: the second component lies in the fibre over the
first. -/
theorem ssnd_mem_gen {u v : Nat} {A p : V} {Bf : V → V}
    (hA : A ∈ˢ (univ u : V))
    (hB : ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V))
    (hp : p ∈ˢ sigmaSet (Nat.max u v) A Bf) :
    ssnd p ∈ˢ Bf (sfst p) := by
  obtain ⟨a, b, ha, hb, h0, hne⟩ := mem_sigma_elim hp
  by_cases hw : Nat.max u v = 0
  · have hu : u = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_left u v)
    have hv : v = 0 := Nat.le_zero.mp (hw ▸ Nat.le_max_right u v)
    have hapt : a = pt := mem_univ_zero (hu ▸ hA) ha
    have hBa : Bf a ∈ˢ (univ 0 : V) := hv ▸ hB a ha
    have hbpt : b = pt := mem_univ_zero hBa hb
    rw [h0 hw, ssnd_pt, sfst_pt, show Bf pt = Bf a by rw [hapt]]
    exact hbpt ▸ hb
  · rw [hne hw, ssnd_spair, sfst_spair]; exact hb

/-- **`fst`.**  Interface facts: the subject's `Σ`-package — which
is exactly what `WellDenoted`'s `fst` clause carries, so this row
consumes the invariant and nothing else. -/
theorem sound_proj_fst {ρ : Nat → V} {ea : AnnotTerm}
    (hok : WellDenoted V ρ (.fst ea)) :
    ∃ (u : Nat) (A : V), A ∈ˢ (univ u : V) ∧
      interp V ρ (.fst ea) ∈ˢ A := by
  rw [WellDenoted_fst] at hok
  obtain ⟨-, u, v, A, Bf, hp, hA, -⟩ := hok
  refine ⟨u, A, hA, ?_⟩
  rw [interp_fst]
  exact sfst_mem_gen V hA hp

end ConLeche.Semantics
