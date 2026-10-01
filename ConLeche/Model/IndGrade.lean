module

public import ConLeche.Model.IndRename
public section

/-!
# The frame's gradings, discharged (task #161, IND TIER part 4)

**The part-4 hinge.**  `ctxOk_of_openers` (part 3) takes the openers'
gradings as `hokA` — the premise part 3 named as the place where the
premise set grows, because `CtxOkR`'s per-leaf obligation is a
derivation that carries its own justification while `CtxOk`'s is an
equation *plus a grading*.  Every one of the surviving stages fires a
recorded run through `defEqAt_of_run`, and every one of those needs
`hokA` at the padded frame.  This file discharges it once, from the
statement type's own grading.

**Why it matters that this works, and works this way.**  The obvious
route — descend the tower along the value *chain*, the way
`teleFitPA_of_tower` and `teleFitPA_to_chain` do — needs the fired
spine's arguments to be **graded**, because the chain's step is an
`instE` at cut `n` and `AnnotOkP_inst` charges for the substituted
value.  That would have been fatal: `RecRuleLaw`'s interp-equality
half is stated with *no* grading premise on `xs`/`ys` (the gradings
appear only in the truthfulness half, behind their own arrows), so a
zipper that needed them could not establish the frozen statement.

The route that works descends **top-down along the satisfying
environment** instead.  `Sat` already says every context entry's own
value inhabits its own reading, which is exactly the membership the
`.pi` split consumes, and the environments line up on the nose:
`cons (ρ' q) (fun j => ρ' (j + q + 1))` *is* `fun j => ρ' (j + q)`.  So
the descent spends the satisfaction the stage already has and asks the
arguments for nothing.

This is also why v1's `annotOkV_descend` — retired at part 2 and
therefore not transposed by part 3's survey — is not what was needed:
it descends along the chain.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **The tower's domains are graded along a satisfying environment**,
top-down: to grade the domain at slot `p` it is enough to have the
whole tower graded at the ambient environment below it and the
memberships at the slots *above* `p`.

The two environment identities that make it work are pointwise and
need no lemma: `fun j => ρ' (j + k)` is the ambient below a `k`-slot
tower, and `cons (ρ' q) (fun j => ρ' (j + q + 1)) = fun j => ρ' (j + q)`
is the `.pi` split's extension. -/
theorem wellDenotedV_tower_slot :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ρ' : Nat → V},
      WellDenotedV V (fun j => ρ' (j + k)) T →
      ∀ p, p < k →
        (∀ q, p < q → q < k →
          ρ' q ∈ˢ interp V (fun j => ρ' (j + q + 1)) (Γ.getD q default)) →
        WellDenotedV V (fun j => ρ' (j + p + 1)) (Γ.getD p default) := by
  intro k
  induction k with
  | zero => intro T Γ R _ ρ' _ p hp; exact absurd hp (by omega)
  | succ k ih =>
    intro T Γ R h ρ' hokT p hp hmem
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    have hΓ'len : Γ'.length = k := htail.length
    have hgetA : (Γ' ++ [A]).getD k default = A := by
      rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
      simp
    -- the tower's grading, at the environment the `.pi` split reads
    have hokT' : WellDenotedV V (fun j => ρ' (j + k + 1))
        (AnnotTerm.pi u v A B) := hokT
    have hsplitA : WellDenotedV V (fun j => ρ' (j + k + 1)) A :=
      ⟨((WellDenoted_pi V (fun j => ρ' (j + k + 1)) u v A B) ▸ hokT'.1).1,
        ((AnnotValid_pi V (fun j => ρ' (j + k + 1)) u v A B)
          ▸ hokT'.2).1⟩
    rcases Nat.lt_or_ge p k with hpk | hpk
    · -- an inner slot: descend past the head, spending its membership
      have hmemk : ρ' k ∈ˢ interp V (fun j => ρ' (j + k + 1)) A := by
        have := hmem k (by omega) (by omega)
        rwa [hgetA] at this
      have henv : cons (ρ' k) (fun j => ρ' (j + k + 1))
          = (fun j => ρ' (j + k)) := by
        funext j
        cases j with
        | zero =>
          show cons (ρ' k) (fun j => ρ' (j + k + 1)) 0 = ρ' (0 + k)
          rw [cons_zero]
          congr 1
          omega
        | succ j =>
          show cons (ρ' k) (fun j => ρ' (j + k + 1)) (j + 1)
            = ρ' (j + 1 + k)
          rw [cons_succ]
          show ρ' (j + k + 1) = ρ' (j + 1 + k)
          congr 1
          omega
      have hokB : WellDenotedV V (fun j => ρ' (j + k)) B := by
        refine ⟨?_, ?_⟩
        · have h := ((WellDenoted_pi V (fun j => ρ' (j + k + 1)) u v A B)
            ▸ hokT'.1).2 (ρ' k) hmemk
          rwa [henv] at h
        · have h := ((AnnotValid_pi V (fun j => ρ' (j + k + 1)) u v A B)
            ▸ hokT'.2).2.1 (ρ' k) hmemk
          rwa [henv] at h
      have hgetΓ' : ∀ q, q < k →
          (Γ' ++ [A]).getD q default = Γ'.getD q default := by
        intro q hq
        rw [List.getD, List.getD, List.getElem?_append_left (by omega)]
      rw [hgetΓ' p hpk]
      exact ih htail hokB p hpk (fun q hq1 hq2 => by
        have := hmem q hq1 (by omega)
        rwa [hgetΓ' q hq2] at this)
    · -- the head slot itself
      obtain rfl : p = k := by omega
      rw [hgetA]
      exact hsplitA

/-- **`ctxOk_of_openers`'s `hokA`, discharged at the padded frame** —
the shape every surviving stage consumes.  The padding never carries a
tower slot the conclusion mentions: a slot `K - 1 - i` with `i < n`
sits at index `≥ K - n`, which is exactly where the padded context's
entries *are* the tower's. -/
theorem hokA_padded {K n : Nat} {Tstmt : AnnotTerm} {Γs : List AnnotTerm}
    {Rbody : AnnotTerm} (htower : PiTeleAV K Tstmt Γs Rbody)
    (hokT : ∀ σ : Nat → V, WellDenotedV V σ Tstmt) (hn : n ≤ K) :
    ∀ i, i < n → ∀ ρ' : Nat → V,
      Sat V (List.replicate (K - n) (.sort 0) ++ Γs.drop (K - n)) ρ' →
      WellDenotedV V (fun j => ρ' (j + (K - 1 - i) + 1))
        (Γs.getD (K - 1 - i) default) := by
  intro i hi ρ' hsat
  have hΓlen : Γs.length = K := htower.length
  -- above the padding the padded context is the tower's
  have hpad : ∀ q, K - n ≤ q → q < K →
      (List.replicate (K - n) (AnnotTerm.sort 0) ++ Γs.drop (K - n))[q]?
        = some (Γs.getD q default) := by
    intro q hq1 hq2
    rw [List.getElem?_append_right (by simpa using hq1),
      List.length_replicate, List.getElem?_drop,
      show K - n + (q - (K - n)) = q from by omega, List.getD]
    rcases hg : Γs[q]? with _ | A
    · rw [List.getElem?_eq_none_iff] at hg; omega
    · rfl
  refine wellDenotedV_tower_slot K htower (hokT _) (K - 1 - i) (by omega)
    (fun q hq1 hq2 => ?_)
  have hq0 : K - n ≤ q := by omega
  exact hsat q (Γs.getD q default) (hpad q hq0 hq2)

end ConLeche.Model
