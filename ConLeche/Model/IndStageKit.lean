module

public import ConLeche.Model.IndSubst

public section

/-!
# The stages' semantic prelude (task #161, IND TIER part 4, step 1)

`Install/IndStagesS.lean`'s first two hundred lines at the validated
reading — the four pieces the surviving stages use and that the part-3
frame kit deliberately left out, because they are the *stages'* own
scaffolding rather than the frame's:

* `PiTeleAV.prefix` — a tower splits at any depth, in `drop`/`take`
  form (v1's `PiTele.prefix`).  It is `PiTeleAV.split` with the two
  context halves identified by their lengths, so it is a corollary
  here where v1 needed an induction;
* `TeleFitPA.take` — a fit's prefix fits, to *some* residual;
* `sat_pad_of_mems` — **the zipper's introduce half**: the first `n`
  fitted readings satisfy the tower's outer context, padded to full
  depth by `.sort 0`/`empty` slots.  The pair with `padE2_shiftE` (the
  strip half, part 3) is what lets the strong induction fire a walk at
  step `n` while only `n` memberships are in hand;
* `teleFitPA_to_chain` — `teleFitPA_of_tower`'s converse: a fit's
  memberships, read back in chain form against the tower's context.
  The zipper spends this on both incoming fits (the recursor prefix's
  and the constructor's).

The transposition is faithful; the one delta worth naming is
`PiTeleAV.prefix`, and it is a saving.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Towers -/

/-- **A tower splits at any depth** (`PiTele.prefix`), in the
`drop`/`take` form the padding consumes.  A corollary of
`PiTeleAV.split` rather than an induction: `split` already produces the
two halves, and their lengths identify them as `Γ.drop`/`Γ.take`. -/
theorem PiTeleAV.prefix : ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm}, PiTeleAV k T Γ R → ∀ n, n ≤ k →
    ∃ mid, PiTeleAV n T (Γ.drop (k - n)) mid ∧
      PiTeleAV (k - n) mid (Γ.take (k - n)) R := by
  intro k T Γ R h n hn
  obtain ⟨Γ₁, Γ₂, M, hΓ, h2, h1, hpre, hpost⟩ :=
    PiTeleAV.split n (k - n)
      (by rw [show n + (k - n) = k from by omega]; exact h)
  refine ⟨M, ?_, ?_⟩
  · rw [show Γ.drop (k - n) = Γ₂ from by
      rw [hΓ, ← h1, List.drop_left]]
    exact hpre
  · rw [show Γ.take (k - n) = Γ₁ from by
      rw [hΓ, ← h1, List.take_left]]
    exact hpost

/-! ## Fits -/

/-- **A fit's memberships in chain form** (`teleFitV_to_chain`):
`teleFitPA_of_tower`'s converse — argument `n`'s reading inhabits the
tower's `n`-th open domain, read at the chain of the arguments outside
it. -/
theorem teleFitPA_to_chain :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ws : List AnnotTerm} {ρ : Nat → V}
        {rest : AnnotTerm},
      ws.length = k → TeleFitPA V ρ T ws rest →
      ∀ n, n < k →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (chain V ρ (ws.take n))
            (Γ.getD (k - 1 - n) default) := by
  intro k
  induction k with
  | zero => intro T Γ R h ws ρ rest hlen hfit n hn; exact nomatch hn
  | succ k ihk =>
    intro T Γ R h ws ρ rest hlen hfit n hn
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    cases hfit with
    | cons hmem htailFit =>
    match n, hn with
    | 0, _ =>
      rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
          rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
          simp]
      simpa using hmem
    | n + 1, hn =>
      have hinst := htail.inst w 0
      have h1 := ihk hinst hlen' htailFit n (by omega)
      rw [ctxInstAtAV_getD w 0 Γ' (k - 1 - n) (by omega),
        show 0 + Γ'.length - 1 - (k - 1 - n) = n from by omega,
        interp_inst] at h1
      have htklen : (ws'.take n).length = n := by
        rw [List.length_take]
        omega
      rw [show shiftE n 0 (chain V ρ (ws'.take n)) = ρ from by
          funext j
          show chain V ρ (ws'.take n) (j + n) = ρ j
          rw [chain_ge (by omega), htklen]
          congr 1
          omega,
        show instE n (interp V ρ w) (chain V ρ (ws'.take n))
            = chain V ρ (w :: ws'.take n) from by
          rw [chain_cons_eq_instE, htklen]] at h1
      rw [List.getD_cons_succ,
        show (w :: ws').take (n + 1) = w :: ws'.take n from rfl,
        show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
            = Γ'.getD (k - 1 - n) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by omega)]
          congr 2
          omega]
      exact h1

/-! ## The zipper's introduce half -/

/-- **The padded satisfaction from partial chain memberships**
(`sat_pad_of_mems`): the first `n` fitted readings satisfy the tower's
outer context, padded to full depth by `.sort 0` slots whose values
are `empty`.

This and `padE2_shiftE` (part 3's frame kit) are the pair the zipper's
strong induction introduces and strips at every step — a walk fires at
depth `K` while only `n ≤ K` memberships are in hand. -/
theorem sat_pad_of_mems {K : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (htower : PiTeleAV K T Γ R) {zs : List AnnotTerm}
    {ρ : Nat → V} (hlen : zs.length = K) {n : Nat} (hn : n ≤ K)
    (hmem : ∀ m, m < n →
      interp V ρ (zs.getD m default)
        ∈ˢ interp V (chain V ρ (zs.take m))
          (Γ.getD (K - 1 - m) default)) :
    Sat V (List.replicate (K - n) (.sort 0) ++ Γ.drop (K - n))
      (padE2 V (K - n) (chain V ρ (zs.take n))) := by
  obtain ⟨mid, hpre, -⟩ := htower.prefix n hn
  have hΓlen : Γ.length = K := htower.length
  refine sat_padded (K - n) (sat_of_tower hpre
    (ws := zs.take n) (by rw [List.length_take]; omega) ?_)
  intro m hm
  have h1 := hmem m (by omega)
  rw [show (zs.take n).getD m default = zs.getD m default from by
      rw [List.getD, List.getD, List.getElem?_take_of_lt hm],
    show (zs.take n).take m = zs.take m from by
      rw [List.take_take]
      congr 1
      omega,
    show (Γ.drop (K - n)).getD (n - 1 - m) default
        = Γ.getD (K - 1 - m) default from by
      rw [List.getD, List.getD, List.getElem?_drop,
        show K - n + (n - 1 - m) = K - 1 - m from by omega]]
  exact h1

end ConLeche.Model
