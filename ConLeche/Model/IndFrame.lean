module

public import ConLeche.Model.IndTele
import ConLeche.Model.Annot.BitInst
public section

/-!
# The P-tier frame kit (task #161, IND TIER part 3, step 1)

`Install/IndFrameS.lean`'s machinery at the validated-reading currency
— the environment vocabulary the surviving modeled-iota stages
(`zipperS`/`pointS`/`reductS`/`annotS`) are stated in.

**What this file is, and what it deliberately is not.**  The part-2
correction budgeted a fresh ~350-line transposition of the whole of
`IndFrameS`.  A per-name survey of the four surviving stages says the
kit they actually read is much narrower, and that part 2 had already
landed its core under another name:

* **the chain already exists.**  `consN` (`IndTeleP.lean:262`) is
  `consChain` definitionally — same cons order, same fold — and
  `consN_shift`/`consN_getElem?` are `chainE_ge`/`chainE_lt`'s content
  at bare values.  So `chain` below is a *wrapper*: the chain of a
  spine's **readings**, `consN (ws.map (interp V ρ)) ρ`, and its two
  lookup lemmas are three lines each rather than two inductions;
* **`chainFrom` and its three lemmas do not transpose.**  v1 needs the
  value/base split because `chainE` is defined by a `foldl` over
  *expressions*; going through `consN` there is nothing to split, and
  the survey confirms `chainFrom_cons`/`chainFrom_lt`/`chainFrom_ge`
  have zero occurrences in `IndStagesS.lean` anyway;
* **six more names are dead weight** and are not transposed:
  `padE_zero`, `consChain_nil`, `consChain_cons`,
  `chainE_eq_consChain` (definitional here), `TeleFitV.appN_val` and
  `annotOkV_descend` — the first five have no occurrence anywhere in
  `IndStagesS.lean`, and the last is consumed only by `fireS`, which
  part 2's four-move firing already retired.

What *is* transposed is what the stages consume: the chain and its two
lookups, the `instSeq` pivot between chain-reading and
substituted-reading, and the padding pair — which never appears in a
stage's statement, but is introduced and stripped inside the zipper's
strong induction (`sat_pad_of_mems` up, `padE_shiftE` down).

**The currency delta that matters.**  `Sat` becomes `Sat` and the
context becomes a `List AnnotTerm`, so the padding slot is `AnnotTerm.sort 0`
and its value fact is `empty_mem_univ 0` through `interp_sort` —
`interp` of a sort is `univ` on the nose, so the `.sort 0`/`empty`
trick transposes with no `dummyPropT` detour at all.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The reading chain

`chainE`'s twin: the environment a fired spine's *readings* build over
the ambient one, outermost first, so `.bvar 0` names the innermost
(last) argument and indices past the spine read the ambient
environment shifted. -/

/-- The value chain of a spine of readings (outermost first). -/
@[expose] noncomputable def chain (V : Type w) [SetTheory V] (ρ : Nat → V)
    (ws : List AnnotTerm) : Nat → V :=
  consN (ws.map (interp V ρ)) ρ

@[simp] theorem chain_nil (ρ : Nat → V) : chain V ρ [] = ρ := rfl

/-- Chain lookup at or above the spine: the ambient environment,
shifted (`chainE_ge`). -/
theorem chain_ge {ρ : Nat → V} {ws : List AnnotTerm} {i : Nat}
    (hi : ws.length ≤ i) : chain V ρ ws i = ρ (i - ws.length) := by
  have hlen : (ws.map (interp V ρ)).length = ws.length := by simp
  have h := consN_shift (ws.map (interp V ρ)) ρ (i - ws.length)
  rw [hlen, show i - ws.length + ws.length = i from by omega] at h
  exact h

/-- Chain lookup below the spine: the reading of the
`(len - 1 - i)`-th spine element (`chainE_lt`). -/
theorem chain_lt {ρ : Nat → V} {ws : List AnnotTerm} {i : Nat}
    (hi : i < ws.length) :
    chain V ρ ws i = interp V ρ (ws.getD (ws.length - 1 - i) default) := by
  have hlen : (ws.map (interp V ρ)).length = ws.length := by simp
  have h := consN_getElem? (ws.map (interp V ρ)) ρ i (by rw [hlen]; exact hi)
  rw [hlen] at h
  have hlt : ws.length - 1 - i < ws.length := by omega
  obtain ⟨w, hw⟩ : ∃ w, ws[ws.length - 1 - i]? = some w :=
    ⟨ws[ws.length - 1 - i]'hlt, List.getElem?_eq_getElem hlt⟩
  rw [List.getElem?_map, hw] at h
  simp only [Option.map_some, Option.some.injEq] at h
  rw [List.getD, hw]
  exact h.symm

/-- The tail of a chain at an entry position is the partial chain of
the outer readings (`chainE_tail`). -/
theorem chain_tail {ρ : Nat → V} {ws : List AnnotTerm} {i : Nat}
    (hi : i < ws.length) :
    (fun j => chain V ρ ws (j + i + 1))
      = chain V ρ (ws.take (ws.length - 1 - i)) := by
  funext j
  have htk : (ws.take (ws.length - 1 - i)).length = ws.length - 1 - i := by
    rw [List.length_take]; omega
  by_cases hj : j + i + 1 < ws.length
  · have hYlt : ws.length - 1 - i - 1 - j < ws.length - 1 - i := by omega
    rw [chain_lt hj, chain_lt (by rw [htk]; omega), htk,
      show ws.length - 1 - (j + i + 1)
          = ws.length - 1 - i - 1 - j from by omega,
      List.getD, List.getD, List.getElem?_take_of_lt hYlt]
  · rw [chain_ge (by omega), chain_ge (by rw [htk]; omega), htk]
    congr 1
    omega

/-- Inserting the outermost chain reading is `instE` at the spine's
length (`chainE_cons_eq_instE`). -/
theorem chain_cons_eq_instE (ρ : Nat → V) (w : AnnotTerm)
    (ws : List AnnotTerm) :
    chain V ρ (w :: ws)
      = instE ws.length (interp V ρ w) (chain V ρ ws) := by
  funext i
  unfold instE
  by_cases h1 : i < ws.length
  · rw [if_pos h1, chain_lt h1,
      chain_lt (ws := w :: ws) (by simp only [List.length_cons]; omega),
      show (w :: ws).length - 1 - i = (ws.length - 1 - i) + 1 from by
        simp only [List.length_cons]; omega,
      List.getD_cons_succ]
  · rw [if_neg h1]
    by_cases h2 : i = ws.length
    · rw [if_pos h2, h2, chain_lt (ws := w :: ws)
        (by simp only [List.length_cons]; omega),
        show (w :: ws).length - 1 - ws.length = 0 from by
          simp only [List.length_cons]; omega,
        List.getD_cons_zero]
    · rw [if_neg h2, chain_ge (ws := ws) (by omega),
        chain_ge (ws := w :: ws)
          (by simp only [List.length_cons]; omega)]
      congr 1
      simp only [List.length_cons]
      omega

/-! ## Evaluation is instantiation

The design's central saving, one currency over: interpreting a fully
spine-instantiated reading is interpreting the open reading at the
value chain.  `AnnotTerm.instSeq` is `Term.instSeq`'s twin — outermost
argument first, at descending cuts. -/

/-- Instantiate a spine of readings at descending cuts, outermost
first (`Term.instSeq`'s twin). -/
@[expose] def _root_.ConLeche.Model.AnnotTerm.instSeq :
    List AnnotTerm → Nat → AnnotTerm → AnnotTerm
  | [], _, e => e
  | a :: as, t, e => ConLeche.Model.AnnotTerm.instSeq as (t - 1) (e.inst a t)

@[simp] theorem AnnotTerm.instSeq_nil (t : Nat) (e : AnnotTerm) :
    ConLeche.Model.AnnotTerm.instSeq [] t e = e := rfl

theorem AnnotTerm.instSeq_cons (a : AnnotTerm) (as : List AnnotTerm) (t : Nat)
    (e : AnnotTerm) :
    ConLeche.Model.AnnotTerm.instSeq (a :: as) t e
      = ConLeche.Model.AnnotTerm.instSeq as (t - 1) (e.inst a t) := rfl

/-- **Evaluation is instantiation** (`interp_instSeq`'s twin). -/
theorem interp_instSeq :
    ∀ (ws : List AnnotTerm) (e : AnnotTerm) (ρ : Nat → V),
      interp V ρ (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1) e)
        = interp V (chain V ρ ws) e := by
  intro ws
  induction ws with
  | nil => intro e ρ; rfl
  | cons w ws ih =>
    intro e ρ
    rw [show (w :: ws).length - 1 = ws.length from by simp,
      AnnotTerm.instSeq_cons, ih (e.inst w ws.length) ρ, interp_inst]
    congr 1
    funext i
    show instE ws.length
        (interp V (shiftE ws.length 0 (chain V ρ ws)) w)
        (chain V ρ ws) i
      = chain V ρ (w :: ws) i
    have hsh : shiftE ws.length 0 (chain V ρ ws) = ρ := by
      funext j
      show chain V ρ ws (j + ws.length) = ρ j
      rw [chain_ge (by omega), Nat.add_sub_cancel]
    rw [hsh, chain_cons_eq_instE]

/-! ## The padding

An untouched inner context slot is `.sort 0`, its chain value `empty`,
and `empty ∈ˢ univ 0` — so a partially-fitted chain satisfies a
full-depth context with no strengthening lemma.  `interp` of a sort
is `univ` on the nose (`interp_sort`), so the trick is even shorter
here than in v1. -/

/-- Pad an environment with `m` copies of `empty` below (`padE`). -/
@[expose] noncomputable def padE2 (V : Type w) [SetTheory V] (m : Nat)
    (ρ' : Nat → V) : Nat → V :=
  fun i => if i < m then SetTheory.empty else ρ' (i - m)

/-- Shifting past the padding cancels it — the strip half of the
zipper's introduce/strip pair. -/
theorem padE2_shiftE (m : Nat) (ρ' : Nat → V) :
    shiftE m 0 (padE2 V m ρ') = ρ' := by
  funext i
  show (if i < 0 then _ else padE2 V m ρ' (i + m)) = _
  rw [if_neg (Nat.not_lt_zero i)]
  show (if i + m < m then SetTheory.empty else ρ' (i + m - m)) = _
  rw [if_neg (by omega), Nat.add_sub_cancel]

/-- **A padded prefix keeps a context satisfied** (`sat_padded`): the
padding entries are `.sort 0`, their values `empty`, and every older
entry's reading consults only the environment above the padding. -/
theorem sat_padded {Δa : List AnnotTerm} {ρ' : Nat → V} (m : Nat)
    (h : Sat V Δa ρ') :
    Sat V (List.replicate m (.sort 0) ++ Δa) (padE2 V m ρ') := by
  intro i Aa hi
  by_cases him : i < m
  · rw [List.getElem?_append_left (by simpa using him),
      List.getElem?_replicate_of_lt him] at hi
    obtain rfl := Option.some.inj hi
    show padE2 V m ρ' i ∈ˢ interp V _ (.sort 0)
    rw [interp_sort, show padE2 V m ρ' i = SetTheory.empty from by
      simp [padE2, him]]
    exact empty_mem_univ 0
  · rw [List.getElem?_append_right (by simpa using him)] at hi
    simp only [List.length_replicate] at hi
    have h1 := h (i - m) Aa hi
    have henv : (fun j => padE2 V m ρ' (j + i + 1))
        = (fun j => ρ' (j + (i - m) + 1)) := by
      funext j
      show padE2 V m ρ' (j + i + 1) = ρ' (j + (i - m) + 1)
      rw [show padE2 V m ρ' (j + i + 1) = ρ' (j + i + 1 - m) from by
        simp only [padE2, if_neg (show ¬ j + i + 1 < m by omega)],
        show j + i + 1 - m = j + (i - m) + 1 from by omega]
    show padE2 V m ρ' i ∈ˢ interp V (fun j => padE2 V m ρ' (j + i + 1)) Aa
    rw [show padE2 V m ρ' i = ρ' (i - m) from by simp [padE2, him], henv]
    exact h1

/-! ## The telescope, substituted

`ctxInstAt`/`PiTele.inst` at the reading.  These are V-free — pure
`AnnotTerm` bookkeeping — so they transpose as a rename, and they are
what lets the fit's induction step speak about the tail tower after
one argument goes in. -/

/-- A context's entries, instantiated after a variable *below* all of
them is substituted (`ctxInstAt`). -/
@[expose] def ctxInstAtAV (v : AnnotTerm) (j : Nat) : List AnnotTerm → List AnnotTerm
  | [] => []
  | B :: Γ => B.inst v (j + Γ.length) :: ctxInstAtAV v j Γ

@[simp] theorem ctxInstAtAV_nil (v : AnnotTerm) (j : Nat) :
    ctxInstAtAV v j [] = [] := rfl

theorem ctxInstAtAV_cons (v : AnnotTerm) (j : Nat) (B : AnnotTerm)
    (Γ : List AnnotTerm) :
    ctxInstAtAV v j (B :: Γ) = B.inst v (j + Γ.length) :: ctxInstAtAV v j Γ := by
  rfl

theorem ctxInstAtAV_append (v : AnnotTerm) (j : Nat) :
    ∀ (Γ₁ Γ₂ : List AnnotTerm),
      ctxInstAtAV v j (Γ₁ ++ Γ₂) =
        ctxInstAtAV v (j + Γ₂.length) Γ₁ ++ ctxInstAtAV v j Γ₂
  | [], _ => rfl
  | B :: Γ₁, Γ₂ => by
    simp only [List.cons_append, ctxInstAtAV_cons,
      ctxInstAtAV_append v j Γ₁ Γ₂, List.length_append, List.cons.injEq]
    exact ⟨by congr 1; omega, trivial⟩

theorem ctxInstAtAV_snoc (v : AnnotTerm) (j : Nat) (Γ : List AnnotTerm)
    (A : AnnotTerm) :
    ctxInstAtAV v j (Γ ++ [A]) = ctxInstAtAV v (j + 1) Γ ++ [A.inst v j] := by
  rw [ctxInstAtAV_append]
  rfl

/-- `ctxInstAtAV`, per entry: the entry at index `i` is instantiated at
its own residual depth (`ctxInstAt_getD`). -/
theorem ctxInstAtAV_getD (v : AnnotTerm) (j : Nat) :
    ∀ (Γ : List AnnotTerm) (i : Nat), i < Γ.length →
      (ctxInstAtAV v j Γ).getD i default =
        (Γ.getD i default).inst v (j + Γ.length - 1 - i)
  | [], _, h => absurd h (by simp)
  | B :: Γ, 0, _ => by
    simp only [ctxInstAtAV_cons, List.getD_cons_zero, List.length_cons,
      Nat.sub_zero]
    congr 1
  | B :: Γ, i + 1, h => by
    simp only [ctxInstAtAV_cons, List.getD_cons_succ, List.length_cons]
    rw [ctxInstAtAV_getD v j Γ i (by simpa using h)]
    congr 1
    omega

/-- A substituted tower is a tower over the substituted context
(`PiTele.inst`). -/
theorem PiTeleAV.inst : ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm}, PiTeleAV k T Γ R → ∀ (v : AnnotTerm) (j : Nat),
      PiTeleAV k (T.inst v j) (ctxInstAtAV v j Γ) (R.inst v (j + k)) := by
  intro k T Γ R h
  induction h with
  | nil => intro v j; simpa using PiTeleAV.nil
  | @cons k u v' A B R Γ _ ih =>
    intro v j
    rw [AnnotTerm.inst_pi, ctxInstAtAV_snoc]
    have h1 := ih v (j + 1)
    rw [show j + 1 + k = j + (k + 1) from by omega] at h1
    exact PiTeleAV.cons h1

/-! ## The tower producers

zipperS's two payoff lines, at the reading.  Both consume the *same*
per-step chain memberships — argument `n`'s reading inhabits the
tower's `n`-th open domain, read at the chain of the arguments
outside it — and they are the only two places in the surviving stages
where a `Sat`/fit is manufactured rather than moved.

The fit's transpose has one shape delta worth naming, and it is
benign: `TeleFitPA` peels by *substitution* (`B.inst a`) where
`TeleFitV` peels by substitution too, so the two inductions coincide
step for step and `PiTeleAV.inst` plays exactly the role `PiTele.inst`
plays in `teleFitV_of_tower`.  What changes is only the residual's
spelling — `AnnotTerm.instSeq` in place of `Term.instSeq`. -/

/-- **`Sat` of a tower's context at the chain** (`sat_of_tower`),
from per-step chain memberships. -/
theorem sat_of_tower {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm}
    {R : AnnotTerm} (h : PiTeleAV k T Γ R) {ws : List AnnotTerm} {ρ : Nat → V}
    (hlen : ws.length = k)
    (hmem : ∀ n, n < k →
      interp V ρ (ws.getD n default)
        ∈ˢ interp V (chain V ρ (ws.take n))
          (Γ.getD (k - 1 - n) default)) :
    Sat V Γ (chain V ρ ws) := by
  intro i Aa hi
  have hΓlen : Γ.length = k := h.length
  have hik : i < k := by
    rw [← hΓlen]
    rcases Nat.lt_or_ge i Γ.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hi
      exact nomatch hi
  have h1 := hmem (k - 1 - i) (by omega)
  rw [show k - 1 - (k - 1 - i) = i from by omega,
    show Γ.getD i default = Aa from by rw [List.getD, hi]; rfl] at h1
  rw [chain_lt (by omega),
    show ws.length - 1 - i = k - 1 - i from by omega,
    show (fun j => chain V ρ ws (j + i + 1))
        = chain V ρ (ws.take (k - 1 - i)) from by
      rw [← show ws.length - 1 - i = k - 1 - i from by omega]
      exact chain_tail (by omega)]
  exact h1

/-- **The tower fitting, from chain memberships** (`teleFitV_of_tower`
at the reading): readings that inhabit the tower's open domains at the
progressive chains fit the tower, with the fully instantiated body as
residual. -/
theorem teleFitPA_of_tower :
    ∀ (k : Nat) {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      PiTeleAV k T Γ R → ∀ {ws : List AnnotTerm} {ρ : Nat → V},
      ws.length = k →
      (∀ n, n < k →
        interp V ρ (ws.getD n default)
          ∈ˢ interp V (chain V ρ (ws.take n))
            (Γ.getD (k - 1 - n) default)) →
      TeleFitPA V ρ T ws (ConLeche.Model.AnnotTerm.instSeq ws (k - 1) R) := by
  intro k
  induction k with
  | zero =>
    intro T Γ R h ws ρ hlen _
    cases h
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact TeleFitPA.nil
  | succ k ihk =>
    intro T Γ R h ws ρ hlen hmem
    obtain ⟨u, v, A, B, Γ', rfl, rfl, htail⟩ := h.succ_inv
    match ws, hlen with
    | w :: ws', hlen =>
    have hlen' : ws'.length = k := by simpa using hlen
    have hΓ'len : Γ'.length = k := htail.length
    -- the head membership: entry `k` of `Γ' ++ [A]` is `A`
    have h0 := hmem 0 (by omega)
    rw [show (Γ' ++ [A]).getD (k + 1 - 1 - 0) default = A from by
        rw [List.getD, List.getElem?_append_right (by omega), hΓ'len]
        simp] at h0
    simp only [List.getD_cons_zero, List.take_zero, chain_nil] at h0
    refine TeleFitPA.cons h0 ?_
    -- the tail: the instantiated tower via the recursion at `k`
    have hinst := htail.inst w 0
    have hfit := ihk hinst (ws := ws') (ρ := ρ) hlen' ?_
    · rw [show ConLeche.Model.AnnotTerm.instSeq (w :: ws') (k + 1 - 1) R
          = ConLeche.Model.AnnotTerm.instSeq ws' (k - 1) (R.inst w k) from by
        rw [AnnotTerm.instSeq_cons]
        simp only [Nat.add_sub_cancel]]
      rw [show (0 : Nat) + k = k from Nat.zero_add k] at hfit
      exact hfit
    · intro n hn
      have h1 := hmem (n + 1) (by omega)
      rw [List.getD_cons_succ,
        show (w :: ws').take (n + 1) = w :: ws'.take n from rfl,
        show (Γ' ++ [A]).getD (k + 1 - 1 - (n + 1)) default
            = Γ'.getD (k - 1 - n) default from by
          rw [List.getD, List.getD,
            List.getElem?_append_left (by omega)]
          congr 2
          omega] at h1
      rw [ctxInstAtAV_getD w 0 Γ' (k - 1 - n) (by omega),
        show 0 + Γ'.length - 1 - (k - 1 - n) = n from by omega]
      have htklen : (ws'.take n).length = n := by
        rw [List.length_take]
        omega
      rw [interp_inst,
        show shiftE n 0 (chain V ρ (ws'.take n)) = ρ from by
          funext j
          show chain V ρ (ws'.take n) (j + n) = ρ j
          rw [chain_ge (by omega), htklen]
          congr 1
          omega,
        show instE n (interp V ρ w) (chain V ρ (ws'.take n))
            = chain V ρ (w :: ws'.take n) from by
          rw [chain_cons_eq_instE, htklen]]
      exact h1

/-! ## `CtxOk` at the opened frame

`ctxOkR_of_openers`'s transpose, and the one place in this kit where
the premise set genuinely *grows* — the lesson part 2 recorded, met
again.  `CtxOkR`'s per-leaf obligation is a *derivation* (`Infer.bvar`
onto `DefEq.refl`), which carries its own justification; `CtxOk`'s is
a **semantic equation plus a grading**, and while the equation is free
(it is `interp_liftN` against a `shiftE` that computes), the grading
is not: nothing about an opener's index says its annotation reads to a
graded annotation.  So this transpose takes the openers' grading as
`hokA`, where v1 took nothing.

The equation half is worth recording as a small saving: it needs no
`Sat` at all.  Lifting the entry to the leaf's depth shifts the
environment by exactly `k - i`, and the context clause reads the entry
at `fun j => ρ (j + (k - 1 - i) + 1)` — the same function whenever
`i < k`.  So the two sides agree pointwise before any satisfaction
hypothesis is consulted, and `ctxOk_of_openers` never inspects `ρ`. -/

/-- **`CtxOk` at the opened frame** (`ctxOkR_of_openers`'s
transpose): a context whose entries at the touched indices are the
frame's own-depth read annotations correlates with a kit expression;
padding slots are never consulted. -/
theorem ctxOk_of_openers {env : Env} {m : EnvModel V env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (m.acval n ψ).liftN 1 k = m.acval n ψ)
    {k : Nat} {fvs : List Expr} {Aa : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {e : Expr} {n : Nat}
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltE : ∀ l ∈ e.fvarLeaves, l.1 < n)
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < n → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i)) :
    CtxOk m φ k Δa e := by
  refine ⟨hΔlen, ?_⟩
  intro l hl
  have hmem := hleaf l hl
  obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
  obtain ⟨ty, hx⟩ := hshape pos _ hpos
  obtain ⟨h1, h2⟩ : l.1 = pos ∧ l.2 = ty := by
    injection hx with a b
    exact ⟨a, b⟩
  subst h1 h2
  have hlt : l.1 < n := hltE l hl
  have hw := hws _ (List.mem_of_getElem? hpos)
  have hwty : l.1 < k ∧ Expr.WScoped l.1 l.2 := by
    simpa [Expr.WScoped] using hw
  refine ⟨hwty.1, hwty.2.fvarsBelow, (Aa l.1).liftN (k - l.1) 0, Aa l.1,
    ?_, hent l.1 hlt, ?_, ?_⟩
  · have hd1 := hdoms l.1 _ hpos
    rw [show Expr.fvarTypeD (Expr.fvar l.1 l.2) = l.2 from rfl]
      at hd1
    rw [denoteMeta_lift hacl hwty.2 k (by omega), hd1]
    rfl
  · -- the equation: `interp_liftN`'s `shiftE` against the entry's own
    -- context environment; both are `fun j => ρ (j + (k - l.1))`
    intro ρ _
    rw [interp_liftN]
    congr 1
    funext j
    show (if j < 0 then ρ j else ρ (j + (k - l.1))) = ρ (j + (k - 1 - l.1) + 1)
    rw [if_neg (Nat.not_lt_zero j)]
    congr 1
    omega
  · -- the grading: the entry's, transported across the same lift
    intro ρ hρ
    refine (WellDenotedV_liftN V (k - l.1) (Aa l.1) 0 ρ).mpr ?_
    have h := hokA l.1 hlt ρ hρ
    have henv : shiftE (k - l.1) 0 ρ = fun j => ρ (j + (k - 1 - l.1) + 1) := by
      funext j
      show (if j < 0 then ρ j else ρ (j + (k - l.1))) = _
      rw [if_neg (Nat.not_lt_zero j)]
      congr 1
      omega
    rw [henv]
    exact h

end ConLeche.Model
