module

public import ConLeche.Model.IndFrame
import ConLeche.Verify.IotaWalkInv
public section

/-!
# The walks' recorded runs, converted (task #161, IND TIER part 4)

The part-3 wall, consumed.  Every P tier is built from the checker's
**recorded runs**; the ind tier's `R`-predicates used to reach their
comparisons only through `IotaWalksR`, six rows of quantified-context
*derivation packs* at the v1 currency, which no P proof can read
(`interp2_ne_interp_erase` refutes the transport, and derivation → run
is false for a fuel-bounded incomplete checker).  The lead's widening
(`IotaRuns`, `SetR/Decl.lean`) records the runs the producer already
held; this file is their conversion.

`defEqAt_of_run` is `openWalk_eqS`'s P transpose and the pivot of
every surviving stage: where v1 instantiates a `DefEqAtW` derivation
at the padded pinned context and reads it through `DefEq.sound`, the P
tier hands the *run* to `DefEqClaim` at the same context, built by
`ctxOk_of_openers`.  One conversion, no soundness theorem in
between.

**The premise set grows, and the reason is structural** (part 2's
lesson, met for the fourth time).  A `DefEqAtW` pack *carries* its two
readings — `∃ Av Bv, denote … = some Av ∧ …` — because a derivation is
a datum about denotations.  A run is a datum about *syntax*: it says
the checker accepted, and says nothing about what the two sides read
to.  So the P conversion takes

* the two readings (`haa`/`hba`) and their gradings (`hga`/`hgb`), and
* the two sides' syntactic guards (`WScoped`/`looseBVarsBounded`/
  `LeavesBounded`), which `DefEqClaim` requires and which a
  derivation supplied implicitly,

as premises.  Every one of them is available at the stage that calls
this — the frame's openers are `fvar`s with the tower's own domains,
and the comparison lists' readings come from the tower kits — but
none of them is *free*, and transposing the conclusion alone would
have dropped them silently.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name isDefEqCore DefEqListOk)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## One comparison -/

/-- **A recorded comparison fires at a padded frame** —
`openWalk_eqS`'s P transpose, at the currency `IotaRuns`'s rows are
recorded in.

The context is the opened frame's (`ctxOk_of_openers`), built once
for each side from the same opener data; `DefEqClaim` turns the
run into the `interp` equality at any satisfying valuation.  Note
what is *absent* relative to v1: no `DefEq.sound`, no `EnvSHyp`, and
no derivation — the claims conclude the semantic equality directly
(the two-step collapses to one, exactly as part 3's resume-here
predicted for `annotPFrameEqS`). -/
theorem defEqAt_of_run {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {k : Nat} {fvs : List Expr} {Aa : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {n : Nat}
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < n → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i))
    {a b : Expr}
    (hrun : isDefEqCore μ env F k a b = .ok true)
    (hwa : Expr.WScoped k a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped k b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    (hleafA : ∀ l ∈ a.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltA : ∀ l ∈ a.fvarLeaves, l.1 < n)
    (hleafB : ∀ l ∈ b.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs)
    (hltB : ∀ l ∈ b.fvarLeaves, l.1 < n)
    {aa ba : AnnotTerm}
    (haa : denoteMeta m.acval env φ k a = some aa)
    (hbaR : denoteMeta m.acval env φ k b = some ba)
    (hga : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (hgb : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba)
    {ρ : Nat → V} (hsat : Sat V Δa ρ) :
    interp V ρ aa = interp V ρ ba :=
  hclaims hrun hwa hba hLa hwb hbb hLb
    (ctxOk_of_openers m.acval_closed hΔlen hshape hws hdoms hleafA
      hltA hent hokA)
    (ctxOk_of_openers m.acval_closed hΔlen hshape hws hdoms hleafB
      hltB hent hokA)
    haa hbaR hga hgb ρ hsat

/-! ## A comparison list

`DefEqListOk` is a *pairwise* run predicate over two `List Expr`s, so
its conversion is an index lookup, not an induction over the semantic
side: the caller already holds the two readings per index (they come
from the two towers), and all this lemma does is find the run at that
index. -/

/-- The run at one index of a recorded comparison list. -/
theorem defEqListOk_getElem {F : Nat} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk μ F env d as bs →
      ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b →
        isDefEqCore μ env F d a b = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h i a b ha _
    exact nomatch ha
  | cons a₀ as ih =>
    intro bs h i a b ha hb
    match bs, h with
    | b₀ :: bs, ⟨hhead, htail⟩ =>
      match i with
      | 0 =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        exact hhead
      | i + 1 =>
        exact ih htail i a b (by simpa using ha) (by simpa using hb)

/-- The run at one index, in `getD` form — the shape the stages read
their comparison lists in (v1's `DefEqListW` is consumed the same
way). -/
theorem defEqListOk_getD {F : Nat} {d : Nat} {as bs : List Expr}
    (h : DefEqListOk μ F env d as bs) (i : Nat) (hi : i < as.length) :
    isDefEqCore μ env F d (as.getD i default) (bs.getD i default)
      = .ok true := by
  have hlen : as.length = bs.length := h.length
  rcases ha : as[i]? with _ | a
  · rw [List.getElem?_eq_none_iff] at ha; omega
  rcases hb : bs[i]? with _ | b
  · rw [List.getElem?_eq_none_iff] at hb; omega
  rw [List.getD, ha, List.getD, hb]
  exact defEqListOk_getElem h i a b ha hb

/-- **A recorded comparison list fires, pointwise** — the list form of
`defEqAt_of_run`, at one index.  The two readings are the caller's
(they come from the two towers the lists' entries are the domains of);
what this adds is the frame's context and the claims. -/
theorem defEqListFueled_of_runs {m : EnvModel V env} {F : Nat}
    (hclaims : DefEqClaim μ m φ F)
    {k : Nat} {fvs : List Expr} {Aa : Nat → AnnotTerm} {Δa : List AnnotTerm}
    (hΔlen : Δa.length = k)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped k x)
    (hdoms : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta m.acval env φ i (Expr.fvarTypeD x) = some (Aa i))
    {n : Nat}
    (hent : ∀ i, i < n → Δa[k - 1 - i]? = some (Aa i))
    (hokA : ∀ i, i < n → ∀ ρ : Nat → V, Sat V Δa ρ →
      WellDenotedV V (fun j => ρ (j + (k - 1 - i) + 1)) (Aa i))
    {as bs : List Expr} (hruns : DefEqListOk μ F env k as bs)
    (i : Nat) (hi : i < as.length)
    (hwa : Expr.WScoped k (as.getD i default))
    (hba : (as.getD i default).looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded (as.getD i default))
    (hwb : Expr.WScoped k (bs.getD i default))
    (hbb : (bs.getD i default).looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded (bs.getD i default))
    (hleafA : ∀ l ∈ (as.getD i default).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs)
    (hltA : ∀ l ∈ (as.getD i default).fvarLeaves, l.1 < n)
    (hleafB : ∀ l ∈ (bs.getD i default).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs)
    (hltB : ∀ l ∈ (bs.getD i default).fvarLeaves, l.1 < n)
    {aa ba : AnnotTerm}
    (haa : denoteMeta m.acval env φ k (as.getD i default) = some aa)
    (hbaR : denoteMeta m.acval env φ k (bs.getD i default) = some ba)
    (hga : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ aa)
    (hgb : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ba)
    {ρ : Nat → V} (hsat : Sat V Δa ρ) :
    interp V ρ aa = interp V ρ ba :=
  defEqAt_of_run hclaims hΔlen hshape hws hdoms hent hokA
    (defEqListOk_getD hruns i hi) hwa hba hLa hwb hbb hLb hleafA hltA hleafB hltB
    haa hbaR hga hgb hsat

end ConLeche.Model
