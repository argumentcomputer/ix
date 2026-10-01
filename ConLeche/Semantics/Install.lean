module

public import ConLeche.Semantics.Canon
import ConLeche.Semantics.WellDenoted
import ConLeche.Verify.EnvGuards
public import ConLeche.Verify.Denote.Install

@[expose] public section

/-!
# The `acval` install algebra — the install tier's V-free half

*(Re-based to `ConLeche/SetBase/*` at THE SEPARATION's S2, task #161.
The module's own title says it: this is the V-free half, and the one
theorem that does mention `V` (`acvalWith_wellDenoted`) takes `WellDenoted` as a
hypothesis and returns it — no `EnvS`, no `EnvModel`.  Its
`Annot/EnvModel` import was transitive cover for four base facts
(`natLitSupported_inv`, `strLitSupported_inv`, `cvalWith_{ne,self}`),
which it now takes directly.  Path and module name changed;
namespaces, statements and proofs verbatim.)*

The keys survey (task: the six install keys over `interp`) found
that the `EnvModel` delta over `EnvS` is **six syntactic fields and
two semantic ones** (seven syntactic before the cleanup seal withdrew
`cval_annot`): `acval` (data), `acval_erase`, `acval_closed`,
`acval_params`, `acval_defn` and `acval_thm` mention no
`V` at all, while only `acval_wellDenoted` and `mem_type2` do.  So the first
thing the install tier needs is not semantics — it is the *algebra*
of extending a canonical annotated valuation at one fresh name, and
the fact that extending it there moves nothing already denoted.

That is this file, and it is the exact mirror of what
`ConLeche/Verify/Denote/Install.lean` provides on the v1 lane
(`cvalWith`, `cvalWith_ne`, `cvalWith_self`) — except for one lemma
v1 never needed:

**`denoteAnnot_acval_congr`.**  `denote` reads `cval` at *any* name;
`denoteAnnot` reads `acval` only where the environment stores something.
Every constant leaf sits behind `env.find? n = some ci`, and the two
literal spines sit behind `natLitSupported`/`strLitSupported`, whose
inversions produce the stored entries for all seven support names.
So a valuation change confined to a **fresh** name is invisible to
`denoteAnnot` on the old environment — which is what carries `acval_defn`,
`acval_thm` and `mem_type2` for the *already installed* constants
across a new declaration's install.

## What this file deliberately does **not** contain

There is no transport of `acval_defn`/`acval_thm` across the
environment *extension* itself.  On the v1 lane that step is free —
`denote` reads `env` only through `find?`, so a fresh `cons` cannot
change it.  Over `interp` it is not: `denoteAnnot`'s binder clauses call
`sortOfE`/`lamSortE`, which run `inferTypeCore` and `whnf` **in
`env`**, and nothing in the tree says a checker run is stable when the
environment grows.  That is a named gap, not an omission — see the
survey's supplier requests.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name natLitSupported strLitSupported)

universe w

/-! ## The one-name update -/

/-- Extend a canonical annotated valuation at one name — the `acval`
mirror of `cvalWith`. -/
def acvalWith (acval : Name → (Name → Nat) → AnnotTerm) (n : Name)
    (A : (Name → Nat) → AnnotTerm) : Name → (Name → Nat) → AnnotTerm :=
  fun c ψ => if c = n then A ψ else acval c ψ

theorem acvalWith_ne {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm} {c : Name} (h : c ≠ n) :
    acvalWith acval n A c = acval c := by
  funext ψ; simp [acvalWith, h]

theorem acvalWith_self {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm} :
    acvalWith acval n A n = A := by
  funext ψ; simp [acvalWith]

/-! ## `denoteAnnot` reads only what the environment stores -/

/-- **The congruence.**  `denoteAnnot` consults its valuation only at
names the environment stores — every `.const` leaf behind its own
`find?`, the two literal spines behind their support guards.  So two
valuations agreeing on the stored names denote every term alike.

Stated as an equation rather than an implication: the two runs are
`none` together as well, which is what a *fresh* install needs (an
annotation may not exist, and the statement must not silently assume
one does). -/
theorem denoteAnnot_acval_congr {mode : CheckMode}
    {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {fuel : Nat}
    (hag : ∀ n, (env.find? n).isSome = true → acval₁ n = acval₂ n) :
    ∀ (d : Nat) (e : Expr),
      denoteAnnot mode acval₁ env φ fuel d e
        = denoteAnnot mode acval₂ env φ fuel d e := by
  intro d e
  induction d, e using denoteAnnot.induct (env := env) with
  | case1 d u => rw [denoteAnnot, denoteAnnot]
  | case2 d idx ty => rw [denoteAnnot, denoteAnnot]
  | case3 d n us ci hf hlen =>
    rw [denoteAnnot, denoteAnnot, hf]
    dsimp only
    rw [if_pos hlen, if_pos hlen, hag n (by rw [hf]; rfl)]
  | case4 d n us ci hf hlen =>
    rw [denoteAnnot, denoteAnnot, hf]
    dsimp only
    rw [if_neg hlen, if_neg hlen]
  | case5 d n us hf => rw [denoteAnnot, denoteAnnot, hf]
  | case6 d ty body m ihty ihbody =>
    rw [denoteAnnot, denoteAnnot, ihty, ihbody]
  | case7 d ty body m ihty ihbody =>
    rw [denoteAnnot, denoteAnnot, ihty, ihbody]
  | case8 d f a ihf iha => rw [denoteAnnot, denoteAnnot, ihf, iha]
  | case9 d ty val body =>
    rw [denoteAnnot, denoteAnnot]
  | case10 d sn i e ihe => rw [denoteAnnot, denoteAnnot, ihe]
  | case11 d n hsup =>
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hS, -⟩ :=
      natLitSupported_inv hsup
    rw [denoteAnnot, denoteAnnot, if_pos hsup, if_pos hsup,
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hS]; rfl)]
  | case12 d n hsup =>
    rw [denoteAnnot, denoteAnnot, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    obtain ⟨hnat, ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
      hfS, hfO, hfL, hfN, hfC, hfH, hfF, -⟩ :=
      strLitSupported_inv hsup
    obtain ⟨cvN, caps, cv0, i0, j0, cv1, i1, j1, hN, hZ, hSu, -⟩ :=
      natLitSupported_inv hnat
    rw [denoteAnnot, denoteAnnot, if_pos hsup, if_pos hsup,
      hag stringOfListName (by rw [hfO]; rfl),
      hag listNilName (by rw [hfN]; rfl),
      hag listConsName (by rw [hfC]; rfl),
      hag charName (by rw [hfH]; rfl),
      hag charOfNatName (by rw [hfF]; rfl),
      hag natZeroName (by rw [hZ]; rfl),
      hag natSuccName (by rw [hSu]; rfl)]
  | case14 d s hsup =>
    rw [denoteAnnot, denoteAnnot, if_neg hsup, if_neg hsup]
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i => rw [denoteAnnot.eq_def, denoteAnnot.eq_def]
    | sort u => exact absurd rfl (hs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n us => exact absurd rfl (hc n us)
    | forallE ty b m => exact absurd rfl (hpi ty b m)
    | lam ty b m => exact absurd rfl (hlam ty b m)
    | app f a => exact absurd rfl (happ f a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal n => exact absurd rfl (hnat n)
      | strVal s => exact absurd rfl (hstr s)

/-! ## The three syntactic fields, transported

`acval_erase`, `acval_closed` and `acval_params` are conditions on an
install-fixed object with no `denoteAnnot` and no `interp` in them (the
`EnvModel` docstrings say so of the last two).  Each therefore extends by
a case split on the updated name and nothing else. -/

/-- `acval_closed` extends. -/
theorem acvalWith_closed {acval : Name → (Name → Nat) → AnnotTerm}
    {n : Name} {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acval m ψ).liftN 1 k = acval m ψ)
    (hA : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ) :
    ∀ (m : Name) (ψ : Name → Nat) (k : Nat),
      (acvalWith acval n A m ψ).liftN 1 k
        = acvalWith acval n A m ψ := by
  intro m ψ k
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ k
  · rw [acvalWith_ne hm]
    exact h m ψ k

/-- `acval_params` extends across a `cons`: the stored entries are the
old ones plus the installed one, and the new leaf answers for itself.

Note the environment moves here, unlike in the two above — the field
is indexed by `env.find?`.  Freshness is **not** needed: the `cons`
shadows, so the installed entry answers first either way. -/
theorem acvalWith_params {acval : Name → (Name → Nat) → AnnotTerm}
    {env : Env} {c₀ : ConLeche.ConstantInfo}
    {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      env.find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acval m ψ₁ = acval m ψ₂)
    (hA : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂) :
    ∀ (m : Name) (ci : ConLeche.ConstantInfo),
      (⟨c₀ :: env.consts⟩ : Env).find? m = some ci →
      ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
        acvalWith acval c₀.name A m ψ₁
          = acvalWith acval c₀.name A m ψ₂ := by
  intro m ci hf ψ₁ ψ₂ hp
  rw [Env.find?_cons] at hf
  by_cases hm : c₀.name = m
  · rw [if_pos hm] at hf
    obtain rfl := Option.some.inj hf
    subst hm
    rw [acvalWith_self]
    exact hA ψ₁ ψ₂ hp
  · rw [if_neg hm] at hf
    rw [acvalWith_ne (fun hh => hm hh.symm)]
    exact h m ci hf ψ₁ ψ₂ hp

/-! ## The one semantic field that extends for free

`acval_wellDenoted` is one of the two `EnvModel` fields that mention `V` at all,
and it is the one that carries no environment index: it is a fact
about each leaf on its own.  So its extension asks the install for
exactly the new leaf's truthfulness and nothing more.

Its partner `mem_type2` does **not** extend here, and the reason is
worth the contrast: `mem_type2` conditions on a `denoteAnnot` run of the
constant's *type* **in the extended environment**, so its transport
needs the run-stability fact this file names as missing, not a case
split. -/

/-- `acval_wellDenoted` extends. -/
theorem acvalWith_wellDenoted {V : Type w} [SetTheory V]
    {acval : Name → (Name → Nat) → AnnotTerm} {n : Name}
    {A : (Name → Nat) → AnnotTerm}
    (h : ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acval m ψ))
    (hA : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenoted V ρ (A ψ)) :
    ∀ (m : Name) (ψ : Name → Nat) (ρ : Nat → V),
      WellDenoted V ρ (acvalWith acval n A m ψ) := by
  intro m ψ ρ
  by_cases hm : m = n
  · subst hm
    rw [acvalWith_self]
    exact hA ψ ρ
  · rw [acvalWith_ne hm]
    exact h m ψ ρ

end ConLeche.Semantics
