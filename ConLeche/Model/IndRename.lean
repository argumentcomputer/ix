module

public import ConLeche.Model.IndZipField
import ConLeche.Model.Annot.BitRename
public section

/-!
# The block renaming, at the reading (task #161, IND TIER part 4)

`RenameOkT`/`denote_renameConsts`/`RenEqT.denote`
(`Verify/Denote/Rename.lean`) at `denoteMeta`/`AnnotTerm`, and the
establishment of the P condition at the provisional environment
(`blockRenameOkT`'s twin).

**Why the resolving form already in the tree does not suffice.**
`Annot/BitRename.lean` proves `denoteMeta_renameConsts_resolve` under the
*first and third* `RenameOkT` conjuncts plus a `constsResolve` side
condition on the subject, and its own docstring records why: at the
member install the renamed name is **not stored yet**, so the full
`RenameOkT` is unavailable there.  At the **iota** install it is
available — the whole block is provisioned before any rule fires, which
is precisely what `provisionRecsPM` is for — and the zipper's prefix
branch needs the unconditional form, because the expressions it renames
are frame *openers'* annotations, for which no `constsResolve` is in
hand.  So this file adds the unconditional law under the whole
condition, at the reading.

`RenameOk`'s third conjunct is exactly what `BlockAcvalInstalled`
stores — an installed member's leaf *is* its model's — so
`blockRenameOk` is `blockRenameOkT`'s twin with the valuation clause
read off the annotated invariant rather than the collapse-lane one.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo)

universe w

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The renaming condition at the reading** (`RenameOkT`): every
renamed constant resolves with the same level parameters, unresolved
names stay unresolved, and the *annotated* valuation agrees on the
renaming. -/
@[expose] def RenameOk (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (f : Name → Name) : Prop :=
  (∀ n ci, env.find? n = some ci → ∃ ci', env.find? (f n) = some ci' ∧
    ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams) ∧
  (∀ n, env.find? n = none → env.find? (f n) = none) ∧
  (∀ (n : Name) (ψ : Name → Nat), acval (f n) ψ = acval n ψ)
  -- (the W3 tower-freeness conjunct is gone with W5's `renameConsts`
  -- fix — see `RenameOkT`)

/-- **Renaming is invisible to the reading** (`denote_renameConsts`).
Clause for clause; the `fvar`, `lit` and `proj` clauses are the cheap
ones for the same reason as in v1 — the reading never consults an
`fvar`'s annotation or a `proj`'s structure name, and `renameConsts`
does not descend into literals. -/
theorem denoteMeta_renameConsts {f : Name → Name}
    (hro : RenameOk acval env f) :
    ∀ (e : Expr) (d : Nat),
      denoteMeta acval env φ d (e.renameConsts f) = denoteMeta acval env φ d e
  | .bvar _, _ => by simp [Expr.renameConsts]
  | .sort _, _ => by simp [Expr.renameConsts]
  | .fvar _ _, _ => by simp [Expr.renameConsts, denoteMeta_fvar]
  | .lit (.natVal _), _ => by rw [Expr.renameConsts]
  | .lit (.strVal _), _ => by rw [Expr.renameConsts]
  | .const n ws, d => by
    simp only [Expr.renameConsts]
    cases hf : env.find? n with
    | none =>
      rw [denoteMeta, denoteMeta, hf, hro.2.1 n hf]
    | some ci =>
      obtain ⟨ci', hf', hlp⟩ := hro.1 n ci hf
      rw [denoteMeta, denoteMeta, hf, hf']
      dsimp only
      rw [hlp]
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal, if_pos hal, hro.2.2]
      · rw [if_neg hal, if_neg hal]
  | .app g a, d => by
    simp only [Expr.renameConsts, denoteMeta_app,
      denoteMeta_renameConsts hro g d, denoteMeta_renameConsts hro a d]
  | .proj s i e, d => by
    -- the struct name is fixed under renaming, so both readings
    -- consult the same entry
    simp only [Expr.renameConsts, denoteMeta_proj, denoteMeta_renameConsts hro e d]
  | .forallE ty body m, d => by
    simp only [Expr.renameConsts, denoteMeta_forallE]
    rw [← Expr.renameConsts_instantiate1]
    rw [denoteMeta_renameConsts hro ty d,
      denoteMeta_renameConsts hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .lam ty body m, d => by
    simp only [Expr.renameConsts, denoteMeta_lam]
    rw [← Expr.renameConsts_instantiate1]
    rw [denoteMeta_renameConsts hro ty d,
      denoteMeta_renameConsts hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .letE ty val body, d => by
    simp only [Expr.renameConsts]
    rw [denoteMeta, denoteMeta]
  termination_by e => e.sizeB
  decreasing_by
    all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

/-- **Renamed-equal expressions read equally** (`RenEqT.denote`). -/
theorem RenEqT.denoteMeta {f : Name → Name} (hro : RenameOk acval env f)
    {e₁ e₂ : Expr} (h : RenEqT f e₁ e₂) (d : Nat) :
    denoteMeta acval env φ d e₂ = denoteMeta acval env φ d e₁ := by
  rw [← denoteMeta_erasedEq h d]
  exact denoteMeta_renameConsts hro e₁ d

/-! ## The condition, established at the provisional environment -/

/-- **The block renaming is sound at the provisional environment, at
the reading** (`blockRenameOkT`'s twin).  The two `find?` conjuncts are
V-free and come from `BlockInstalledTT` exactly as in v1; the valuation
conjunct is `BlockAcvalInstalled` — an installed member's *leaf* is its
model's — which is what the annotated invariant stores in place of v1's
`cval` clause.

`hnames` is the same premise v1 takes and for the same reason: a block
name that is *not yet stored* would have its model looked up as if it
were, and the second conjunct would be false. -/
theorem blockRenameOk {blockNames : List Name} {cval : TConstVal}
    (hIS : BlockInstalledTT blockNames env cval)
    (hIA : BlockAcvalInstalled blockNames env acval)
    (hnames : ∀ n, blockNames.contains n = true →
      (env.find? n).isSome = true) :
    RenameOk acval env (fun n =>
      if blockNames.contains n then n.str "_model" else n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ciS hfS
    dsimp only
    by_cases hc : blockNames.contains n = true
    · rw [if_pos hc]
      obtain ⟨cvmS, mvalS, hmS, hfmS, hlpsS, -, -⟩ := hIS n hc ciS hfS
      exact ⟨.defnInfo cvmS mvalS hmS, hfmS, hlpsS⟩
    · rw [if_neg hc]
      exact ⟨ciS, hfS, rfl⟩
  · intro n hfS
    dsimp only
    by_cases hc : blockNames.contains n = true
    · have := hnames n hc
      rw [hfS] at this
      exact nomatch this
    · rw [if_neg hc]
      exact hfS
  · intro n ψ
    dsimp only
    by_cases hc : blockNames.contains n = true
    · rw [if_pos hc]
      rcases hfS : env.find? n with _ | ciS
      · have := hnames n hc
        rw [hfS] at this
        exact nomatch this
      · exact hIA n hc ciS hfS ψ
    · rw [if_neg hc]

end ConLeche.Model
