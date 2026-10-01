module

import ConLeche.Verify.InstLevels
public import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.EnvModel

public section

/-!
# The level crossing for `denoteMeta`: algebra, outright (task #161, P3)

`Steps/Levels.lean` factored the canonical reading's level crossing
(`Denote2InstLevels`) into algebra plus **two open checker
metatheorems** — `SortOfEInstLevels`/`LamSortEInstLevels`, "inference
and head normalisation commute with level instantiation" — refuted as
stated over a bare `Env` (`Steps/LevelsInst.lean`), repaired under
`EnvWF`, and still residues.

For the validated-annotation reading the crossing **is** the algebra:
`denoteMeta` runs no checker function, its binder numerals ride the metas
that `Expr.instantiateLevelParams` pushes `Level.substPW` through, and
`PropWhen.holds_substPW` says the pushed datum reads out the composed
valuation's bit.  So the theorem below is

* **unconditional** — no checker residue, no `EnvWF`, and
* an **equality** — not `Denote2InstLevels`' one-directional
  implication with `∃ F' ≥ F` fuel slack; there is no fuel, and no run
  that instantiation could make succeed or fail asymmetrically.

This is the P3 pivot's first full payoff, measured: what was two open
metatheorems plus a conditional induction is one proved walk.

Lives in `Model/Annot/` since task #305 closing (it was
`Model/Steps/BitLevels.lean`; nothing in it is stated over a run).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ### The literal-support slot lemmas, transposed to the core

`Steps/Levels.lean`'s `acval_isEmpty`/`acval_oneParam`/`acval_scalar`/
`acval_one`/`acval_natPair` are stated over `EnvModelUM`; each reads the
`acval_params` field and nothing else, so each re-proves verbatim over
`EnvModel` (batch 8 — the canonical file stays untouched). -/

/-- A parameter-free slot is valued independently of the assignment. -/
theorem acval_isEmpty (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval n ψ₁ = m.acval n ψ₂ := by
  refine m.acval_params n ci hf ψ₁ ψ₂ fun p hpm => ?_
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment. -/
theorem acval_oneParam (m : EnvModel V env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval n (Level.substFn ψ₁ ci.toConstantVal.levelParams [.zero])
      = m.acval n
        (Level.substFn ψ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine m.acval_params n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p
    hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- The scalar literal-support slots, read off their shape guards. -/
theorem acval_scalar (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : m.acval nm ψ₁ = m.acval nm ψ₂ := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    rw [hx] at hfok
    exact acval_isEmpty m hx (hshape ci hfok) _ _

/-- The two one-parameter literal-support slots. -/
theorem acval_one (m : EnvModel V env) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    m.acval nm (Level.substFn ψ₁ (levelParamsAt env nm) [.zero])
      = m.acval nm
        (Level.substFn ψ₂ (levelParamsAt env nm) [.zero]) := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    have hlp : levelParamsAt env nm = ci.toConstantVal.levelParams := by
      simp [levelParamsAt, hx]
    rw [hx] at hfok
    rw [hlp]
    exact acval_oneParam m hx (hshape ci hfok) _ _

/-- The `Nat`-literal leaves are assignment-independent. -/
theorem acval_natPair (m : EnvModel V env)
    (hg : ConLeche.natLitSupported env = true) (ψ₁ ψ₂ : Name → Nat) :
    m.acval natZeroName ψ₁ = m.acval natZeroName ψ₂ ∧
      m.acval natSuccName ψ₁ = m.acval natSuccName ψ₂ := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hz⟩, hs⟩ := hg
  refine ⟨acval_scalar m natZeroName natZeroOk hz rfl ?_ _ _,
    acval_scalar m natSuccName natSuccOk hs rfl ?_ _ _⟩
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natZeroOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natZeroOk] at h
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [natSuccOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [natSuccOk] at h

/-- **The level crossing for `denoteMeta`, unconditional and exact**:
reading an instantiated term at `φ` is reading the term at the
composed valuation `Level.substFn φ ks us`.  The binder step is
`pwBit_substPW` (i.e. `PropWhen.holds_substPW`); the constant step is
`EnvModel.acval_params` + `Level.substFn_map_subst`, as in the canonical
walk. -/
theorem denotePInstLevels (m : EnvModel V env)
    (φ : Name → Nat) (ks : List Name) (us : List Level) :
    ∀ (d : Nat) (e : Expr),
      denoteMeta m.acval env φ d (e.instantiateLevelParams ks us)
        = denoteMeta m.acval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, Level.eval_subst]
  | case2 d idx ty =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta]
  | case3 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_pos hlen, if_pos (by simpa using hlen)]
    exact congrArg some
      (m.acval_params n ci hf _ _ fun p hp =>
        Level.substFn_map_subst hlen hp)
  | case4 d n vs ci hf hlen =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
    dsimp only
    rw [if_neg hlen, if_neg (by simpa using hlen)]
  | case5 d n vs hf =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, hf]
  | case6 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case7 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      ← Expr.instantiateLevelParams_instantiate1 ks us body 0,
      ihty, ihbody]
    simp only [pwBit_substPW]
  | case8 d fe a ihf iha =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, ihf, iha]
  | case9 d ty val body =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, ihe]
  | case11 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn (Level.substFn φ ks us) [] [])
      (Level.substFn φ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      (Level.substFn φ ks us) φ
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta,
      if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    cases x with
    | bvar i =>
      rw [Expr.instantiateLevelParams, denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

/-- **The reading's φ-congruence at the expression's own parameters**
(`denote_params_ext`'s mirror; the harvest layer's `hAparams`
supplier).  The one new step against the v1 walk is the binder
numeral: `PropWhen.holds_ext` at the meta's `paramsDefined` conjunct —
which is exactly why task #161 folded the datum's footprint into
`Expr.allLevelParamsDefined`. -/
theorem denoteMeta_params_ext (m : EnvModel V env)
    {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Expr), e.allLevelParamsDefined ps = true →
      denoteMeta m.acval env φ₁ d e = denoteMeta m.acval env φ₂ d e := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro hd
    rw [denoteMeta, denoteMeta,
      Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hd) hφ]
  | case2 d idx ty => intro _; rw [denoteMeta, denoteMeta]
  | case3 d n us ci h1 h2 =>
    intro hd
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_pos h2, if_pos h2]
    refine congrArg _ (m.acval_params n ci h1 _ _ fun p hpm => ?_)
    refine Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _
    rw [denoteMeta, denoteMeta, h1]
    dsimp only
    rw [if_neg h2, if_neg h2]
  | case5 d n us h1 => intro _; rw [denoteMeta, denoteMeta, h1]
  | case6 d ty body mb ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (ConLeche.Expr.allLevelParamsDefined_instantiate1 hd.1.1 0
        hd.1.2)]
    simp only [hpw]
  | case7 d ty body mb ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    have hpw : pwBit φ₁ mb.pw = pwBit φ₂ mb.pw := by
      unfold pwBit
      rw [ConLeche.PropWhen.holds_ext hd.2 hφ]
    rw [denoteMeta, denoteMeta, ← ihty hd.1.1,
      ← ihbody (ConLeche.Expr.allLevelParamsDefined_instantiate1 hd.1.1 0
        hd.1.2)]
    simp only [hpw]
  | case8 d fe a ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denoteMeta, denoteMeta, ← ihf hd.1, ← iha hd.2]
  | case9 d ty val body =>
    intro _
    rw [denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    intro hd
    rw [denoteMeta, denoteMeta,
      ← ihe (by simpa [Expr.allLevelParamsDefined] using hd)]
  | case11 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    obtain ⟨ez, es⟩ := acval_natPair m hsup
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    rw [ez, es]
  | case12 d k hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case13 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_pos hsup, if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acval_natPair m h0
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have esol := acval_scalar m stringOfListName stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have echar := acval_scalar m charName charTyOk h6 rfl
      (by intro ci hh
          simp only [charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have eofn := acval_scalar m charOfNatName charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ₁ [] []) (Level.substFn φ₂ [] [])
    have enil := acval_one m listNilName listNilTyOk h4 rfl
      (by intro ci hh
          simp only [listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    have econs := acval_one m listConsName listConsTyOk h5 rfl
      (by intro ci hh
          simp only [listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ₁ φ₂
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    intro _
    rw [denoteMeta, denoteMeta, if_neg hsup, if_neg hsup]
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro _
    cases x with
    | bvar i => rw [denoteMeta.eq_def, denoteMeta.eq_def]
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b mb => exact absurd rfl (hpi ty b mb)
    | lam ty b mb => exact absurd rfl (hlam ty b mb)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Model
