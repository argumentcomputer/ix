module

public import ConLeche.Semantics.Tower.TowerLeaf
public import ConLeche.Verify.Denote

@[expose] public section

/-!
# Canonical annotations (task #151 tier C — the R1 resolution of WALL 3)

`denoteAnnot` is `denote` fused with the checker's *own* sort computation:
each binder numeral is the sort `inferTypeCore` + `whnf` produce — the
#100-stage-6 annotate pass resurrected **at the metatheory level**.
It is a definition in the proof development, never run by the binary:
zero runtime cost, and being a *function* it is coherent by
construction — two annotation threads meeting at one term in one
context carry the same numerals, which is what WALL 3 demanded and no
relational invariant could supply.

The stored-constant leaves come from the **canonical annotated
valuation** `acval` (an `EnvModel`-side object fixed at install), so
`denoteAnnot` is parametric in it exactly as `denote` is in `cval`; the
erasure law (`denoteAnnot_erase`) links the two levels pointwise under the
valuation-side link.

Sort computations live in `sortOfE` (the type's sort: infer, then
whnf to a sort, then evaluate the ground level) and the λ clause's
`lamSortE` (the *body type's* sort — the #152 chain fact, per node
here because the metatheory pays no interning cost).

The load-bearing piece — **the stability metatheorem** (canonicity
survives the checker's own substitutions and reductions, the
sort-level fragment of subject reduction over ground numerals) — is
deliberately NOT in this seal; it is the next one, alone, with its
own STOP condition (a genuine instability counterexample would be a
design finding, not a proof gap).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level inferTypeCore whnf
  natLitSupported strLitSupported)

/-- The sort of `e`'s **type**, as the checker computes it: infer,
whnf to a sort, evaluate the ground level. -/
def sortOfE (mode : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel d : Nat) (e : Expr) : Option Nat :=
  match (inferTypeCore mode env fuel d e).toOption with
  | none => none
  | some t =>
    match (whnf mode env fuel d t).toOption with
    | some (.sort ℓ) => some (ℓ.eval φ)
    | _ => none

/-- The λ-body's codomain sort: the sort of the body's *type* — the
#152 chain fact, computed per node. -/
def lamSortE (mode : CheckMode) (env : Env) (φ : Name → Nat)
    (fuel d : Nat) (body : Expr) : Option Nat :=
  match (inferTypeCore mode env fuel d body).toOption with
  | none => none
  | some bt => sortOfE mode env φ fuel d bt

/-- The annotated `Nat`-literal spine (the `natLitT` mirror over the
annotated valuation). -/
def natLitAV (za sa : AnnotTerm) : Nat → AnnotTerm
  | 0 => za
  | n + 1 => .app sa (natLitAV za sa n)

/-- The annotated character-list spine (the `charListT` mirror). -/
def charListAV (nilA consA ofNatA za sa : AnnotTerm) :
    List Char → AnnotTerm
  | [] => nilA
  | c :: cs =>
    .app (.app consA (.app ofNatA (natLitAV za sa c.toNat)))
      (charListAV nilA consA ofNatA za sa cs)

/-- The uniform projection spellings erase onto each other:
`projAV`'s image is `projNV` (task #175 wiring W3). -/
theorem erase_projAV : ∀ (i : Nat) (ea : AnnotTerm),
    (projAV i ea).erase = ConLeche.Verify.projNV i ea.erase
  | 0, _ => rfl
  | i + 1, ea => erase_projAV i (.snd ea)

/-- The canonical annotation pass: `denote` with every binder numeral
computed by the checker's own functions and every constant leaf drawn
from the canonical annotated valuation.  Clause for clause the
`denote` recursion (`ConLeche/Verify/Denote.lean`), so the two erase
pointwise (`denoteAnnot_erase`). -/
def denoteAnnot (mode : CheckMode) (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (fuel : Nat) :
    (d : Nat) → Expr → Option AnnotTerm
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (acval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE ty body _m => do
    let ta ← denoteAnnot mode acval env φ fuel d ty
    let ba ← denoteAnnot mode acval env φ fuel (d + 1)
      (body.instantiate1 (.fvar d ty))
    let u ← sortOfE mode env φ fuel d ty
    let v ← sortOfE mode env φ fuel (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.pi u v ta ba)
  | d, .lam ty body _m => do
    let ta ← denoteAnnot mode acval env φ fuel d ty
    let ba ← denoteAnnot mode acval env φ fuel (d + 1)
      (body.instantiate1 (.fvar d ty))
    let v ← lamSortE mode env φ fuel (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.lam v ta ba)
  | d, .app f a => do
    let fa ← denoteAnnot mode acval env φ fuel d f
    let aa ← denoteAnnot mode acval env φ fuel d a
    some (.app fa aa)
  | _, .letE _ _ _ =>
    -- **`none` by design** (task #241); see `denoteMeta`'s clause
    none
  | d, .proj sn i e => do
    let ea ← denoteAnnot mode acval env φ fuel d e
    -- the entry-kind branch (task #175 wiring W3), clause-parallel
    -- with `denote` and `denoteMeta`
    match env.findProj? sn i with
    | some entry => some (projAV (i + entry.off) ea)
    | none => AnnotTerm.projPair? i ea
  | _, .lit (.natVal n) =>
    if natLitSupported env then
      some (natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    if strLitSupported env then
      some (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListAV
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList))
    else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ## The erasure law

`denoteAnnot` erases to `denote`, pointwise under the valuation link: the
canonical annotation is an annotation *of the denotation*, exactly. -/

/-- The literal spines erase pointwise. -/
theorem natLitAV_erase {za sa : AnnotTerm} {zv sv : Term}
    (hz : za.erase = zv) (hs : sa.erase = sv) :
    ∀ n : Nat, (natLitAV za sa n).erase = natLitT zv sv n := by
  intro n
  induction n with
  | zero => exact hz
  | succ m ih => simp [natLitAV, natLitT, hs, ih]

theorem charListAV_erase {nilA consA ofNatA za sa : AnnotTerm}
    {nilV consV ofNatV zv sv : Term}
    (h1 : nilA.erase = nilV) (h2 : consA.erase = consV)
    (h3 : ofNatA.erase = ofNatV) (hz : za.erase = zv)
    (hs : sa.erase = sv) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).erase
        = charListT nilV consV ofNatV zv sv cs := by
  intro cs
  induction cs with
  | nil => exact h1
  | cons c cs ih =>
    simp [charListAV, charListT, h2, h3, ih, natLitAV_erase hz hs]

/-- **The erasure law**: the canonical annotation is an annotation of
the denotation, exactly (no ζ slack — `denoteAnnot`'s `letE` clause is
structural). -/
theorem denoteAnnot_erase {mode : CheckMode}
    {acval : Name → (Name → Nat) → AnnotTerm} {cval : TConstVal}
    {env : Env} {φ : Name → Nat} {fuel : Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ) :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteAnnot mode acval env φ fuel d e = some ea →
      denote cval env φ d e = some ea.erase := by
  intro d e
  induction d, e using denoteAnnot.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denoteAnnot] at h
    obtain rfl := Option.some.inj h
    rw [denote_sort]
    rfl
  | case2 d idx ty =>
    intro ea h
    rw [denoteAnnot] at h
    obtain rfl := Option.some.inj h
    rw [denote_fvar]
    rfl
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denoteAnnot, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    rw [denote_const, hf]
    dsimp only
    rw [if_pos hlen, hlink]
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denoteAnnot, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denoteAnnot, hf] at h
    exact nomatch h
  | case6 d ty body m ihty ihbody =>
    intro ea h
    rw [denoteAnnot] at h
    rcases hta : denoteAnnot mode acval env φ fuel d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteAnnot mode acval env φ fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hu : sortOfE mode env φ fuel d ty with _ | u
    · rw [hu] at h; exact nomatch h
    rw [hu] at h
    rcases hv : sortOfE mode env φ fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain rfl := Option.some.inj h
    rw [denote_forallE, ihty hta, ihbody hba]
    rfl
  | case7 d ty body m ihty ihbody =>
    intro ea h
    rw [denoteAnnot] at h
    rcases hta : denoteAnnot mode acval env φ fuel d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteAnnot mode acval env φ fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    rcases hv : lamSortE mode env φ fuel (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | v
    · rw [hv] at h; exact nomatch h
    rw [hv] at h
    obtain rfl := Option.some.inj h
    rw [denote_lam, ihty hta, ihbody hba]
    rfl
  | case8 d f a ihf iha =>
    intro ea h
    rw [denoteAnnot] at h
    rcases hfa : denoteAnnot mode acval env φ fuel d f with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteAnnot mode acval env φ fuel d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain rfl := Option.some.inj h
    rw [denote_app, ihf hfa, iha haa]
    rfl
  | case9 d ty val body =>
    intro ea h
    rw [denoteAnnot] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea h
    rw [denoteAnnot] at h
    rcases hea : denoteAnnot mode acval env φ fuel d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    replace h : (match env.findProj? sn i with
        | some entry => some (projAV (i + entry.off) ea')
        | none => AnnotTerm.projPair? i ea')
          = some ea := h
    rw [denote_proj, ihe hea]
    dsimp only
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h ⊢
      obtain rfl := Option.some.inj h
      rw [erase_projAV]
    | none =>
      rw [hfp] at h
      dsimp only at h ⊢
      match i with
      | 0 =>
        obtain rfl := Option.some.inj h
        rfl
      | 1 =>
        obtain rfl := Option.some.inj h
        rfl
      | _ + 2 => exact nomatch h
  | case11 d n hsup =>
    intro ea h
    rw [denoteAnnot, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_natLit, if_pos hsup,
      natLitAV_erase (hlink _ _) (hlink _ _)]
  | case12 d n hsup =>
    intro ea h
    rw [denoteAnnot, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denoteAnnot, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_strLit, if_pos hsup]
    refine congrArg some ?_ |>.symm
    show Term.app _ _ = _
    rw [ConLeche.Verify.strLitT]
    congr 1
    · exact hlink _ _
    · refine charListAV_erase ?_ ?_ (hlink _ _) (hlink _ _)
        (hlink _ _) s.toList
      · show Term.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
      · show Term.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
  | case14 d s hsup =>
    intro ea h
    rw [denoteAnnot, if_neg hsup] at h
    exact nomatch h
  | case15 d x hs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i =>
      rw [denoteAnnot.eq_def] at h
      exact nomatch h
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

end ConLeche.Semantics
