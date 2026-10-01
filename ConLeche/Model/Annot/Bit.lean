module

public import ConLeche.Semantics.Canon
import ConLeche.Verify.PropWhen
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# `denoteMeta` — the validated-annotation reading (task #161, P3)

`denoteMeta` is the pw-driven sibling of `denoteAnnot` (`Annot/Canon.lean`):
clause for clause the same recursion, with every binder numeral read
off the term's **own validated annotation** — `pwBit φ m.pw`, the
datum's zero bit at the ground valuation — instead of `denoteAnnot`'s
`sortOfE`/`lamSortE` checker runs.

The consequences are the P3 pivot in miniature:

* **No fuel, no mode.**  `denoteMeta` runs no checker function, so the
  parameters that existed only to feed `sortOfE` are gone, and every
  lemma about it is fuel-slack-free.
* **The level crossing is algebra.**  Where `Denote2InstLevels` is a
  residue riding two *open* checker metatheorems
  (`SortOfEInstLevels`/`LamSortEInstLevels`, "inference and head
  normalisation commute with level instantiation" — false as stated,
  repaired only under `EnvWF`, still unproven), `denoteMeta`'s crossing
  is `PropWhen.holds_substPW` at each binder: **proved outright**
  (`Steps/BitLevels.lean`, `denotePInstLevels`).
* **The bit is canonical.**  `pwBit` lands in `{0, 1}`, so two data
  that agree on zero-ness produce *equal* numerals — the
  `piR_zero_agree`/`lamR_zero_agree` step is `rfl`-shaped where the
  canonical lane needed sort-agreement residues (`BinderSortAgree2`,
  residue 9): the checker's own P2 validation sites
  (`(defeq-forall)`/`(defeq-lam)`/`(eta)`) compare the data with
  `==` (equality of canonical data) exactly where the run lemmas open two annotations at one
  index.

**The `pi` `u`-slot.**  `AnnotTerm.pi` carries a domain-sort numeral `u`
that `interp` and `WellDenoted` never read (`interp_pi` matches `.pi _
v A B`; `DefEq`'s congruence rows hold at `u ≠ u'`).  Amendment 1
deliberately dropped the domain datum from the input language, so
`denoteMeta` fills the slot with `0`.  If any consumer downstream turns
out to *read* `u`, that is a named finding against the prop-only
amendment, not a plumbing gap.

API discipline (task #161 ruling): `PropWhen` is consumed only through
`holds` and the named battery laws — `pwBit` is `holds` composed with
a two-point test, and every lemma below factors through
`zeronessOf_sound` / `holds_substPW`; a validated or compared datum
is *equal* to its counterpart (task #197), so no transport lemma is
needed.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-! ## The regime bit -/

/-- The regime numeral a validated datum contributes at a ground
valuation: `0` (the squash regime) exactly when the datum holds —
"the codomain is a proposition here" — and `1` otherwise.  The value
`1` is arbitrary; `interp` reads binder numerals only through the
`v = 0` test (`piR_zero_agree`/`lamR_zero_agree`). -/
@[expose] def pwBit (φ : Name → Nat) (pw : PropWhen) : Nat :=
  if pw.holds φ then 0 else 1

@[simp] theorem pwBit_eq_zero_iff {φ : Name → Nat} {pw : PropWhen} :
    pwBit φ pw = 0 ↔ pw.holds φ = true := by
  unfold pwBit; split <;> simp_all

theorem pwBit_ne_zero_iff {φ : Name → Nat} {pw : PropWhen} :
    pwBit φ pw ≠ 0 ↔ pw.holds φ = false := by
  rw [Ne, pwBit_eq_zero_iff]
  simp

/-! ### The io gate's exactness (task #161 bucket 2)

The kernel's licensed check-skips test `PropWhen.isNever` — the one
thing about a datum a kernel can decide without a valuation.  The
sealed claims split on `pwBit φ pw = 0` at the *ambient* valuation.
The two lemmas below are the receipt that the gate's condition is the
**∀-`φ` uniform version of the claims' positive branch, exactly** —
sound (a gated site is positive at every valuation, so the claim's
cert-free arm applies) and complete (no other datum is positive at
every valuation, so the gate cannot be widened without leaving the
licensed branch).

Landed at stage 1 on `agent/bucket2-s1` (commit `0c865695`) and
re-landed here verbatim: the exactness is a fact about the datum, not
about which site reads it, so it serves the io lane's application
clause (`inferBodyIO`) and any future β-cert gate alike. -/

/-- **Soundness of the gate's condition**: a `never` datum is positive
at every valuation. -/
theorem pwBit_ne_zero_of_isNever {pw : PropWhen}
    (h : ConLeche.PropWhen.isNever pw = true) (φ : Name → Nat) :
    pwBit φ pw ≠ 0 := by
  cases pw with
  | never => rw [pwBit_ne_zero_iff]; rfl
  | ifAllZero ps => simp at h

/-- **Exactness of the gate's condition**: `never` is *the* datum that
is positive at every valuation — an `ifAllZero` datum lands in the
squash regime at the all-zero valuation, where the certificate is
consumed and the skip would be unlicensed. -/
theorem isNever_iff_forall_pwBit_ne_zero {pw : PropWhen} :
    ConLeche.PropWhen.isNever pw = true ↔ ∀ φ : Name → Nat, pwBit φ pw ≠ 0 := by
  constructor
  · exact pwBit_ne_zero_of_isNever
  · intro h
    cases pw with
    | never => rfl
    | ifAllZero ps =>
      exact absurd (pwBit_eq_zero_iff.mpr
        (by simp)) (h (fun _ => 0))

/-- **The establishment reading**: the datum the checker validated
against a computed codomain sort is `zeronessOf v` itself (the run
inversions' conjunct `Level.zeronessOf v = m.pw` — an equality, since
the datum is canonical, task #194/#197), and its bit is the sort's
true zero bit. -/
theorem pwBit_zeronessOf (φ : Name → Nat) (v : Level) :
    (pwBit φ (Level.zeronessOf v) = 0 ↔ Level.eval φ v = 0) := by
  rw [pwBit_eq_zero_iff, ConLeche.PropWhen.zeronessOf_sound]
  simp

/-- **The crossing reading**: the instantiated datum's bit at `φ` is
the datum's bit at the composed valuation — `denotePInstLevels`'
binder step. -/
theorem pwBit_substPW (φ : Name → Nat) (ks : List Name)
    (vs : List Level) (pw : PropWhen) :
    pwBit φ (Level.substPW ks vs pw) = pwBit (Level.substFn φ ks vs) pw := by
  unfold pwBit
  rw [ConLeche.Level.holds_substPW]

/-! ## The reading -/

/-- The validated-annotation reading: `denoteAnnot`'s recursion with every
binder numeral read off the term's own meta (`pwBit φ m.pw`) — no
checker runs, no fuel, no mode.  See the module docstring for the
`pi` `u`-slot convention. -/
@[expose] def denoteMeta (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) :
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
  | d, .forallE ty body m => do
    let ta ← denoteMeta acval env φ d ty
    let ba ← denoteMeta acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.pi 0 (pwBit φ m.pw) ta ba)
  | d, .lam ty body m => do
    let ta ← denoteMeta acval env φ d ty
    let ba ← denoteMeta acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.lam (pwBit φ m.pw) ta ba)
  | d, .app f a => do
    let fa ← denoteMeta acval env φ d f
    let aa ← denoteMeta acval env φ d a
    some (.app fa aa)
  | _, .letE _ _ _ =>
    -- **`none` by design** (task #241).  `AnnotTerm` has no `letE`
    -- former, and it needs none: the checker's own `letE` arms are
    -- positive errors, so an accepting run never reaches this clause
    -- (`inferTypeCore_letE_inv`).
    none
  | d, .proj sn i e => do
    let ea ← denoteMeta acval env φ d e
    -- the entry-kind branch (task #175 wiring W3): a tower-backed
    -- entry reads field `i` by the uniform iterated spelling
    -- (`projAV`, whose `WellDenoted`/substitution batteries are the
    -- introduction machinery's); the pair/absent side is the pre-W3
    -- clause
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

`denoteMeta` erases to `denote` exactly as `denoteAnnot` does
(`denoteAnnot_erase`): the annotations differ between the two readings,
the denotation does not. -/

/-- The validated-annotation reading is an annotation of the
denotation, exactly. -/
theorem denoteMeta_erase {acval : Name → (Name → Nat) → AnnotTerm}
    {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ) :
    ∀ (d : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta acval env φ d e = some ea →
      denote cval env φ d e = some ea.erase := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    rw [denote_sort]
    rfl
  | case2 d idx ty =>
    intro ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    rw [denote_fvar]
    rfl
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_pos hlen] at h
    obtain rfl := Option.some.inj h
    rw [denote_const, hf]
    dsimp only
    rw [if_pos hlen, hlink]
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [if_neg hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body mb ihty ihbody =>
    intro ea h
    rw [denoteMeta] at h
    rcases hta : denoteMeta acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_forallE, ihty hta, ihbody hba]
    rfl
  | case7 d ty body mb ihty ihbody =>
    intro ea h
    rw [denoteMeta] at h
    rcases hta : denoteMeta acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_lam, ihty hta, ihbody hba]
    rfl
  | case8 d fe a ihf iha =>
    intro ea h
    rw [denoteMeta] at h
    rcases hfa : denoteMeta acval env φ d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteMeta acval env φ d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain rfl := Option.some.inj h
    rw [denote_app, ihf hfa, iha haa]
    rfl
  | case9 d ty val body =>
    intro ea h
    rw [denoteMeta] at h
    exact nomatch h
  | case10 d sn i e ihe =>
    intro ea h
    rw [denoteMeta] at h
    rcases hea : denoteMeta acval env φ d e with _ | ea'
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
  | case11 d k hsup =>
    intro ea h
    rw [denoteMeta, if_pos hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_natLit, if_pos hsup,
      natLitAV_erase (hlink _ _) (hlink _ _)]
  | case12 d k hsup =>
    intro ea h
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denoteMeta, if_pos hsup] at h
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
    rw [denoteMeta, if_neg hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
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
