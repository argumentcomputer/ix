module

public import ConLeche.Model.BasisEmpty

public section

/-!
# `denoteMeta` crosses level instantiation (task #161, ENDGAME G)

The basis tier's remaining bill — twenty type readings and seven
`RecRuleLaw` rows — is stated at *instantiated* subjects:
`RecRuleLaw` reads `rhs.instantiateLevelParams cv.levelParams us` and
`cv.type.instantiateLevelParams cv.levelParams us`, and
`EnvModelM.type_reads` reads the stored type at the identity
substitution.  Walking a substituted tree with the `denoteP_*` clause
equations is possible but miserable: every `.sort` carries a
`Level.subst`, every `.const` a `List.map (Level.subst …)`, and every
binder a `Level.substPW`, so the clause equations no longer see
constructor applications and the `acval_basis_pinned` leaves no longer
match.

The fix is the crossing law, and for `denoteMeta` it is **pure algebra**:

> `denoteMeta acval env φ d (e.instantiateLevelParams ks us)`
> `= denoteMeta acval env (Level.substFn φ ks us) d e`

v1 has it (`denote_instLevels`, `Verify/Denote/Levels.lean`) and the
denoteAnnot tier has it *conditionally* (`denote2_instLevels_of`,
`Steps/Levels.lean`, premised on the checker's two sort computations
commuting with instantiation, which is an open metatheorem).  `denoteMeta`
runs no checker, so neither premise exists and the law is unconditional
— which is one more instance of the reading tier's whole point.

The binder step is `pwBit_substPW`, whose docstring already names this
theorem as its consumer; the constant step is `Level.substFn_map_subst`
under `acval_params`; the two literal clauses are the assignment-
insensitivity of the support slots, restated here off a bare
`acval_params` hypothesis rather than off `EnvModelUM` (`Steps/Levels.lean`
states them at the U carrier, which the P tier does not have).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env}

/-! ## The valuation-leaf side, off a bare `acval_params` -/

/-- A leaf reads only its own level parameters — `EnvModel.acval_params`
as a standalone predicate, so the crossing does not need a carrier. -/
def AcvalParamsAt (env : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      acval n ψ₁ = acval n ψ₂

/-- Every core carrier has it. -/
theorem acvalParamsAt_of_core (m : EnvModel V env) :
    AcvalParamsAt env m.acval := m.acval_params

variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- A stored slot with no level parameters is valued independently of
the assignment (`acval_isEmpty`, off the bare hypothesis). -/
theorem acvalAt_isEmpty (hp : AcvalParamsAt env acval) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : acval n ψ₁ = acval n ψ₂ := by
  refine hp n ci hf ψ₁ ψ₂ fun p hpm => ?_
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment (`acval_oneParam`). -/
theorem acvalAt_oneParam (hp : AcvalParamsAt env acval) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    acval n (Level.substFn ψ₁ ci.toConstantVal.levelParams [.zero])
      = acval n
        (Level.substFn ψ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine hp n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p
    hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- The scalar literal-support slots, read off their shape guards. -/
theorem acvalAt_scalar (hp : AcvalParamsAt env acval) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.isEmpty = true)
    (ψ₁ ψ₂ : Name → Nat) : acval nm ψ₁ = acval nm ψ₂ := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    rw [hx] at hfok
    exact acvalAt_isEmpty hp hx (hshape ci hfok) _ _

/-- The two one-parameter literal-support slots. -/
theorem acvalAt_one (hp : AcvalParamsAt env acval) (nm : Name)
    (f : Option ConstantInfo → Bool) (hfok : f (env.find? nm) = true)
    (hnone : f none = false)
    (hshape : ∀ ci, f (some ci) = true →
      ci.toConstantVal.levelParams.length = 1)
    (ψ₁ ψ₂ : Name → Nat) :
    acval nm (Level.substFn ψ₁ (ConLeche.Verify.levelParamsAt env nm) [.zero])
      = acval nm
        (Level.substFn ψ₂ (ConLeche.Verify.levelParamsAt env nm) [.zero]) := by
  cases hx : env.find? nm with
  | none => rw [hx, hnone] at hfok; exact nomatch hfok
  | some ci =>
    have hlp : ConLeche.Verify.levelParamsAt env nm
        = ci.toConstantVal.levelParams := by
      simp [ConLeche.Verify.levelParamsAt, hx]
    rw [hx] at hfok
    rw [hlp]
    exact acvalAt_oneParam hp hx (hshape ci hfok) _ _

/-- The `Nat`-literal leaves are assignment-independent. -/
theorem acvalAt_natPair (hp : AcvalParamsAt env acval)
    (hg : ConLeche.natLitSupported env = true) (ψ₁ ψ₂ : Name → Nat) :
    acval ConLeche.natZeroName ψ₁ = acval ConLeche.natZeroName ψ₂ ∧
      acval ConLeche.natSuccName ψ₁ = acval ConLeche.natSuccName ψ₂ := by
  simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, hz⟩, hs⟩ := hg
  refine ⟨acvalAt_scalar hp ConLeche.natZeroName ConLeche.natZeroOk hz rfl
      ?_ _ _,
    acvalAt_scalar hp ConLeche.natSuccName ConLeche.natSuccOk hs rfl ?_ _ _⟩
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [ConLeche.natZeroOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [ConLeche.natZeroOk] at h
  · intro ci h
    cases ci with
    | ctorInfo cv a b =>
      simp only [ConLeche.natSuccOk, Bool.and_eq_true] at h
      simpa [ConstantInfo.toConstantVal] using h.1
    | _ => simp [ConLeche.natSuccOk] at h

/-! ## The crossing -/

set_option maxHeartbeats 1000000 in
/-- **`denoteMeta` crosses level instantiation** — unconditionally, since
the reading runs no checker.  v1's `denote_instLevels` clause for
clause, with `pwBit_substPW` at the binders (its docstring's named
consumer) and `AcvalParamsAt` where v1 has `ValParams`. -/
theorem denoteMeta_instLevels (hp : AcvalParamsAt env acval)
    {ks : List Name} {us : List Level} (φ : Name → Nat) :
    ∀ (d : Nat) (e : Expr),
      denoteMeta acval env φ d (e.instantiateLevelParams ks us)
        = denoteMeta acval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denoteMeta.induct
    (env := env) with
  | case1 d u =>
    simp only [Expr.instantiateLevelParams, denoteMeta_sort, Level.eval_subst]
  | case2 d idx ty =>
    simp only [Expr.instantiateLevelParams, denoteMeta_fvar]
  | case3 d n ws ci h1 h2 =>
    rw [Expr.instantiateLevelParams,
      denoteMeta_const h1 (by simpa using h2), denoteMeta_const h1 h2]
    exact congrArg some
      (hp n ci h1 _ _ fun p hpm => Level.substFn_map_subst h2 hpm)
  | case4 d n ws ci h1 h2 =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, h1]
    simp only []
    rw [if_neg h2, if_neg (by simpa using h2)]
  | case5 d n ws h1 =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, h1]
  | case6 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta_forallE, denoteMeta_forallE,
      ihty, pwBit_substPW,
      ← Expr.instantiateLevelParams_instantiate1, ihbody]
  | case7 d ty body mb ihty ihbody =>
    rw [Expr.instantiateLevelParams, denoteMeta_lam, denoteMeta_lam,
      ihty, pwBit_substPW,
      ← Expr.instantiateLevelParams_instantiate1, ihbody]
  | case8 d fe a ihf iha =>
    rw [Expr.instantiateLevelParams, denoteMeta_app, denoteMeta_app, ihf, iha]
  | case9 d ty val body =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta]
  | case10 d sn i e ihe =>
    rw [Expr.instantiateLevelParams, denoteMeta_proj, denoteMeta_proj, ihe]
  | case11 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, if_pos hsup,
      if_pos hsup]
    obtain ⟨ez, es⟩ := acvalAt_natPair hp hsup
      (Level.substFn φ [] []) (Level.substFn (Level.substFn φ ks us) [] [])
    rw [ez, es]
  | case12 d k hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, if_neg hsup,
      if_neg hsup]
  | case13 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, if_pos hsup,
      if_pos hsup]
    have hg := hsup
    simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
    obtain ⟨ez, es⟩ := acvalAt_natPair hp h0
      (Level.substFn φ [] []) (Level.substFn (Level.substFn φ ks us) [] [])
    have esol := acvalAt_scalar hp ConLeche.stringOfListName
      ConLeche.stringOfListTyOk h2 rfl
      (by intro ci hh
          simp only [ConLeche.stringOfListTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ [] []) (Level.substFn (Level.substFn φ ks us) [] [])
    have echar := acvalAt_scalar hp ConLeche.charName ConLeche.charTyOk h6 rfl
      (by intro ci hh
          simp only [ConLeche.charTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ [] []) (Level.substFn (Level.substFn φ ks us) [] [])
    have eofn := acvalAt_scalar hp ConLeche.charOfNatName
      ConLeche.charOfNatTyOk h7 rfl
      (by intro ci hh
          simp only [ConLeche.charOfNatTyOk, Bool.and_eq_true] at hh
          exact hh.1)
      (Level.substFn φ [] []) (Level.substFn (Level.substFn φ ks us) [] [])
    have enil := acvalAt_one hp ConLeche.listNilName ConLeche.listNilTyOk h4
      rfl
      (by intro ci hh
          simp only [ConLeche.listNilTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ (Level.substFn φ ks us)
    have econs := acvalAt_one hp ConLeche.listConsName ConLeche.listConsTyOk
      h5 rfl
      (by intro ci hh
          simp only [ConLeche.listConsTyOk] at hh
          split at hh
          · next p hpe => simp [hpe]
          · exact nomatch hh)
      φ (Level.substFn φ ks us)
    rw [ez, es, esol, echar, eofn, enil, econs]
  | case14 d s hsup =>
    rw [Expr.instantiateLevelParams, denoteMeta, denoteMeta, if_neg hsup,
      if_neg hsup]
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

end ConLeche.Model
