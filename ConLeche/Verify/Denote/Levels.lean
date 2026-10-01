module

public import ConLeche.Verify.Denote
public import ConLeche.Verify.InstLevels

public section

/-!
# The denotation and level parameters

Relocated out of `ConLeche/TTVerify/Extend.lean` (task #148, T3): this
block is **V-free and lane-independent** — it says that `denote` reads
an expression's *own* level parameters and nothing else
(`denote_params_ext`), and that level instantiation composes the
assignment (`denote_instLevels`).  Both the TT lane (`EnvTT.cons`'s
`hparams`, the delta step) and the `ConLeche/SetR/*` bridge need them, so
they live below both rather than inside one.

The statements are unchanged; only the module is new.  (The campaign
design's T1 lists exactly this kind of move — "relocate the V-free
denote stack to a neutral home"; this is the slice the bridge forced.)
-/

namespace ConLeche.Verify

open ConLeche.Term

/-! ## The denotation reads only an expression's own level parameters

The fact every install case needs to discharge its `hparams`
obligation: a definition's denotation is a function of its *own* level
parameters, so storing it as the new constant's value respects
`val_params`.

The literal clauses need to know that the literal-support constants
carry no level parameters, and they get it from the branch condition
rather than from an inversion lemma: `denote` only builds `natLitT`
when `natLitSupported` holds, and that guard's own shape checks say
`levelParams.isEmpty`.  `List.nil`/`List.cons` are the two that *do*
have a parameter, and there the substituted level is `Level.zero`,
which no assignment can see. -/

/-- A literal-support slot with an empty parameter list is valued
independently of the assignment. -/
private theorem cval_of_isEmpty {env : Env} {cval : TConstVal}
    (hp : ∀ n ci, env.find? n = some ci →
      ∀ φ₁ φ₂ : Name → Nat,
        (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
        cval n φ₁ = cval n φ₂)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (he : ci.toConstantVal.levelParams.isEmpty = true)
    (φ₁ φ₂ : Name → Nat) : cval n φ₁ = cval n φ₂ := by
  refine hp n ci hf φ₁ φ₂ ?_
  intro p hpm
  rw [List.isEmpty_iff] at he
  rw [he] at hpm
  exact nomatch hpm

/-- The abbreviation the two literal helpers and the main lemma share:
a valuation reads a constant only at that constant's own parameters. -/
abbrev ValParams (env : Env) (cval : TConstVal) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂

/-- A `Nat` literal's term does not depend on the level assignment. -/
private theorem natLitT_params {env : Env} {cval : TConstVal}
    (hp : ValParams env cval) (hg : natLitSupported env = true)
    (φ₁ φ₂ : Name → Nat) (n : Nat) :
    natLitT (cval natZeroName (Level.substFn φ₁ [] []))
        (cval natSuccName (Level.substFn φ₁ [] [])) n
      = natLitT (cval natZeroName (Level.substFn φ₂ [] []))
        (cval natSuccName (Level.substFn φ₂ [] [])) n := by
  simp only [natLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨-, h2⟩, h3⟩ := hg
  have e2 : cval natZeroName (Level.substFn φ₁ [] [])
      = cval natZeroName (Level.substFn φ₂ [] []) := by
    cases hx : env.find? natZeroName with
    | none => rw [hx] at h2; exact nomatch h2
    | some ci =>
      refine cval_of_isEmpty hp hx ?_ _ _
      rw [hx] at h2
      cases ci with
      | ctorInfo cv a b =>
        simp only [natZeroOk, Bool.and_eq_true] at h2
        simpa [ConstantInfo.toConstantVal] using h2.1
      | _ => simp [natZeroOk] at h2
  have e3 : cval natSuccName (Level.substFn φ₁ [] [])
      = cval natSuccName (Level.substFn φ₂ [] []) := by
    cases hx : env.find? natSuccName with
    | none => rw [hx] at h3; exact nomatch h3
    | some ci =>
      refine cval_of_isEmpty hp hx ?_ _ _
      rw [hx] at h3
      cases ci with
      | ctorInfo cv a b =>
        simp only [natSuccOk, Bool.and_eq_true] at h3
        simpa [ConstantInfo.toConstantVal] using h3.1
      | _ => simp [natSuccOk] at h3
  rw [e2, e3]

/-- A one-parameter slot substituted at `Level.zero` is valued
independently of the assignment: the substitution overrides the only
parameter the valuation may read. -/
private theorem cval_of_oneParam {env : Env} {cval : TConstVal}
    (hp : ValParams env cval) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci)
    (hlen : ci.toConstantVal.levelParams.length = 1) (φ₁ φ₂ : Name → Nat) :
    cval n (Level.substFn φ₁ ci.toConstantVal.levelParams [.zero])
      = cval n (Level.substFn φ₂ ci.toConstantVal.levelParams [.zero]) := by
  refine hp n ci hf _ _ ?_
  intro p hpm
  refine Level.substFn_ext (ps := []) (fun q hq => nomatch hq) ?_ ?_ p hpm
  · intro u hu
    simp only [List.mem_singleton] at hu
    subst hu
    rfl
  · simp [hlen]

/-- A `String` literal's term does not depend on the level assignment
either. -/
private theorem strLitT_params {env : Env} {cval : TConstVal}
    (hp : ValParams env cval) (hg : strLitSupported env = true)
    (φ₁ φ₂ : Name → Nat) (s : String) :
    strLitT cval env φ₁ s = strLitT cval env φ₂ s := by
  simp only [strLitSupported, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, -⟩, h2⟩, -⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hg
  simp only [natLitSupported, Bool.and_eq_true] at h0
  obtain ⟨⟨-, hz⟩, hs⟩ := h0
  -- the five scalar slots
  have scalar : ∀ (nm : Name) (f : Option ConstantInfo → Bool),
      f (env.find? nm) = true → f none = false →
      (∀ ci, f (some ci) = true → ci.toConstantVal.levelParams.isEmpty = true) →
      cval nm (Level.substFn φ₁ [] []) = cval nm (Level.substFn φ₂ [] []) := by
    intro nm f hfok hnone hshape
    cases hx : env.find? nm with
    | none => rw [hx, hnone] at hfok; exact nomatch hfok
    | some ci =>
      rw [hx] at hfok
      exact cval_of_isEmpty hp hx (hshape ci hfok) _ _
  have esol := scalar stringOfListName stringOfListTyOk h2 rfl
    (by intro ci h; simp only [stringOfListTyOk, Bool.and_eq_true] at h
        exact h.1)
  have echar := scalar charName charTyOk h6 rfl
    (by intro ci h; simp only [charTyOk, Bool.and_eq_true] at h; exact h.1)
  have eofn := scalar charOfNatName charOfNatTyOk h7 rfl
    (by intro ci h; simp only [charOfNatTyOk, Bool.and_eq_true] at h
        exact h.1)
  have ez : cval natZeroName (Level.substFn φ₁ [] [])
      = cval natZeroName (Level.substFn φ₂ [] []) :=
    scalar natZeroName natZeroOk hz rfl
      (by intro ci h; cases ci with
          | ctorInfo cv a b =>
            simp only [natZeroOk, Bool.and_eq_true] at h
            simpa [ConstantInfo.toConstantVal] using h.1
          | _ => simp [natZeroOk] at h)
  have es : cval natSuccName (Level.substFn φ₁ [] [])
      = cval natSuccName (Level.substFn φ₂ [] []) :=
    scalar natSuccName natSuccOk hs rfl
      (by intro ci h; cases ci with
          | ctorInfo cv a b =>
            simp only [natSuccOk, Bool.and_eq_true] at h
            simpa [ConstantInfo.toConstantVal] using h.1
          | _ => simp [natSuccOk] at h)
  -- the two one-parameter slots
  have oneParam : ∀ (nm : Name) (f : Option ConstantInfo → Bool),
      f (env.find? nm) = true → f none = false →
      (∀ ci, f (some ci) = true →
        ci.toConstantVal.levelParams.length = 1) →
      cval nm (Level.substFn φ₁ (levelParamsAt env nm) [.zero])
        = cval nm (Level.substFn φ₂ (levelParamsAt env nm) [.zero]) := by
    intro nm f hfok hnone hshape
    cases hx : env.find? nm with
    | none => rw [hx, hnone] at hfok; exact nomatch hfok
    | some ci =>
      have hlp : levelParamsAt env nm = ci.toConstantVal.levelParams := by
        simp [levelParamsAt, hx]
      rw [hx] at hfok
      rw [hlp]
      exact cval_of_oneParam hp hx (hshape ci hfok) _ _
  have enil := oneParam listNilName listNilTyOk h4 rfl
    (by intro ci h
        simp only [listNilTyOk] at h
        split at h
        · next p hpe => simp [hpe]
        · exact nomatch h)
  have econs := oneParam listConsName listConsTyOk h5 rfl
    (by intro ci h
        simp only [listConsTyOk] at h
        split at h
        · next p hpe => simp [hpe]
        · exact nomatch h)
  simp only [strLitT, esol, echar, eofn, ez, es, enil, econs]

/-- **The denotation reads the assignment only at the expression's own
level parameters.**  Transpose of `interp_params_ext`.  This is what
lets an install store `⟦value⟧` as the new constant's valuation and
still satisfy `val_params`. -/
theorem denote_params_ext {env : Env} {cval : TConstVal}
    (hp : ValParams env cval) {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (d : Nat) (e : Expr), e.allLevelParamsDefined ps = true →
      denote cval env φ₁ d e = denote cval env φ₂ d e := by
  intro d e
  induction d, e using denote.induct (cval := cval) (env := env) (φ := φ₁) with
  | case1 d u =>
    intro hd
    rw [denote_sort, denote_sort,
      Level.eval_ext (by simpa [Expr.allLevelParamsDefined] using hd) hφ]
  | case2 d idx ty => intro _; rw [denote_fvar, denote_fvar]
  | case3 d n us ci h1 h2 =>
    intro hd
    simp only [denote_const, h1, if_pos h2]
    refine congrArg _ (hp n ci h1 _ _ fun p hpm => ?_)
    refine Level.substFn_ext hφ ?_ h2 p hpm
    intro u hu
    simp only [Expr.allLevelParamsDefined, List.all_eq_true] at hd
    exact hd u hu
  | case4 d n us ci h1 h2 =>
    intro _; simp only [denote_const, h1, if_neg h2]
  | case5 d n us h1 => intro _; simp only [denote_const, h1]
  | case6 d ty body mb h1 ihty =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_forallE, denote_forallE, ← ihty hd.1.1, h1]
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_forallE, denote_forallE, ← ihty hd.1.1,
      ← ihbody (Expr.allLevelParamsDefined_instantiate1 hd.1.1 0 hd.1.2)]
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_forallE, denote_forallE, ← ihty hd.1.1,
      ← ihbody (Expr.allLevelParamsDefined_instantiate1 hd.1.1 0 hd.1.2)]
  | case9 d ty body mb h1 ihty =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_lam, denote_lam, ← ihty hd.1.1, h1]
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_lam, denote_lam, ← ihty hd.1.1,
      ← ihbody (Expr.allLevelParamsDefined_instantiate1 hd.1.1 0 hd.1.2)]
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_lam, denote_lam, ← ihty hd.1.1,
      ← ihbody (Expr.allLevelParamsDefined_instantiate1 hd.1.1 0 hd.1.2)]
  | case12 d f a vf va h1 h2 ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_app, denote_app, ← ihf hd.1, ← iha hd.2]
  | case13 d f a hbad ihf iha =>
    intro hd
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    rw [denote_app, denote_app, ← ihf hd.1, ← iha hd.2]
  | case14 d ty val body =>
    intro _
    rw [denote_letE, denote_letE]
  | case15 d sn i e h1 ihe =>
    intro hd
    rw [denote_proj, denote_proj,
      ← ihe (by simpa [Expr.allLevelParamsDefined] using hd)]
  | case16 d sn i e B h1 entry h2 ihe =>
    intro hd
    rw [denote_proj, denote_proj,
      ← ihe (by simpa [Expr.allLevelParamsDefined] using hd)]
  | case17 d sn i e B h1 h2 ihe =>
    intro hd
    rw [denote_proj, denote_proj,
      ← ihe (by simpa [Expr.allLevelParamsDefined] using hd)]
  | case18 d n hg =>
    intro _
    rw [denote_natLit, denote_natLit, natLitT_params hp hg φ₁ φ₂ n]
  | case19 d n hg =>
    intro _
    rw [denote_natLit, denote_natLit, if_neg hg, if_neg hg]
  | case20 d t hg =>
    intro _
    rw [denote_strLit, denote_strLit, strLitT_params hp hg φ₁ φ₂ t]
  | case21 d t hg =>
    intro _
    rw [denote_strLit, denote_strLit, if_neg hg, if_neg hg]
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    intro _
    match x with
    | .bvar i => rw [denote_bvar, denote_bvar]
    | .sort u => exact (k1 u rfl).elim
    | .fvar a c => exact (k2 a c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE b c dd => exact (k4 b c dd rfl).elim
    | .lam b c dd => exact (k5 b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE b c dd => exact (k7 b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

/-- **Level instantiation composes the level assignment.**  The delta
step needs it: `unfoldDefinition` substitutes the levels *into* the
stored value, while `defn_eq` speaks about the stored value under a
substituted *assignment*, and this is the bridge between the two.

Its literal clauses are `natLitT_params` and `strLitT_params` applied
at the two assignments — the guards carry them (§8.4), so no inversion
lemma is needed here either. -/
theorem denote_instLevels {env : Env} {cval : TConstVal}
    (hp : ValParams env cval) {ks : List Name} {us : List Level}
    (φ : Name → Nat) :
    ∀ (d : Nat) (e : Expr),
      denote cval env φ d (e.instantiateLevelParams ks us) =
        denote cval env (Level.substFn φ ks us) d e := by
  intro d e
  induction d, e using denote.induct
    (cval := cval) (env := env) (φ := Level.substFn φ ks us) with
  | case1 d u =>
    simp only [Expr.instantiateLevelParams, denote_sort, Level.eval_subst]
  | case2 d idx ty =>
    simp only [Expr.instantiateLevelParams, denote_fvar]
  | case3 d n ws ci h1 h2 =>
    simp only [Expr.instantiateLevelParams, denote_const, h1]
    have hlen : (ws.map (Level.subst ks us)).length = ws.length := by simp
    rw [if_pos (by rw [hlen]; exact h2), if_pos h2]
    refine congrArg _ (hp n ci h1 _ _ fun q hq => ?_)
    exact Level.substFn_map_subst h2 hq
  | case4 d n ws ci h1 h2 =>
    simp only [Expr.instantiateLevelParams, denote_const, h1]
    have hlen : (ws.map (Level.subst ks us)).length = ws.length := by simp
    rw [if_neg (by rw [hlen]; exact h2), if_neg h2]
  | case5 d n ws h1 =>
    simp only [Expr.instantiateLevelParams, denote_const, h1]
  | case6 d ty body mb h1 ihty =>
    simp only [Expr.instantiateLevelParams, denote_forallE, ihty, h1]
  | case7 d ty body mb B h1 h2 ihty ihbody =>
    simp only [Expr.instantiateLevelParams, denote_forallE, ihty, h1]
    rw [← Expr.instantiateLevelParams_instantiate1, ihbody, h2]
  | case8 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [Expr.instantiateLevelParams, denote_forallE, ihty, h1]
    rw [← Expr.instantiateLevelParams_instantiate1, ihbody, h2]
  | case9 d ty body mb h1 ihty =>
    simp only [Expr.instantiateLevelParams, denote_lam, ihty, h1]
  | case10 d ty body mb B h1 h2 ihty ihbody =>
    simp only [Expr.instantiateLevelParams, denote_lam, ihty, h1]
    rw [← Expr.instantiateLevelParams_instantiate1, ihbody, h2]
  | case11 d ty body mb B h1 B' h2 ihty ihbody =>
    simp only [Expr.instantiateLevelParams, denote_lam, ihty, h1]
    rw [← Expr.instantiateLevelParams_instantiate1, ihbody, h2]
  | case12 d f a vf va h1 h2 ihf iha =>
    simp only [Expr.instantiateLevelParams, denote_app, ihf, iha]
  | case13 d f a hbad ihf iha =>
    simp only [Expr.instantiateLevelParams, denote_app, ihf, iha]
  | case14 d ty val body =>
    simp only [Expr.instantiateLevelParams, denote_letE]
  | case15 d sn i e h1 ihe =>
    simp only [Expr.instantiateLevelParams, denote_proj, ihe]
  | case16 d sn i e B h1 entry h2 ihe =>
    simp only [Expr.instantiateLevelParams, denote_proj, ihe]
  | case17 d sn i e B h1 h2 ihe =>
    simp only [Expr.instantiateLevelParams, denote_proj, ihe]
  | case18 d n hg =>
    simp only [Expr.instantiateLevelParams, denote_natLit]
    rw [if_pos hg, if_pos hg, natLitT_params hp hg φ (Level.substFn φ ks us)]
  | case19 d n hg =>
    simp only [Expr.instantiateLevelParams, denote_natLit]
    rw [if_neg hg, if_neg hg]
  | case20 d t hg =>
    simp only [Expr.instantiateLevelParams, denote_strLit]
    rw [if_pos hg, if_pos hg, strLitT_params hp hg φ (Level.substFn φ ks us)]
  | case21 d t hg =>
    simp only [Expr.instantiateLevelParams, denote_strLit]
    rw [if_neg hg, if_neg hg]
  | case22 d x k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 =>
    match x with
    | .bvar i => simp only [Expr.instantiateLevelParams, denote_bvar]
    | .sort u => exact (k1 u rfl).elim
    | .fvar a c => exact (k2 a c rfl).elim
    | .const a b => exact (k3 a b rfl).elim
    | .forallE b c dd => exact (k4 b c dd rfl).elim
    | .lam b c dd => exact (k5 b c dd rfl).elim
    | .app a b => exact (k6 a b rfl).elim
    | .letE b c dd => exact (k7 b c dd rfl).elim
    | .proj a b c => exact (k8 a b c rfl).elim
    | .lit (.natVal n) => exact (k9 n rfl).elim
    | .lit (.strVal t) => exact (k10 t rfl).elim

end ConLeche.Verify
