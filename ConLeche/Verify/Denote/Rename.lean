module

public import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Denote.Inst

public section

/-!
# Constant renaming and level instantiation, on the denotation side

`denote_renameConsts` — the transpose of `interp_renameConsts` — plus
the prefix relation the telescope folds state their domain agreement
with.

**Why the bridge needs it and `DeclBasisTT` did not.**  A pinned basis
constant has no `_model` counterpart, so nothing has to be renamed.  A
modeled block's install does: the capability pins describe the
`T._model` artifact, while the laws (`EtaLawTT`, `UnitLawTT`) are
stated at the **public** former, and `checkMemberVal`'s comparison
relates the two only *through* `renameConsts`.

`RenEqT`/`PiDomsRenEqT` are `V`-free, which is why they live here and
not in the model tier: **do not** import `ConLeche/Model/*` from this
hierarchy — the model tier (`ConLeche/Model/IndRename.lean` and the
frame files around it) imports them from here instead.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-! ## Renaming constants -/

/-- The condition under which renaming constants is invisible to the
denotation: every renamed constant resolves with the same level
parameters, unresolved names stay unresolved, and the valuation agrees
on the renaming.  Transpose of `RenameOk`. -/
@[expose] def RenameOkT (cval : TConstVal) (env : Env) (f : Name → Name) : Prop :=
  (∀ n ci, env.find? n = some ci → ∃ ci', env.find? (f n) = some ci' ∧
    ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams) ∧
  (∀ n, env.find? n = none → env.find? (f n) = none) ∧
  (∀ (n : Name) (ψ : Name → Nat), cval (f n) ψ = cval n ψ)
  -- (task #175 wiring W3 added a fourth, tower-freeness conjunct here
  -- because the branched `.proj` reading consulted the table at both
  -- the source and the image name; W5 fixed the struct name under
  -- `renameConsts` instead, and the conjunct is gone.)

/-- Renaming constants along a `RenameOkT` map preserves the
denotation.  Transpose of `interp_renameConsts`, clause for clause;
the `fvar`, `lit` and `proj` clauses are *cheaper* than the model's for
the reason recorded in `ConLeche/Verify/Denote.lean` — `denote` never
reads an `fvar`'s annotation or a `proj`'s structure name. -/
theorem denote_renameConsts {f : Name → Name} (hro : RenameOkT cval env f) :
    ∀ (e : Expr) (d : Nat),
      denote cval env φ d (e.renameConsts f) = denote cval env φ d e
  | .bvar _, _ => by simp [Expr.renameConsts]
  | .sort _, _ => by simp [Expr.renameConsts]
  | .fvar _ _, _ => by simp [Expr.renameConsts]
  | .lit (.natVal _), _ => by rw [Expr.renameConsts]
  | .lit (.strVal _), _ => by rw [Expr.renameConsts]
  | .const n ws, d => by
    simp only [Expr.renameConsts, denote_const]
    cases hf : env.find? n with
    | none => rw [hro.2.1 n hf]
    | some ci =>
      obtain ⟨ci', hf', hlp⟩ := hro.1 n ci hf
      rw [hf']
      dsimp only
      rw [hlp]
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal, if_pos hal, hro.2.2]
      · rw [if_neg hal, if_neg hal]
  | .app g a, d => by
    simp only [Expr.renameConsts, denote_app,
      denote_renameConsts hro g d, denote_renameConsts hro a d]
  | .proj s i e, d => by
    -- the struct name is fixed under renaming, so both readings
    -- consult the same entry
    simp only [Expr.renameConsts, denote_proj, denote_renameConsts hro e d]
  | .forallE ty body m, d => by
    simp only [Expr.renameConsts, denote_forallE]
    rw [← Expr.renameConsts_instantiate1]
    rw [denote_renameConsts hro ty d,
      denote_renameConsts hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .lam ty body m, d => by
    simp only [Expr.renameConsts, denote_lam]
    rw [← Expr.renameConsts_instantiate1]
    rw [denote_renameConsts hro ty d,
      denote_renameConsts hro (body.instantiate1 (.fvar d ty)) (d + 1)]
  | .letE ty val body, d => by
    simp only [Expr.renameConsts, denote_letE]
  termination_by e => e.sizeB
  decreasing_by
    all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

/-! ## The domain-agreement prefix relation

Only the *first `k`* domains are constrained, and the residuals are
left free: at a fold's use site the two telescopes agree on the
parameter prefix and then diverge — the type former ends in a sort, the
checked theorem in an equation. -/

/-- Related by constant renaming, modulo the positions the denotation
never reads. -/
@[expose] def RenEqT (f : Name → Name) (e₁ e₂ : Expr) : Prop :=
  Expr.ErasedEq (e₁.renameConsts f) e₂

/-- Renamed-equal expressions denote equally. -/
theorem RenEqT.denote {f : Name → Name} (hro : RenameOkT cval env f)
    {e₁ e₂ : Expr} (h : RenEqT f e₁ e₂) (d : Nat) :
    denote cval env φ d e₂ = denote cval env φ d e₁ := by
  rw [← denote_erasedEq h d]
  exact denote_renameConsts hro e₁ d

/-- Renamed-equality survives instantiating both sides with related
arguments. -/
theorem RenEqT.instantiate1 {f : Name → Name} {e₁ e₂ a₁ a₂ : Expr} {k : Nat}
    (he : RenEqT f e₁ e₂) (ha : RenEqT f a₁ a₂) :
    RenEqT f (e₁.instantiate1 a₁ k) (e₂.instantiate1 a₂ k) := by
  unfold RenEqT
  rw [Expr.renameConsts_instantiate1_gen]
  exact Expr.ErasedEq.instantiate1 he ha

/-- **Two telescopes' opening variables are renamed-equal**, whatever
their binders were called and whatever they were annotated with:
`renameConsts` reaches only the annotation, and erasure compares only
the index.  This is what lets one alignment step open *both* sides. -/
theorem RenEqT.fvar {f : Name → Name} {i : Nat}
    {ty ty' : Expr} : RenEqT f (.fvar i ty) (.fvar i ty') := by
  show Expr.ErasedEq (.fvar i (ty.renameConsts f)) (.fvar i ty')
  rfl

/-- The first `k` domains of two `∀`-telescopes are related by the
renaming; their residuals are unconstrained. -/
def PiDomsRenEqT (f : Name → Name) : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .forallE d₁ b₁ _, e₂ =>
    ∃ d₂ b₂ m₂, e₂ = .forallE d₂ b₂ m₂ ∧ RenEqT f d₁ d₂ ∧
      PiDomsRenEqT f k b₁ b₂
  | _ + 1, _, _ => False

/-- Domain relatedness survives instantiating both sides with related
arguments. -/
theorem PiDomsRenEqT.instantiate1 {f : Name → Name} {a₁ a₂ : Expr}
    (ha : RenEqT f a₁ a₂) :
    ∀ (k : Nat) {e₁ e₂ : Expr} (j : Nat), PiDomsRenEqT f k e₁ e₂ →
      PiDomsRenEqT f k (e₁.instantiate1 a₁ j) (e₂.instantiate1 a₂ j) := by
  intro k
  induction k with
  | zero => intro e₁ e₂ j _; trivial
  | succ k ih =>
    intro e₁ e₂ j h
    match e₁, h with
    | .forallE d₁ b₁ m₁, h =>
      obtain ⟨d₂, b₂, m₂, rfl, hd, hb⟩ := h
      exact ⟨d₂.instantiate1 a₂ j, b₂.instantiate1 a₂ (j + 1), m₂, rfl,
        RenEqT.instantiate1 hd ha, ih (j + 1) hb⟩

/-- Pointwise domain relatedness assembles the prefix relation. -/
theorem PiDomsRenEqT.of_pointwise {f : Name → Name} :
    ∀ (k : Nat) {e₁ e₂ : Expr}
      {bs₁ bs₂ : List (Expr × BinderMeta)} {body₁ body₂ : Expr},
      e₁.stripPis k = some (bs₁, body₁) →
      e₂.stripPis k = some (bs₂, body₂) →
      (∀ (i : Nat) (b₁ b₂ : Expr × BinderMeta),
        bs₁[i]? = some b₁ → bs₂[i]? = some b₂ → RenEqT f b₁.1 b₂.1) →
      PiDomsRenEqT f k e₁ e₂ := by
  intro k
  induction k with
  | zero => intro e₁ e₂ bs₁ bs₂ body₁ body₂ _ _ _; trivial
  | succ k ih =>
    intro e₁ e₂ bs₁ bs₂ body₁ body₂ h1 h2 hdoms
    match e₁, e₂, h1, h2 with
    | .forallE d₁ b₁ m₁, .forallE d₂ b₂ m₂, h1, h2 =>
      simp only [Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : b₂.stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, -⟩ : (d₁, m₁) :: p1.1 = bs₁ ∧ p1.2 = body₁ := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, -⟩ : (d₂, m₂) :: p2.1 = bs₂ ∧ p2.2 = body₂ := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hb2
      refine ⟨d₂, b₂, m₂, rfl, ?_, ?_⟩
      · exact hdoms 0 (d₁, m₁) (d₂, m₂) rfl rfl
      · exact ih hs1 hs2 (fun i c₁ c₂ hc₁ hc₂ =>
          hdoms (i + 1) c₁ c₂ (by simpa using hc₁) (by simpa using hc₂))

/-- **Renaming preserves the denotation of a *resolving* expression**
under the first and third `RenameOkT` clauses alone.  The second
clause (unstored maps to unstored) exists only to keep an unstored
constant from acquiring a denotation; an expression every constant of
which resolves never reaches it.  That is what lets a block's own
renaming be used at a *member* environment, where the block's later
members are not stored yet (task #148 T6). -/
theorem denote_renameConsts_resolve {f : Name → Name}
    (hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? (f n) = some ci' ∧
        ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams)
    (hval : ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      ∀ ψ : Name → Nat, cval (f n) ψ = cval n ψ) :
    ∀ (e : Expr) (d : Nat), e.constsResolve env = true →
      denote cval env φ d (e.renameConsts f) = denote cval env φ d e
  | .bvar _, _, _ => by simp [Expr.renameConsts]
  | .sort _, _, _ => by simp [Expr.renameConsts]
  | .fvar _ _, _, _ => by simp [Expr.renameConsts]
  | .lit (.natVal _), _, _ => by rw [Expr.renameConsts]
  | .lit (.strVal _), _, _ => by rw [Expr.renameConsts]
  | .const n ws, d, hr => by
    simp only [Expr.renameConsts, denote_const]
    cases hf : env.find? n with
    | none =>
      rw [Expr.constsResolve, hf] at hr
      exact nomatch hr
    | some ci =>
      obtain ⟨ci', hf', hlp⟩ := hup n ci hf
      rw [hf']
      dsimp only
      rw [hlp]
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal, if_pos hal, hval n ci hf]
      · rw [if_neg hal, if_neg hal]
  | .app g a, d, hr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, denote_app,
      denote_renameConsts_resolve hup hval g d hr.1,
      denote_renameConsts_resolve hup hval a d hr.2]
  | .proj s i e, d, hr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, denote_proj,
      denote_renameConsts_resolve hup hval e d hr.2]
  | .forallE ty body m, d, hr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, denote_forallE]
    rw [← Expr.renameConsts_instantiate1]
    rw [denote_renameConsts_resolve hup hval ty d hr.1,
      denote_renameConsts_resolve hup hval
        (body.instantiate1 (.fvar d ty)) (d + 1)
        (Expr.constsResolve_instantiate1 hr.1 0 hr.2)]
  | .lam ty body m, d, hr => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hr
    simp only [Expr.renameConsts, denote_lam]
    rw [← Expr.renameConsts_instantiate1]
    rw [denote_renameConsts_resolve hup hval ty d hr.1,
      denote_renameConsts_resolve hup hval
        (body.instantiate1 (.fvar d ty)) (d + 1)
        (Expr.constsResolve_instantiate1 hr.1 0 hr.2)]
  | .letE ty val body, d, hr => by
    simp only [Expr.renameConsts, denote_letE]
  termination_by e => e.sizeB
  decreasing_by
    all_goals first
    | (simp [Expr.sizeB]; omega)
    | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
    | (simp [Expr.sizeB])

end ConLeche.Verify
