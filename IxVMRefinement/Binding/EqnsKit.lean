import IxVMRefinement.Binding.RenderedSpecs
import IxVMRefinement.RoleVal.GroupWalkLim
import IxVMRefinement.RoleOps.Guards
import IxC.Kernel.Rules.Derived
import IxC.Kernel.Rules.Transport

/-! # Closed-equation reduction kit (`EqnsKit`)

Reusable infrastructure turning validated equation-group facts (`RoleExactTy`, `EqnValid`,
`EqnsRoleShape`) into kernel `DefEq` and `Red` derivations on closed literal terms at every
depth. Powers the certified `Int`, `String`, and `BitVec` primitive families. -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Rules (Red DefEq Infer PiRed Grade)

/-! ## Exact specified types and equations for `.eqns` roles and their anchors -/

/-- Set the `BinderMeta` on leading `ForallE` binders to `m`. -/
def setOuterForallMeta (m : Ix.Kernel.BinderMeta) : KExpr → KExpr
  | .forallE d b _ => .forallE d (setOuterForallMeta m b) m
  | e => e

/-- The roles whose `role_type` we read with exact `BinderMeta` (all anchors and equation
definitions in indices `59..102`). -/
def isEqnsOrAnchorRole (r : Role) : Bool :=
  59 ≤ r.idx && r.idx ≤ 102

/-- Exact `BinderMeta` for the leading `ForallE` binders of `specTypeRaw r` for `59 ≤ r.idx ≤ 102`. -/
def roleOuterMeta : Role → Ix.Kernel.BinderMeta
  | .ofDecideEqTrue | .ofDecideEqFalse => { pw := .ifAllZero [] }
  | .ifThenElse => { pw := .ifAllZero [0] }
  | _ => { pw := .never }

/-- Exact expected universe parameter count of role `r` from `specDecl`. -/
def roleSpecLevels (r : Role) : Option Nat :=
  (specDecl r).map fun d => d.1.length

/-- Exact expected term rendered by `KernelRoleSpec::role_type(tbl, r)` for `59 ≤ r.idx ≤ 102`. -/
def roleTypeExact (r : Role) : Option KExpr :=
  (specTypeRaw r).map (setOuterForallMeta (roleOuterMeta r))

/-- The equations of a role (`Spec.eqns`), empty for other specification kinds. -/
def eqnsOfRole (r : Role) : List (Ix.Kernel.Equation .anon) :=
  match r.spec (md := .anon) with
  | .eqns _ _ eqs => eqs
  | _ => []

/-- Close an equation side over its variables (`λ vars, side`), with exact `BinderMeta`
`bmeta e.level`, matching `IxVM.RoleSpecGen.closeEqnSide`. -/
def eqnsSideExact (e : Ix.Kernel.Equation .anon) (side : KExpr) : KExpr :=
  e.vars.zipIdx.foldr
    (fun (ti : KExpr × Nat) body => Ix.Kernel.Expr.lam ti.1 (body.abstract1 ti.2) (bmeta e.level))
    side

/-- Close an equation statement over its variables and hypotheses
(`Π vars, Π hyps, @Eq.{level} carrier lhs rhs`), with exact `BinderMeta := { pw := .ifAllZero [] }`,
matching `IxVM.RoleSpecGen.closeEqnStatement`. -/
def eqnsStmtExact (e : Ix.Kernel.Equation .anon) : KExpr :=
  let n := e.vars.length
  let eqApp : KExpr :=
    .app (.app (.app (.const Ix.Kernel.eqName [e.level]) e.carrier) e.lhs) e.rhs
  let withHyps : KExpr :=
    e.hyps.zipIdx.foldr
      (fun (hj : KExpr × Nat) body =>
        Ix.Kernel.Expr.forallE hj.1 (body.abstract1 (n + hj.2)) { pw := .ifAllZero [] })
      eqApp
  e.vars.zipIdx.foldr
    (fun (ti : KExpr × Nat) body =>
      Ix.Kernel.Expr.forallE ti.1 (body.abstract1 ti.2) { pw := .ifAllZero [] })
    withHyps

/-! ## Anchors walked by `validate_eqns_anchors` -/

/-- The bound anchors checked with their closures by `KernelRoles::validate_eqns_anchors`
when validating equation role `r`. -/
abbrev eqnsAnchorsOf : Role → List Role := RoleVal.eqnsAnchorsOf

/-! ## Validated shapes accumulated by `Shapes` across groups `46..76` -/

/-- A role constant is stored in `env`, not a projection table, with its specified universe
parameter count and type definitionally equal to its exact rendered specification type. -/
def RoleExactTy (env : Ix.Kernel.Env .anon) (r : Role) : Prop :=
  ∃ ci T₀, env.find? (.role r) = some ci ∧ ci.isTowerEntry = false ∧
    roleSpecLevels r = some ci.toConstantVal.levelParams.length ∧
    roleTypeExact r = some T₀ ∧
    DefEq env 0 (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type) T₀

theorem RoleExactTy.weaken {env env' : Ix.Kernel.Env .anon} (hext : Ix.Kernel.EnvExt env env')
    {r : Role} (h : RoleExactTy env r) : RoleExactTy env' r := by
  obtain ⟨ci, T₀, hf, hnt, hlv, hrt, hde⟩ := h
  exact ⟨ci, T₀, hext.find hf, hnt, hlv, hrt, DefEq.weaken hext hde⟩

/-- One equation `e` of an equation-specified role `r`, validated either by definitional
equality on its closed lambda sides or by a stored theorem whose type meets its closed
equality statement. -/
def EqnValid (env : Ix.Kernel.Env .anon) (r : Role) (e : Ix.Kernel.Equation .anon) : Prop :=
  (e.hyps.isEmpty = true ∧ DefEq env 0 (eqnsSideExact e e.lhs) (eqnsSideExact e e.rhs)) ∨
  (∃ (kThm : Core.KKey) (cv : Ix.Kernel.ConstantVal .anon) (val : KExpr),
    env.find? kThm = some (.thmInfo cv val) ∧
    roleSpecLevels r = some cv.levelParams.length ∧
    DefEq env 0 (Core.posOf cv.levelParams cv.type) (eqnsStmtExact e))

theorem EqnValid.weaken {env env' : Ix.Kernel.Env .anon} (hext : Ix.Kernel.EnvExt env env')
    {r : Role} {e : Ix.Kernel.Equation .anon} (h : EqnValid env r e) : EqnValid env' r e := by
  rcases h with ⟨hu, hde⟩ | ⟨kThm, cv, val, hf, hlv, hde⟩
  · exact Or.inl ⟨hu, DefEq.weaken hext hde⟩
  · exact Or.inr ⟨kThm, cv, val, hext.find hf, hlv, DefEq.weaken hext hde⟩

/-- The validated equation and walked-anchor facts of a role `r` in groups `46..76`. -/
def EqnsRoleShape (env : Ix.Kernel.Env .anon) (r : Role) : Prop :=
  (RoleVal.roleSpecKindNat r = 5 →
    RoleExactTy env r ∧
    (∀ ar ∈ eqnsAnchorsOf r, RoleExactTy env ar) ∧
    (∀ e ∈ eqnsOfRole r, EqnValid env r e)) ∧
  (RoleVal.roleSpecKindNat r = 1 → RoleVal.anchorWalked r = true → RoleExactTy env r)

theorem EqnsRoleShape.weaken {env env' : Ix.Kernel.Env .anon} (hext : Ix.Kernel.EnvExt env env')
    {r : Role} (h : EqnsRoleShape env r) : EqnsRoleShape env' r :=
  ⟨fun h5 =>
    let ⟨hty, hanc, heqns⟩ := h.1 h5
    ⟨hty.weaken hext, fun ar har => (hanc ar har).weaken hext,
      fun e he => (heqns e he).weaken hext⟩,
   fun h1 haw => (h.2 h1 haw).weaken hext⟩

/-! ## Grade weakening (`Infer .full → Infer .io`) -/

mutual

private theorem red_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {e e' : KExpr}, Red env d e e' → True
  | _, _, _, _ => trivial

private theorem defEq_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {a b : KExpr}, DefEq env d a b → True
  | _, _, _, _ => trivial

private theorem infer_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer env g d e t → Infer env .io d e t
  | _, _, _, _, .sort => .sort
  | _, _, _, _, .fvar hlt => .fvar hlt
  | _, _, _, _, .const hf hnt hlen => .const hf hnt hlen
  | _, _, _, _, .natLit hn => .natLit hn
  | _, _, _, _, .strLit hs => .strLit hs
  | _, _, _, _, .forallE hs hru hbs hrv hz =>
    .forallE (infer_toIO_aux hs) hru (infer_toIO_aux hbs) hrv hz
  | _, _, _, _, .lam _ _ hbt hpw hbtt hrt hz =>
    .lam (s := .sort .zero) (u := .zero) (fun h => nomatch h) (fun h => nomatch h)
      (infer_toIO_aux hbt) hpw hbtt hrt hz
  | _, _, _, _, .app hf hrf ha hde => .app (infer_toIO_aux hf) hrf (infer_toIO_aux ha) hde
  | _, _, _, _, .appSkip hf hrf hnev => .appSkip (infer_toIO_aux hf) hrf hnev
  | _, _, _, _, .proj hpe hrp hfn hfp hlen hus hfs =>
    .proj (infer_toIO_aux hpe) hrp hfn hfp hlen hus hfs

private theorem certs_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {lic : Bool} {T : KExpr} {as : List KExpr}, Ix.Kernel.Rules.Certs env d lic T as → True
  | _, _, _, _, _ => trivial

private theorem defEqList_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {as bs : List KExpr}, Ix.Kernel.Rules.DefEqList env d as bs → True
  | _, _, _, _ => trivial

private theorem etaProjCerts_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {T : Core.KKey} {us : List KLevel} {targs : List KExpr} {b : KExpr}
      {lps : List Ix.Kernel.LevelParam} {is : List Nat},
      Ix.Kernel.Rules.EtaProjCerts env d T us targs b lps is → True
  | _, _, _, _, _, _, _, _ => trivial

private theorem piRed_toIO_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {e e' : KExpr}, PiRed env d e e' → True
  | _, _, _, _ => trivial

end

/-- Every full-grade inference is also an io-grade inference. -/
theorem _root_.Ix.Kernel.Rules.Infer.toIO {env : Ix.Kernel.Env .anon} {d : Nat} {e t : KExpr}
    (h : Infer env .full d e t) : Infer env .io d e t :=
  infer_toIO_aux h

/-! ## Closed expressions -/

/-- A closed kernel expression (no free variables and no loose bound variables). -/
def TermClosed (e : KExpr) : Prop :=
  e.hasFvar = false ∧ e.looseBVarsBounded 0 = true

theorem TermClosed.sort (u : KLevel) : TermClosed (.sort u) := ⟨rfl, rfl⟩
theorem TermClosed.const (k : Core.KKey) (us : List KLevel) : TermClosed (.const k us) := ⟨rfl, rfl⟩
theorem TermClosed.lit (l : Ix.Kernel.Literal) : TermClosed (.lit l) := ⟨rfl, rfl⟩
theorem TermClosed.app {f a : KExpr} (hf : TermClosed f) (ha : TermClosed a) :
    TermClosed (.app f a) := by
  exact ⟨by simp [Ix.Kernel.Expr.hasFvar, hf.1, ha.1],
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hf.2, ha.2]⟩

theorem looseBVarsBounded_mono : ∀ (e : KExpr) {m n : Nat}, m ≤ n →
    e.looseBVarsBounded m = true → e.looseBVarsBounded n = true
  | .bvar i, m, n, hmn, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢; omega
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, m, n, hmn, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono f hmn h.1, looseBVarsBounded_mono a hmn h.2⟩
  | .lam t b _, m, n, hmn, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono t hmn h.1, looseBVarsBounded_mono b (Nat.succ_le_succ hmn) h.2⟩
  | .forallE t b _, m, n, hmn, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨looseBVarsBounded_mono t hmn h.1, looseBVarsBounded_mono b (Nat.succ_le_succ hmn) h.2⟩
  | .letE t v b _, m, n, hmn, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h ⊢
    exact ⟨⟨looseBVarsBounded_mono t hmn h.1.1, looseBVarsBounded_mono v hmn h.1.2⟩,
      looseBVarsBounded_mono b (Nat.succ_le_succ hmn) h.2⟩
  | .proj _ _ e, m, n, hmn, h => looseBVarsBounded_mono e hmn h

theorem instantiate1_eq_self : ∀ (e : KExpr) {v : KExpr} {k : Nat},
    e.looseBVarsBounded k = true → e.instantiate1 v k = e
  | .bvar i, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp [Ix.Kernel.Expr.instantiate1, show ¬ (i = k) by omega, show ¬ (i > k) by omega]
  | .fvar _ _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .app f a, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self f h.1, instantiate1_eq_self a h.2]
  | .lam t b m, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self t h.1, instantiate1_eq_self b h.2]
  | .forallE t b m, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self t h.1, instantiate1_eq_self b h.2]
  | .letE t val b m, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self t h.1.1, instantiate1_eq_self val h.1.2,
      instantiate1_eq_self b h.2]
  | .proj s i e, v, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded] at h
    simp [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self e h]

theorem abstract1_eq_self : ∀ (e : KExpr) {d k : Nat},
    e.hasFvar = false → e.abstract1 d k = e
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => rfl
  | .fvar _ _, _, _, h => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .app f a, d, k, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self f h.1, abstract1_eq_self a h.2]
  | .lam t b m, d, k, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self t h.1, abstract1_eq_self b h.2]
  | .forallE t b m, d, k, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self t h.1, abstract1_eq_self b h.2]
  | .letE t v b m, d, k, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self t h.1.1, abstract1_eq_self v h.1.2,
      abstract1_eq_self b h.2]
  | .proj s i e, d, k, h => by
    simp only [Ix.Kernel.Expr.hasFvar] at h
    simp [Ix.Kernel.Expr.abstract1, abstract1_eq_self e h]

theorem hasFvar_instantiate1 : ∀ (e : KExpr) {v : KExpr} {k : Nat},
    e.hasFvar = false → v.hasFvar = false → (e.instantiate1 v k).hasFvar = false
  | .bvar i, v, k, _, hv => by
    simp only [Ix.Kernel.Expr.instantiate1]
    split
    · exact hv
    · split <;> rfl
  | .fvar _ _, _, _, h, _ => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.hasFvar,
      hasFvar_instantiate1 f h.1 hv, hasFvar_instantiate1 a h.2 hv]
  | .lam t b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.hasFvar,
      hasFvar_instantiate1 t h.1 hv, hasFvar_instantiate1 b h.2 hv]
  | .forallE t b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.hasFvar,
      hasFvar_instantiate1 t h.1 hv, hasFvar_instantiate1 b h.2 hv]
  | .letE t val b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.hasFvar,
      hasFvar_instantiate1 t h.1.1 hv, hasFvar_instantiate1 val h.1.2 hv, hasFvar_instantiate1 b h.2 hv]
  | .proj s i e, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.hasFvar] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.hasFvar, hasFvar_instantiate1 e h hv]

theorem looseBVarsBounded_instantiate1' : ∀ (e : KExpr) {v : KExpr} {k : Nat},
    e.looseBVarsBounded (k + 1) = true → v.looseBVarsBounded 0 = true →
    (e.instantiate1 v k).looseBVarsBounded k = true
  | .bvar i, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp only [Ix.Kernel.Expr.instantiate1]
    split
    · exact looseBVarsBounded_mono v (Nat.zero_le k) hv
    · split
      · simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]; omega
      · simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq]; omega
  | .fvar _ _, _, _, _, _ | .sort _, _, _, _, _ | .const _ _, _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .app f a, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instantiate1' f h.1 hv, looseBVarsBounded_instantiate1' a h.2 hv]
  | .lam t b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instantiate1' t h.1 hv, looseBVarsBounded_instantiate1' b h.2 hv]
  | .forallE t b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instantiate1' t h.1 hv, looseBVarsBounded_instantiate1' b h.2 hv]
  | .letE t val b m, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instantiate1' t h.1.1 hv, looseBVarsBounded_instantiate1' val h.1.2 hv,
      looseBVarsBounded_instantiate1' b h.2 hv]
  | .proj s i e, v, k, h, hv => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded] at h
    simp [Ix.Kernel.Expr.instantiate1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instantiate1' e h hv]

theorem hasFvar_instLevels (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).hasFvar = e.hasFvar
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ _ => rfl
  | .app f a => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.hasFvar,
      hasFvar_instLevels ks us f, hasFvar_instLevels ks us a]
  | .lam t b _ => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.hasFvar,
      hasFvar_instLevels ks us t, hasFvar_instLevels ks us b]
  | .forallE t b _ => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.hasFvar,
      hasFvar_instLevels ks us t, hasFvar_instLevels ks us b]
  | .letE t v b _ => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.hasFvar,
      hasFvar_instLevels ks us t, hasFvar_instLevels ks us v, hasFvar_instLevels ks us b]
  | .proj _ _ e => hasFvar_instLevels ks us e

theorem looseBVarsBounded_instLevels (ks : List Ix.Kernel.LevelParam) (us : List KLevel) :
    ∀ (e : KExpr) (k : Nat),
      (e.instantiateLevelParams ks us).looseBVarsBounded k = e.looseBVarsBounded k
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .app f a, k => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instLevels ks us f k, looseBVarsBounded_instLevels ks us a k]
  | .lam t b _, k => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instLevels ks us t k, looseBVarsBounded_instLevels ks us b (k + 1)]
  | .forallE t b _, k => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instLevels ks us t k, looseBVarsBounded_instLevels ks us b (k + 1)]
  | .letE t v b _, k => by simp [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_instLevels ks us t k, looseBVarsBounded_instLevels ks us v k,
      looseBVarsBounded_instLevels ks us b (k + 1)]
  | .proj _ _ e, k => looseBVarsBounded_instLevels ks us e k

/-! ## Simple-expression substitution congruence -/

/-- Expressions built from variables, sorts, constants, literals, and applications only
(no binders, lets, or projections): every equation side, carrier, and hypothesis in the
specification set has this shape. -/
def isSimpleExpr : KExpr → Bool
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lit _ => true
  | .app f a => isSimpleExpr f && isSimpleExpr a
  | _ => false

theorem defEq_instantiate_simple {env : Ix.Kernel.Env .anon} {d : Nat} {x y : KExpr}
    (hxy : DefEq env d x y) :
    ∀ (k : Nat) (e : KExpr), isSimpleExpr e = true →
      DefEq env d (e.instantiate1 x k) (e.instantiate1 y k)
  | k, .bvar j, _ => by
    simp only [Ix.Kernel.Expr.instantiate1]
    split
    · exact hxy
    · exact .refl
  | _, .fvar _ _, _ | _, .sort _, _ | _, .const _ _, _ | _, .lit _, _ => .refl
  | k, .app f a, h => by
    simp only [isSimpleExpr, Bool.and_eq_true] at h
    exact .app (defEq_instantiate_simple hxy k f h.1) (defEq_instantiate_simple hxy k a h.2)

/-! ## Closed well-typed terms (`ClosedAt`) and identity-lambda casts -/

/-- A closed term `a` witnessed at type `T` by a closed well-typed non-lambda term that
reduces to `a` in the empty context. -/
structure ClosedAt (env : Ix.Kernel.Env .anon) (a T : KExpr) where
  closed : TermClosed a
  witness : KExpr
  wClosed : TermClosed witness
  wInfer : Infer env .full 0 witness T
  wRed : Red env 0 witness a
  wLamPw : witness.lamPw = none := by rfl

abbrev ClosedAt.mk' {env : Ix.Kernel.Env .anon} {a T : KExpr}
    (hc : TermClosed a) (w : KExpr) (hwc : TermClosed w)
    (hwi : Infer env .full 0 w T) (hwr : Red env 0 w a) (hnl : w.lamPw = none := by rfl) :
    ClosedAt env a T :=
  ⟨hc, w, hwc, hwi, hwr, hnl⟩

/-- A closed type `T` whose sort in the empty context reduces to `Sort u`. -/
structure ClosedType (env : Ix.Kernel.Env .anon) (T : KExpr) (u : KLevel) where
  closed : TermClosed T
  sortExpr : KExpr
  infer : Infer env .full 0 T sortExpr
  redSort : Red env 0 sortExpr (.sort u)

abbrev ClosedType.mk' {env : Ix.Kernel.Env .anon} {T : KExpr} {u : KLevel}
    (hc : TermClosed T) (s : KExpr) (hi : Infer env .full 0 T s) (hr : Red env 0 s (.sort u)) :
    ClosedType env T u :=
  ⟨hc, s, hi, hr⟩

theorem ClosedAt.defEq_trans {env : Ix.Kernel.Env .anon} {d : Nat} {a b c Tb : KExpr}
    (hb : ClosedAt env b Tb) (hab : DefEq env d a b) (hbc : DefEq env d b c) :
    DefEq env d a c :=
  .transClosed hb.closed.1 hb.closed.2 hb.wClosed.1 hb.wClosed.2 hb.wInfer (.ofRed hb.wRed) hab hbc

theorem ClosedAt.defEq_trans_w {env : Ix.Kernel.Env .anon} {d : Nat} {a b c Tb : KExpr}
    (hb : ClosedAt env b Tb) (hab : DefEq env d a hb.witness) (hbc : DefEq env d hb.witness c) :
    DefEq env d a c :=
  .transClosed hb.wClosed.1 hb.wClosed.2 hb.wClosed.1 hb.wClosed.2 hb.wInfer (.ofRed .refl) hab hbc

theorem ClosedType.defEq_trans {env : Ix.Kernel.Env .anon} {d : Nat} {a b c : KExpr} {u : KLevel}
    (hb : ClosedType env b u) (hab : DefEq env d a b) (hbc : DefEq env d b c) :
    DefEq env d a c :=
  .transClosed hb.closed.1 hb.closed.2 hb.closed.1 hb.closed.2 hb.infer (.ofRed .refl) hab hbc

theorem ClosedType.defEq_trans_piRed {env : Ix.Kernel.Env .anon} {d : Nat}
    {a b b' c : KExpr} {u : KLevel}
    (hbCl : TermClosed b) (hb' : ClosedType env b' u) (hpb : PiRed env 0 b' b)
    (hab : DefEq env d a b) (hbc : DefEq env d b c) :
    DefEq env d a c :=
  .transClosed hbCl.1 hbCl.2 hb'.closed.1 hb'.closed.2 hb'.infer hpb hab hbc

abbrev ClosedAt.ofInfer {env : Ix.Kernel.Env .anon} {a T : KExpr}
    (hc : TermClosed a) (hi : Infer env .full 0 a T) (hnl : a.lamPw = none := by rfl) :
    ClosedAt env a T :=
  .mk' hc a hc hi .refl hnl

theorem ClosedAt.defEq_witness {env : Ix.Kernel.Env .anon} {a T : KExpr} (h : ClosedAt env a T) :
    DefEq env 0 h.witness a :=
  .ofRed h.wRed

/-- **Identity-lambda cast from an existential inference**: cast closed term `a` to `B`
whenever `∃ A, Infer env .full 0 a A ∧ DefEq env 0 A B`. The resulting witness is
independent of the existential witness `A`. -/
def ClosedAt.ofCast {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {a B : KExpr} {u : KLevel} (ha : TermClosed a) (hB : ClosedType env B u)
    (hExists : ∃ A, Infer env .full 0 a A ∧ DefEq env 0 A B) :
    ClosedAt env a B := by
  let mb : Ix.Kernel.BinderMeta := { pw := u.zeronessOf }
  let idLam : KExpr := .lam B (.bvar 0) mb
  have hidClosed : TermClosed idLam :=
    ⟨by simp [idLam, Ix.Kernel.Expr.hasFvar, hB.closed.1],
      by simp [idLam, Ix.Kernel.Expr.looseBVarsBounded, hB.closed.2]⟩
  refine ⟨ha, .app idLam a, hidClosed.app ha, ?_, ?_, rfl⟩
  · obtain ⟨A, hInf, hAB⟩ := hExists
    have hidLamInfer : Infer env .full 0 idLam (.forallE B (B.abstract1 0) mb) := by
      refine .lam (fun _ => hB.infer) (fun _ => hB.redSort)
        (by simpa [Ix.Kernel.Expr.instantiate1] using (Infer.fvar (env := env) (g := .full) (d := 1) (idx := 0) (ty := B) (by omega)))
        (fun _ hp => by simp [Ix.Kernel.Expr.lamPw] at hp)
        (fun _ => by
          have hlift := Infer.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.infer.toIO
          simpa [Ix.Kernel.Expr.renFV_of_not_hasFvar hB.closed.1] using hlift)
        (fun _ => by
          have hlift := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.redSort
          simpa [Ix.Kernel.Expr.renFV] using hlift)
        (fun _ => rfl)
    rw [abstract1_eq_self B hB.closed.1] at hidLamInfer
    have h1 := Infer.app hidLamInfer .refl hInf hAB
    rwa [instantiate1_eq_self B hB.closed.2] at h1
  · obtain ⟨A, hInf, hAB⟩ := hExists
    exact Red.beta hInf.toIO hAB

/-- **Identity-lambda cast**: convert `ClosedAt env a A` to `ClosedAt env a B` along
`DefEq env 0 A B`, for any closed well-sorted type `B`. -/
def ClosedAt.cast {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {a A B : KExpr} {u : KLevel} (h : ClosedAt env a A) (hAB : DefEq env 0 A B)
    (hB : ClosedType env B u) : ClosedAt env a B := by
  let mb : Ix.Kernel.BinderMeta := { pw := u.zeronessOf }
  let idLam : KExpr := .lam B (.bvar 0) mb
  have hidLamInfer : Infer env .full 0 idLam (.forallE B (B.abstract1 0) mb) := by
    refine .lam (fun _ => hB.infer) (fun _ => hB.redSort)
      (by simpa [Ix.Kernel.Expr.instantiate1] using (Infer.fvar (env := env) (g := .full) (d := 1) (idx := 0) (ty := B) (by omega)))
      (fun _ hp => by simp [Ix.Kernel.Expr.lamPw] at hp)
      (fun _ => by
        have hlift := Infer.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.infer.toIO
        simpa [Ix.Kernel.Expr.renFV_of_not_hasFvar hB.closed.1] using hlift)
      (fun _ => by
        have hlift := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.redSort
        simpa [Ix.Kernel.Expr.renFV] using hlift)
      (fun _ => rfl)
  rw [abstract1_eq_self B hB.closed.1] at hidLamInfer
  have hAppInfer : Infer env .full 0 (.app idLam h.witness) B := by
    have h1 := Infer.app hidLamInfer .refl h.wInfer hAB
    rwa [instantiate1_eq_self B hB.closed.2] at h1
  have hAppRed : Red env 0 (.app idLam h.witness) a := by
    have hb : Red env 0 (.app idLam h.witness) h.witness :=
      Red.beta h.wInfer.toIO hAB
    exact .trans hb h.wRed
  have hidClosed : TermClosed idLam := by
    exact ⟨by simp [idLam, Ix.Kernel.Expr.hasFvar, hB.closed.1],
      by simp [idLam, Ix.Kernel.Expr.looseBVarsBounded, hB.closed.2]⟩
  exact .mk' h.closed (.app idLam h.witness) (hidClosed.app h.wClosed) hAppInfer hAppRed

private theorem ClosedAt.app_nondep_de_infer {env : Ix.Kernel.Env .anon} {f a A B ta : KExpr}
    {mb : Ix.Kernel.BinderMeta} (hf : ClosedAt env f (.forallE A B mb))
    (ha : ClosedAt env a ta) (hta : DefEq env 0 ta A) (hB : B.looseBVarsBounded 0 = true) :
    Infer env .full 0 (.app hf.witness ha.witness) B := by
  have h1 := Infer.app hf.wInfer .refl ha.wInfer hta
  rwa [instantiate1_eq_self B hB] at h1

/-- Non-dependent application of closed well-typed terms (`B` does not mention `bvar 0`),
accepting any `DefEq env 0 ta A`. -/
abbrev ClosedAt.app_nondep_de {env : Ix.Kernel.Env .anon} {f a A B ta : KExpr}
    {mb : Ix.Kernel.BinderMeta} (hf : ClosedAt env f (.forallE A B mb))
    (ha : ClosedAt env a ta) (hta : DefEq env 0 ta A) (hB : B.looseBVarsBounded 0 = true) :
    ClosedAt env (.app f a) B :=
  .mk' (hf.closed.app ha.closed) (.app hf.witness ha.witness) (hf.wClosed.app ha.wClosed)
    (ClosedAt.app_nondep_de_infer hf ha hta hB) (.trans (.appFn hf.wRed) (.appArg ha.wRed))

/-- Non-dependent application of closed well-typed terms (`B` does not mention `bvar 0`). -/
abbrev ClosedAt.app_nondep {env : Ix.Kernel.Env .anon} {f a A B : KExpr}
    {mb : Ix.Kernel.BinderMeta} (hf : ClosedAt env f (.forallE A B mb))
    (ha : ClosedAt env a A) (hB : B.looseBVarsBounded 0 = true) :
    ClosedAt env (.app f a) B :=
  hf.app_nondep_de ha .refl hB

/-- Dependent application of closed well-typed terms, returning a witness at `B.instantiate1 ha.witness`. -/
def ClosedAt.app_dep_raw {env : Ix.Kernel.Env .anon} {f a A B ta : KExpr}
    {mb : Ix.Kernel.BinderMeta} (hf : ClosedAt env f (.forallE A B mb))
    (ha : ClosedAt env a ta) (hta : DefEq env 0 ta A) :
    ClosedAt env (.app f a) (B.instantiate1 ha.witness) :=
  .mk' (hf.closed.app ha.closed) (.app hf.witness ha.witness) (hf.wClosed.app ha.wClosed)
    (Infer.app hf.wInfer .refl ha.wInfer hta) (.trans (.appFn hf.wRed) (.appArg ha.wRed))

/-- Dependent application of closed well-typed terms, casting the result type from
`B.instantiate1 ha.witness` to `B.instantiate1 a`. -/
def ClosedAt.app_dep {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {f a A B : KExpr} {mb : Ix.Kernel.BinderMeta} {u : KLevel}
    (hf : ClosedAt env f (.forallE A B mb)) (ha : ClosedAt env a A)
    (hsimp : isSimpleExpr B = true)
    (hBa : ClosedType env (B.instantiate1 a) u) :
    ClosedAt env (.app f a) (B.instantiate1 a) :=
  (hf.app_dep_raw ha .refl).cast hsc (defEq_instantiate_simple ha.defEq_witness 0 B hsimp) hBa

/-- Turn a closed definitional equality between closed well-typed terms (LHS neither a sort
nor a `∀`) into `Red env d a b` at every depth `d` via `Red.defEqClosed`. -/
theorem ClosedAt.red_of_defEq {env : Ix.Kernel.Env .anon} {a b Ta Tb : KExpr}
    (hns : Ix.Kernel.Rules.isSortOrPi a = false)
    (ha : ClosedAt env a Ta) (hb : ClosedAt env b Tb) (hde : DefEq env 0 a b) :
    ∀ d, Red env d a b := fun d =>
  .defEqClosed hns ha.closed.1 ha.closed.2 hb.closed.1 hb.closed.2
    ha.wClosed.1 ha.wClosed.2 hb.wClosed.1 hb.wClosed.2
    ha.wInfer ha.wRed hb.wInfer hb.wRed
    (.redBoth ha.wRed hb.wRed hde)

/-- A 0-level role constant with validated exact type `T₀`. -/
def ClosedAt.ofRole0 {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {r : Role} {T₀ : KExpr} {u : KLevel} (hr : RoleExactTy env r)
    (hlv0 : roleSpecLevels r = some 0) (hrt : roleTypeExact r = some T₀)
    (hT : ClosedType env T₀ u) :
    ClosedAt env (.const (.role r) []) T₀ :=
  ClosedAt.ofCast hsc (.const _ _) hT <| by
    obtain ⟨ci, T₁, hf, hnt, hlv, hrt1, hde⟩ := hr
    have hlen : ci.toConstantVal.levelParams.length = 0 :=
      Option.some.inj (hlv.symm.trans hlv0)
    have hlps : ci.toConstantVal.levelParams = [] := List.eq_nil_of_length_eq_zero hlen
    obtain rfl : T₀ = T₁ := Option.some.inj (hrt.symm.trans hrt1)
    have hpos : Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type =
        ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [] := by
      simp [Core.posOf, Core.posLevels, hlps]
    rw [hpos] at hde
    exact ⟨_, .const hf hnt (by simp [hlps]), hde⟩

private theorem level_allParamsDefined_instSingle (p : Ix.Kernel.LevelParam) (l : KLevel)
    (h : l.allParamsDefined [p] = true) :
    (Ix.Kernel.Level.subst [p] [.param 0] l).allParamsDefined [0] = true := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih h
  | max a b iha ihb =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Level.subst, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | imax a b iha ihb =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Level.subst, Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | param q =>
    simp only [Ix.Kernel.Level.allParamsDefined, List.contains_eq_mem, decide_eq_true_eq,
      List.mem_singleton] at h
    subst h
    simp [Ix.Kernel.Level.subst, Ix.Kernel.Level.subst.go, Ix.Kernel.Level.allParamsDefined]

private theorem level_subst_comp_single (p : Ix.Kernel.LevelParam) (u : KLevel) (l : KLevel)
    (h : l.allParamsDefined [p] = true) :
    Ix.Kernel.Level.subst [0] [u] (Ix.Kernel.Level.subst [p] [.param 0] l) =
      Ix.Kernel.Level.subst [p] [u] l := by
  induction l with
  | zero => rfl
  | succ l ih => exact congrArg Ix.Kernel.Level.succ (ih h)
  | max a b iha ihb =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Level.subst, iha h.1, ihb h.2]
  | imax a b iha ihb =>
    simp only [Ix.Kernel.Level.allParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Level.subst, iha h.1, ihb h.2]
  | param q =>
    simp only [Ix.Kernel.Level.allParamsDefined, List.contains_eq_mem, decide_eq_true_eq,
      List.mem_singleton] at h
    subst h
    simp [Ix.Kernel.Level.subst, Ix.Kernel.Level.subst.go]

private theorem substPW_comp_single (p : Ix.Kernel.LevelParam) (u : KLevel)
    (pw : Ix.Kernel.PropWhen) (h : pw.paramsDefined [p] = true) :
    Ix.Kernel.Level.substPW [0] [u] (Ix.Kernel.Level.substPW [p] [.param 0] pw) =
      Ix.Kernel.Level.substPW [p] [u] pw := by
  apply Ix.Kernel.PropWhen.eq_of_holds
  intro φ
  rw [Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW, Ix.Kernel.Level.holds_substPW]
  apply Ix.Kernel.PropWhen.holds_ext h
  intro q hq
  simp only [List.mem_singleton] at hq
  subst hq
  simp [Ix.Kernel.Level.substFn, Ix.Kernel.Level.eval]

private theorem allLevelParamsDefined_instSingle (p : Ix.Kernel.LevelParam) :
    ∀ (e : KExpr), e.allLevelParamsDefined [p] = true →
      (e.instantiateLevelParams [p] [.param 0]).allLevelParamsDefined [0] = true
  | .bvar _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => allLevelParamsDefined_instSingle p ty h
  | .sort u, h => level_allParamsDefined_instSingle p u h
  | .const _ us, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.allLevelParamsDefined,
      List.all_map, List.all_eq_true]
    intro l hl
    exact level_allParamsDefined_instSingle p l (h l hl)
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true]
    exact ⟨allLevelParamsDefined_instSingle p f h.1, allLevelParamsDefined_instSingle p a h.2⟩
  | .lam ty b m, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instSingle p ty h.1.1, allLevelParamsDefined_instSingle p b h.1.2⟩,
      Ix.Kernel.Level.substPW_paramsDefined rfl
        (fun l hl => by simp only [List.mem_singleton] at hl; subst hl; rfl) h.2⟩
  | .forallE ty b m, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instSingle p ty h.1.1, allLevelParamsDefined_instSingle p b h.1.2⟩,
      Ix.Kernel.Level.substPW_paramsDefined rfl
        (fun l hl => by simp only [List.mem_singleton] at hl; subst hl; rfl) h.2⟩
  | .letE ty v b _, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.allLevelParamsDefined,
      Bool.and_eq_true]
    exact ⟨⟨allLevelParamsDefined_instSingle p ty h.1.1, allLevelParamsDefined_instSingle p v h.1.2⟩,
      allLevelParamsDefined_instSingle p b h.2⟩
  | .proj _ _ e, h => allLevelParamsDefined_instSingle p e h

private theorem instLevelParams_comp_single (p : Ix.Kernel.LevelParam) (u : KLevel) :
    ∀ (e : KExpr), e.allLevelParamsDefined [p] = true →
      (e.instantiateLevelParams [p] [.param 0]).instantiateLevelParams [0] [u] =
        e.instantiateLevelParams [p] [u]
  | .bvar _, _ | .lit _, _ => rfl
  | .fvar _ ty, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, instLevelParams_comp_single p u ty h]
  | .sort l, h => by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, level_subst_comp_single p u l h]
  | .const n us, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, List.all_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, List.map_map]
    congr 1
    exact List.map_congr_left fun l hl => level_subst_comp_single p u l (h l hl)
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams,
      instLevelParams_comp_single p u f h.1, instLevelParams_comp_single p u a h.2]
  | .lam ty b m, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams,
      instLevelParams_comp_single p u ty h.1.1, instLevelParams_comp_single p u b h.1.2,
      substPW_comp_single p u m.pw h.2]
  | .forallE ty b m, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams,
      instLevelParams_comp_single p u ty h.1.1, instLevelParams_comp_single p u b h.1.2,
      substPW_comp_single p u m.pw h.2]
  | .letE ty v b _, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams,
      instLevelParams_comp_single p u ty h.1.1, instLevelParams_comp_single p u v h.1.2,
      instLevelParams_comp_single p u b h.2]
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined] at h
    simp only [Ix.Kernel.Expr.instantiateLevelParams, instLevelParams_comp_single p u e h]

/-- A 1-level role constant instantiated at `u`, with validated exact type `T₀[0 ↦ u]`. -/
def ClosedAt.ofRole1 {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {r : Role} {T₀ : KExpr} {u v : KLevel} (hr : RoleExactTy env r)
    (hlv1 : roleSpecLevels r = some 1) (hrt : roleTypeExact r = some T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hTu : ClosedType env (T₀.instantiateLevelParams [0] [u]) v) :
    ClosedAt env (.const (.role r) [u]) (T₀.instantiateLevelParams [0] [u]) :=
  ClosedAt.ofCast hsc (.const _ _) hTu <| by
    obtain ⟨ci, T₁, hf, hnt, hlv, hrt1, hde⟩ := hr
    have hlen : ci.toConstantVal.levelParams.length = 1 :=
      Option.some.inj (hlv.symm.trans hlv1)
    obtain ⟨p, hp⟩ : ∃ p, ci.toConstantVal.levelParams = [p] := by
      cases hl : ci.toConstantVal.levelParams with
      | nil => simp [hl] at hlen
      | cons p rest =>
        cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp [hl] at hlen
    obtain rfl : T₀ = T₁ := Option.some.inj (hrt.symm.trans hrt1)
    have hpos_def : Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type =
        ci.toConstantVal.type.instantiateLevelParams [p] [.param 0] := by
      simp [Core.posOf, Core.posLevels, hp]
    have hwfC := hwf ci (List.mem_of_find?_eq_some hf)
    have hci_lv : ci.toConstantVal.type.allLevelParamsDefined [p] = true := by
      have h1 := hwfC.2.1; rw [hp] at h1; exact h1
    have hci_cl : TermClosed ci.toConstantVal.type := ⟨hwfC.1, hwfC.2.2.2.1⟩
    have hpos_lv : (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type).allLevelParamsDefined [0] = true := by
      rw [hpos_def]
      exact allLevelParamsDefined_instSingle p ci.toConstantVal.type hci_lv
    have hpos_cl : TermClosed (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type) := by
      rw [hpos_def]
      exact ⟨by rw [hasFvar_instLevels]; exact hci_cl.1,
        by rw [looseBVarsBounded_instLevels]; exact hci_cl.2⟩
    have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [u]) rfl hpos_lv hTlv
      hpos_cl.1 hpos_cl.2 hT0cl.1 hT0cl.2 hde
    have hcomp : (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type).instantiateLevelParams [0] [u] =
        ci.toConstantVal.type.instantiateLevelParams [p] [u] := by
      rw [hpos_def]
      exact instLevelParams_comp_single p u ci.toConstantVal.type hci_lv
    rw [hcomp] at hinst
    have hc1 : Infer env .full 0 (.const (.role r) [u])
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [u]) :=
      .const hf hnt (by simp [hp])
    rw [hp] at hc1
    exact ⟨_, hc1, hinst⟩

/-- A 0-level stored theorem cast to its exact statement `T₀`. -/
def ClosedAt.ofThm0 {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon} {val T₀ : KExpr} {u : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv0 : cv.levelParams.length = 0)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hT : ClosedType env T₀ u) :
    ClosedAt env (.const kThm []) T₀ :=
  ClosedAt.ofCast hsc (.const _ _) hT <| by
    have hlps : cv.levelParams = [] := List.eq_nil_of_length_eq_zero hlv0
    have hpos : Core.posOf cv.levelParams cv.type =
        cv.type.instantiateLevelParams cv.levelParams [] := by
      simp [Core.posOf, Core.posLevels, hlps]
    rw [hpos] at hde
    exact ⟨_, .const (ci := .thmInfo cv val) hf rfl
      (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlps]), hde⟩

/-- A 1-level stored theorem instantiated at `u`, cast to `T₀[0 ↦ u]`. -/
def ClosedAt.ofThm1 {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon}
    {val T₀ : KExpr} {u v : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv1 : cv.levelParams.length = 1)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hTu : ClosedType env (T₀.instantiateLevelParams [0] [u]) v) :
    ClosedAt env (.const kThm [u]) (T₀.instantiateLevelParams [0] [u]) :=
  ClosedAt.ofCast hsc (.const _ _) hTu <| by
    obtain ⟨p, hp⟩ : ∃ p, cv.levelParams = [p] := by
      cases hl : cv.levelParams with
      | nil => simp [hl] at hlv1
      | cons p rest =>
        cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp [hl] at hlv1
    have hpos_def : Core.posOf cv.levelParams cv.type =
        cv.type.instantiateLevelParams [p] [.param 0] := by
      simp [Core.posOf, Core.posLevels, hp]
    have hwfC := hwf (.thmInfo cv val) (List.mem_of_find?_eq_some hf)
    have hlpDef : cv.type.allLevelParamsDefined [p] = true := by
      have h1 := hwfC.2.1; simp only [Ix.Kernel.ConstantInfo.toConstantVal, hp] at h1; exact h1
    have hclTy : TermClosed cv.type := ⟨hwfC.1, hwfC.2.2.2.1⟩
    have hposLv : (Core.posOf cv.levelParams cv.type).allLevelParamsDefined [0] = true := by
      rw [hpos_def]
      exact allLevelParamsDefined_instSingle p cv.type hlpDef
    have hposCl : TermClosed (Core.posOf cv.levelParams cv.type) := by
      rw [hpos_def]
      exact ⟨by rw [hasFvar_instLevels]; exact hclTy.1,
             by rw [looseBVarsBounded_instLevels]; exact hclTy.2⟩
    have hinst : DefEq env 0
        ((Core.posOf cv.levelParams cv.type).instantiateLevelParams [0] [u])
        (T₀.instantiateLevelParams [0] [u]) :=
      DefEq.instClosed (ks := [0]) (us := [u]) rfl hposLv hTlv hposCl.1 hposCl.2 hT0cl.1 hT0cl.2 hde
    have hcomp : (Core.posOf cv.levelParams cv.type).instantiateLevelParams [0] [u] =
        cv.type.instantiateLevelParams [p] [u] := by
      rw [hpos_def]
      exact instLevelParams_comp_single p u cv.type hlpDef
    rw [hcomp] at hinst
    have hc1 : Infer env .full 0 (.const kThm [u]) (cv.type.instantiateLevelParams cv.levelParams [u]) :=
      .const (ci := .thmInfo cv val) hf rfl
        (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hp])
    rw [hp] at hc1
    exact ⟨_, hc1, hinst⟩

/-! ## Closed type constructors (`ClosedType`) -/

def ClosedType.sort (env : Ix.Kernel.Env .anon) (u : KLevel) :
    ClosedType env (.sort u) (.succ u) :=
  .mk' (.sort u) (.sort (.succ u)) .sort .refl

def ClosedType.forall_nondep {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {A B : KExpr} {u v : KLevel}
    (hA : ClosedType env A u) (hB : ClosedType env B v) :
    ClosedType env (.forallE A B { pw := v.zeronessOf }) (.imax u v) := by
  have hS1 : Red env 1 (hB.sortExpr.renFV (fun i => i + 1)) (.sort v) := by
    have hlift := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.redSort
    simpa [Ix.Kernel.Expr.renFV] using hlift
  refine .mk' ⟨by simp [Ix.Kernel.Expr.hasFvar, hA.closed.1, hB.closed.1],
      by simp [Ix.Kernel.Expr.looseBVarsBounded, hA.closed.2,
        looseBVarsBounded_mono B (Nat.zero_le 1) hB.closed.2]⟩
    (.sort (.imax u v)) ?_ .refl
  refine .forallE hA.infer hA.redSort ?_ hS1 rfl
  rw [instantiate1_eq_self B hB.closed.2]
  have hlift := Infer.lift (Ix.Kernel.EnvExt.refl env) hsc (g := 1) hB.infer
  simpa [Ix.Kernel.Expr.renFV_of_not_hasFvar hB.closed.1] using hlift

/-! ## Closed equality reflection helper -/

/-- `eqA` has 1 level parameter (`uN = 0`) and type `∀ (α : Sort u) (a b : α), Prop`. -/
theorem eqA_type_shape :
    (Ix.Kernel.eqA (md := .anon)).toConstantVal.levelParams = [Ix.Kernel.uN] ∧
    ∃ m1 m2 m3, (Ix.Kernel.eqA (md := .anon)).toConstantVal.type =
      .forallE (.sort (.param Ix.Kernel.uN))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) m3) m2) m1 := by
  refine ⟨rfl, _, _, _, rfl⟩

/-- `eqReflA` has 1 level parameter (`uN = 0`) and type `∀ (α : Sort u) (a : α), Eq.{u} α a a`. -/
theorem eqReflA_type_shape :
    (Ix.Kernel.eqReflA (md := .anon)).toConstantVal.levelParams = [Ix.Kernel.uN] ∧
    ∃ m1 m2, (Ix.Kernel.eqReflA (md := .anon)).toConstantVal.type =
      .forallE (.sort (.param Ix.Kernel.uN))
        (.forallE (.bvar 0)
          (.app (.app (.app (.const Ix.Kernel.eqName [.param Ix.Kernel.uN]) (.bvar 1)) (.bvar 0)) (.bvar 0))
          m2) m1 := by
  refine ⟨rfl, _, _, rfl⟩

/-- Closed type `@Eq.{u} carrier a b : Prop` from `eqA` stored and `a, b : carrier : Sort u`. -/
private theorem closedType_eq_infer {env : Ix.Kernel.Env .anon}
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {carrier a b : KExpr} {u : KLevel}
    (hC : ClosedType env carrier u)
    (ha : Infer env .full 0 a carrier)
    (hb : Infer env .full 0 b carrier) :
    Infer env .full 0 (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) a) b) (.sort .zero) := by
  obtain ⟨hlps, m1, m2, m3, hty⟩ := eqA_type_shape
  have hcEq : Infer env .full 0 (.const Ix.Kernel.eqName [u])
      ((Ix.Kernel.eqA (md := .anon)).toConstantVal.type.instantiateLevelParams [Ix.Kernel.uN] [u]) :=
    .const heq rfl (by simp [hlps])
  rw [hty] at hcEq
  simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
    Ix.Kernel.Level.subst.go, ↓reduceIte] at hcEq
  have h1 := Infer.app hcEq .refl hC.infer (.ofRed hC.redSort)
  simp [Ix.Kernel.Expr.instantiate1] at h1
  have h2 := Infer.app h1 .refl ha .refl
  simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self carrier hC.closed.2] at h2
  have h3 := Infer.app h2 .refl hb .refl
  simpa [Ix.Kernel.Expr.instantiate1] using h3

abbrev closedType_eq {env : Ix.Kernel.Env .anon}
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {carrier a b : KExpr} {u : KLevel}
    (hC : ClosedType env carrier u)
    (ha : Infer env .full 0 a carrier) (hac : TermClosed a)
    (hb : Infer env .full 0 b carrier) (hbc : TermClosed b) :
    ClosedType env (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) a) b) .zero :=
  .mk' ((((TermClosed.const _ _).app hC.closed).app hac).app hbc) (.sort .zero)
    (closedType_eq_infer heq hC ha hb) .refl

/-- Turn a closed proof `ClosedAt env p (@Eq.{u} carrier lhs rhs)` into `DefEq env 0 lhs rhs`. -/
theorem defEq_of_eqProof {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {p carrier lhs rhs : KExpr} {u : KLevel}
    (hp : ClosedAt env p (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) lhs) rhs))
    (hlhs : ClosedAt env lhs carrier) (hrhs : ClosedAt env rhs carrier)
    (hC : ClosedType env carrier u) :
    DefEq env 0 lhs rhs := by
  have hEqTy := closedType_eq heq hC hlhs.wInfer hlhs.wClosed hrhs.wInfer hrhs.wClosed
  have hdeEq : DefEq env 0
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) lhs) rhs)
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) hlhs.witness) hrhs.witness) :=
    .app (.app (.app .refl .refl) hlhs.defEq_witness.symm) hrhs.defEq_witness.symm
  have hp' := hp.cast hsc hdeEq hEqTy
  have hdeW : DefEq env 0 hlhs.witness hrhs.witness :=
    .eqProof heq hlhs.wClosed.1 hlhs.wClosed.2 hrhs.wClosed.1 hrhs.wClosed.2
      hp'.wClosed.1 hp'.wClosed.2 hp'.wInfer hlhs.wInfer .refl hrhs.wInfer .refl
      hC.infer hC.redSort (fun _ => rfl)
  exact hlhs.defEq_trans_w hlhs.defEq_witness.symm (hrhs.defEq_trans_w hdeW hrhs.defEq_witness)

/-- Build `ClosedAt env (@Eq.refl.{u} carrier a) (@Eq.{u} carrier ha.witness ha.witness)`.
Since `ha.witness` is definitionally equal to `a`, any `app_nondep_de` accepting `Eq.{u} carrier lhs rhs`
with `DefEq env 0 lhs a` and `DefEq env 0 rhs a` consumes this directly without casting. -/
def closedAt_eqRefl {env : Ix.Kernel.Env .anon}
    (heqRefl : env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA)
    {carrier a : KExpr} {u : KLevel}
    (hC : ClosedType env carrier u) (ha : ClosedAt env a carrier) :
    ClosedAt env (.app (.app (.const Ix.Kernel.eqReflName [u]) carrier) a)
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) ha.witness) ha.witness) :=
  .mk' (((TermClosed.const _ _).app hC.closed).app ha.closed)
    (.app (.app (.const Ix.Kernel.eqReflName [u]) carrier) ha.witness)
    (((TermClosed.const _ _).app hC.closed).app ha.wClosed)
    (by
      obtain ⟨hlps, m1, m2, hty⟩ := eqReflA_type_shape
      have hcR : Infer env .full 0 (.const Ix.Kernel.eqReflName [u])
          ((Ix.Kernel.eqReflA (md := .anon)).toConstantVal.type.instantiateLevelParams [Ix.Kernel.uN] [u]) :=
        .const heqRefl rfl (by simp [hlps])
      rw [hty] at hcR
      simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
        Ix.Kernel.Level.subst.go, List.map, ↓reduceIte] at hcR
      have h1 := Infer.app hcR .refl hC.infer (.ofRed hC.redSort)
      simp [Ix.Kernel.Expr.instantiate1] at h1
      have h2 := Infer.app h1 .refl ha.wInfer .refl
      simpa [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self carrier hC.closed.2] using h2)
    (.appArg ha.wRed)

/-- Turn a closed proof `ClosedAt env p ta` with `DefEq env 0 ta (@Eq.{u} carrier lhs rhs)`
into `DefEq env 0 lhs rhs`. -/
theorem defEq_of_eqProof_de {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {p ta carrier lhs rhs : KExpr} {u : KLevel}
    (hp : ClosedAt env p ta)
    (hta : DefEq env 0 ta (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) lhs) rhs))
    (hlhs : ClosedAt env lhs carrier) (hrhs : ClosedAt env rhs carrier)
    (hC : ClosedType env carrier u) :
    DefEq env 0 lhs rhs := by
  have hEqTy := closedType_eq heq hC hlhs.wInfer hlhs.wClosed hrhs.wInfer hrhs.wClosed
  have hredEq : Red env 0
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) hlhs.witness) hrhs.witness)
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) lhs) rhs) :=
    .trans (.appFn (.appArg hlhs.wRed)) (.appArg hrhs.wRed)
  have hdeEq : DefEq env 0 ta
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) carrier) hlhs.witness) hrhs.witness) :=
    .redR hredEq hta
  have hp' := hp.cast hsc hdeEq hEqTy
  have hdeW : DefEq env 0 hlhs.witness hrhs.witness :=
    .eqProof heq hlhs.wClosed.1 hlhs.wClosed.2 hrhs.wClosed.1 hrhs.wClosed.2
      hp'.wClosed.1 hp'.wClosed.2 hp'.wInfer hlhs.wInfer .refl hrhs.wInfer .refl
      hC.infer hC.redSort (fun _ => rfl)
  exact hlhs.defEq_trans_w hlhs.defEq_witness.symm (hrhs.defEq_trans_w hdeW hrhs.defEq_witness)

/-! ## Base environment kit (`Nat`, `Bool`, `Eq`) -/

/-- The base environment facts available at group 76 (and any later environment):
store closure/WF, pinned `Eq` and `Nat` basis constants, `Bool` shapes, `Nat` literal support,
and all binary `Nat` operations stored. -/
structure BaseKit (env : Ix.Kernel.Env .anon) : Prop where
  storeClosed : Ix.Kernel.StoreClosed env
  wf : Ix.Kernel.EnvWF env
  eqStored : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA
  eqReflStored : env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA
  natStored : env.find? Ix.Kernel.natName = some Ix.Kernel.natA
  natZeroStored : env.find? Ix.Kernel.natZeroName = some Ix.Kernel.natZeroA
  natSuccStored : env.find? Ix.Kernel.natSuccName = some Ix.Kernel.natSuccA
  natLit : Ix.Kernel.natLitSupported env = true
  natPredOk : Ix.Kernel.natOpStoredOk env Ix.Kernel.natPredName = true
  natOpsOk : ∀ r : Role, (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames →
    Ix.Kernel.natOpStoredOk env (.role r) = true
  boolPinned : RoleOps.BoolPinned env
  boolCtorsStored : RoleOps.BoolCtorsStored env
  boolCtorsTyped : RoleOps.BoolCtorsTyped env

namespace BaseKit

abbrev natT : KExpr := .const Ix.Kernel.natName []
abbrev boolT : KExpr := .const Ix.Kernel.boolName []
abbrev trueE : KExpr := .const Ix.Kernel.boolTrueName []
abbrev falseE : KExpr := .const Ix.Kernel.boolFalseName []
abbrev natZeroE : KExpr := .const Ix.Kernel.natZeroName []
abbrev natSuccE : KExpr := .const Ix.Kernel.natSuccName []

def natType {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedType env natT (.succ .zero) :=
  ⟨.const _ _, .sort (.succ .zero), .const bk.natStored rfl rfl, .refl⟩

def boolType {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedType env boolT (.succ .zero) :=
  ⟨.const _ _, .sort (.succ .zero), by
    obtain ⟨ci, hf, hlp, hty⟩ := bk.boolPinned
    have hnm : ci.name = Ix.Kernel.boolName := by
      have h1 := List.find?_some (p := fun c : Ix.Kernel.ConstantInfo .anon => c.name == Ix.Kernel.boolName) hf
      exact beq_iff_eq.mp h1
    have hnt : ci.isTowerEntry = false := by
      cases ci with
      | projInfo tbl =>
        simp [Ix.Kernel.ConstantInfo.name, Ix.Kernel.ConstantInfo.toConstantVal,
          Ix.Kernel.projTableName, Ix.Kernel.auxKey, Ix.Kernel.boolName] at hnm
      | _ => rfl
    have h1 : Infer env .full 0 boolT (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams []) :=
      .const hf hnt (by simp [hlp])
    simpa [hlp, hty, Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst] using h1, .refl⟩

abbrev natLitAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) (n : Nat) :
    ClosedAt env (.lit (.natVal n)) natT :=
  .ofInfer (.lit _) (.natLit bk.natLit)

abbrev natZeroAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedAt env natZeroE natT :=
  .ofInfer (.const _ _) (.const bk.natZeroStored rfl rfl)

abbrev natSuccAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedAt env natSuccE (.forallE natT natT { pw := .never }) :=
  .ofInfer (.const _ _) (.const bk.natSuccStored rfl rfl)

abbrev natSuccApp {env : Ix.Kernel.Env .anon} (bk : BaseKit env) {e : KExpr}
    (he : ClosedAt env e natT) : ClosedAt env (.app natSuccE e) natT :=
  bk.natSuccAt.app_nondep he rfl

private theorem boolTrueInfer {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    Infer env .full 0 trueE boolT := by
  obtain ⟨⟨ci, hf, hlp⟩, -⟩ := bk.boolCtorsStored
  obtain ⟨⟨ci2, hf2, hty⟩, -⟩ := bk.boolCtorsTyped
  obtain rfl : ci = ci2 := Option.some.inj (hf.symm.trans hf2)
  have hnt : ci.isTowerEntry = false := by
    cases ci <;> first | rfl | (simp [Ix.Kernel.ConstantInfo.toConstantVal] at hty)
  have h1 := Infer.const (g := .full) (d := 0) hf hnt (us := []) (by simp [hlp])
  simpa [hlp, hty, Ix.Kernel.Expr.instantiateLevelParams] using h1

abbrev boolTrueAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedAt env trueE boolT :=
  .ofInfer (.const _ _) bk.boolTrueInfer

private theorem boolFalseInfer {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    Infer env .full 0 falseE boolT := by
  obtain ⟨-, ⟨ci, hf, hlp⟩⟩ := bk.boolCtorsStored
  obtain ⟨-, ⟨ci2, hf2, hty⟩⟩ := bk.boolCtorsTyped
  obtain rfl : ci = ci2 := Option.some.inj (hf.symm.trans hf2)
  have hnt : ci.isTowerEntry = false := by
    cases ci <;> first | rfl | (simp [Ix.Kernel.ConstantInfo.toConstantVal] at hty)
  have h1 := Infer.const (g := .full) (d := 0) hf hnt (us := []) (by simp [hlp])
  simpa [hlp, hty, Ix.Kernel.Expr.instantiateLevelParams] using h1

abbrev boolFalseAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ClosedAt env falseE boolT :=
  .ofInfer (.const _ _) bk.boolFalseInfer

theorem red_natZero_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    Red env 0 natZeroE (.lit (.natVal 0)) :=
  .natZeroLit bk.natLit

theorem red_natSucc_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) (n : Nat) :
    Red env 0 (.app natSuccE (.lit (.natVal n))) (.lit (.natVal (n + 1))) :=
  .natSucc bk.natLit .refl rfl

theorem red_natPred_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) (n : Nat) :
    Red env 0 (.app (.const Ix.Kernel.natPredName []) (.lit (.natVal n))) (.lit (.natVal (n - 1))) :=
  .natPred (RoleOps.natOpStored_of_storedOk bk.natPredOk) .refl rfl

theorem red_natOp {env : Ix.Kernel.Env .anon} (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames) {a b : Nat} {res : KExpr}
    (hres : Ix.Kernel.natOpResult (.role r) a b = some res) :
    Red env 0 (.app (.app (.const (.role r) []) (.lit (.natVal a))) (.lit (.natVal b))) res :=
  .natOp hm (RoleOps.natOpStored_of_storedOk (bk.natOpsOk r hm)) .refl rfl .refl rfl hres

theorem defEq_natZero_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    DefEq env 0 natZeroE (.lit (.natVal 0)) :=
  .ofRed bk.red_natZero_lit

theorem defEq_natSucc_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) (n : Nat) :
    DefEq env 0 (.app natSuccE (.lit (.natVal n))) (.lit (.natVal (n + 1))) :=
  .ofRed (bk.red_natSucc_lit n)

theorem defEq_natPred_lit {env : Ix.Kernel.Env .anon} (bk : BaseKit env) (n : Nat) :
    DefEq env 0 (.app (.const Ix.Kernel.natPredName []) (.lit (.natVal n))) (.lit (.natVal (n - 1))) :=
  .ofRed (bk.red_natPred_lit n)

theorem defEq_natOp {env : Ix.Kernel.Env .anon} (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames) {a b : Nat} {res : KExpr}
    (hres : Ix.Kernel.natOpResult (.role r) a b = some res) :
    DefEq env 0 (.app (.app (.const (.role r) []) (.lit (.natVal a))) (.lit (.natVal b))) res :=
  .ofRed (bk.red_natOp hm hres)

private theorem substPW_nil (pw : Ix.Kernel.PropWhen) :
    Ix.Kernel.Level.substPW [] [] pw = pw :=
  Ix.Kernel.PropWhen.eq_of_holds fun _ => by
    rw [Ix.Kernel.Level.holds_substPW]; rfl

theorem natPredAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) :
    ∃ mb, Nonempty (ClosedAt env (.const Ix.Kernel.natPredName []) (.forallE natT natT mb)) := by
  obtain ⟨cv, v, hint, hf, hlp, hpin⟩ := RoleOps.natOpStoredOk_inv bk.natPredOk
  unfold Ix.Kernel.natOpTyPinned at hpin
  simp only [↓reduceIte] at hpin
  cases hty : cv.type with
  | forallE dom body mb =>
    rw [hty] at hpin
    simp only [Ix.Kernel.natOpCod, Bool.and_eq_true, beq_iff_eq] at hpin
    have hne1 : Ix.Kernel.natPredName (md := .anon) ≠ Ix.Kernel.natBeqName := by decide
    have hne2 : Ix.Kernel.natPredName (md := .anon) ≠ Ix.Kernel.natBleName := by decide
    simp [hne1, hne2] at hpin
    obtain ⟨rfl, rfl⟩ := hpin
    refine ⟨mb, ⟨.ofInfer (.const _ _) ?_⟩⟩
    have h1 := Infer.const (g := .full) (d := 0) (ci := .defnInfo cv v hint) hf rfl (us := [])
      (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlp])
    simpa [Ix.Kernel.ConstantInfo.toConstantVal, hlp, hty, Ix.Kernel.Expr.instantiateLevelParams,
      substPW_nil] using h1
  | _ => rw [hty] at hpin; cases hpin

theorem natBinNatAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames)
    (hneBeq : (.role r : Core.KKey) ≠ Ix.Kernel.natBeqName)
    (hneBle : (.role r : Core.KKey) ≠ Ix.Kernel.natBleName) :
    ∃ mb1 mb2, Nonempty (ClosedAt env (.const (.role r) []) (.forallE natT (.forallE natT natT mb2) mb1)) := by
  obtain ⟨cv, v, hint, hf, hlp, hpin⟩ := RoleOps.natOpStoredOk_inv (bk.natOpsOk r hm)
  have hnePred : (.role r : Core.KKey) ≠ Ix.Kernel.natPredName := by
    intro h; rw [h] at hm; exact absurd hm (by decide)
  unfold Ix.Kernel.natOpTyPinned at hpin
  simp only [hnePred, ↓reduceIte] at hpin
  cases hty : cv.type with
  | forallE dom rest mb1 =>
    rw [hty] at hpin
    cases rest with
    | forallE dom2 body mb2 =>
      simp [Ix.Kernel.natOpCod, hneBeq, hneBle] at hpin
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hpin
      refine ⟨mb1, mb2, ⟨.ofInfer (.const _ _) ?_⟩⟩
      have h1 := Infer.const (g := .full) (d := 0) (ci := .defnInfo cv v hint) hf rfl (us := [])
        (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlp])
      simpa [Ix.Kernel.ConstantInfo.toConstantVal, hlp, hty, Ix.Kernel.Expr.instantiateLevelParams,
        substPW_nil] using h1
    | _ => simp at hpin
  | _ => rw [hty] at hpin; cases hpin

theorem natBinBoolAt {env : Ix.Kernel.Env .anon} (bk : BaseKit env) {r : Role}
    (hm : (.role r : Core.KKey) ∈ Ix.Kernel.Rules.natBinOpNames)
    (hcmp : (.role r : Core.KKey) = Ix.Kernel.natBeqName ∨ (.role r : Core.KKey) = Ix.Kernel.natBleName) :
    ∃ mb1 mb2, Nonempty (ClosedAt env (.const (.role r) []) (.forallE natT (.forallE natT boolT mb2) mb1)) := by
  obtain ⟨cv, v, hint, hf, hlp, hpin⟩ := RoleOps.natOpStoredOk_inv (bk.natOpsOk r hm)
  have hnePred : (.role r : Core.KKey) ≠ Ix.Kernel.natPredName := by
    rcases hcmp with h | h <;> rw [h] <;> decide
  unfold Ix.Kernel.natOpTyPinned at hpin
  simp only [hnePred, ↓reduceIte] at hpin
  cases hty : cv.type with
  | forallE dom rest mb1 =>
    rw [hty] at hpin
    cases rest with
    | forallE dom2 body mb2 =>
      have hor : ((.role r : Core.KKey) = Ix.Kernel.natBeqName || (.role r : Core.KKey) = Ix.Kernel.natBleName) = true := by
        rcases hcmp with h | h <;> simp [h]
      simp only [Ix.Kernel.natOpCod, hor, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hpin
      obtain ⟨⟨rfl, rfl⟩, rfl, -⟩ := hpin
      refine ⟨mb1, mb2, ⟨.ofInfer (.const _ _) ?_⟩⟩
      have h1 := Infer.const (g := .full) (d := 0) (ci := .defnInfo cv v hint) hf rfl (us := [])
        (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hlp])
      simpa [Ix.Kernel.ConstantInfo.toConstantVal, hlp, hty, Ix.Kernel.Expr.instantiateLevelParams,
        substPW_nil] using h1
    | _ => simp at hpin
  | _ => rw [hty] at hpin; cases hpin

end BaseKit

/-! ## Casts along definitional equality and open-term typing combinators -/

def ClosedType.ofClosedAt {env : Ix.Kernel.Env .anon} {T : KExpr} {u : KLevel}
    (h : ClosedAt env T (.sort u)) : ClosedType env h.witness u :=
  ⟨h.wClosed, .sort u, h.wInfer, .refl⟩

mutual

private theorem red_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {e e' : KExpr}, Red env d e e' → True
  | _, _, _, _ => trivial

private theorem defEq_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {a b : KExpr}, DefEq env d a b → True
  | _, _, _, _ => trivial

private theorem infer_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer env g d e t → True
  | _, _, _, _, _ => trivial

private theorem certs_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {lic : Bool} {T : KExpr} {as : List KExpr}, Ix.Kernel.Rules.Certs env d lic T as → True
  | _, _, _, _, _ => trivial

private theorem defEqList_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {as bs : List KExpr}, Ix.Kernel.Rules.DefEqList env d as bs → True
  | _, _, _, _ => trivial

private theorem etaProjCerts_piRed_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {T : Core.KKey} {us : List KLevel} {targs : List KExpr} {b : KExpr}
      {lps : List Ix.Kernel.LevelParam} {is : List Nat},
      Ix.Kernel.Rules.EtaProjCerts env d T us targs b lps is → True
  | _, _, _, _, _, _, _, _ => trivial

private theorem piRed_toDefEq_aux {env : Ix.Kernel.Env .anon} :
    ∀ {d : Nat} {a b : KExpr}, PiRed env d a b → DefEq env d a b
  | _, _, _, .ofRed hr => .ofRed hr
  | _, _, _, .app hf ha => .app (piRed_toDefEq_aux hf) (piRed_toDefEq_aux ha)
  | _, _, _, .forallE _ hA hB =>
    (DefEq.forallE (piRed_toDefEq_aux hA).symm (piRed_toDefEq_aux hB).symm rfl).symm
  | _, _, _, .lam _ hA hB =>
    (DefEq.lam (piRed_toDefEq_aux hA).symm (piRed_toDefEq_aux hB).symm rfl).symm

end

theorem _root_.Ix.Kernel.Rules.PiRed.toDefEq {env : Ix.Kernel.Env .anon} {d : Nat} {a b : KExpr}
    (h : PiRed env d a b) : DefEq env d a b :=
  piRed_toDefEq_aux h

theorem wscopedB_of_hasFvar_false {d : Nat} :
    ∀ (e : KExpr), e.hasFvar = false → e.wscopedB d = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => by simp [Ix.Kernel.Expr.wscopedB]
  | .fvar _ _, h => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false f h.1, wscopedB_of_hasFvar_false a h.2]
  | .lam t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false t h.1, wscopedB_of_hasFvar_false b h.2]
  | .forallE t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false t h.1, wscopedB_of_hasFvar_false b h.2]
  | .letE t v b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [Ix.Kernel.Expr.wscopedB, wscopedB_of_hasFvar_false t h.1.1,
      wscopedB_of_hasFvar_false v h.1.2, wscopedB_of_hasFvar_false b h.2]
  | .proj _ _ e, h => by
    simp only [Ix.Kernel.Expr.hasFvar] at h
    simp only [Ix.Kernel.Expr.wscopedB]
    exact wscopedB_of_hasFvar_false e h

def ClosedAt.ofRole0_de {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {r : Role} {T₀ T' : KExpr} {u : KLevel} (hr : RoleExactTy env r)
    (hlv0 : roleSpecLevels r = some 0) (hrt : roleTypeExact r = some T₀)
    (hT0cl : TermClosed T₀) (hPi : PiRed env 0 T' T₀) (hT : ClosedType env T' u) :
    ClosedAt env (.const (.role r) []) T' :=
  ClosedAt.ofCast hsc (.const _ _) hT <| by
    obtain ⟨ci, T₁, hf, hnt, hlv, hrt1, hde⟩ := hr
    have hlen : ci.toConstantVal.levelParams.length = 0 :=
      Option.some.inj (hlv.symm.trans hlv0)
    have hlps : ci.toConstantVal.levelParams = [] := List.eq_nil_of_length_eq_zero hlen
    obtain rfl : T₀ = T₁ := Option.some.inj (hrt.symm.trans hrt1)
    have hpos : Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type =
        ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [] := by
      simp [Core.posOf, Core.posLevels, hlps]
    rw [hpos] at hde
    exact ⟨_, .const hf hnt (by simp [hlps]),
      hT.defEq_trans_piRed hT0cl hPi hde hPi.toDefEq.symm⟩

def ClosedAt.ofRole1_de {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {r : Role} {T₀ T' : KExpr} {u v : KLevel} (hr : RoleExactTy env r)
    (hlv1 : roleSpecLevels r = some 1) (hrt : roleTypeExact r = some T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hPi : PiRed env 0 T' (T₀.instantiateLevelParams [0] [u]))
    (hT : ClosedType env T' v) :
    ClosedAt env (.const (.role r) [u]) T' :=
  ClosedAt.ofCast hsc (.const _ _) hT <| by
    obtain ⟨ci, T₁, hf, hnt, hlv, hrt1, hde⟩ := hr
    have hlen : ci.toConstantVal.levelParams.length = 1 :=
      Option.some.inj (hlv.symm.trans hlv1)
    obtain ⟨p, hp⟩ : ∃ p, ci.toConstantVal.levelParams = [p] := by
      cases hl : ci.toConstantVal.levelParams with
      | nil => simp [hl] at hlen
      | cons p rest =>
        cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp [hl] at hlen
    obtain rfl : T₀ = T₁ := Option.some.inj (hrt.symm.trans hrt1)
    have hpos_def : Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type =
        ci.toConstantVal.type.instantiateLevelParams [p] [.param 0] := by
      simp [Core.posOf, Core.posLevels, hp]
    have hwfC := hwf ci (List.mem_of_find?_eq_some hf)
    have hci_lv : ci.toConstantVal.type.allLevelParamsDefined [p] = true := by
      have h1 := hwfC.2.1; rw [hp] at h1; exact h1
    have hci_cl : TermClosed ci.toConstantVal.type := ⟨hwfC.1, hwfC.2.2.2.1⟩
    have hpos_lv : (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type).allLevelParamsDefined [0] = true := by
      rw [hpos_def]
      exact allLevelParamsDefined_instSingle p ci.toConstantVal.type hci_lv
    have hpos_cl : TermClosed (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type) := by
      rw [hpos_def]
      exact ⟨by rw [hasFvar_instLevels]; exact hci_cl.1,
        by rw [looseBVarsBounded_instLevels]; exact hci_cl.2⟩
    have hinst := DefEq.instClosed (d := 0) (ks := [0]) (us := [u]) rfl hpos_lv hTlv
      hpos_cl.1 hpos_cl.2 hT0cl.1 hT0cl.2 hde
    have hcomp : (Core.posOf ci.toConstantVal.levelParams ci.toConstantVal.type).instantiateLevelParams [0] [u] =
        ci.toConstantVal.type.instantiateLevelParams [p] [u] := by
      rw [hpos_def]
      exact instLevelParams_comp_single p u ci.toConstantVal.type hci_lv
    rw [hcomp] at hinst
    have hc1 : Infer env .full 0 (.const (.role r) [u])
        (ci.toConstantVal.type.instantiateLevelParams ci.toConstantVal.levelParams [u]) :=
      .const hf hnt (by simp [hp])
    rw [hp] at hc1
    have hT0instCl : TermClosed (T₀.instantiateLevelParams [0] [u]) :=
      ⟨by rw [hasFvar_instLevels]; exact hT0cl.1, by rw [looseBVarsBounded_instLevels]; exact hT0cl.2⟩
    exact ⟨_, hc1, hT.defEq_trans_piRed hT0instCl hPi hinst hPi.toDefEq.symm⟩

def ClosedAt.ofThm0_de {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon} {val T₀ T' : KExpr} {u : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv0 : cv.levelParams.length = 0)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hT0cl : TermClosed T₀) (hPi : PiRed env 0 T' T₀)
    (hT : ClosedType env T' u) :
    ClosedAt env (.const kThm []) T' :=
  ClosedAt.ofThm0 hsc hf hlv0 (hT.defEq_trans_piRed hT0cl hPi hde hPi.toDefEq.symm) hT

def ClosedAt.ofThm1_de {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon}
    {val T₀ T' : KExpr} {u v : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv1 : cv.levelParams.length = 1)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hPi : PiRed env 0 T' (T₀.instantiateLevelParams [0] [u]))
    (hT : ClosedType env T' v) :
    ClosedAt env (.const kThm [u]) T' :=
  ClosedAt.ofCast hsc (.const _ _) hT <| by
    obtain ⟨p, hp⟩ : ∃ p, cv.levelParams = [p] := by
      cases hl : cv.levelParams with
      | nil => simp [hl] at hlv1
      | cons p rest =>
        cases rest with
        | nil => exact ⟨p, rfl⟩
        | cons _ _ => simp [hl] at hlv1
    have hpos_def : Core.posOf cv.levelParams cv.type =
        cv.type.instantiateLevelParams [p] [.param 0] := by
      simp [Core.posOf, Core.posLevels, hp]
    have hwfC := hwf (.thmInfo cv val) (List.mem_of_find?_eq_some hf)
    have hlpDef : cv.type.allLevelParamsDefined [p] = true := by
      have h1 := hwfC.2.1; simp only [Ix.Kernel.ConstantInfo.toConstantVal, hp] at h1; exact h1
    have hclTy : TermClosed cv.type := ⟨hwfC.1, hwfC.2.2.2.1⟩
    have hposLv : (Core.posOf cv.levelParams cv.type).allLevelParamsDefined [0] = true := by
      rw [hpos_def]
      exact allLevelParamsDefined_instSingle p cv.type hlpDef
    have hposCl : TermClosed (Core.posOf cv.levelParams cv.type) := by
      rw [hpos_def]
      exact ⟨by rw [hasFvar_instLevels]; exact hclTy.1,
             by rw [looseBVarsBounded_instLevels]; exact hclTy.2⟩
    have hinst : DefEq env 0
        ((Core.posOf cv.levelParams cv.type).instantiateLevelParams [0] [u])
        (T₀.instantiateLevelParams [0] [u]) :=
      DefEq.instClosed (ks := [0]) (us := [u]) rfl hposLv hTlv hposCl.1 hposCl.2 hT0cl.1 hT0cl.2 hde
    have hcomp : (Core.posOf cv.levelParams cv.type).instantiateLevelParams [0] [u] =
        cv.type.instantiateLevelParams [p] [u] := by
      rw [hpos_def]
      exact instLevelParams_comp_single p u cv.type hlpDef
    rw [hcomp] at hinst
    have hc1 : Infer env .full 0 (.const kThm [u]) (cv.type.instantiateLevelParams cv.levelParams [u]) :=
      .const (ci := .thmInfo cv val) hf rfl (by simp [Ix.Kernel.ConstantInfo.toConstantVal, hp])
    rw [hp] at hc1
    have hT0instCl : TermClosed (T₀.instantiateLevelParams [0] [u]) :=
      ⟨by rw [hasFvar_instLevels]; exact hT0cl.1, by rw [looseBVarsBounded_instLevels]; exact hT0cl.2⟩
    exact ⟨_, hc1, hT.defEq_trans_piRed hT0instCl hPi hinst hPi.toDefEq.symm⟩

/-! ## Free-variable context invariant (`FVarOk`) and substitution (`fvarSubst`) -/

def fvarUpdate (Γ : Nat → KExpr) (d : Nat) (T : KExpr) : Nat → KExpr :=
  fun i => if i = d then T else Γ i

/-- Every free variable leaf in `e` has index `< d` and annotation equal to `Γ idx`. -/
def FVarOk (d : Nat) (Γ : Nat → KExpr) : KExpr → Prop
  | .fvar idx ty => idx < d ∧ ty = Γ idx
  | .app f a => FVarOk d Γ f ∧ FVarOk d Γ a
  | .lam t b _ | .forallE t b _ => FVarOk d Γ t ∧ FVarOk d Γ b
  | .letE t v b _ => FVarOk d Γ t ∧ FVarOk d Γ v ∧ FVarOk d Γ b
  | .proj _ _ e => FVarOk d Γ e
  | _ => True

theorem FVarOk.hasFvar_false {Γ : Nat → KExpr} :
    ∀ {e : KExpr}, FVarOk 0 Γ e → e.hasFvar = false
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ _, h => absurd h.1 (Nat.not_lt_zero _)
  | .app f a, h => by simp [Ix.Kernel.Expr.hasFvar, FVarOk.hasFvar_false h.1, FVarOk.hasFvar_false h.2]
  | .lam t b _, h => by simp [Ix.Kernel.Expr.hasFvar, FVarOk.hasFvar_false h.1, FVarOk.hasFvar_false h.2]
  | .forallE t b _, h => by simp [Ix.Kernel.Expr.hasFvar, FVarOk.hasFvar_false h.1, FVarOk.hasFvar_false h.2]
  | .letE t v b _, h => by
    simp [Ix.Kernel.Expr.hasFvar, FVarOk.hasFvar_false h.1, FVarOk.hasFvar_false h.2.1,
      FVarOk.hasFvar_false h.2.2]
  | .proj _ _ e, h => FVarOk.hasFvar_false (e := e) h

theorem FVarOk.of_hasFvar_false {d : Nat} {Γ : Nat → KExpr} :
    ∀ {e : KExpr}, e.hasFvar = false → FVarOk d Γ e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => trivial
  | .fvar _ _, h => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨FVarOk.of_hasFvar_false h.1, FVarOk.of_hasFvar_false h.2⟩
  | .lam t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨FVarOk.of_hasFvar_false h.1, FVarOk.of_hasFvar_false h.2⟩
  | .forallE t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨FVarOk.of_hasFvar_false h.1, FVarOk.of_hasFvar_false h.2⟩
  | .letE t v b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    exact ⟨FVarOk.of_hasFvar_false h.1.1, FVarOk.of_hasFvar_false h.1.2, FVarOk.of_hasFvar_false h.2⟩
  | .proj _ _ e, h => FVarOk.of_hasFvar_false (e := e) h

theorem FVarOk.abstract1 {d : Nat} {Γ : Nat → KExpr} {T : KExpr} :
    ∀ {e : KExpr} (k : Nat), FVarOk (d + 1) (fvarUpdate Γ d T) e → FVarOk d Γ (e.abstract1 d k)
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => trivial
  | .fvar idx ty, k, h => by
    simp only [Ix.Kernel.Expr.abstract1]
    by_cases hidx : idx = d
    · simp [hidx, FVarOk]
    · simp only [hidx, ↓reduceIte, FVarOk]
      refine ⟨by have := h.1; omega, ?_⟩
      have h2 := h.2
      simp [fvarUpdate, hidx] at h2
      exact h2
  | .app f a, k, h => ⟨FVarOk.abstract1 k h.1, FVarOk.abstract1 k h.2⟩
  | .lam t b _, k, h => ⟨FVarOk.abstract1 k h.1, FVarOk.abstract1 (k + 1) h.2⟩
  | .forallE t b _, k, h => ⟨FVarOk.abstract1 k h.1, FVarOk.abstract1 (k + 1) h.2⟩
  | .letE t v b _, k, h => ⟨FVarOk.abstract1 k h.1, FVarOk.abstract1 k h.2.1, FVarOk.abstract1 (k + 1) h.2.2⟩
  | .proj _ _ e, k, h => FVarOk.abstract1 (e := e) k h

theorem looseBVarsBounded_abstract1' {d : Nat} :
    ∀ {e : KExpr} {k : Nat}, e.looseBVarsBounded k = true →
      (e.abstract1 d k).looseBVarsBounded (k + 1) = true
  | .bvar i, k, h => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h ⊢
    omega
  | .fvar idx _, k, _ => by
    simp only [Ix.Kernel.Expr.abstract1]
    split <;> simp [Ix.Kernel.Expr.looseBVarsBounded]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_abstract1' h.1, looseBVarsBounded_abstract1' h.2]
  | .lam t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_abstract1' h.1, looseBVarsBounded_abstract1' h.2]
  | .forallE t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_abstract1' h.1, looseBVarsBounded_abstract1' h.2]
  | .letE t v b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.looseBVarsBounded,
      looseBVarsBounded_abstract1' h.1.1, looseBVarsBounded_abstract1' h.1.2,
      looseBVarsBounded_abstract1' h.2]
  | .proj _ _ e, k, h => looseBVarsBounded_abstract1' (e := e) h

/-- Replace every `.fvar d _` leaf with `v` (mirroring `abstract1` without descending into
`fvar` type annotations). -/
def fvarSubst (d : Nat) (v : KExpr) : KExpr → KExpr
  | .fvar idx ty => if idx = d then v else .fvar idx ty
  | .app f a => .app (fvarSubst d v f) (fvarSubst d v a)
  | .lam t b m => .lam (fvarSubst d v t) (fvarSubst d v b) m
  | .forallE t b m => .forallE (fvarSubst d v t) (fvarSubst d v b) m
  | .letE t val b m => .letE (fvarSubst d v t) (fvarSubst d v val) (fvarSubst d v b) m
  | .proj s i e => .proj s i (fvarSubst d v e)
  | e => e

theorem fvarSubst_of_not_hasFvar {d : Nat} {v : KExpr} :
    ∀ {e : KExpr}, e.hasFvar = false → fvarSubst d v e = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar _ _, h => by simp [Ix.Kernel.Expr.hasFvar] at h
  | .app f a, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarSubst, fvarSubst_of_not_hasFvar h.1, fvarSubst_of_not_hasFvar h.2]
  | .lam t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarSubst, fvarSubst_of_not_hasFvar h.1, fvarSubst_of_not_hasFvar h.2]
  | .forallE t b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarSubst, fvarSubst_of_not_hasFvar h.1, fvarSubst_of_not_hasFvar h.2]
  | .letE t val b _, h => by
    simp only [Ix.Kernel.Expr.hasFvar, Bool.or_eq_false_iff] at h
    simp [fvarSubst, fvarSubst_of_not_hasFvar h.1.1, fvarSubst_of_not_hasFvar h.1.2,
      fvarSubst_of_not_hasFvar h.2]
  | .proj _ _ e, h => by simp [fvarSubst, fvarSubst_of_not_hasFvar (e := e) h]

theorem abstract1_instantiate1_eq_fvarSubst {d : Nat} {v : KExpr} :
    ∀ {e : KExpr} {k : Nat}, e.looseBVarsBounded k = true →
      (e.abstract1 d k).instantiate1 v k = fvarSubst d v e
  | .bvar i, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, decide_eq_true_eq] at h
    simp [Ix.Kernel.Expr.abstract1, fvarSubst,
      show ¬ (i = k) by omega, show ¬ (i > k) by omega]
  | .fvar idx ty, k, _ => by
    simp only [Ix.Kernel.Expr.abstract1, fvarSubst]
    split <;> simp [Ix.Kernel.Expr.instantiate1]
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1, fvarSubst,
      abstract1_instantiate1_eq_fvarSubst h.1, abstract1_instantiate1_eq_fvarSubst h.2]
  | .lam t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1, fvarSubst,
      abstract1_instantiate1_eq_fvarSubst h.1, abstract1_instantiate1_eq_fvarSubst h.2]
  | .forallE t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1, fvarSubst,
      abstract1_instantiate1_eq_fvarSubst h.1, abstract1_instantiate1_eq_fvarSubst h.2]
  | .letE t val b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1, fvarSubst,
      abstract1_instantiate1_eq_fvarSubst h.1.1, abstract1_instantiate1_eq_fvarSubst h.1.2,
      abstract1_instantiate1_eq_fvarSubst h.2]
  | .proj _ _ e, k, h => by
    simp only [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.instantiate1, fvarSubst,
      abstract1_instantiate1_eq_fvarSubst (e := e) h]

theorem FVarOk.fvarSubst_self {d : Nat} {Γ : Nat → KExpr} {T : KExpr} :
    ∀ {e : KExpr}, FVarOk (d + 1) (fvarUpdate Γ d T) e → fvarSubst d (.fvar d T) e = e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar idx ty, h => by
    simp only [fvarSubst]
    by_cases hidx : idx = d
    · subst hidx
      have h2 := h.2
      simp [fvarUpdate] at h2
      simp [h2]
    · simp [hidx]
  | .app f a, h => by simp [fvarSubst, FVarOk.fvarSubst_self h.1, FVarOk.fvarSubst_self h.2]
  | .lam t b _, h => by simp [fvarSubst, FVarOk.fvarSubst_self h.1, FVarOk.fvarSubst_self h.2]
  | .forallE t b _, h => by simp [fvarSubst, FVarOk.fvarSubst_self h.1, FVarOk.fvarSubst_self h.2]
  | .letE t v b _, h => by
    simp [fvarSubst, FVarOk.fvarSubst_self h.1, FVarOk.fvarSubst_self h.2.1,
      FVarOk.fvarSubst_self h.2.2]
  | .proj _ _ e, h => by simp [fvarSubst, FVarOk.fvarSubst_self (e := e) h]

theorem FVarOk.abstract1_instantiate1 {d : Nat} {Γ : Nat → KExpr} {T e : KExpr} {k : Nat}
    (hok : FVarOk (d + 1) (fvarUpdate Γ d T) e) (hbl : e.looseBVarsBounded k = true) :
    (e.abstract1 d k).instantiate1 (.fvar d T) k = e := by
  rw [abstract1_instantiate1_eq_fvarSubst hbl, hok.fvarSubst_self]

theorem fvarSubst_abstract1_comm_gen {d₁ d₂ : Nat} {v : KExpr} (hne : d₁ ≠ d₂)
    (hv : ∀ k, v.abstract1 d₂ k = v) :
    ∀ {e : KExpr} {k : Nat},
      (fvarSubst d₁ v e).abstract1 d₂ k = fvarSubst d₁ v (e.abstract1 d₂ k)
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => rfl
  | .fvar idx ty, k => by
    by_cases h1 : idx = d₁
    · subst h1
      simp only [fvarSubst, ↓reduceIte, Ix.Kernel.Expr.abstract1, hne, hv k]
    · by_cases h2 : idx = d₂
      · subst h2
        simp [fvarSubst, Ix.Kernel.Expr.abstract1, h1]
      · simp [fvarSubst, Ix.Kernel.Expr.abstract1, h1, h2]
  | .app f a, k => by
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, fvarSubst_abstract1_comm_gen hne hv]
  | .lam t b _, k => by
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, fvarSubst_abstract1_comm_gen hne hv]
  | .forallE t b _, k => by
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, fvarSubst_abstract1_comm_gen hne hv]
  | .letE t val b _, k => by
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, fvarSubst_abstract1_comm_gen hne hv]
  | .proj _ _ e, k => by
    simp [fvarSubst, Ix.Kernel.Expr.abstract1, fvarSubst_abstract1_comm_gen (e := e) hne hv]

theorem fvarSubst_abstract1_comm {d₁ d₂ : Nat} {v : KExpr} (hne : d₁ ≠ d₂)
    (hv : v.hasFvar = false) {e : KExpr} {k : Nat} :
    (fvarSubst d₁ v e).abstract1 d₂ k = fvarSubst d₁ v (e.abstract1 d₂ k) :=
  fvarSubst_abstract1_comm_gen hne (fun _ => abstract1_eq_self v hv)

theorem fvarSubst_abstract1_comm_fvar {d₁ d₂ : Nat} {ty : KExpr} (hne : d₁ ≠ d₂)
    {e : KExpr} {k : Nat} :
    (fvarSubst d₁ (.fvar d₁ ty) e).abstract1 d₂ k = fvarSubst d₁ (.fvar d₁ ty) (e.abstract1 d₂ k) :=
  fvarSubst_abstract1_comm_gen hne (fun _ => by simp [Ix.Kernel.Expr.abstract1, hne])

theorem fvarSubst_looseBVarsBounded {d : Nat} {v : KExpr} (hv : v.looseBVarsBounded 0 = true) :
    ∀ {e : KExpr} {k : Nat}, e.looseBVarsBounded k = true →
      (fvarSubst d v e).looseBVarsBounded k = true
  | .bvar _, _, h => h
  | .fvar idx _, k, _ => by
    simp only [fvarSubst]
    split
    · exact looseBVarsBounded_mono v (Nat.zero_le k) hv
    · rfl
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [fvarSubst, Ix.Kernel.Expr.looseBVarsBounded,
      fvarSubst_looseBVarsBounded hv h.1, fvarSubst_looseBVarsBounded hv h.2]
  | .lam t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [fvarSubst, Ix.Kernel.Expr.looseBVarsBounded,
      fvarSubst_looseBVarsBounded hv h.1, fvarSubst_looseBVarsBounded hv h.2]
  | .forallE t b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [fvarSubst, Ix.Kernel.Expr.looseBVarsBounded,
      fvarSubst_looseBVarsBounded hv h.1, fvarSubst_looseBVarsBounded hv h.2]
  | .letE t val b _, k, h => by
    simp only [Ix.Kernel.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp [fvarSubst, Ix.Kernel.Expr.looseBVarsBounded,
      fvarSubst_looseBVarsBounded hv h.1.1, fvarSubst_looseBVarsBounded hv h.1.2,
      fvarSubst_looseBVarsBounded hv h.2]
  | .proj _ _ e, k, h => fvarSubst_looseBVarsBounded (e := e) hv h

theorem fvarSubst_defEq {env : Ix.Kernel.Env .anon} {d i : Nat} {v₁ v₂ : KExpr}
    (hv : DefEq env d v₁ v₂) :
    ∀ {e : KExpr}, isSimpleExpr e = true →
      DefEq env d (fvarSubst i v₁ e) (fvarSubst i v₂ e)
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => .refl
  | .fvar idx _, _ => by
    simp only [fvarSubst]
    split
    · exact hv
    · exact .refl
  | .app f a, h => by
    simp only [isSimpleExpr, Bool.and_eq_true] at h
    exact .app (fvarSubst_defEq hv h.1) (fvarSubst_defEq hv h.2)

def ClosedAt.app_abs {env : Ix.Kernel.Env .anon} {f a A B ta : KExpr} {d : Nat}
    {mb : Ix.Kernel.BinderMeta}
    (hf : ClosedAt env f (.forallE A (B.abstract1 d) mb))
    (ha : ClosedAt env a ta) (hta : DefEq env 0 ta A)
    (hBl : B.looseBVarsBounded 0 = true) :
    ClosedAt env (.app f a) (fvarSubst d ha.witness B) := by
  have h1 := hf.app_dep_raw ha hta
  rwa [abstract1_instantiate1_eq_fvarSubst hBl] at h1

/-- Every free-variable type annotation in `Γ` below `d` is well-scoped below its own index. -/
def CtxWs (d : Nat) (Γ : Nat → KExpr) : Prop :=
  ∀ i < d, (Γ i).wscopedB i = true

theorem CtxWs.zero (Γ : Nat → KExpr) : CtxWs 0 Γ :=
  fun _ h => absurd h (Nat.not_lt_zero _)

theorem CtxWs.update {d : Nat} {Γ : Nat → KExpr} {T : KExpr}
    (hΓ : CtxWs d Γ) (hT : T.wscopedB d = true) :
    CtxWs (d + 1) (fvarUpdate Γ d T) := by
  intro i hi
  by_cases h : i = d
  · subst h; simpa [fvarUpdate] using hT
  · simpa [fvarUpdate, h] using hΓ i (by omega)

theorem FVarOk.wscopedB {d : Nat} {Γ : Nat → KExpr} (hΓ : CtxWs d Γ) :
    ∀ (e : KExpr), FVarOk d Γ e → e.wscopedB d = true
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => by simp [Ix.Kernel.Expr.wscopedB]
  | .fvar idx ty, h => by
    obtain ⟨hlt, rfl⟩ := h
    simp [Ix.Kernel.Expr.wscopedB, hlt, hΓ idx hlt]
  | .app f a, h => by
    simp [Ix.Kernel.Expr.wscopedB, FVarOk.wscopedB hΓ f h.1, FVarOk.wscopedB hΓ a h.2]
  | .lam t b _, h => by
    simp [Ix.Kernel.Expr.wscopedB, FVarOk.wscopedB hΓ t h.1, FVarOk.wscopedB hΓ b h.2]
  | .forallE t b _, h => by
    simp [Ix.Kernel.Expr.wscopedB, FVarOk.wscopedB hΓ t h.1, FVarOk.wscopedB hΓ b h.2]
  | .letE t v b _, h => by
    simp [Ix.Kernel.Expr.wscopedB, FVarOk.wscopedB hΓ t h.1,
      FVarOk.wscopedB hΓ v h.2.1, FVarOk.wscopedB hΓ b h.2.2]
  | .proj _ _ e, h => by
    simp only [FVarOk] at h
    simp only [Ix.Kernel.Expr.wscopedB]
    exact FVarOk.wscopedB hΓ e h

theorem FVarOk.of_instantiate1 {d : Nat} {Γ : Nat → KExpr} {T : KExpr} :
    ∀ (e : KExpr) (k : Nat),
      e.wscopedB d = true →
      FVarOk (d + 1) (fvarUpdate Γ d T) (e.instantiate1 (.fvar d T) k) →
      FVarOk d Γ e
  | .bvar _, _, _, _ | .sort _, _, _, _ | .const _ _, _, _, _ | .lit _, _, _, _ => trivial
  | .fvar idx ty, _, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true, decide_eq_true_eq] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    have hne : idx ≠ d := Nat.ne_of_lt hws.1
    have h2 := hok.2
    simp only [fvarUpdate, hne, ↓reduceIte] at h2
    exact ⟨hws.1, h2⟩
  | .app f a, k, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    exact ⟨FVarOk.of_instantiate1 f k hws.1 hok.1, FVarOk.of_instantiate1 a k hws.2 hok.2⟩
  | .lam t b _, k, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    exact ⟨FVarOk.of_instantiate1 t k hws.1 hok.1, FVarOk.of_instantiate1 b (k + 1) hws.2 hok.2⟩
  | .forallE t b _, k, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    exact ⟨FVarOk.of_instantiate1 t k hws.1 hok.1, FVarOk.of_instantiate1 b (k + 1) hws.2 hok.2⟩
  | .letE t v b _, k, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB, Bool.and_eq_true] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    exact ⟨FVarOk.of_instantiate1 t k hws.1.1 hok.1,
      FVarOk.of_instantiate1 v k hws.1.2 hok.2.1,
      FVarOk.of_instantiate1 b (k + 1) hws.2 hok.2.2⟩
  | .proj _ _ e, k, hws, hok => by
    simp only [Ix.Kernel.Expr.wscopedB] at hws
    simp only [Ix.Kernel.Expr.instantiate1, FVarOk] at hok
    exact FVarOk.of_instantiate1 e k hws hok

theorem FVarOk.abstract1_of_fvarSubst {d : Nat} {Γ : Nat → KExpr} {T : KExpr} :
    ∀ (e : KExpr) (k : Nat),
      FVarOk (d + 1) (fvarUpdate Γ d T) (fvarSubst d (.fvar d T) e) →
      FVarOk d Γ (e.abstract1 d k)
  | .bvar _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => trivial
  | .fvar idx ty, k, hok => by
    by_cases hidx : idx = d
    · simp [Ix.Kernel.Expr.abstract1, hidx, FVarOk]
    · simp only [fvarSubst, hidx, ↓reduceIte, FVarOk, fvarUpdate] at hok
      simp only [Ix.Kernel.Expr.abstract1, hidx, ↓reduceIte, FVarOk]
      exact ⟨by omega, hok.2⟩
  | .app f a, k, hok => by
    simp only [fvarSubst, FVarOk] at hok
    exact ⟨FVarOk.abstract1_of_fvarSubst f k hok.1, FVarOk.abstract1_of_fvarSubst a k hok.2⟩
  | .lam t b _, k, hok => by
    simp only [fvarSubst, FVarOk] at hok
    exact ⟨FVarOk.abstract1_of_fvarSubst t k hok.1, FVarOk.abstract1_of_fvarSubst b (k + 1) hok.2⟩
  | .forallE t b _, k, hok => by
    simp only [fvarSubst, FVarOk] at hok
    exact ⟨FVarOk.abstract1_of_fvarSubst t k hok.1, FVarOk.abstract1_of_fvarSubst b (k + 1) hok.2⟩
  | .letE t v b _, k, hok => by
    simp only [fvarSubst, FVarOk] at hok
    exact ⟨FVarOk.abstract1_of_fvarSubst t k hok.1,
      FVarOk.abstract1_of_fvarSubst v k hok.2.1,
      FVarOk.abstract1_of_fvarSubst b (k + 1) hok.2.2⟩
  | .proj _ _ e, k, hok => by
    simp only [fvarSubst, FVarOk] at hok
    simp only [Ix.Kernel.Expr.abstract1, FVarOk]
    exact FVarOk.abstract1_of_fvarSubst e k hok

/-! ## Open-term and open-type witness combinators (`OpenAt`, `OpenType`) -/

/-- Open term `e` at depth `d` under context `Γ`, witnessed by `w` with `Infer env .full d w T`
and `PiRed env d w e`. -/
structure OpenAt (env : Ix.Kernel.Env .anon) (d : Nat) (Γ : Nat → KExpr) (e w T : KExpr) : Prop where
  wOk : FVarOk d Γ w
  wClosed : w.looseBVarsBounded 0 = true
  eOk : FVarOk d Γ e
  eClosed : e.looseBVarsBounded 0 = true
  wInfer : Infer env .full d w T
  wPiRed : PiRed env d w e

theorem OpenAt.wDe {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr} {e w T : KExpr}
    (h : OpenAt env d Γ e w T) : DefEq env d e w :=
  h.wPiRed.toDefEq.symm

/-- Open type `e` at depth `d` under context `Γ`, witnessed by `w` of sort `u` with
`PiRed env d w e`. -/
structure OpenType (env : Ix.Kernel.Env .anon) (d : Nat) (Γ : Nat → KExpr)
    (e w : KExpr) (u : KLevel) where
  wOk : FVarOk d Γ w
  wClosed : w.looseBVarsBounded 0 = true
  eOk : FVarOk d Γ e
  eClosed : e.looseBVarsBounded 0 = true
  sortExpr : KExpr
  wInfer : Infer env .full d w sortExpr
  wRed : Red env d sortExpr (.sort u)
  wPiRed : PiRed env d w e

theorem OpenType.wDe {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {e w : KExpr} {u : KLevel} (h : OpenType env d Γ e w u) :
    DefEq env d e w :=
  h.wPiRed.toDefEq.symm

theorem OpenType.eTermClosed {env : Ix.Kernel.Env .anon} {Γ : Nat → KExpr}
    {e w : KExpr} {u : KLevel} (h : OpenType env 0 Γ e w u) :
    TermClosed e :=
  ⟨h.eOk.hasFvar_false, h.eClosed⟩

theorem OpenAt.ofClosed {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {d : Nat} {Γ : Nat → KExpr} {a T : KExpr}
    (ha : ClosedAt env a T) (hTf : T.hasFvar = false) :
    OpenAt env d Γ a ha.witness T := by
  have hi := Infer.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := d) ha.wInfer
  have hr := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := d) ha.wRed
  rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar ha.wClosed.1,
      Ix.Kernel.Expr.renFV_of_not_hasFvar hTf] at hi
  rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar ha.wClosed.1,
      Ix.Kernel.Expr.renFV_of_not_hasFvar ha.closed.1] at hr
  exact ⟨FVarOk.of_hasFvar_false ha.wClosed.1, ha.wClosed.2,
    FVarOk.of_hasFvar_false ha.closed.1, ha.closed.2, hi, .ofRed hr⟩

theorem OpenAt.fvar {env : Ix.Kernel.Env .anon} {d idx : Nat} {Γ : Nat → KExpr} (hlt : idx < d) :
    OpenAt env d Γ (.fvar idx (Γ idx)) (.fvar idx (Γ idx)) (Γ idx) :=
  ⟨⟨hlt, rfl⟩, rfl, ⟨hlt, rfl⟩, rfl, .fvar hlt, .ofRed .refl⟩

theorem OpenAt.app_nondep {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {f fw a aw A B ta : KExpr} {mb : Ix.Kernel.BinderMeta}
    (hf : OpenAt env d Γ f fw (.forallE A B mb))
    (ha : OpenAt env d Γ a aw ta) (hta : DefEq env d ta A)
    (hBl : B.looseBVarsBounded 0 = true) :
    OpenAt env d Γ (.app f a) (.app fw aw) B := by
  have hi := Infer.app hf.wInfer .refl ha.wInfer hta
  rw [instantiate1_eq_self B hBl] at hi
  exact ⟨⟨hf.wOk, ha.wOk⟩, by simp [Ix.Kernel.Expr.looseBVarsBounded, hf.wClosed, ha.wClosed],
    ⟨hf.eOk, ha.eOk⟩, by simp [Ix.Kernel.Expr.looseBVarsBounded, hf.eClosed, ha.eClosed],
    hi, .app hf.wPiRed ha.wPiRed⟩

theorem OpenAt.app_dep {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {f fw a aw A B ta : KExpr} {mb : Ix.Kernel.BinderMeta}
    (hf : OpenAt env d Γ f fw (.forallE A B mb))
    (ha : OpenAt env d Γ a aw ta) (hta : DefEq env d ta A) :
    OpenAt env d Γ (.app f a) (.app fw aw) (B.instantiate1 aw) :=
  ⟨⟨hf.wOk, ha.wOk⟩, by simp [Ix.Kernel.Expr.looseBVarsBounded, hf.wClosed, ha.wClosed],
    ⟨hf.eOk, ha.eOk⟩, by simp [Ix.Kernel.Expr.looseBVarsBounded, hf.eClosed, ha.eClosed],
    Infer.app hf.wInfer .refl ha.wInfer hta, .app hf.wPiRed ha.wPiRed⟩

theorem OpenAt.app_abs {env : Ix.Kernel.Env .anon} {d i : Nat} {Γ : Nat → KExpr}
    {f fw a aw A B ta : KExpr} {mb : Ix.Kernel.BinderMeta}
    (hf : OpenAt env d Γ f fw (.forallE A (B.abstract1 i) mb))
    (ha : OpenAt env d Γ a aw ta) (hta : DefEq env d ta A)
    (hBl : B.looseBVarsBounded 0 = true) :
    OpenAt env d Γ (.app f a) (.app fw aw) (fvarSubst i aw B) := by
  have h1 := hf.app_dep ha hta
  rwa [abstract1_instantiate1_eq_fvarSubst hBl] at h1

def OpenType.ofOpenAt {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {e w : KExpr} {u : KLevel} (h : OpenAt env d Γ e w (.sort u)) :
    OpenType env d Γ e w u :=
  ⟨h.wOk, h.wClosed, h.eOk, h.eClosed, .sort u, h.wInfer, .refl, h.wPiRed⟩

def OpenType.sort {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr} (u : KLevel) :
    OpenType env d Γ (.sort u) (.sort u) (.succ u) :=
  ⟨trivial, rfl, trivial, rfl, .sort (.succ u), .sort, .refl, .ofRed .refl⟩

def OpenType.ofClosed {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {d : Nat} {Γ : Nat → KExpr} {T : KExpr} {u : KLevel} (h : ClosedType env T u) :
    OpenType env d Γ T T u :=
  ⟨FVarOk.of_hasFvar_false h.closed.1, h.closed.2,
    FVarOk.of_hasFvar_false h.closed.1, h.closed.2,
    h.sortExpr.renFV (fun i => if i < 0 then i else i + d),
    by
      have hi := Infer.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := d) h.infer
      rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar h.closed.1] at hi
      exact hi,
    by
      have hr := Red.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := d) h.redSort
      rw [Nat.zero_add] at hr
      simpa [Ix.Kernel.Expr.renFV] using hr,
    .ofRed .refl⟩

def OpenType.liftClosed {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {d : Nat} {Γ : Nat → KExpr} {C Cw : KExpr} {u : KLevel}
    (hC : ClosedType env Cw u) (hPi : PiRed env 0 Cw C) (hCcl : TermClosed C) :
    OpenType env d Γ C Cw u :=
  let h0 := OpenType.ofClosed hsc (d := d) (Γ := Γ) hC
  ⟨h0.wOk, h0.wClosed, FVarOk.of_hasFvar_false hCcl.1, hCcl.2, h0.sortExpr, h0.wInfer, h0.wRed, by
    have hpi := PiRed.lift (Ix.Kernel.EnvExt.refl env) hsc (p := 0) (g := d) hPi
    rw [Nat.zero_add, Ix.Kernel.Expr.renFV_of_not_hasFvar hC.closed.1,
        Ix.Kernel.Expr.renFV_of_not_hasFvar hCcl.1] at hpi
    exact hpi⟩

def OpenType.ofClosedAt {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {d : Nat} {Γ : Nat → KExpr} {T : KExpr} {u : KLevel} (h : ClosedAt env T (.sort u)) :
    OpenType env d Γ T h.witness u :=
  OpenType.ofOpenAt (OpenAt.ofClosed hsc h rfl)

theorem OpenAt.eq {env : Ix.Kernel.Env .anon}
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {d : Nat} {Γ : Nat → KExpr} {C Cw a aw b bw ta tb : KExpr} {u : KLevel}
    (hC : OpenType env d Γ C Cw u)
    (ha : OpenAt env d Γ a aw ta) (haDe : DefEq env d ta Cw)
    (hb : OpenAt env d Γ b bw tb) (hbDe : DefEq env d tb Cw) :
    OpenAt env d Γ
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) C) a) b)
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) Cw) aw) bw)
      (.sort .zero) := by
  obtain ⟨hlps, m1, m2, m3, hty⟩ := eqA_type_shape
  have hcEq : Infer env .full d (.const Ix.Kernel.eqName [u])
      ((Ix.Kernel.eqA (md := .anon)).toConstantVal.type.instantiateLevelParams [Ix.Kernel.uN] [u]) :=
    .const heq rfl (by simp [hlps])
  rw [hty] at hcEq
  simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Level.subst,
    Ix.Kernel.Level.subst.go, ↓reduceIte] at hcEq
  have h1 := Infer.app hcEq .refl hC.wInfer (.ofRed hC.wRed)
  simp [Ix.Kernel.Expr.instantiate1] at h1
  have h2 := Infer.app h1 .refl ha.wInfer haDe
  simp only [Ix.Kernel.Expr.instantiate1, instantiate1_eq_self Cw hC.wClosed] at h2
  have h3 : Infer env .full d (.app (.app (.app (.const Ix.Kernel.eqName [u]) Cw) aw) bw) (.sort .zero) := by
    have := Infer.app h2 .refl hb.wInfer hbDe
    simpa [Ix.Kernel.Expr.instantiate1] using this
  exact ⟨⟨⟨⟨trivial, hC.wOk⟩, ha.wOk⟩, hb.wOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hC.wClosed, ha.wClosed, hb.wClosed],
    ⟨⟨⟨trivial, hC.eOk⟩, ha.eOk⟩, hb.eOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hC.eClosed, ha.eClosed, hb.eClosed],
    h3, .app (.app (.app (.ofRed .refl) hC.wPiRed) ha.wPiRed) hb.wPiRed⟩

def OpenType.eq {env : Ix.Kernel.Env .anon}
    (heq : env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA)
    {d : Nat} {Γ : Nat → KExpr} {C Cw a aw b bw ta tb : KExpr} {u : KLevel}
    (hC : OpenType env d Γ C Cw u)
    (ha : OpenAt env d Γ a aw ta) (haDe : DefEq env d ta Cw)
    (hb : OpenAt env d Γ b bw tb) (hbDe : DefEq env d tb Cw) :
    OpenType env d Γ
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) C) a) b)
      (.app (.app (.app (.const Ix.Kernel.eqName [u]) Cw) aw) bw)
      .zero :=
  OpenType.ofOpenAt (OpenAt.eq heq hC ha haDe hb hbDe)

def OpenType.forallE {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyE bodyW : KExpr} {u v : KLevel} {mb : Ix.Kernel.BinderMeta}
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenType env (d + 1) (fvarUpdate Γ d domW) (bodyE.instantiate1 (.fvar d domW)) bodyW v)
    (hmb : v.zeronessOf = mb.pw)
    (hBws : bodyE.wscopedB d = true := by simp [Ix.Kernel.Expr.wscopedB])
    (hBlbb : bodyE.looseBVarsBounded 1 = true := by simp [Ix.Kernel.Expr.looseBVarsBounded]) :
    OpenType env d Γ (.forallE dom bodyE mb) (.forallE domW (bodyW.abstract1 d) mb) (.imax u v) :=
  ⟨⟨hDom.wOk, hBody.wOk.abstract1 0⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.wClosed, looseBVarsBounded_abstract1' hBody.wClosed],
    ⟨hDom.eOk, FVarOk.of_instantiate1 bodyE 0 hBws hBody.eOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.eClosed, hBlbb],
    .sort (.imax u v),
    by
      have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
      exact .forallE hDom.wInfer hDom.wRed (by rw [hround]; exact hBody.wInfer) hBody.wRed hmb,
    .refl,
    by
      have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
      exact .forallE hBws hDom.wPiRed (by rw [hround]; exact hBody.wPiRed)⟩

def OpenType.forallE_abs {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyRaw bodyW : KExpr} {u v : KLevel} {pw : Ix.Kernel.PropWhen}
    (hbl : bodyRaw.looseBVarsBounded 0 = true)
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenType env (d + 1) (fvarUpdate Γ d domW) (fvarSubst d (.fvar d domW) bodyRaw) bodyW v)
    (hmb : v.zeronessOf = pw)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenType env d Γ (.forallE dom (bodyRaw.abstract1 d) { pw := pw })
      (.forallE domW (bodyW.abstract1 d) { pw := pw }) (.imax u v) :=
  OpenType.forallE hDom
    (by rwa [abstract1_instantiate1_eq_fvarSubst hbl])
    hmb
    ((FVarOk.abstract1_of_fvarSubst bodyRaw 0 hBody.eOk).wscopedB hCtx)
    (looseBVarsBounded_abstract1' hbl)

def OpenType.forallE_abs_id {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyE bodyW : KExpr} {u v : KLevel} {pw : Ix.Kernel.PropWhen}
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenType env (d + 1) (fvarUpdate Γ d domW) bodyE bodyW v)
    (hmb : v.zeronessOf = pw)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenType env d Γ (.forallE dom (bodyE.abstract1 d) { pw := pw })
      (.forallE domW (bodyW.abstract1 d) { pw := pw }) (.imax u v) :=
  OpenType.forallE hDom
    (by rw [hBody.eOk.abstract1_instantiate1 hBody.eClosed]; exact hBody)
    hmb
    ((hBody.eOk.abstract1 0).wscopedB hCtx)
    (looseBVarsBounded_abstract1' hBody.eClosed)

def OpenType.toClosedType {env : Ix.Kernel.Env .anon} {Γ : Nat → KExpr}
    {e w : KExpr} {u : KLevel} (h : OpenType env 0 Γ e w u) :
    ClosedType env w u :=
  ⟨⟨h.wOk.hasFvar_false, h.wClosed⟩, h.sortExpr, h.wInfer, h.wRed⟩

def ClosedAt.ofRole0_open {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {r : Role} {Γ : Nat → KExpr} {T₀ T' : KExpr} {u : KLevel} (hr : RoleExactTy env r)
    (hlv0 : roleSpecLevels r = some 0) (hrt : roleTypeExact r = some T₀)
    (hO : OpenType env 0 Γ T₀ T' u) :
    ClosedAt env (.const (.role r) []) T' :=
  ClosedAt.ofRole0_de hsc hr hlv0 hrt hO.eTermClosed hO.wPiRed hO.toClosedType

def ClosedAt.ofRole1_open {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {r : Role} {Γ : Nat → KExpr} {T₀ T' : KExpr} {u v : KLevel}
    (hr : RoleExactTy env r) (hlv1 : roleSpecLevels r = some 1) (hrt : roleTypeExact r = some T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hO : OpenType env 0 Γ (T₀.instantiateLevelParams [0] [u]) T' v) :
    ClosedAt env (.const (.role r) [u]) T' :=
  ClosedAt.ofRole1_de hsc hwf hr hlv1 hrt hTlv hT0cl hO.wPiRed hO.toClosedType

def ClosedAt.ofThm0_open {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon} {Γ : Nat → KExpr} {val T₀ T' : KExpr}
    {u : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv0 : cv.levelParams.length = 0)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hO : OpenType env 0 Γ T₀ T' u) :
    ClosedAt env (.const kThm []) T' :=
  ClosedAt.ofThm0_de hsc hf hlv0 hde hO.eTermClosed hO.wPiRed hO.toClosedType

def ClosedAt.ofThm1_open {env : Ix.Kernel.Env .anon} (hsc : Ix.Kernel.StoreClosed env)
    (hwf : Ix.Kernel.EnvWF env) {kThm : Core.KKey} {cv : Ix.Kernel.ConstantVal .anon}
    {Γ : Nat → KExpr} {val T₀ T' : KExpr} {u v : KLevel}
    (hf : env.find? kThm = some (.thmInfo cv val))
    (hlv1 : cv.levelParams.length = 1)
    (hde : DefEq env 0 (Core.posOf cv.levelParams cv.type) T₀)
    (hTlv : T₀.allLevelParamsDefined [0] = true) (hT0cl : TermClosed T₀)
    (hO : OpenType env 0 Γ (T₀.instantiateLevelParams [0] [u]) T' v) :
    ClosedAt env (.const kThm [u]) T' :=
  ClosedAt.ofThm1_de hsc hwf hf hlv1 hde hTlv hT0cl hO.wPiRed hO.toClosedType

theorem lamPw_abstract1 {d k : Nat} :
    ∀ (e : KExpr), (e.abstract1 d k).lamPw = e.lamPw
  | .bvar _ | .sort _ | .const _ _ | .lit _ | .app _ _ | .forallE _ _ _ | .letE _ _ _ _ | .proj _ _ _ => rfl
  | .fvar idx _ => by simp only [Ix.Kernel.Expr.abstract1]; split <;> rfl
  | .lam _ _ _ => rfl

/-- Build an `OpenAt` for the innermost lambda abstraction over a non-lambda body `bodyW`. -/
theorem OpenAt.lam_abs_inner {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyRaw bodyW T sT : KExpr} {u v : KLevel} {pw : Ix.Kernel.PropWhen}
    (hbl : bodyRaw.looseBVarsBounded 0 = true)
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenAt env (d + 1) (fvarUpdate Γ d domW)
      (fvarSubst d (.fvar d domW) bodyRaw) bodyW T)
    (hT : Infer env .full (d + 1) T sT) (hTred : Red env (d + 1) sT (.sort v))
    (hmb : v.zeronessOf = pw)
    (hNoLam : bodyW.lamPw = none := by rfl)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenAt env d Γ (.lam dom (bodyRaw.abstract1 d) { pw := pw })
      (.lam domW (bodyW.abstract1 d) { pw := pw }) (.forallE domW (T.abstract1 d) { pw := pw }) := by
  have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
  have hAbsOk : FVarOk d Γ (bodyRaw.abstract1 d) :=
    FVarOk.abstract1_of_fvarSubst bodyRaw 0 hBody.eOk
  have hAbsWs : (bodyRaw.abstract1 d).wscopedB d = true := hAbsOk.wscopedB hCtx
  have hNoLam' : (bodyW.abstract1 d).lamPw = none := by rw [lamPw_abstract1, hNoLam]
  have hi : Infer env .full d (.lam domW (bodyW.abstract1 d) { pw := pw })
      (.forallE domW (T.abstract1 d) { pw := pw }) :=
    .lam (fun _ => hDom.wInfer) (fun _ => hDom.wRed)
      (by rw [hround]; exact hBody.wInfer)
      (fun _ hp => by rw [hNoLam'] at hp; cases hp)
      (fun _ => hT.toIO) (fun _ => hTred) (fun _ => hmb)
  have hpi : PiRed env d (.lam domW (bodyW.abstract1 d) { pw := pw })
      (.lam dom (bodyRaw.abstract1 d) { pw := pw }) :=
    .lam hAbsWs hDom.wPiRed
      (by rw [hround, abstract1_instantiate1_eq_fvarSubst hbl]; exact hBody.wPiRed)
  exact ⟨⟨hDom.wOk, hBody.wOk.abstract1 0⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.wClosed, looseBVarsBounded_abstract1' hBody.wClosed],
    ⟨hDom.eOk, hAbsOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.eClosed, looseBVarsBounded_abstract1' hbl],
    hi, hpi⟩

/-- Build an `OpenAt` for an outer lambda abstraction over an inner lambda with matching `mb`. -/
theorem OpenAt.lam_abs_outer {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyRaw d₂ b₂ T : KExpr} {u : KLevel} {mb : Ix.Kernel.BinderMeta}
    (hbl : bodyRaw.looseBVarsBounded 0 = true)
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenAt env (d + 1) (fvarUpdate Γ d domW)
      (fvarSubst d (.fvar d domW) bodyRaw) (.lam d₂ b₂ mb) T)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenAt env d Γ (.lam dom (bodyRaw.abstract1 d) mb)
      (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb) (.forallE domW (T.abstract1 d) mb) := by
  have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
  have hAbsOk : FVarOk d Γ (bodyRaw.abstract1 d) :=
    FVarOk.abstract1_of_fvarSubst bodyRaw 0 hBody.eOk
  have hAbsWs : (bodyRaw.abstract1 d).wscopedB d = true := hAbsOk.wscopedB hCtx
  have hi : Infer env .full d (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb)
      (.forallE domW (T.abstract1 d) mb) :=
    .lam (btt := .sort .zero) (v := .zero) (fun _ => hDom.wInfer) (fun _ => hDom.wRed)
      (by rw [hround]; exact hBody.wInfer)
      (fun _ hp => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at hp; exact hp)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
  have hpi : PiRed env d (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb)
      (.lam dom (bodyRaw.abstract1 d) mb) :=
    .lam hAbsWs hDom.wPiRed
      (by rw [hround, abstract1_instantiate1_eq_fvarSubst hbl]; exact hBody.wPiRed)
  exact ⟨⟨hDom.wOk, hBody.wOk.abstract1 0⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.wClosed, looseBVarsBounded_abstract1' hBody.wClosed],
    ⟨hDom.eOk, hAbsOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.eClosed, looseBVarsBounded_abstract1' hbl],
    hi, hpi⟩

theorem OpenAt.lam_abs_inner_id {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyE bodyW T sT : KExpr} {u v : KLevel} {pw : Ix.Kernel.PropWhen}
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenAt env (d + 1) (fvarUpdate Γ d domW) bodyE bodyW T)
    (hT : Infer env .full (d + 1) T sT) (hTred : Red env (d + 1) sT (.sort v))
    (hmb : v.zeronessOf = pw)
    (hNoLam : bodyW.lamPw = none := by rfl)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenAt env d Γ (.lam dom (bodyE.abstract1 d) { pw := pw })
      (.lam domW (bodyW.abstract1 d) { pw := pw }) (.forallE domW (T.abstract1 d) { pw := pw }) := by
  have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
  have hroundE := hBody.eOk.abstract1_instantiate1 hBody.eClosed
  have hAbsOk : FVarOk d Γ (bodyE.abstract1 d) := hBody.eOk.abstract1 0
  have hAbsWs : (bodyE.abstract1 d).wscopedB d = true := hAbsOk.wscopedB hCtx
  have hNoLam' : (bodyW.abstract1 d).lamPw = none := by rw [lamPw_abstract1, hNoLam]
  have hi : Infer env .full d (.lam domW (bodyW.abstract1 d) { pw := pw })
      (.forallE domW (T.abstract1 d) { pw := pw }) :=
    .lam (fun _ => hDom.wInfer) (fun _ => hDom.wRed)
      (by rw [hround]; exact hBody.wInfer)
      (fun _ hp => by rw [hNoLam'] at hp; cases hp)
      (fun _ => hT.toIO) (fun _ => hTred) (fun _ => hmb)
  have hpi : PiRed env d (.lam domW (bodyW.abstract1 d) { pw := pw })
      (.lam dom (bodyE.abstract1 d) { pw := pw }) :=
    .lam hAbsWs hDom.wPiRed (by rw [hround, hroundE]; exact hBody.wPiRed)
  exact ⟨⟨hDom.wOk, hBody.wOk.abstract1 0⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.wClosed, looseBVarsBounded_abstract1' hBody.wClosed],
    ⟨hDom.eOk, hAbsOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.eClosed, looseBVarsBounded_abstract1' hBody.eClosed],
    hi, hpi⟩

theorem OpenAt.lam_abs_outer_id {env : Ix.Kernel.Env .anon} {d : Nat} {Γ : Nat → KExpr}
    {dom domW bodyE d₂ b₂ T : KExpr} {u : KLevel} {mb : Ix.Kernel.BinderMeta}
    (hDom : OpenType env d Γ dom domW u)
    (hBody : OpenAt env (d + 1) (fvarUpdate Γ d domW) bodyE (.lam d₂ b₂ mb) T)
    (hCtx : CtxWs d Γ := by exact CtxWs.zero _) :
    OpenAt env d Γ (.lam dom (bodyE.abstract1 d) mb)
      (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb) (.forallE domW (T.abstract1 d) mb) := by
  have hround := hBody.wOk.abstract1_instantiate1 hBody.wClosed
  have hroundE := hBody.eOk.abstract1_instantiate1 hBody.eClosed
  have hAbsOk : FVarOk d Γ (bodyE.abstract1 d) := hBody.eOk.abstract1 0
  have hAbsWs : (bodyE.abstract1 d).wscopedB d = true := hAbsOk.wscopedB hCtx
  have hi : Infer env .full d (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb)
      (.forallE domW (T.abstract1 d) mb) :=
    .lam (btt := .sort .zero) (v := .zero) (fun _ => hDom.wInfer) (fun _ => hDom.wRed)
      (by rw [hround]; exact hBody.wInfer)
      (fun _ hp => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at hp; exact hp)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
      (fun h => by simp [Ix.Kernel.Expr.abstract1, Ix.Kernel.Expr.lamPw] at h)
  have hpi : PiRed env d (.lam domW ((Ix.Kernel.Expr.lam d₂ b₂ mb).abstract1 d) mb)
      (.lam dom (bodyE.abstract1 d) mb) :=
    .lam hAbsWs hDom.wPiRed (by rw [hround, hroundE]; exact hBody.wPiRed)
  exact ⟨⟨hDom.wOk, hBody.wOk.abstract1 0⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.wClosed, looseBVarsBounded_abstract1' hBody.wClosed],
    ⟨hDom.eOk, hAbsOk⟩,
    by simp [Ix.Kernel.Expr.looseBVarsBounded, hDom.eClosed, looseBVarsBounded_abstract1' hBody.eClosed],
    hi, hpi⟩

/-- Chain two closed well-typed applications witnessed by `OpenAt` across `DefEq env 0 appLhs appRhs`
and beta-reductions `appLhsW → lhsW ≡ lhsA`, `appRhsW → rhsW ≡ rhsA`. -/
theorem OpenAt.defEq_chain {env : Ix.Kernel.Env .anon} {Γ : Nat → KExpr}
    {appLhs appLhsW appRhs appRhsW T₁ T₂ lhsW rhsW lhsA rhsA : KExpr}
    (hLhs : OpenAt env 0 Γ appLhs appLhsW T₁)
    (hRhs : OpenAt env 0 Γ appRhs appRhsW T₂)
    (hde : DefEq env 0 appLhs appRhs)
    (hRedL : Red env 0 appLhsW lhsW) (hL : DefEq env 0 lhsW lhsA)
    (hRedR : Red env 0 appRhsW rhsW) (hR : DefEq env 0 rhsW rhsA) :
    DefEq env 0 lhsA rhsA := by
  have h1 : DefEq env 0 lhsA appLhsW := (DefEq.redL hRedL hL).symm
  have h2 : DefEq env 0 appLhsW appLhs := hLhs.wPiRed.toDefEq
  have h3 : DefEq env 0 appRhs appRhsW := hRhs.wPiRed.toDefEq.symm
  have h4 : DefEq env 0 appRhsW rhsA := DefEq.redL hRedR hR
  have hA : DefEq env 0 appLhs appRhsW :=
    .transClosed hRhs.eOk.hasFvar_false hRhs.eClosed hRhs.wOk.hasFvar_false hRhs.wClosed
      hRhs.wInfer hRhs.wPiRed hde h3
  have hB : DefEq env 0 appLhs rhsA :=
    .transClosed hRhs.wOk.hasFvar_false hRhs.wClosed hRhs.wOk.hasFvar_false hRhs.wClosed
      hRhs.wInfer (.ofRed .refl) hA h4
  have hC : DefEq env 0 appLhsW rhsA :=
    .transClosed hLhs.eOk.hasFvar_false hLhs.eClosed hLhs.wOk.hasFvar_false hLhs.wClosed
      hLhs.wInfer hLhs.wPiRed h2 hB
  exact .transClosed hLhs.wOk.hasFvar_false hLhs.wClosed hLhs.wOk.hasFvar_false hLhs.wClosed
    hLhs.wInfer (.ofRed .refl) h1 hC

end IxVM.Refinement.Binding
