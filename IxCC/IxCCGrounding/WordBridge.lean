import IxCCGrounding.WordLe
import IxCCGrounding.WordFits
import IxCCGrounding.WordForm
import IxCCGrounding.Eqn

/-!
# The bridge from `UIntN.ofNat` to the word tower (`IxCCGrounding.WordBridge`, step W)

A width's `ofNat` entry names a stored theorem whose statement is the reducing bridge
`∀ x (h : Nat.le (Nat.succ (x % S)) S), UIntN.ofNat x = UIntN.ofBitVec (BitVec.ofFin W (Fin.mk S (x % S) h))`
(`W`, `S` the width's bits and size, literals; `Table.wordEqnType`, measured on every word closure).
**In every model, at every literal `a`, `UIntN.ofNat a` denotes the tower of `a % S` with the proof
point** (`ofNat_tow`): `mem` of the theorem at `litSet a`, its binder inhabited by `pt`
(`pt_mem_natLe`: `a % S + 1 ≤ S`), then `eq_of_inhabited` (`mem` of `Eq`, `eq_equality`); the bridge's
`x % S` is evaluated by `nat_accel` (`form_den`). No other law.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

/-- The keys a width's bridge names: the type `UIntN`, `UIntN.ofNat`, the tower's constructors
`UIntN.ofBitVec`, `BitVec.ofFin`, `Fin.mk`, and `Nat.le`. -/
structure TowKeys where
  ty : KKey
  ofNat : KKey
  u : KKey
  b : KKey
  f : KKey
  le : KKey
  deriving DecidableEq

/-- `x % S` over the role key of `Nat.mod`. -/
def modK (e : KExpr) (S : Nat) : KExpr := .app (.app (.const (primKey .mod) []) e) (litE S)

/-- The tower `UIntN.ofBitVec (BitVec.ofFin W (Fin.mk S n h))` as a kernel term. -/
def towK (tk : TowKeys) (W S : Nat) (n h : KExpr) : KExpr :=
  .app (.const tk.u []) (.app (.app (.const tk.b []) (litE W))
    (.app (.app (.app (.const tk.f []) (litE S)) n) h))

/-- **The reducing bridge's statement** (binder data as stored). -/
def bridgeK (tk : TowKeys) (W S : Nat) (m1 m2 : BinderMeta) : KExpr :=
  .forallE natK
    (.forallE (leApp tk.le (.app (.const natSuccName []) (modK (.bvar 0) S)) (litE S))
      (Expr.mkAppN (.const eqName [.succ .zero])
        [.const tk.ty [], .app (.const tk.ofNat []) (.bvar 1), towK tk W S (modK (.bvar 1) S) (.bvar 0)])
      m2) m1

section Bridge

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **The tower of `n` in the model**, its proof field the proof point. -/
noncomputable def towV (M : Model V env) (tk : TowKeys) (W S : Nat) (φ : LevelParam → Nat) (n : Nat) : V :=
  app (M.cval tk.u φ) (app (app (M.cval tk.b φ) (litSet M φ W))
    (app (app (app (M.cval tk.f φ) (litSet M φ S)) (litSet M φ n)) pt))

/-- **What the bridge lemma reads, stored** (decided by the check): the bridge theorem with its exact
statement, `Nat.le` and its constructors, and the keys the statement names stored without level
parameters. -/
structure BridgeStored (env : KEnv) (tk : TowKeys) (W S : Nat) (kThm kR kS : KKey) : Prop where
  thm : ∃ (cv : ConstantVal .anon) (pf : KExpr) (m1 m2 : BinderMeta),
    env.find? kThm = some (.thmInfo cv pf) ∧ cv.type = bridgeK tk W S m1 m2
  le : NatLeBasis env tk.le kR kS
  keys : ∀ k ∈ [tk.ofNat, tk.u, tk.b, tk.f, primKey .mod],
    ∃ ci : ConstantInfo .anon, env.find? k = some ci ∧ ci.toConstantVal.levelParams = []
  pos : 0 < S

theorem BridgeStored.den {tk : TowKeys} {W S : Nat} {kThm kR kS : KKey}
    (hB : BridgeStored env tk W S kThm kR kS) (M : Model V env) {k : KKey}
    (hk : k ∈ [tk.ofNat, tk.u, tk.b, tk.f, primKey .mod]) (φ : LevelParam → Nat) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const k []) (M.cval k φ) := by
  obtain ⟨ci, hf, hl⟩ := hB.keys k hk
  exact (den_const0 hf hl).mpr rfl

/-- `x % S` at a variable bound to a literal. -/
theorem den_modK (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) {tk : TowKeys}
    {W S : Nat} {kThm kR kS : KKey} (hB : BridgeStored env tk W S kThm kR kS)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {i a : Nat}
    (hi : Denotes M.cval env φ ρ (.bvar i) (litSet M φ a)) :
    Denotes M.cval env φ ρ (modK (.bvar i) S) (litSet M φ (a % S)) := by
  have h := form_den M hacc hN (ex := .bvar i) (ey := .bvar i) hi hi (.op .mod .x (.lit S)) rfl
    (fun o ho => by
      simp [NForm.ops] at ho
      subst ho
      exact hB.keys _ (by simp))
  exact h

/-- **`UIntN.ofNat a` denotes the tower of `a % S`.** -/
theorem ofNat_tow (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hE : EqBasis env)
    {tk : TowKeys} {W S : Nat} {kThm kR kS : KKey} (hB : BridgeStored env tk W S kThm kR kS)
    (φ : LevelParam → Nat) (a : Nat) :
    app (M.cval tk.ofNat φ) (litSet M φ a) = towV M tk W S φ (a % S) := by
  have hF := natFacts M hN φ
  obtain ⟨cv, pf, m1, m2, hfT, htT⟩ := hB.thm
  let ρ0 : BVarIdx → V := fun _ => empty
  obtain ⟨TT, hTT, hm⟩ := mem_key M hfT φ ρ0
  simp only [ConstantInfo.toConstantVal, htT, bridgeK] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF a)
  let ρ1 := push (litSet M φ a) ρ0
  have hmod1 : Denotes M.cval env φ ρ1 (modK (.bvar 0) S) (litSet M φ (a % S)) :=
    den_modK M hacc hN hB (i := 0) .bvar
  have hdom : Denotes M.cval env φ ρ1
      (leApp tk.le (.app (.const natSuccName []) (modK (.bvar 0) S)) (litE S))
      (app (app (M.cval tk.le φ) (litSet M φ (a % S + 1))) (litSet M φ S)) :=
    .app (.app (den_le_const M hB.le ρ1) (.app ((hF.succD _ _).mpr rfl) hmod1))
      ((lit_den M hF ρ1 S _).mpr rfl)
  have hpt := pt_mem_natLe M hN hB.le φ (Nat.mod_lt a hB.pos)
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 hdom hm1 hpt
  let ρ2 := push (pt : V) ρ1
  obtain ⟨x, hx1, hx2⟩ := eq_of_inhabited M hE hB2 hm2
  have hlhs : Denotes M.cval env φ ρ2 (.app (.const tk.ofNat []) (.bvar 1))
      (app (M.cval tk.ofNat φ) (litSet M φ a)) :=
    .app (hB.den M (by simp) φ ρ2) (.bvar (i := 1))
  have hmod2 : Denotes M.cval env φ ρ2 (modK (.bvar 1) S) (litSet M φ (a % S)) :=
    den_modK M hacc hN hB (i := 1) .bvar
  have hrhs : Denotes M.cval env φ ρ2 (towK tk W S (modK (.bvar 1) S) (.bvar 0))
      (towV M tk W S φ (a % S)) :=
    .app (hB.den M (by simp) φ ρ2)
      (.app (.app (hB.den M (by simp) φ ρ2) ((lit_den M hF ρ2 W _).mpr rfl))
        (.app (.app (.app (hB.den M (by simp) φ ρ2) ((lit_den M hF ρ2 S _).mpr rfl)) hmod2)
          (.bvar (i := 0))))
  exact (Denotes_functional hx1 hlhs).symm.trans (Denotes_functional hx2 hrhs)

end Bridge

/-! ## The tower's constructors fit, at the bridge's tower (`tow_fits`)

The tower F6w builds for a word `n` of a width (`Program.mkWord?`) is related to `towV n` by three
uses of `RelV.con`, each asking the constructor's arguments to fit its stored type. They are read off
the stored bridge: at `x = n` and the proof point, `graded` (`GradedLaw`) on the bridge's statement
gives a graded spine at each of the tower's three constructors (`spineMem_of_graded`), and the
constructors' stored types, telescopes whose binders are in the graph regime, turn each into `Fits`
(`fits_of_spineMem`). Laws: `graded`, `nat_accel` (the bridge's `x % S`), `Model.mem`. -/

/-- The tower's other keys: `BitVec`, `Fin`, `BitVec.toFin`, `LT.lt`. -/
structure TowAux where
  bv : KKey
  fin : KKey
  toFin : KKey
  lt : KKey
  deriving DecidableEq

/-- `Fin.mk`'s proof domain, `@LT.lt.{ls} a1 a2 #0 #1`. -/
def ltSpine (ta : TowAux) (ls : List Level) (a1 a2 : KExpr) : KExpr :=
  Expr.mkAppN (.const ta.lt ls) [a1, a2, .bvar 0, .bvar 1]

/-- **The tower's stored shapes** (decided by the check): `BitVec` and `Fin`, inductives of type
`Nat → Sort _` with a graph-regime binder and projection tables whose constructor is the tower's,
never propositions; the three constructors without level parameters, closed, of the stored
telescopes (binder data never); `LT.lt` a telescope of four graph-regime binders ending in `Sort 0`;
`BitVec.toFin` the projection function of `BitVec`'s field, of type `∀ n (b : BitVec n), Fin P[n]`
with `Fin P` `ofFin`'s field domain. -/
structure TowerStored (env : KEnv) (tk : TowKeys) (ta : TowAux) : Prop where
  bv : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon) (u : Level) (m : BinderMeta),
    env.find? ta.bv = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .forallE natK (.sort u) m ∧ m.pw = .never ∧ cv.type.hasLevelParam = false
  bvProj : ∃ e : ProjEntry .anon, env.findProj? ta.bv 0 = some e ∧ e.ctor = tk.b ∧
    e.numParams = 1 ∧ e.numFields = 1 ∧ ∀ ψ, Level.eval ψ e.structSort ≠ 0
  fin : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon) (u : Level) (m : BinderMeta),
    env.find? ta.fin = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .forallE natK (.sort u) m ∧ m.pw = .never ∧ cv.type.hasLevelParam = false
  finProj : ∃ off, ∀ i, i < 2 → ∃ e : ProjEntry .anon, env.findProj? ta.fin i = some e ∧
    e.ctor = tk.f ∧ e.numParams = 1 ∧ e.numFields = 2 ∧ e.off = off ∧ ∀ ψ, Level.eval ψ e.structSort ≠ 0
  u : ∃ (cv : ConstantVal .anon) (N8 : KExpr) (m : BinderMeta),
    env.find? tk.u = some (.ctorInfo cv 0 1) ∧ cv.levelParams = [] ∧
    cv.type = piTele [(.app (.const ta.bv []) N8, m)] (.const tk.ty []) ∧ m.pw = .never ∧
    bvarsLt 0 cv.type = true ∧ cv.type.hasLevelParam = false ∧ cv.type.allLevelParamsDefined [] = true
  b : ∃ (cv : ConstantVal .anon) (Pe : KExpr) (m1 m2 : BinderMeta),
    env.find? tk.b = some (.ctorInfo cv 1 1) ∧ cv.levelParams = [] ∧
    cv.type = piTele [(natK, m1), (.app (.const ta.fin []) Pe, m2)]
      (.app (.const ta.bv []) (.bvar 1)) ∧
    m1.pw = .never ∧ m2.pw = .never ∧ bvarsLt 0 cv.type = true ∧ cv.type.hasLevelParam = false ∧
    cv.type.allLevelParamsDefined [] = true ∧
    ∃ (cvF : ConstantVal .anon) (hint : ReducibilityHint) (mF1 mF2 mG1 mG2 : BinderMeta),
      env.find? ta.toFin = some (.defnInfo cvF
        (.lam natK (.lam (.app (.const ta.bv []) (.bvar 0)) (.proj ta.bv 0 (.bvar 0)) mF2) mF1)
        hint) ∧
      cvF.levelParams = [] ∧
      cvF.type = .forallE natK (.forallE (.app (.const ta.bv []) (.bvar 0))
        ((Expr.app (.const ta.fin []) Pe).liftLooseBVars 1 0) mG2) mG1
  f : ∃ (cv : ConstantVal .anon) (ls : List Level) (a1 a2 : KExpr) (m1 m2 m3 : BinderMeta),
    env.find? tk.f = some (.ctorInfo cv 1 2) ∧ cv.levelParams = [] ∧
    cv.type = piTele [(natK, m1), (natK, m2), (ltSpine ta ls a1 a2, m3)]
      (.app (.const ta.fin []) (.bvar 2)) ∧
    m1.pw = .never ∧ m2.pw = .never ∧ m3.pw = .never ∧ bvarsLt 0 cv.type = true ∧
    cv.type.hasLevelParam = false ∧ cv.type.allLevelParamsDefined [] = true ∧
    ∃ (ci : ConstantInfo .anon) (bs : List (KExpr × BinderMeta)), env.find? ta.lt = some ci ∧
      ls.length = ci.toConstantVal.levelParams.length ∧
      ci.toConstantVal.type = piTele bs (.sort .zero) ∧ bs.length = 4 ∧ ∀ bm ∈ bs, bm.2.pw = .never

section Fits

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- The tower's `Fin` level. -/
noncomputable def towF (M : Model V env) (tk : TowKeys) (S : Nat) (φ : LevelParam → Nat)
    (n : Nat) : V :=
  app (app (app (M.cval tk.f φ) (litSet M φ S)) (litSet M φ n)) pt

/-- The tower's `BitVec` level. -/
noncomputable def towB (M : Model V env) (tk : TowKeys) (W S : Nat) (φ : LevelParam → Nat)
    (n : Nat) : V :=
  app (app (M.cval tk.b φ) (litSet M φ W)) (towF M tk S φ n)

theorem towV_eq (M : Model V env) (tk : TowKeys) (W S : Nat) (φ : LevelParam → Nat) (n : Nat) :
    towV M tk W S φ n = app (M.cval tk.u φ) (towB M tk W S φ n) := rfl

/-- `GradedBy` of a `∀`, unfolded. -/
theorem gradedBy_forallE {D : (BVarIdx → V) → KExpr → V → Prop} {ρ : BVarIdx → V} {A B : KExpr}
    {m : BinderMeta} (h : GradedBy D ρ (.forallE A B m)) :
    GradedBy D ρ A ∧ ∀ X, D ρ A X → ∀ x, x ∈ˢ X → GradedBy D (push x ρ) B := h

/-- `GradedBy` of an application, its two sides. -/
theorem gradedBy_app {D : (BVarIdx → V) → KExpr → V → Prop} {ρ : BVarIdx → V} {f a : KExpr}
    (h : GradedBy D ρ (.app f a)) : GradedBy D ρ f ∧ GradedBy D ρ a := ⟨h.1, h.2.1⟩

theorem never_regime {φ : LevelParam → Nat} {m : BinderMeta} (h : m.pw = .never) :
    regime φ m.pw ≠ 0 := by
  rw [h, regime_never]; decide

/-- A constructor stored with a telescope of graph-regime binders, applied along a graded spine:
the arguments fit its type. -/
theorem fits_of_graded_head (M : Model V env) {φ : LevelParam → Nat} {ρ : BVarIdx → V}
    {k : KKey} {cv : ConstantVal .anon} {np nf : Nat} (hf : env.find? k = some (.ctorInfo cv np nf))
    {bs : List (KExpr × BinderMeta)} {C : KExpr} (ht : cv.type = piTele bs C)
    (hnv : ∀ bm ∈ bs, bm.2.pw = .never) {args : List KExpr} {xs : List V}
    (hg : GradedBy (Denotes M.cval env φ) ρ (Expr.mkAppN (.const k []) args))
    (hk : Denotes M.cval env φ ρ (.const k []) (M.cval k φ))
    (hxs : DenotesList M.cval env φ ρ args xs) (hl : xs.length = bs.length) :
    ∃ σ R, Fits M.cval env φ (fun _ => empty) cv.type xs σ R := by
  have hsp := spineMem_of_graded M args hg hk hxs
  obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal] at hT
  rw [ht] at hT ⊢
  obtain ⟨hfit, -⟩ := fits_of_spineMem M bs C hT hm hsp hl
    (fun bm hbm => never_regime (hnv bm hbm))
  exact ⟨_, _, hfit⟩

/-- **The bridge's tower fits the constructors' stored types** at every word below the size. -/
theorem tow_fits (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hgr : GradedLaw M.cval env) {tk : TowKeys} {ta : TowAux} {W S : Nat} {kThm kR kS : KKey}
    (hB : BridgeStored env tk W S kThm kR kS) (hT : TowerStored env tk ta)
    (φ : LevelParam → Nat) {n : Nat} (hn : n < S) :
    ∃ (cvU cvB cvF : ConstantVal .anon),
      env.find? tk.u = some (.ctorInfo cvU 0 1) ∧ env.find? tk.b = some (.ctorInfo cvB 1 1) ∧
      env.find? tk.f = some (.ctorInfo cvF 1 2) ∧
      (∃ σ R, Fits M.cval env φ (fun _ => empty) cvF.type
        [litSet M φ S, litSet M φ n, pt] σ R) ∧
      (∃ σ R, Fits M.cval env φ (fun _ => empty) cvB.type
        [litSet M φ W, towF M tk S φ n] σ R) ∧
      (∃ σ R, Fits M.cval env φ (fun _ => empty) cvU.type [towB M tk W S φ n] σ R) := by
  have hF := natFacts M hN φ
  obtain ⟨cv, pf, m1, m2, hfT, htT⟩ := hB.thm
  let ρ0 : BVarIdx → V := fun _ => empty
  have hg := (hgr _ (find_mem hfT) φ ρ0).1
  simp only [ConstantInfo.toConstantVal] at hg
  rw [htT] at hg
  have hg2 := (gradedBy_forallE hg).2 _ ((hF.natD ρ0 _).mpr rfl) _ (lit_mem M hF n)
  let ρ1 := push (litSet M φ n) ρ0
  have hmod1 : Denotes M.cval env φ ρ1 (modK (.bvar 0) S) (litSet M φ (n % S)) :=
    den_modK M hacc hN hB (i := 0) .bvar
  have hdom : Denotes M.cval env φ ρ1
      (leApp tk.le (.app (.const natSuccName []) (modK (.bvar 0) S)) (litE S))
      (app (app (M.cval tk.le φ) (litSet M φ (n % S + 1))) (litSet M φ S)) :=
    .app (.app (den_le_const M hB.le ρ1) (.app ((hF.succD _ _).mpr rfl) hmod1))
      ((lit_den M hF ρ1 S _).mpr rfl)
  have hg4 := (gradedBy_forallE hg2).2 _ hdom pt
    (pt_mem_natLe M hN hB.le φ (Nat.mod_lt n hB.pos))
  let ρ2 := push (pt : V) ρ1
  have hgt := (gradedBy_mkAppN (D := Denotes M.cval env φ) (ρ := ρ2) _ hg4).2
    (towK tk W S (modK (.bvar 1) S) (.bvar 0)) (by simp)
  simp only [towK] at hgt
  have hmod2 : Denotes M.cval env φ ρ2 (modK (.bvar 1) S) (litSet M φ n) := by
    have h := den_modK M hacc hN hB (φ := φ) (ρ := ρ2) (i := 1) (a := n) .bvar
    rwa [Nat.mod_eq_of_lt hn] at h
  have hgB := (gradedBy_app hgt).2
  have hgF := (gradedBy_app hgB).2
  have hlW : Denotes M.cval env φ ρ2 (litE W) (litSet M φ W) := (lit_den M hF ρ2 W _).mpr rfl
  have hlS : Denotes M.cval env φ ρ2 (litE S) (litSet M φ S) := (lit_den M hF ρ2 S _).mpr rfl
  have hdF : Denotes M.cval env φ ρ2
      (.app (.app (.app (.const tk.f []) (litE S)) (modK (.bvar 1) S)) (.bvar 0))
      (towF M tk S φ n) :=
    .app (.app (.app (hB.den M (by simp) φ ρ2) hlS) hmod2) (.bvar (i := 0))
  have hdB : Denotes M.cval env φ ρ2
      (.app (.app (.const tk.b []) (litE W))
        (.app (.app (.app (.const tk.f []) (litE S)) (modK (.bvar 1) S)) (.bvar 0)))
      (towB M tk W S φ n) :=
    .app (.app (hB.den M (by simp) φ ρ2) hlW) hdF
  obtain ⟨cvU, N8, mU, hfU, -, htU, hmU, -, -, -⟩ := hT.u
  obtain ⟨cvB, Pe, mB1, mB2, hfB, -, htB, hmB1, hmB2, -, -, -, -⟩ := hT.b
  obtain ⟨cvF, ls, a1, a2, mF1, mF2, mF3, hfF, -, htF, hmF1, hmF2, hmF3, -, -, -, -⟩ := hT.f
  refine ⟨cvU, cvB, cvF, hfU, hfB, hfF, ?_, ?_, ?_⟩
  · exact fits_of_graded_head M hfF htF (by simp [hmF1, hmF2, hmF3])
      (args := [litE S, modK (.bvar 1) S, .bvar 0]) hgF (hB.den M (by simp) φ ρ2)
      (.cons hlS (.cons hmod2 (.cons .bvar .nil))) rfl
  · exact fits_of_graded_head M hfB htB (by simp [hmB1, hmB2])
      (args := [litE W, .app (.app (.app (.const tk.f []) (litE S)) (modK (.bvar 1) S)) (.bvar 0)])
      hgB (hB.den M (by simp) φ ρ2) (.cons hlW (.cons hdF .nil)) rfl
  · exact fits_of_graded_head M hfU htU (by simp [hmU])
      (args := [.app (.app (.const tk.b []) (litE W))
        (.app (.app (.app (.const tk.f []) (litE S)) (modK (.bvar 1) S)) (.bvar 0))])
      hgt (hB.den M (by simp) φ ρ2) (.cons hdB .nil) rfl

end Fits

end IxCC.Grounding
