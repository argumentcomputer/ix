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

end IxCC.Grounding
