import IxCCGrounding.WordBridge
import IxCCGrounding.Support

/-!
# A word's tower is canonical (`IxCCGrounding.WordCanon`, step W)

SrcEval reads a value as a word (`Program.asWord?`) by its number alone: the tower's parameter slots
and its proof are not read, and a run term may build a tower whose parameters are arbitrary terms.
**Two towers of one number whose arguments fit the constructors' stored types are one set**
(`tower_eq`): at each level the constructor image lies in its family (the enclosing constructor's
argument fits its stored type), so structure η (`proj_law`) rebuilds it at the family's own
parameter. At `BitVec` the field's family is read through the stored projection function
`BitVec.toFin` (δ and `mem`; `field_mem`); at `Fin` both fields are read back by the projection law
(`fin_level`), and the proof field lies in a proposition (`LT.lt` ends in `Sort 0`, `graded` on
`Fin.mk`'s type; `ltProp_pt`), so it is the proof point. The family parameters are what the stored
types' terms denote, the same for both towers. Laws: `proj_law`, `defn_value`, `graded`, and
`Model.mem`; `cval_params` to move a tower built at another assignment (`fits_move`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

section Canon

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- A constant without level parameters has one set at every assignment (`cval_params`). -/
theorem cval0_eq (M : Model V env) (hcv : CvalParams M) {k : KKey} {ci : ConstantInfo .anon}
    (hf : env.find? k = some ci) (hl : ci.toConstantVal.levelParams = [])
    (φ ψ : LevelParam → Nat) : M.cval k φ = M.cval k ψ :=
  hcv k ci hf φ ψ (fun q hq => by rw [hl] at hq; simp at hq)

/-- `Fits` of a closed telescope without level parameters moves to any assignment and
environment (`cval_params`). -/
theorem fits_move (M : Model V env) (hcv : CvalParams M) {T : KExpr} (hc : bvarsLt 0 T = true)
    (hd : T.allLevelParamsDefined [] = true) {ψ : LevelParam → Nat} {ρ σ : BVarIdx → V}
    {R : KExpr} {xs : List V} (h : Fits M.cval env ψ ρ T xs σ R) (φ : LevelParam → Nat)
    (ρ' : BVarIdx → V) : ∃ σ' R', Fits M.cval env φ ρ' T xs σ' R' := by
  obtain ⟨σ2, hfit2⟩ := fits_agree h (ρ' := ρ') fun i hi =>
    absurd (lt_of_bvarsLt hc hi) (Nat.not_lt_zero i)
  have h3 := fits_inst_cv M hcv (ks := []) (us := []) (φ := φ) (ψ := ψ)
    (fun _ hp => by simp at hp) hfit2 hd
  have hi0 := inst_self ([] : List LevelParam) T
  simp only [List.map_nil] at hi0
  rw [hi0] at h3
  exact ⟨σ2, _, h3⟩

/-- **The field of a one-field structure through its stored projection function** (GW's trial,
promoted): a constructor image `ofFin P F` whose arguments fit the constructor's type at an
arbitrary parameter `P`, lying in the family at `N`, is `ofFin N F` (η and the projection law's
first conjunct), and `F` lies in the field's domain at `N` (δ and `mem` of the projection function
`kF`). -/
theorem field_mem (M : Model V env) (hPL : ProjLaw M.cval env) (hδ : DefnValue M)
    (hNB : NatBasis env)
    {kT kC kF : KKey} {cvT : ConstantVal .anon} {caps : IndCaps .anon} {entry : ProjEntry .anon}
    {cvC cvF : ConstantVal .anon} {hint : ReducibilityHint}
    {D : KExpr} {mF1 mF2 mT mG1 mG2 : BinderMeta} {u : Level}
    (hfT : env.find? kT = some (.indInfo cvT caps)) (hlT : cvT.levelParams = [])
    (htT : cvT.type = .forallE natK (.sort u) mT) (hTl : cvT.type.hasLevelParam = false)
    (hpj : env.findProj? kT 0 = some entry) (hec : entry.ctor = kC) (hnp : entry.numParams = 1)
    (hnf : entry.numFields = 1) (hss : ∀ ψ, Level.eval ψ entry.structSort ≠ 0)
    (hfC : env.find? kC = some (.ctorInfo cvC 1 1)) (hlC : cvC.levelParams = [])
    (hCl : cvC.type.hasLevelParam = false)
    (hfF : env.find? kF = some (.defnInfo cvF
      (.lam natK (.lam (.app (.const kT []) (.bvar 0)) (.proj kT 0 (.bvar 0)) mF2) mF1) hint))
    (htF : cvF.type = .forallE natK (.forallE (.app (.const kT []) (.bvar 0))
      (D.liftLooseBVars 1 0) mG2) mG1)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {N P F : V}
    (hNn : N ∈ˢ M.cval natName φ) (hFits : Fits M.cval env φ ρ cvC.type [P, F] σ R)
    (hB : app (app (M.cval kC φ) P) F ∈ˢ app (M.cval kT φ) N) :
    app (app (M.cval kC φ) P) F = app (app (M.cval kC φ) N) F ∧
      ∃ X, Denotes M.cval env φ (push N ρ) D X ∧ F ∈ˢ X := by
  have hF := natFacts M hNB φ
  obtain ⟨hlpT, -, cvC', hfC', hlpC, -, hlaw⟩ := hPL kT 0 entry cvT caps hpj hfT
  rw [hec, hnp, hnf, hfC] at hfC'
  cases hfC'
  have hFT : Denotes M.cval env φ ρ (.const kT []) (M.cval kT φ) := (den_const0 hfT hlT).mpr rfl
  have hKC : Denotes M.cval env φ ρ (.const entry.ctor []) (M.cval kC φ) := by
    rw [hec]; exact (den_const0 hfC hlC).mpr rfl
  have hlen : ([] : List Level).length = entry.levelParams.length := by
    rw [← hlpT, hlT]; rfl
  obtain ⟨hproj, heta⟩ := hlaw [] φ ρ (M.cval kT φ) (M.cval kC φ) hlen hFT hKC
  -- field `0` of the image is `F` (the guard holds: the structure's sort is never zero)
  have hfield : field entry.off (app (app (M.cval kC φ) P) F) = F := by
    have h := hproj (fun h0 => absurd h0 (hss _)) σ R [P, F] (by rw [hnp, hnf]; rfl) (by
      rw [Expr.instantiateLevelParams_eq_self hCl]; exact hFits)
    simpa [hnp] using h
  -- η at the family's parameter `N`
  have hfitT : Fits M.cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams []) [N]
      (push N ρ) (.sort u) := by
    rw [Expr.instantiateLevelParams_eq_self hTl, htT]
    exact .cons ((hF.natD ρ _).mpr rfl) hNn .nil
  have h2 := heta (push N ρ) (.sort u) [N] _ (by rw [hnp]; rfl) hfitT (by simpa using hB)
  have heq : app (app (M.cval kC φ) P) F =
      app (app (M.cval kC φ) N) (field entry.off (app (app (M.cval kC φ) P) F)) := by
    simpa [hnf] using h2
  rw [hfield] at heq
  refine ⟨by simpa using heq, ?_⟩
  -- the projection function: `mem` puts its value at `N` and the image in the field's domain
  obtain ⟨TT, hTT, hm⟩ := mem_key M hfF φ ρ
  simp only [ConstantInfo.toConstantVal, htF] at hTT
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hTT ((hF.natD ρ _).mpr rfl) hm hNn
  have hdomB : Denotes M.cval env φ (push N ρ) (.app (.const kT []) (.bvar 0))
      (app (M.cval kT φ) N) := .app ((den_const0 hfT hlT).mpr rfl) .bvar
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 hdomB hm1 hB
  rw [den_lift 1 D 0, skipEnv_push_one] at hB2
  -- δ: the projection function's value is the field
  have hval := hδ cvF _ hint (find_mem hfF) φ ρ
  have hn : cvF.name = kF := find_name hfF
  rw [hn] at hval
  obtain ⟨Y, hY, hY'⟩ := app_den_lam hval ((hF.natD ρ _).mpr rfl) hNn
  obtain ⟨Z, hZ, hZ'⟩ := app_den_lam hY hdomB hB
  have hZf : Z = field entry.off (app (app (M.cval kC φ) P) F) := by
    cases hZ with
    | proj_table ht he =>
      rw [hpj] at ht
      cases ht
      cases he
      simp [push]
    | proj_fst ht _ => rw [hpj] at ht; cases ht
  rw [hfield] at hZf
  refine ⟨B2, hB2, ?_⟩
  rw [← hY'] at hZ'
  rw [hZ', hZf] at hm2
  exact hm2

/-- The argument of a stored family `Nat → Sort _` (a graph-regime binder) along a graded
application is a `Nat`. -/
theorem arg_nat (M : Model V env) (hN : NatBasis env) {kT : KKey} {cvT : ConstantVal .anon}
    {caps : IndCaps .anon} {u : Level} {mT : BinderMeta}
    (hfT : env.find? kT = some (.indInfo cvT caps)) (hlT : cvT.levelParams = [])
    (htT : cvT.type = .forallE natK (.sort u) mT) (hmT : mT.pw = .never)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : KExpr} {N : V}
    (hg : GradedBy (Denotes M.cval env φ) ρ (.app (.const kT []) e))
    (he : Denotes M.cval env φ ρ e N) : N ∈ˢ M.cval natName φ := by
  have hF := natFacts M hN φ
  have hsp := spineMem_of_graded M [e] (h := .const kT []) hg ((den_const0 hfT hlT).mpr rfl)
    (.cons he .nil)
  obtain ⟨T, hT, hm⟩ := mem_key M hfT φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal] at hT
  rw [htT] at hT
  obtain ⟨hfit, -⟩ := fits_of_spineMem M [(natK, mT)] (.sort u) hT hm hsp rfl
    (fun bm hbm => by
      rw [List.mem_singleton] at hbm
      subst hbm
      exact never_regime hmT)
  cases hfit with
  | cons hA hx _ => rwa [(hF.natD _ _).mp hA] at hx

/-- **The proof field of `Fin.mk` is the proof point**: its domain `LT.lt … #0 #1` is a spine of
`LT.lt`, whose stored type is a telescope of graph-regime binders ending in `Sort 0`; `graded` on
`Fin.mk`'s type puts the spine in that telescope's body, `univ 0`. -/
theorem ltProp_pt (M : Model V env) (hgr : GradedLaw M.cval env) {kC kLT : KKey}
    {cvC : ConstantVal .anon} {np nf : Nat} {ls : List Level} {a1 a2 Cf : KExpr}
    {m1 m2 m3 : BinderMeta} (hfC : env.find? kC = some (.ctorInfo cvC np nf))
    (htC : cvC.type = .forallE natK (.forallE natK
      (.forallE (Expr.mkAppN (.const kLT ls) [a1, a2, .bvar 0, .bvar 1]) Cf m3) m2) m1)
    {ci : ConstantInfo .anon} {bs : List (KExpr × BinderMeta)} (hfL : env.find? kLT = some ci)
    (hlL : ls.length = ci.toConstantVal.levelParams.length)
    (htL : ci.toConstantVal.type = piTele bs (.sort .zero)) (hbl : bs.length = 4)
    (hbn : ∀ bm ∈ bs, bm.2.pw = .never)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {Q a Z : V}
    (hFits : Fits M.cval env φ ρ cvC.type [Q, a, Z] σ R) : Z = pt := by
  have hg := (hgr _ (find_mem hfC) φ ρ).1
  simp only [ConstantInfo.toConstantVal] at hg
  rw [htC] at hg hFits
  cases hFits with
  | cons hA1 hQ h2 =>
    cases h2 with
    | cons hA2 ha h3 =>
      cases h3 with
      | cons hA3 hZ _ =>
        have hg1 := (gradedBy_forallE hg).2 _ hA1 _ hQ
        have hg2 := (gradedBy_forallE hg1).2 _ hA2 _ ha
        have hg3 := (gradedBy_forallE hg2).1
        obtain ⟨H, Xs, hH, hXs, rfl⟩ := (den_mkAppN [a1, a2, .bvar 0, .bvar 1]).mp hA3
        have hsp := spineMem_of_graded M [a1, a2, .bvar 0, .bvar 1] hg3 hH hXs
        have hc : Denotes M.cval env φ (push a (push Q ρ)) (.const kLT ls)
            (M.cval kLT (Level.substFn φ ci.toConstantVal.levelParams ls)) :=
          Denotes.const hfL hlL
        obtain rfl := Denotes_functional hH hc
        obtain ⟨T, hT, hm⟩ := mem_key M hfL (Level.substFn φ ci.toConstantVal.levelParams ls)
          (fun _ => empty)
        rw [htL] at hT
        have hlX : Xs.length = bs.length := (denotesList_length hXs).trans (by simp [hbl])
        obtain ⟨-, Rr, hRr, hmem⟩ := fits_of_spineMem M bs (.sort .zero) hT hm hsp hlX
          (fun bm hbm => never_regime (hbn bm hbm))
        rw [den_sort.mp hRr] at hmem
        simp only [Level.eval] at hmem
        rw [univ_zero] at hmem
        exact eq_pt_of_mem_univZero hmem hZ

/-- **At `Fin`**: an image `Fin.mk Q a Z` whose arguments fit the constructor's type, lying in the
family at `N`, is `Fin.mk N a Z` (η at `N`, and both fields read back by the projection law). -/
theorem fin_level (M : Model V env) (hPL : ProjLaw M.cval env) (hN : NatBasis env)
    {kT kC : KKey} {cvT : ConstantVal .anon} {caps : IndCaps .anon} {u : Level} {mT : BinderMeta}
    {cvC : ConstantVal .anon}
    (hfT : env.find? kT = some (.indInfo cvT caps)) (hlT : cvT.levelParams = [])
    (htT : cvT.type = .forallE natK (.sort u) mT) (hTl : cvT.type.hasLevelParam = false)
    (hpj : ∃ off, ∀ i, i < 2 → ∃ e : ProjEntry .anon, env.findProj? kT i = some e ∧
      e.ctor = kC ∧ e.numParams = 1 ∧ e.numFields = 2 ∧ e.off = off ∧
      ∀ ψ, Level.eval ψ e.structSort ≠ 0)
    (hfC : env.find? kC = some (.ctorInfo cvC 1 2)) (hlC : cvC.levelParams = [])
    (hCl : cvC.type.hasLevelParam = false)
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {N Q a Z : V}
    (hNn : N ∈ˢ M.cval natName φ) (hFits : Fits M.cval env φ ρ cvC.type [Q, a, Z] σ R)
    (hB : app (app (app (M.cval kC φ) Q) a) Z ∈ˢ app (M.cval kT φ) N) :
    app (app (app (M.cval kC φ) Q) a) Z = app (app (app (M.cval kC φ) N) a) Z := by
  have hF := natFacts M hN φ
  obtain ⟨off, hpj⟩ := hpj
  have hFT : Denotes M.cval env φ ρ (.const kT []) (M.cval kT φ) := (den_const0 hfT hlT).mpr rfl
  have hfit' : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams [])
      [Q, a, Z] σ R := by
    rw [Expr.instantiateLevelParams_eq_self hCl]; exact hFits
  -- the law at table entry `i`
  have hlawAt : ∀ (i : Nat) (e : ProjEntry .anon), env.findProj? kT i = some e → e.ctor = kC →
      e.numParams = 1 → e.numFields = 2 → (∀ ψ, Level.eval ψ e.structSort ≠ 0) →
      field (i + e.off) ([Q, a, Z].foldl app (M.cval kC φ)) = [Q, a, Z].getD (e.numParams + i) empty ∧
      ∀ x, x ∈ˢ app (M.cval kT φ) N →
        x = ([N] ++ (List.range e.numFields).map fun j => field (j + e.off) x).foldl app
          (M.cval kC φ) := by
    intro i e hp hc hn hf hs
    obtain ⟨hlpT, -, cvC', hfC', hlpC, -, hlaw⟩ := hPL kT i e cvT caps hp hfT
    rw [hc, hn, hf, hfC] at hfC'
    cases hfC'
    have hKC : Denotes M.cval env φ ρ (.const e.ctor []) (M.cval kC φ) := by
      rw [hc]; exact (den_const0 hfC hlC).mpr rfl
    have hlen : ([] : List Level).length = e.levelParams.length := by rw [← hlpT, hlT]; rfl
    obtain ⟨hproj, heta⟩ := hlaw [] φ ρ (M.cval kT φ) (M.cval kC φ) hlen hFT hKC
    refine ⟨hproj (fun h0 => absurd h0 (hs _)) σ R [Q, a, Z] (by simp [hn, hf]) hfit', ?_⟩
    intro x hx
    have hfitT : Fits M.cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams []) [N]
        (push N ρ) (.sort u) := by
      rw [Expr.instantiateLevelParams_eq_self hTl, htT]
      exact .cons ((hF.natD ρ _).mpr rfl) hNn .nil
    exact heta (push N ρ) (.sort u) [N] x (by simp [hn]) hfitT (by simpa using hx)
  obtain ⟨e0, hp0, hc0, hn0, hf0, ho0, hs0⟩ := hpj 0 (by decide)
  obtain ⟨e1, hp1, hc1, hn1, hf1, ho1, hs1⟩ := hpj 1 (by decide)
  have f0 : field off (app (app (app (M.cval kC φ) Q) a) Z) = a := by
    have h := (hlawAt 0 e0 hp0 hc0 hn0 hf0 hs0).1
    rw [ho0, hn0] at h
    simpa using h
  have f1 : field (1 + off) (app (app (app (M.cval kC φ) Q) a) Z) = Z := by
    have h := (hlawAt 1 e1 hp1 hc1 hn1 hf1 hs1).1
    rw [ho1, hn1] at h
    simpa using h
  have h2 := (hlawAt 0 e0 hp0 hc0 hn0 hf0 hs0).2 _ hB
  rw [hf0, ho0] at h2
  have hr2 : List.range 2 = [0, 1] := rfl
  rw [hr2] at h2
  simp only [List.map_cons, List.map_nil, List.singleton_append, List.foldl_cons, List.foldl_nil,
    Nat.zero_add] at h2
  rw [f0, f1] at h2
  exact h2

/-- **Two towers of one number are one set**, when their arguments fit the constructors' stored
types at one assignment, in the empty environment. -/
theorem tower_eq (M : Model V env) (hPL : ProjLaw M.cval env) (hδ : DefnValue M)
    (hN : NatBasis env) (hgr : GradedLaw M.cval env) {tk : TowKeys} {ta : TowAux}
    (hT : TowerStored env tk ta) {φ : LevelParam → Nat} {cvU cvB cvF : ConstantVal .anon}
    (hfU : env.find? tk.u = some (.ctorInfo cvU 0 1))
    (hfB : env.find? tk.b = some (.ctorInfo cvB 1 1))
    (hfF : env.find? tk.f = some (.ctorInfo cvF 1 2)) {a : V} :
    ∀ {P Q Z P' Q' Z' : V} {σ1 σ2 σ3 σ1' σ2' σ3' : BVarIdx → V} {R1 R2 R3 R1' R2' R3' : KExpr},
    Fits M.cval env φ (fun _ => empty) cvF.type [Q, a, Z] σ3 R3 →
    Fits M.cval env φ (fun _ => empty) cvB.type
      [P, app (app (app (M.cval tk.f φ) Q) a) Z] σ2 R2 →
    Fits M.cval env φ (fun _ => empty) cvU.type
      [app (app (M.cval tk.b φ) P) (app (app (app (M.cval tk.f φ) Q) a) Z)] σ1 R1 →
    Fits M.cval env φ (fun _ => empty) cvF.type [Q', a, Z'] σ3' R3' →
    Fits M.cval env φ (fun _ => empty) cvB.type
      [P', app (app (app (M.cval tk.f φ) Q') a) Z'] σ2' R2' →
    Fits M.cval env φ (fun _ => empty) cvU.type
      [app (app (M.cval tk.b φ) P') (app (app (app (M.cval tk.f φ) Q') a) Z')] σ1' R1' →
    app (M.cval tk.u φ) (app (app (M.cval tk.b φ) P) (app (app (app (M.cval tk.f φ) Q) a) Z)) =
      app (M.cval tk.u φ) (app (app (M.cval tk.b φ) P') (app (app (app (M.cval tk.f φ) Q') a) Z'))
    := by
  have hF := natFacts M hN φ
  obtain ⟨cvBV, capsBV, uBV, mBV, hfBV, hlBV, htBV, hmBV, hTlBV⟩ := hT.bv
  obtain ⟨eBV, hpBV, hcBV, hnBV, hnfBV, hsBV⟩ := hT.bvProj
  obtain ⟨cvFin, capsFin, uFin, mFin, hfFin, hlFin, htFin, hmFin, hTlFin⟩ := hT.fin
  obtain ⟨cvU', N8e, mU, hfU', -, htU, -, -, -, -⟩ := hT.u
  obtain ⟨cvB', Pe, mB1, mB2, hfB', hlB, htB, hmB1, -, -, hBl, -, cvTF, hint, mF1, mF2, mG1, mG2,
    hfTF, -, htTF⟩ := hT.b
  obtain ⟨cvF', ls, a1, a2, mf1, mf2, mf3, hfF', hlF, htF, -, -, -, -, hFl, -, ciL, bsL, hfL, hlL,
    htL, hbl, hbn⟩ := hT.f
  rw [hfU] at hfU'
  cases hfU'
  rw [hfB] at hfB'
  cases hfB'
  rw [hfF] at hfF'
  cases hfF'
  let ρ0 : BVarIdx → V := fun _ => empty
  -- one tower, rebuilt at the families' parameters
  have canon : ∀ {P Q Z : V} {σ1 σ2 σ3 : BVarIdx → V} {R1 R2 R3 : KExpr},
      Fits M.cval env φ ρ0 cvF.type [Q, a, Z] σ3 R3 →
      Fits M.cval env φ ρ0 cvB.type [P, app (app (app (M.cval tk.f φ) Q) a) Z] σ2 R2 →
      Fits M.cval env φ ρ0 cvU.type
        [app (app (M.cval tk.b φ) P) (app (app (app (M.cval tk.f φ) Q) a) Z)] σ1 R1 →
      ∃ N8 N', Denotes M.cval env φ ρ0 N8e N8 ∧ Denotes M.cval env φ (push N8 ρ0) Pe N' ∧
        app (M.cval tk.u φ) (app (app (M.cval tk.b φ) P) (app (app (app (M.cval tk.f φ) Q) a) Z)) =
          app (M.cval tk.u φ) (app (app (M.cval tk.b φ) N8)
            (app (app (app (M.cval tk.f φ) N') a) pt)) := by
    intro P Q Z σ1 σ2 σ3 R1 R2 R3 h3 h2 h1
    -- `ofBitVec`'s domain: `BitVec N8`
    have h1' := h1
    rw [htU] at h1'
    simp only [piTele] at h1'
    cases h1' with
    | cons hA hx _ =>
      obtain ⟨Fb, N8, hFb, hN8, rfl⟩ := den_app.mp hA
      rw [(den_const0 hfBV hlBV).mp hFb] at hx
      have hgU := (hgr _ (find_mem hfU) φ ρ0).1
      simp only [ConstantInfo.toConstantVal] at hgU
      rw [htU] at hgU
      simp only [piTele] at hgU
      have hN8n := arg_nat M hN hfBV hlBV htBV hmBV (gradedBy_forallE hgU).1 hN8
      -- at `BitVec`: η at `N8`, the field in `Fin N'`
      obtain ⟨hBeq, X, hX, hXm⟩ := field_mem M hPL hδ hN hfBV hlBV htBV hTlBV hpBV hcBV hnBV hnfBV
        hsBV hfB hlB hBl hfTF htTF hN8n h2 hx
      obtain ⟨Ff, N', hFf, hN', rfl⟩ := den_app.mp hX
      rw [(den_const0 hfFin hlFin).mp hFf] at hXm
      have hgB := (hgr _ (find_mem hfB) φ ρ0).1
      simp only [ConstantInfo.toConstantVal] at hgB
      rw [htB] at hgB
      simp only [piTele] at hgB
      have hgB2 := (gradedBy_forallE hgB).2 _ ((hF.natD ρ0 _).mpr rfl) _ hN8n
      have hN'n := arg_nat M hN hfFin hlFin htFin hmFin (gradedBy_forallE hgB2).1 hN'
      -- at `Fin`: η at `N'`, the proof field the proof point
      have hFeq := fin_level M hPL hN hfFin hlFin htFin hTlFin hT.finProj hfF hlF hFl hN'n h3 hXm
      have hZ : Z = pt := ltProp_pt M hgr hfF htF hfL hlL htL hbl hbn h3
      refine ⟨N8, N', hN8, hN', ?_⟩
      rw [hBeq, hFeq, hZ]
  intro P Q Z P' Q' Z' σ1 σ2 σ3 σ1' σ2' σ3' R1 R2 R3 R1' R2' R3' h3 h2 h1 h3' h2' h1'
  obtain ⟨N8, N', hN8, hN', he⟩ := canon h3 h2 h1
  obtain ⟨N8b, N'b, hN8b, hN'b, he'⟩ := canon h3' h2' h1'
  obtain rfl := Denotes_functional hN8b hN8
  obtain rfl := Denotes_functional hN'b hN'
  rw [he, he']

end Canon

/-! ## The program's towers (`tower_canon`, `relV_mkWord`) -/

open IxCC.Src (Value Slot Term CId Program Levels Width)

/-- **The tower's constructors the program pins at width `w`**, with the keys of `tk`. -/
structure TowPins (p : Program) (κ : CId → KKey) (w : Width) (tk : TowKeys) : Prop where
  u : ∃ c, p.wordCtor? w = some c ∧ κ c = tk.u
  b : ∃ c, p.known.bitVecOfFin = some c ∧ κ c = tk.b
  f : ∃ c, p.known.finMk = some c ∧ κ c = tk.f

/-- What `asWord?` reads: the pinned tower around a literal below the size. -/
theorem asWord?_some {p : Program} {w : Width} {v : Value} {n : Nat}
    (h : p.asWord? w v = some n) :
    ∃ (c c' c'' : CId) (l1 l2 l3 : Levels) (sP sQ : Slot) (z : Value),
      v = .con c l1 [] [.con c' l2 [sP] [.con c'' l3 [sQ] [.lit n, z]]] ∧
      p.wordCtor? w = some c ∧ p.known.bitVecOfFin = some c' ∧ p.known.finMk = some c'' ∧
      n < w.size := by
  unfold Program.asWord? at h
  split at h
  · rename_i c l1 c' l2 sP c'' l3 sQ m z
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
      exact ⟨c, c', c'', l1, l2, l3, sP, sQ, z, rfl, h1.symm, h2.symm, h3.symm, h4⟩
    · cases h
  · cases h

section Prog

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env} {p : Program}
  {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}

/-- **A value read as a word is related only to the bridge's tower of its number** (`tower_canon`),
whatever its parameter slots and proof field: the relation's three constructor levels, moved to one
assignment (`fits_move`), and the bridge's tower (`tow_fits`) are one set (`tower_eq`). -/
theorem tower_canon (hL : LawsCore M) (hPL : ProjLaw M.cval env) (hgr : GradedLaw M.cval env)
    (hN : NatBasis env) {w : Width} {tk : TowKeys} {ta : TowAux} {W Sz : Nat} {kThm kR kS : KKey}
    (hB : BridgeStored env tk W Sz kThm kR kS) (hT : TowerStored env tk ta)
    (hP : TowPins p κ w tk) (hSz : Sz = w.size) {v : Value} {X : V} {n : Nat}
    (hv : RelV M p κ lpsOf S Ok v X) (hw : p.asWord? w v = some n) (φ : LevelParam → Nat) :
    X = towV M tk W Sz φ n := by
  have hcv := hL.cval_params
  obtain ⟨c, c', c'', l1, l2, l3, sP, sQ, z, rfl, hc, hc', hc'', hn⟩ := asWord?_some hw
  obtain ⟨cU, hcU, hkU⟩ := hP.u
  obtain ⟨cB, hcB, hkB⟩ := hP.b
  obtain ⟨cF, hcF, hkF⟩ := hP.f
  rw [hc] at hcU; cases hcU
  rw [hc'] at hcB; cases hcB
  rw [hc''] at hcF; cases hcF
  obtain ⟨cvU, N8e, mU, hfU, hlU, htU, -, hclU, -, hdU⟩ := hT.u
  obtain ⟨cvB, Pe, mB1, mB2, hfB, hlB, htB, -, -, hclB, -, hdB, -⟩ := hT.b
  obtain ⟨cvF, ls, a1, a2, mf1, mf2, mf3, hfF, hlF, htF, -, -, -, hclF, -, hdF, -⟩ := hT.f
  -- the three levels of the relation
  cases hv with
  | @con _ _ _ _ φ1 cv1 np1 nf1 Ps1 Fs1 ρ1 σ1 R1 _ _ hf1 _ _ hPs1 hFs1 hfit1 _ =>
    cases hPs1
    cases hFs1 with
    | @cons _ _ XB _ hXB hnil1 =>
      cases hnil1
      rw [hkU, hfU] at hf1
      cases hf1
      cases hXB with
      | @con _ _ _ _ φ2 cv2 np2 nf2 Ps2 Fs2 ρ2 σ2 R2 _ _ hf2 _ _ hPs2 hFs2 hfit2 _ =>
        cases hPs2 with
        | @cons _ _ P _ _ hnilP =>
          cases hnilP
          cases hFs2 with
          | @cons _ _ XF _ hXF hnil2 =>
            cases hnil2
            rw [hkB, hfB] at hf2
            cases hf2
            cases hXF with
            | @con _ _ _ _ φ3 cv3 np3 nf3 Ps3 Fs3 ρ3 σ3 R3 _ _ hf3 _ _ hPs3 hFs3 hfit3 _ =>
              cases hPs3 with
              | @cons _ _ Q _ _ hnilQ =>
                cases hnilQ
                cases hFs3 with
                | @cons _ _ Xn _ hXn hrest =>
                  cases hrest with
                  | @cons _ _ Zv _ _ hnil3 =>
                    cases hnil3
                    rw [hkF, hfF] at hf3
                    cases hf3
                    have hXn' := relV_lit_eq hL hN φ hXn
                    subst hXn'
                    have e1 := cval0_eq M hcv hfU hlU φ1 φ
                    have e2 := cval0_eq M hcv hfB hlB φ2 φ
                    have e3 := cval0_eq M hcv hfF hlF φ3 φ
                    simp only [List.nil_append, List.singleton_append, List.foldl_cons,
                      List.foldl_nil] at hfit1 hfit2 hfit3 ⊢
                    rw [hkU, hkB, hkF, e1, e2, e3]
                    rw [hkB, hkF, e2, e3] at hfit1
                    rw [hkF, e3] at hfit2
                    obtain ⟨σ1', R1', h1⟩ := fits_move M hcv hclU hdU hfit1 φ (fun _ => empty)
                    obtain ⟨σ2', R2', h2⟩ := fits_move M hcv hclB hdB hfit2 φ (fun _ => empty)
                    obtain ⟨σ3', R3', h3⟩ := fits_move M hcv hclF hdF hfit3 φ (fun _ => empty)
                    obtain ⟨cvU', cvB', cvF', hfU', hfB', hfF', ⟨σ3t, R3t, t3⟩, ⟨σ2t, R2t, t2⟩,
                      ⟨σ1t, R1t, t1⟩⟩ :=
                      tow_fits M hL.nat_accel hN hgr hB hT φ (by rw [hSz]; exact hn)
                    rw [hfU] at hfU'; cases hfU'
                    rw [hfB] at hfB'; cases hfB'
                    rw [hfF] at hfF'; cases hfF'
                    rw [towV_eq]
                    exact tower_eq M hPL hL.defn_value hN hgr hT hfU hfB hfF h3 h2 h1 t3 t2 t1

/-- **F6w's tower of a word is related to the bridge's tower** (`RelV.con` three times, the
arguments fitting by `tow_fits`; the proof field `irr` with no term, related to the proof point). -/
theorem relV_mkWord (hacc : NatAccel M) (hN : NatBasis env) (hgr : GradedLaw M.cval env)
    {w : Width} {tk : TowKeys} {ta : TowAux} {kThm kR kS : KKey}
    (hB : BridgeStored env tk w.bits w.size kThm kR kS) (hT : TowerStored env tk ta)
    (hP : TowPins p κ w tk)
    (hS : ∀ c, (p.wordCtor? w = some c ∨ p.known.bitVecOfFin = some c ∨ p.known.finMk = some c) →
      S c ∧ lpsOf c = [])
    {n : Nat} (hn : n < w.size) {v : Value} (hv : p.mkWord? w n = some v) (φ : LevelParam → Nat) :
    RelV M p κ lpsOf S Ok v (towV M tk w.bits w.size φ n) := by
  obtain ⟨cU, hcU, hkU⟩ := hP.u
  obtain ⟨cB, hcB, hkB⟩ := hP.b
  obtain ⟨cF, hcF, hkF⟩ := hP.f
  have hmk : p.mkWord? w n = some (.con cU [] [] [.con cB [] [.val (.lit w.bits)]
      [.con cF [] [.val (.lit w.size)] [.lit n, .irr none [] []]]]) := by
    unfold Program.mkWord?
    simp [hcU, hcB, hcF]
  rw [hmk] at hv
  cases hv
  obtain ⟨hSU, hlU⟩ := hS cU (.inl hcU)
  obtain ⟨hSB, hlB⟩ := hS cB (.inr (.inl hcB))
  obtain ⟨hSF, hlF⟩ := hS cF (.inr (.inr hcF))
  have hlv : ∀ c, lpsOf c = [] → LvAt φ (lpsOf c) [] := fun c h => by
    rw [h]; intro i q hq; simp at hq
  obtain ⟨cvU, cvB, cvF, hfU, hfB, hfF, ⟨σ3, R3, t3⟩, ⟨σ2, R2, t2⟩, ⟨σ1, R1, t1⟩⟩ :=
    tow_fits M hacc hN hgr hB hT φ hn
  have hF : RelV M p κ lpsOf S Ok (.con cF [] [.val (.lit w.size)] [.lit n, .irr none [] []])
      (towF M tk w.size φ n) := by
    have h := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok)
      (c := cF) (ls := []) (ps := [.val (.lit w.size)]) (fs := [.lit n, .irr none [] []])
      (φ := φ) (cvC := cvF) (np := 1) (nf := 2) (Ps := [litSet M φ w.size])
      (Fs := [litSet M φ n, pt]) hSF (hlv cF hlF) (by rw [hkF]; exact hfF) rfl rfl
      (.cons (.val (relV_lit_intro hN φ _)) .nil)
      (.cons (relV_lit_intro hN φ _) (.cons .irrNone .nil)) t3 (.inl hlF)
    rw [hkF] at h
    exact h
  have hBv : RelV M p κ lpsOf S Ok
      (.con cB [] [.val (.lit w.bits)] [.con cF [] [.val (.lit w.size)] [.lit n, .irr none [] []]])
      (towB M tk w.bits w.size φ n) := by
    have h := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok)
      (c := cB) (ls := []) (φ := φ) (cvC := cvB) (np := 1) (nf := 1)
      (Ps := [litSet M φ w.bits]) (Fs := [towF M tk w.size φ n])
      hSB (hlv cB hlB) (by rw [hkB]; exact hfB) rfl rfl
      (.cons (.val (relV_lit_intro hN φ _)) .nil) (.cons hF .nil) t2 (.inl hlB)
    rw [hkB] at h
    exact h
  have h := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok)
    (c := cU) (ls := []) (φ := φ) (cvC := cvU) (np := 0) (nf := 1) (Ps := [])
    (Fs := [towB M tk w.bits w.size φ n])
    hSU (hlv cU hlU) (by rw [hkU]; exact hfU) rfl rfl .nil (.cons hBv .nil) t1 (.inl hlU)
  rw [hkU] at h
  exact h

end Prog


end IxCC.Grounding
