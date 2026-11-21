module

public import IxC.Kernel.Model.Open.Certs
import IxC.Kernel.Verify.PropRead
import IxC.Kernel.Verify.PropWhen

@[expose] public section

/-!
# The rules' soundness over the public `Model`: the proof fast path

`DefEq.proofFast`: both sides' head data say "a proof at every level assignment"
(`isProofFast`), so both denote the proof point. The datum is read off the head symbol
(`proofPW`), and each way of reading it is a fact of the sets:

* an unapplied `λ` whose datum is always zero denotes `lamR 0 _ _`, the proof point;
* a constant or free-variable head whose type is a `∀` with that datum is a member of a
  product read in regime `0`, the proof point;
* a head whose type is a type former applied to arguments, the former's stored type peeling
  to `Sort u` through `never` binders with `u` of value `0`: the type's reading lands in
  `univ 0` (`peel_spine_mem_univ`: at a `never` binder the former's reading is a graph, and
  the type's grading puts each argument in its domain), so the head is the proof point;

and a spine headed by the proof point denotes it. A constant's type is read at the
assignment the use's levels induce (`Model.mem`, `Model.graded`), a free variable's through
the context. No law beyond membership and grading is read, and no stored-environment fact.
-/

namespace Ix.Kernel.Open

open SetTheory Ix.Kernel.SetModel
open Ix.Kernel.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env md} {M : Model V env} {φ : LevelParam → Nat}

/-! ## The datum -/

/-- The always-zero datum holds at every assignment. -/
theorem holds_of_isProp {pw : PropWhen} (h : pw.isProp = true) (ψ : LevelParam → Nat) :
    pw.holds ψ = true := by
  rw [eq_of_beq h]
  simp

/-- A binder with the always-zero datum is read in regime `0`. -/
theorem regime_eq_zero_of_isProp {pw : PropWhen} (h : pw.isProp = true)
    (ψ : LevelParam → Nat) : regime ψ pw = 0 := by
  simp [regime, holds_of_isProp h ψ]

/-- A level whose zero-ness datum holds evaluates to `0`. -/
theorem eval_eq_zero_of_holds {u : Level} {ψ : LevelParam → Nat}
    (h : (Level.zeronessOf u).holds ψ = true) : Level.eval ψ u = 0 := by
  rw [PropWhen.zeronessOf_sound] at h
  exact beq_iff_eq.mp h

/-! ## Spines -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem fvarLeaves_mkAppN_head : ∀ {as : List (Expr md)} {f : Expr md} {l : Nat × Expr md},
    l ∈ f.fvarLeaves → l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h => fvarLeaves_mkAppN_head (as := as) (f := .app f a)
      (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h)

/-- A leaf of a term's head is a leaf of the term. -/
theorem fvarLeaves_of_getAppFn {e hd : Expr md} (h : e.getAppFn = hd) {l : Nat × Expr md}
    (hl : l ∈ hd.fvarLeaves) : l ∈ e.fvarLeaves := by
  rw [← Expr.mkAppN_getApp e, h]
  exact fvarLeaves_mkAppN_head hl

/-- A spine headed by the proof point is the proof point. -/
theorem pt_foldl_app : ∀ (ws : List V), ws.foldl app (pt : V) = pt
  | [] => rfl
  | w :: ws => by rw [List.foldl_cons, app_pt]; exact pt_foldl_app ws

/-- **A graded closed spine applies its head along its arguments on their domains**: the
closed reading of a spine is its head's applied along the arguments' values, and its
grading grades the head and licenses each application. -/
theorem graded_spine_closed {cval : Key md → (LevelParam → Nat) → V} {ψ : LevelParam → Nat}
    {ρ : BVarIdx → V} :
    ∀ {as : List (Expr md)} {f : Expr md} {W : V},
      Denotes cval env ψ ρ (Expr.mkAppN f as) W →
      GradedBy (Denotes cval env ψ) ρ (Expr.mkAppN f as) →
      GradedBy (Denotes cval env ψ) ρ f ∧
        ∃ (F : V) (vs : List V), Denotes cval env ψ ρ f F ∧ vs.length = as.length ∧
          SpineOk F vs ∧ W = vs.foldl app F
  | [], _, _, hW, hg => ⟨hg, _, [], hW, rfl, True.intro, rfl⟩
  | a :: as, f, _, hW, hg => by
    obtain ⟨hga, F', vs, hF', hlen, hok, rfl⟩ :=
      graded_spine_closed (as := as) (f := .app f a) hW hg
    simp only [GradedBy] at hga
    obtain ⟨hgf, -, r, A, F, X, B, hF, hX, hm, hx, -⟩ := hga
    cases hF' with
    | app hF0 hX0 =>
      obtain rfl := Denotes_functional hF hF0
      obtain rfl := Denotes_functional hX hX0
      exact ⟨hgf, _, _ :: vs, hF0, by simp [hlen], SpineOk.cons_iff.2 ⟨⟨r, A, B, hm, hx⟩, hok⟩,
        rfl⟩

/-! ## Type formers -/

/-- **A type former applied along its domains lands in its result universe**: a reading of a
telescope whose first `vs.length` binders are `never` and whose residual is `Sort u`, a member
`F` of it, and values `F` applies along on their domains. At a `never` binder the reading is a
graph-regime product, so the domain the licence names is the binder's. -/
theorem peel_spine_mem_univ {cval : Key md → (LevelParam → Nat) → V} {ψ : LevelParam → Nat}
    {σ : Nat → V} :
    ∀ (vs : List V) {ρ : BVarIdx → V} {T : Expr md} {u : Level} {TI F : V},
      T.peelNeverPis vs.length = some (.sort u) → DenotesO cval env ψ σ ρ T TI → F ∈ˢ TI →
      SpineOk F vs → vs.foldl app F ∈ˢ (univ (Level.eval ψ u) : V)
  | [], _, T, u, _, _, hp, hT, hF, _ => by
    have hp0 : T.peelNeverPis 0 = some (.sort u) := hp
    obtain rfl := Expr.peelNeverPis_zero_inv hp0
    cases hT
    exact hF
  | x :: xs, _, T, u, _, F, hp, hT, hF, hok => by
    have hp1 : T.peelNeverPis (xs.length + 1) = some (.sort u) := hp
    obtain ⟨ty, b, m, rfl, hnev, hb⟩ := Expr.peelNeverPis_succ_inv hp1
    cases hT with
    | pi _ hB _ =>
      obtain ⟨⟨r, A', B', hF', hxA'⟩, hok'⟩ := SpineOk.cons_iff.1 hok
      have hreg := regime_ne_zero_of_isNever hnev ψ
      have hr : r ≠ 0 := by
        rintro rfl
        rw [eq_pt_of_mem_piR_zero hF'] at hF
        exact not_pt_mem_piR_pos hreg hF
      rw [← piR_dom_unique hreg hr hF hF'] at hxA'
      exact peel_spine_mem_univ xs hb (hB x hxA') (app_mem_piR_pos hreg hF hxA') hok'

/-- **A stored type former at a zero result level, applied along its domains, is a
proposition**: its stored type peels to `Sort u` through `vs.length` `never` binders, and
`u` has value `0` at the assignment it is read at. -/
theorem typeFormer_spine_univ_zero {I : Key md} {ciI : ConstantInfo md}
    (hfI : env.find? I = some ciI) {ψ : LevelParam → Nat} {u : Level} {vs : List V}
    (hpeel : ciI.toConstantVal.type.peelNeverPis vs.length = some (.sort u))
    (hz : Level.eval ψ u = 0) (hok : SpineOk (M.cval I ψ) vs) :
    vs.foldl app (M.cval I ψ) ∈ˢ (univ 0 : V) := by
  obtain ⟨TI, hTI, hcI⟩ := M.mem ciI (List.mem_of_find?_eq_some hfI) ψ ρ₀
  rw [find?_name hfI] at hcI
  have h := peel_spine_mem_univ (σ := fun _ => (empty : V)) vs hpeel
    (DenotesO.of_denotes hTI) hcI hok
  rwa [hz] at h

/-- **A stored constant whose type's head datum holds at an assignment denotes the proof point
there**: its type is a `∀` read in regime `0`, or a type former's instance at a zero result
level. A stored type has no free variable that its reading could read. -/
theorem storedConst_pt {c : Key md} {ci : ConstantInfo md} (hf : env.find? c = some ci)
    {ψ : LevelParam → Nat} {pw0 : PropWhen}
    (hty : typeSortPW env.find? ci.toConstantVal.type = some pw0) (hz : pw0.holds ψ = true) :
    M.cval c ψ = pt := by
  have hmem := List.mem_of_find?_eq_some hf
  obtain ⟨T, hT, hcT⟩ := M.mem ci hmem ψ ρ₀
  rw [find?_name hf] at hcT
  have hg := (M.graded ci hmem ψ ρ₀).1
  rcases typeSortPW_some_inv env.find? hty with
    ⟨A, B, mb, hTy, rfl⟩ | rfl | ⟨I, us', ciI, u, hfnT, hfI, -, -, hpeel, rfl⟩ |
    ⟨idx, ty, u, hfnT, -, -⟩
  · -- a `∀` read in regime `0`
    rw [hTy] at hT
    cases hT with
    | pi _ _ _ =>
      have h0 : regime ψ mb.pw = 0 := by simp [regime, hz]
      rw [h0] at hcT
      exact eq_pt_of_mem_piR_zero hcT
  · -- a sort's datum never holds
    simp at hz
  · -- a type former's instance
    rw [Level.holds_substPW] at hz
    have hsp := eq_mkAppN_of_getAppFn hfnT
    have hT' : Denotes M.cval env ψ ρ₀
        (Expr.mkAppN (.const I us') ci.toConstantVal.type.getAppArgs) T := by
      rw [← hsp]; exact hT
    have hg' : GradedBy (Denotes M.cval env ψ) ρ₀
        (Expr.mkAppN (.const I us') ci.toConstantVal.type.getAppArgs) := by
      rw [← hsp]; exact hg
    obtain ⟨-, F, vs, hF, hlen, hok, rfl⟩ := graded_spine_closed hT' hg'
    obtain rfl : F = M.cval I (Level.substFn ψ ciI.toConstantVal.levelParams us') := by
      cases hF with
      | const hf' _ => rw [hfI] at hf'; cases hf'; rfl
    rw [← hlen] at hpeel
    have huniv := typeFormer_spine_univ_zero hfI hpeel (eval_eq_zero_of_holds hz) hok
    rw [univ_zero] at huniv
    exact eq_pt_of_mem_univZero huniv hcT
  · -- a closed reading reads no free variable
    have hsp := Expr.mkAppN_getApp ci.toConstantVal.type
    rw [hfnT] at hsp
    have hT' : Denotes M.cval env ψ ρ₀
        (Expr.mkAppN (.fvar idx ty) ci.toConstantVal.type.getAppArgs) T := by
      rw [hsp]; exact hT
    have hg' : GradedBy (Denotes M.cval env ψ) ρ₀
        (Expr.mkAppN (.fvar idx ty) ci.toConstantVal.type.getAppArgs) := by
      rw [hsp]; exact hg
    obtain ⟨-, F, vs, hF, -⟩ := graded_spine_closed hT' hg'
    cases hF

/-! ## The rule -/

/-- **A term whose head datum says "proof" is the proof point**, at every context that
satisfies its free variables. -/
theorem proofFast_pt {a : Expr md} (h : isProofFast env.find? a = true) {σ : Nat → V}
    (hC : Ctx M φ σ a) {v : V} (hv : Den M φ σ a v) : v = pt := by
  obtain ⟨pw, hpw, hprop⟩ := isProofFast_inv env.find? h
  rcases proofPW_some_inv env.find? hpw with ⟨ty, bd, mb, rfl, rfl⟩ | ⟨-, hhead⟩
  · -- a `λ` read in regime `0`
    cases hv with
    | lam _ _ _ => rw [regime_eq_zero_of_isProp hprop φ, lamR_zero]
  have hsp : Den M φ σ (Expr.mkAppN a.getAppFn a.getAppArgs) v := by
    rw [Expr.mkAppN_getApp]; exact hv
  obtain ⟨H, ws, hH, -, rfl⟩ := Den.mkAppN_inv hsp
  suffices hpt : H = pt by rw [hpt]; exact pt_foldl_app ws
  rcases headProofPW_some_inv env.find? hhead with
    ⟨c, us, ci, hfn, hf, -, -, pw0, hty, rfl⟩ | ⟨idx, ty, hfn, hty⟩ | rfl
  · -- a constant head: its stored type decides, at the use's levels
    rw [hfn] at hH
    obtain rfl : H = M.cval c (Level.substFn φ ci.toConstantVal.levelParams us) := by
      cases hH with
      | const hf' _ => rw [hf] at hf'; cases hf'; rfl
    exact storedConst_pt hf hty (by rw [← Level.holds_substPW]; exact holds_of_isProp hprop φ)
  · -- a free-variable head: the context gives its type
    rw [hfn] at hH
    cases hH
    have hl : (idx, ty) ∈ a.fvarLeaves := fvarLeaves_of_getAppFn hfn (by simp [Expr.fvarLeaves])
    obtain ⟨⟨T, hT, hxT⟩, hgT⟩ : (∃ T, Den M φ σ ty T ∧ σ idx ∈ˢ T) ∧ Gr M φ σ ty := hC _ hl
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, rfl, rfl⟩ | rfl | ⟨I, us', ciI, u, hfnT, hfI, -, -, hpeel, rfl⟩ |
      ⟨idy, tyy, u, hfnT, hpeel, rfl⟩
    · -- a `∀` read in regime `0`
      cases hT with
      | pi _ _ _ =>
        rw [regime_eq_zero_of_isProp hprop φ] at hxT
        exact eq_pt_of_mem_piR_zero hxT
    · -- a sort's datum is never always zero
      exact absurd hprop (by simp)
    · -- a stored type former's instance
      have hsp := eq_mkAppN_of_getAppFn hfnT
      have hT' : Den M φ σ (Expr.mkAppN (.const I us') ty.getAppArgs) T := by
        rw [← hsp]; exact hT
      have hgT' : Gr M φ σ (Expr.mkAppN (.const I us') ty.getAppArgs) := by
        rw [← hsp]; exact hgT
      obtain ⟨F, vs, hF, hvs, rfl⟩ := Den.mkAppN_inv hT'
      have hok := spineOk_of_graded hgT' hF hvs
      obtain rfl : F = M.cval I (Level.substFn φ ciI.toConstantVal.levelParams us') := by
        cases hF with
        | const hf' _ => rw [hfI] at hf'; cases hf'; rfl
      have hz := holds_of_isProp hprop φ
      rw [Level.holds_substPW] at hz
      rw [hvs.length_eq] at hpeel
      have huniv := typeFormer_spine_univ_zero hfI hpeel (eval_eq_zero_of_holds hz) hok
      rw [univ_zero] at huniv
      exact eq_pt_of_mem_univZero huniv hxT
    · -- a type headed by another free variable: the context gives that one's type too
      have hl' : (idy, tyy) ∈ a.fvarLeaves := fvarLeaves_of_getAppFn hfn (by
        simp only [Expr.fvarLeaves, List.mem_cons]
        exact Or.inr (fvarLeaves_of_getAppFn hfnT (by simp [Expr.fvarLeaves])))
      obtain ⟨⟨Ty, hTy, hyTy⟩, -⟩ : (∃ T, Den M φ σ tyy T ∧ σ idy ∈ˢ T) ∧ Gr M φ σ tyy :=
        hC _ hl'
      have hsp := Expr.mkAppN_getApp ty
      rw [hfnT] at hsp
      have hT' : Den M φ σ (Expr.mkAppN (.fvar idy tyy) ty.getAppArgs) T := by
        rw [hsp]; exact hT
      have hgT' : Gr M φ σ (Expr.mkAppN (.fvar idy tyy) ty.getAppArgs) := by
        rw [hsp]; exact hgT
      obtain ⟨F, vs, hF, hvs, rfl⟩ := Den.mkAppN_inv hT'
      have hok := spineOk_of_graded hgT' hF hvs
      cases hF
      rw [hvs.length_eq] at hpeel
      have huniv := peel_spine_mem_univ vs hpeel hTy hyTy hok
      rw [eval_eq_zero_of_holds (holds_of_isProp hprop φ)] at huniv
      rw [univ_zero] at huniv
      exact eq_pt_of_mem_univZero huniv hxT
  · -- a sort, a `∀`, a literal: never a proof
    exact absurd hprop (by simp)

/-- **The proof fast path** (`DefEq.proofFast`): both sides denote the proof point. -/
theorem DefEq.proofFast_sound {d : Nat} {a b : Expr md} (ha : isProofFast env.find? a = true)
    (hb : isProofFast env.find? b = true) : DefEqS M φ d a b :=
  fun _ _ _ hCa hCb _ _ hx hy _ _ => (proofFast_pt ha hCa hx).trans (proofFast_pt hb hCb hy).symm

end Ix.Kernel.Open
