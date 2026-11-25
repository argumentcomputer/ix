import IxCC.Src.Table.Guess
import IxCCGrounding.Eqn

/-!
# Zero-TCB Grounding of `guess f c θ [θc]` (`IxCCGrounding.Guess`)

Model-level soundness and completeness over any `Ix.Kernel.Model V env`, following
`IxCCGrounding.Eqn`:

* **No extra model laws** (not even `LawsCore`): uses ONLY `Model.mem` (of `Eq`, `Bool`,
  `Bool.true`, `thm`, and optionally `comp`) and `Model.eq_equality`, matching `IxCCGrounding.Eqn`.
* **Soundness / Uniqueness (`guess_sound`, `checkGuess_sound`)**: for every level assignment `φ`,
  every argument tuple `xs` fitting `A₀ … Aₖ₋₁`, and every candidate witness `y` in `B(xs)`, if
  `c xs y` equals (denotes) `M.cval boolTrueName φ`, then `y = f xs` in `M` (via `θ` and
  `IxCCGrounding.eq_of_inhabited`).
* **Completeness (`guess_complete`, `checkGuess_complete`)**: when `comp? = some comp`, for every
  `φ` and `xs` fitting `A₀ … Aₖ₋₁`, `c xs (f xs)` equals (denotes) `M.cval boolTrueName φ` in `M`.
* **Exact Characterization (`guess_iff`)**: when both `θ` and `comp` are present (with matching
  argument domains), `c xs y = Bool.true ↔ y = f xs` in `M`.
* **Bridge from `Src.Table.Guess.checkGuess`**: `guessShape_of_checkGuess` and
  `guessCompShape_of_checkGuess` derive the kernel shapes directly from
  `checkGuess p f c thm comp? = .ok g` and the standard `Src`-to-`KEnv` type correspondence
  (`GuessEnvCorr`), with zero trusted checker logic.
-/

namespace IxCC.Grounding.Guess

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Term CId Program)
open IxCC.Src.Table (safeDefn? peelPis paramUnivs)
open IxCC.Src.Table.Guess
open IxCC.Grounding

universe w

/-! ## Kernel-level shapes and basis -/

/-- The kernel key of `Bool`. -/
abbrev boolKey : KKey := roleKey .bool

/-- `@Eq.{u} T a b` in kernel syntax. -/
def eqApp (u : Level) (T a b : KExpr) : KExpr :=
  Expr.mkAppN (.const eqName [u]) [T, a, b]

/-- Minimal `Bool` basis required by `M.eq_equality` at `@Eq.{1} Bool (c xs y) Bool.true`:
`Bool : Type 0` (`Sort 1`) and `Bool.true : Bool`, both level-monomorphic. -/
structure GuessBoolBasis (env : KEnv) : Prop where
  bool : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? boolKey = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .sort (.succ .zero)
  bTrue : ∃ cv : ConstantVal .anon,
    env.find? boolTrueName = some (.ctorInfo cv 0 0) ∧ cv.levelParams = [] ∧
    cv.type = .const boolKey []

/-- Kernel-level data of a guess-and-verify soundness theorem `θ`:
```
Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁) (y : B) (_ : @Eq.{1} Bool (c.{lps} x₀…xₖ₋₁ y) Bool.true),
  @Eq.{uB} B' y (f.{lps} x₀…xₖ₋₁)
```
mirroring `EqnData` in `IxCCGrounding.Syntax`. -/
structure GuessData where
  /-- Argument binders `(x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁)` of `θ`. -/
  Ds : List (KExpr × BinderMeta)
  /-- Witness domain `B` (under `Ds`). -/
  B : KExpr
  /-- Binder datum of `y : B` in `θ`. -/
  mY : BinderMeta
  /-- Binder datum of `_ : @Eq.{1} Bool (c xs y) Bool.true` in `θ`. -/
  mH : BinderMeta
  /-- Equality universe `u_B` in the conclusion `@Eq.{u_B} B' y (f xs)`. -/
  uB : Level
  /-- Equality type `B'` in the conclusion (under `Ds`, `y`, `h`). -/
  B' : KExpr

/-- Kernel type of a guess soundness theorem `θ` for subject `kf` and checker `kc`
at level parameters `lps`. -/
def GuessData.thmType (d : GuessData) (kf kc : KKey) (lps : List LevelParam) : KExpr :=
  piTele d.Ds
    (.forallE d.B
      (.forallE
        (eqApp (.succ .zero) (.const boolKey [])
          (Expr.mkAppN (.const kc (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
          (.const boolTrueName []))
        (eqApp d.uB d.B' (.bvar 1)
          (Expr.mkAppN (.const kf (lps.map Level.param)) (bvarsFrom 2 d.Ds.length)))
        d.mH)
      d.mY)

/-- **Checked kernel shape of a guess soundness theorem `θ`** (mirroring `EqnShape`). -/
def GuessShape (env : KEnv) (κ : CId → KKey) (f c thm : CId) (d : GuessData) : Prop :=
  EqBasis env ∧ GuessBoolBasis env ∧
  ∃ (ciF ciC : ConstantInfo .anon) (cvT : ConstantVal .anon) (pf : KExpr),
    env.find? (κ f) = some ciF ∧
    env.find? (κ c) = some ciC ∧
    env.find? (κ thm) = some (.thmInfo cvT pf) ∧
    ciC.toConstantVal.levelParams = ciF.toConstantVal.levelParams ∧
    cvT.levelParams = ciF.toConstantVal.levelParams ∧
    cvT.type = d.thmType (κ f) (κ c) cvT.levelParams

/-- Kernel type of a guess completeness theorem `θc` for subject `kf` and checker `kc`
at level parameters `lps`:
```
Π (x₀ : A₀) … (xₖ₋₁ : Aₖ₋₁),
  @Eq.{1} Bool (c.{lps} x₀…xₖ₋₁ (f.{lps} x₀…xₖ₋₁)) Bool.true
``` -/
def guessCompType (Ds : List (KExpr × BinderMeta)) (kf kc : KKey) (lps : List LevelParam) : KExpr :=
  piTele Ds
    (eqApp (.succ .zero) (.const boolKey [])
      (.app
        (Expr.mkAppN (.const kc (lps.map Level.param)) (bvarsFrom 0 Ds.length))
        (Expr.mkAppN (.const kf (lps.map Level.param)) (bvarsFrom 0 Ds.length)))
      (.const boolTrueName []))

/-- **Checked kernel shape of a guess completeness theorem `θc`**. -/
def GuessCompShape (env : KEnv) (κ : CId → KKey) (f c comp : CId)
    (compDs : List (KExpr × BinderMeta)) : Prop :=
  EqBasis env ∧ GuessBoolBasis env ∧
  ∃ (ciF ciC : ConstantInfo .anon) (cvC : ConstantVal .anon) (pf : KExpr),
    env.find? (κ f) = some ciF ∧
    env.find? (κ c) = some ciC ∧
    env.find? (κ comp) = some (.thmInfo cvC pf) ∧
    ciC.toConstantVal.levelParams = ciF.toConstantVal.levelParams ∧
    cvC.levelParams = ciF.toConstantVal.levelParams ∧
    cvC.type = guessCompType compDs (κ f) (κ c) cvC.levelParams

/-! ## Decidable kernel-side checks (mirroring `IxCCGrounding.Check.eqnShapeB`) -/

def guessBoolBasisB (env : KEnv) : Bool :=
  (match env.find? boolKey with
    | some (.indInfo cv _) => cv.levelParams.isEmpty && decide (cv.type = .sort (.succ .zero))
    | _ => false) &&
  (match env.find? boolTrueName with
    | some (.ctorInfo cv 0 0) => cv.levelParams.isEmpty && decide (cv.type = .const boolKey [])
    | _ => false)

theorem guessBoolBasis_of_check {env : KEnv} (h : guessBoolBasisB env = true) :
    GuessBoolBasis env := by
  unfold guessBoolBasisB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hB, hT⟩ := h
  refine ⟨?_, ?_⟩
  · cases hf : env.find? boolKey with
    | none => simp [hf] at hB
    | some ci =>
      simp only [hf] at hB
      cases ci with
      | indInfo cv caps =>
        simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hB
        exact ⟨cv, caps, rfl, hB.1, hB.2⟩
      | _ => simp at hB
  · cases hf : env.find? boolTrueName with
    | none => simp [hf] at hT
    | some ci =>
      simp only [hf] at hT
      cases ci with
      | ctorInfo cv np nf =>
        cases np with
        | zero =>
          cases nf with
          | zero =>
            simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hT
            exact ⟨cv, rfl, hT.1, hT.2⟩
          | succ _ => simp at hT
        | succ _ => simp at hT
      | _ => simp at hT

def guessShapeB (env : KEnv) (κ : CId → KKey) (f c thm : CId) (d : GuessData) : Bool :=
  match env.find? (κ f), env.find? (κ c), env.find? (κ thm) with
  | some ciF, some ciC, some (.thmInfo cvT _) =>
    decide (ciC.toConstantVal.levelParams = ciF.toConstantVal.levelParams) &&
    decide (cvT.levelParams = ciF.toConstantVal.levelParams) &&
    decide (cvT.type = d.thmType (κ f) (κ c) cvT.levelParams)
  | _, _, _ => false

theorem guessShape_of_check {env : KEnv} {κ : CId → KKey} {f c thm : CId} {d : GuessData}
    (hEq : EqBasis env) (hBool : GuessBoolBasis env)
    (h : guessShapeB env κ f c thm d = true) :
    GuessShape env κ f c thm d := by
  unfold guessShapeB at h
  split at h
  · rename_i ciF ciC cvT pf hf hc ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨hEq, hBool, ciF, ciC, cvT, pf, hf, hc, ht, h.1.1, h.1.2, h.2⟩
  · cases h

def guessCompShapeB (env : KEnv) (κ : CId → KKey) (f c comp : CId)
    (compDs : List (KExpr × BinderMeta)) : Bool :=
  match env.find? (κ f), env.find? (κ c), env.find? (κ comp) with
  | some ciF, some ciC, some (.thmInfo cvC _) =>
    decide (ciC.toConstantVal.levelParams = ciF.toConstantVal.levelParams) &&
    decide (cvC.levelParams = ciF.toConstantVal.levelParams) &&
    decide (cvC.type = guessCompType compDs (κ f) (κ c) cvC.levelParams)
  | _, _, _ => false

theorem guessCompShape_of_check {env : KEnv} {κ : CId → KKey} {f c comp : CId}
    {compDs : List (KExpr × BinderMeta)} (hEq : EqBasis env) (hBool : GuessBoolBasis env)
    (h : guessCompShapeB env κ f c comp compDs = true) :
    GuessCompShape env κ f c comp compDs := by
  unfold guessCompShapeB at h
  split at h
  · rename_i ciF ciC cvC pf hf hc ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨hEq, hBool, ciF, ciC, cvC, pf, hf, hc, ht, h.1.1, h.1.2, h.2⟩
  · cases h

/-! ## Environment and telescope helpers -/

section Helpers

variable {V : Type w}

theorem pushAll_cons (x : V) (xs : List V) (ρ : BVarIdx → V) :
    pushAll (x :: xs) ρ = pushAll xs (push x ρ) := by
  funext i
  simp only [pushAll, List.reverse_cons, List.length_cons, List.getD_eq_getElem?_getD]
  by_cases h1 : i < xs.length
  · have hlt : i < xs.reverse.length := by simpa using h1
    rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
    rfl
  · by_cases h2 : i = xs.length
    · subst h2
      have hge : xs.reverse.length ≤ xs.length := by simp
      have hnone : xs.reverse[xs.length]? = none := List.getElem?_eq_none hge
      rw [List.getElem?_append_right hge, List.length_reverse, Nat.sub_self, hnone]
      simp [push]
    · have hi : xs.length < i := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) (Ne.symm h2)
      have hge1 : (xs.reverse ++ [x]).length ≤ i := by
        simp only [List.length_append, List.length_reverse, List.length_singleton]
        exact hi
      have hge2 : xs.reverse.length ≤ i := by
        simp only [List.length_reverse]
        exact Nat.le_of_lt hi
      rw [List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
      simp only [Option.getD_none]
      have hsub : i - xs.length = (i - (xs.length + 1)) + 1 :=
        Nat.sub_eq_of_eq_add (by rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel hi])
      rw [hsub]
      rfl

variable [Ix.Kernel.SetTheory V] {env : KEnv}

/-- Retarget `Fits` across two `∀`-telescopes with identical domain expressions (ignoring
`BinderMeta` and codomain). -/
theorem fits_piTele_retarget {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs bs' : List (KExpr × BinderMeta)) (C C' : KExpr) {ρ σ : BVarIdx → V} {R : KExpr}
      {xs : List V},
      Fits cval env φ ρ (piTele bs C) xs σ R →
      xs.length = bs.length →
      bs.map (·.1) = bs'.map (·.1) →
      Fits cval env φ ρ (piTele bs' C') xs (pushAll xs ρ) C'
  | [], [], _, C', ρ, _, _, [], h, _, _ => by
    cases h with
    | nil => rw [pushAll_nil]; exact .nil
  | [], _ :: _, _, _, _, _, _, _, _, _, hdom => by simp at hdom
  | _ :: _, [], _, _, _, _, _, _, _, _, hdom => by simp at hdom
  | _ :: _, _ :: _, _, _, _, _, _, [], _, hlen, _ => by simp at hlen
  | [], [], _, _, _, _, _, _ :: _, _, hlen, _ => by simp at hlen
  | (A, m) :: bs, (A', m') :: bs', C, C', ρ, σ, R, x :: xs, h, hlen, hdom => by
    simp only [List.map_cons, List.cons.injEq] at hdom
    obtain ⟨rfl, hdom'⟩ := hdom
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      have hrest := fits_piTele_retarget bs bs' C C' h' (by simpa using hlen) hdom'
      rw [pushAll_cons]
      exact .cons hA hx hrest

/-- Apply a stored constant at its own level parameters. -/
private theorem den_const_self (M : Model V env) {φ : LevelParam → Nat} {k : KKey}
    {ci : ConstantInfo .anon} (hf : env.find? k = some ci) {lps : List LevelParam}
    (hlps : ci.toConstantVal.levelParams = lps) (ρ : BVarIdx → V) :
    Denotes M.cval env φ ρ (.const k (lps.map Level.param)) (M.cval k φ) := by
  have h := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ)
    (us := lps.map Level.param) hf (by rw [List.length_map, hlps])
  rwa [hlps, substFn_self] at h

end Helpers

/-! ## Core Model Soundness & Completeness (Zero Extra Laws) -/

section ModelSoundness

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **Zero-TCB soundness / uniqueness of `guess f c θ` in every kernel model `M`**
(matching `IxCCGrounding.eqn_den`: uses ONLY `Model.mem` and `Model.eq_equality`).

For any level assignment `φ`, arguments `xs` fitting `d.Ds` (`A₀ … Aₖ₋₁`), and candidate
witness `y` in the denotation `YB` of `d.B` at `xs`: if `c xs y` equals `M.cval boolTrueName φ`,
then `y = f xs` in `M`. -/
theorem guess_sound (M : Model V env) {κ : CId → KKey} {f c thm : CId} {d : GuessData}
    (hS : GuessShape env κ f c thm d) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
    {xs : List V} {σ : BVarIdx → V} {R : KExpr}
    (hfit : Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) xs σ R)
    (hlen : xs.length = d.Ds.length)
    {YB y : V}
    (hB : Denotes M.cval env φ (pushAll xs ρ0) d.B YB) (hy : y ∈ˢ YB)
    (hcheck : (xs ++ [y]).foldl app (M.cval (κ c) φ) = M.cval boolTrueName φ) :
    y = xs.foldl app (M.cval (κ f) φ) := by
  obtain ⟨hEq, hBool, ciF, ciC, cvT, pfT, hfF, hfC, hfT, hlC, hlT, htT⟩ := hS
  have hEq0 := hEq
  obtain ⟨ciEq, hfEq, hlEq, _⟩ := hEq0
  obtain ⟨cvB, capsB, hfB, hlB, htB⟩ := hBool.bool
  obtain ⟨cvBT, hfBT, hlBT, htBT⟩ := hBool.bTrue
  let lps := cvT.levelParams
  -- 1. `M.mem` on `Bool : Sort 1` and `Bool.true : Bool`.
  have hB1 : M.cval boolKey φ ∈ˢ (univ 1 : V) := by
    obtain ⟨TB, hTB, hmB⟩ := mem_key M hfB φ ρ0
    simp only [ConstantInfo.toConstantVal, htB] at hTB
    simpa [Level.eval] using den_sort.mp hTB ▸ hmB
  have hTmem : M.cval boolTrueName φ ∈ˢ M.cval boolKey φ := by
    obtain ⟨TBT, hTBT, hmBT⟩ := mem_key M hfBT φ ρ0
    simp only [ConstantInfo.toConstantVal, htBT] at hTBT
    rwa [(den_const0 hfB hlB).mp hTBT] at hmBT
  -- 2. `M.mem` on `thm` and `Fits` through `d.Ds` followed by `y : d.B`.
  obtain ⟨TT, hTT, hPm⟩ := mem_key M hfT φ ρ0
  simp only [ConstantInfo.toConstantVal] at hTT
  rw [htT] at hTT
  let conclT : KExpr :=
    .forallE d.B
      (.forallE
        (eqApp (.succ .zero) (.const boolKey [])
          (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
          (.const boolTrueName []))
        (eqApp d.uB d.B' (.bvar 1)
          (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 2 d.Ds.length)))
        d.mH)
      d.mY
  have hfitT := fits_piTele_retarget d.Ds d.Ds (.sort .zero) conclT hfit hlen rfl
  have hfitY := fits_snoc hfitT rfl hB hy
  obtain ⟨TH, hTH, hPy⟩ := fits_app_mem hfitY hTT hPm
  -- 3. Under `ρ₁ = push y (pushAll xs ρ0)`, the check hypothesis `@Eq.{1} Bool (c xs y) Bool.true`
  --    denotes `eqv (c xs y) Bool.true`, inhabited by `pt` since `c xs y = Bool.true`.
  let ρ₁ := push y (pushAll xs ρ0)
  have hρ₁ : pushAll (xs ++ [y]) ρ0 = ρ₁ := pushAll_snoc xs y ρ0
  have hEqD : Denotes M.cval env φ ρ₁ (.const eqName [.succ .zero])
      (M.cval eqName (Level.substFn φ [0] [.succ .zero])) := by
    have h1 := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := ρ₁)
      (us := [.succ .zero]) hfEq (by rw [hlEq]; rfl)
    rwa [hlEq] at h1
  have hcDen : Denotes M.cval env φ ρ₁
      (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
      ((xs ++ [y]).foldl app (M.cval (κ c) φ)) := by
    have hlen1 : (xs ++ [y]).length = d.Ds.length + 1 := by simp [hlen]
    rw [← hlen1]
    refine den_mkAppN_bvars 0 (xs ++ [y]) _ _ (fun j hj => ?_)
      (den_const_self M hfC (by rw [hlC, ← hlT]) ρ₁)
    rw [Nat.zero_add, ← hρ₁]
    exact pushAll_rev (xs ++ [y]) ρ0 j hj
  have hCmem : (xs ++ [y]).foldl app (M.cval (κ c) φ) ∈ˢ M.cval boolKey φ :=
    hcheck ▸ hTmem
  have hDomD : Denotes M.cval env φ ρ₁
      (eqApp (.succ .zero) (.const boolKey [])
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
        (.const boolTrueName []))
      (eqv ((xs ++ [y]).foldl app (M.cval (κ c) φ)) (M.cval boolTrueName φ)) := by
    have h1 := M.eq_equality (.succ .zero) φ ρ₁ _ (M.cval boolKey φ)
      ((xs ++ [y]).foldl app (M.cval (κ c) φ)) (M.cval boolTrueName φ)
      hEqD hB1 hCmem hTmem
    unfold eqApp Expr.mkAppN
    rw [← h1]
    exact .app (.app (.app hEqD ((den_const0 hfB hlB).mpr rfl)) hcDen)
      ((den_const0 hfBT hlBT).mpr rfl)
  have hpt : (pt : V) ∈ˢ eqv ((xs ++ [y]).foldl app (M.cval (κ c) φ)) (M.cval boolTrueName φ) := by
    rw [hcheck]
    exact pt_mem_eqv_self _
  -- 4. Instantiate `θ` at `pt`, yielding inhabitation of `@Eq.{uB} B' #1 (f xs)`.
  obtain ⟨TConcl, hTConcl, hPpt⟩ := app_mem_den_pi hTH hDomD hPy hpt
  -- 5. Apply `eq_of_inhabited` and match `#1 ↦ y` and `f xs ↦ xs.foldl app (M.cval (κ f) φ)`.
  obtain ⟨z, hzL, hzR⟩ := eq_of_inhabited M hEq hTConcl hPpt
  have hyDen : Denotes M.cval env φ (push pt ρ₁) (.bvar 1) y := den_bvar.mpr rfl
  have hfDen : Denotes M.cval env φ (push pt ρ₁)
      (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 2 d.Ds.length))
      (xs.foldl app (M.cval (κ f) φ)) := by
    rw [← hlen]
    refine den_mkAppN_bvars 2 xs _ _ (fun j hj => ?_)
      (den_const_self M hfF hlT.symm (push pt ρ₁))
    have hidx : 2 + xs.length - 1 - j = (xs.length - 1 - j) + 2 := by omega
    rw [hidx]
    exact pushAll_rev xs ρ0 j hj
  rw [Denotes_functional hyDen hzL, Denotes_functional hzR hfDen]

/-- **Zero-TCB soundness in `Denotes` form**: if the kernel application `c.{lps} xs y` denotes
`M.cval boolTrueName φ` at `pushAll (xs ++ [y]) ρ0`, then `y = xs.foldl app (M.cval (κ f) φ)`. -/
theorem guess_sound_denotes (M : Model V env) {κ : CId → KKey} {f c thm : CId} {d : GuessData}
    (hS : GuessShape env κ f c thm d) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
    {xs : List V} {σ : BVarIdx → V} {R : KExpr}
    (hfit : Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) xs σ R)
    (hlen : xs.length = d.Ds.length)
    {YB y : V}
    (hB : Denotes M.cval env φ (pushAll xs ρ0) d.B YB) (hy : y ∈ˢ YB)
    {lps : List LevelParam}
    (hlps : ∀ ci, env.find? (κ c) = some ci → ci.toConstantVal.levelParams = lps)
    (hcheck : Denotes M.cval env φ (pushAll (xs ++ [y]) ρ0)
      (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
      (M.cval boolTrueName φ)) :
    y = xs.foldl app (M.cval (κ f) φ) := by
  have hS0 := hS
  obtain ⟨_, _, _, ciC, _, _, _, hfC, _, _, _, _⟩ := hS0
  have hlC := hlps ciC hfC
  have hcDen : Denotes M.cval env φ (pushAll (xs ++ [y]) ρ0)
      (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (d.Ds.length + 1)))
      ((xs ++ [y]).foldl app (M.cval (κ c) φ)) := by
    have hlen1 : (xs ++ [y]).length = d.Ds.length + 1 := by simp [hlen]
    rw [← hlen1]
    refine den_mkAppN_bvars 0 (xs ++ [y]) _ _ (fun j hj => ?_) (den_const_self M hfC hlC _)
    rw [Nat.zero_add]
    exact pushAll_rev (xs ++ [y]) ρ0 j hj
  exact guess_sound M hS φ ρ0 hfit hlen hB hy (Denotes_functional hcDen hcheck)

/-- **Zero-TCB completeness of `guess f c θ (some comp)` in every kernel model `M`**
(uses ONLY `Model.mem` and `Model.eq_equality`).

For any level assignment `φ` and arguments `xs` fitting `compDs` (`A₀ … Aₖ₋₁`),
`c xs (f xs)` equals `M.cval boolTrueName φ` in `M`. -/
theorem guess_complete (M : Model V env) {κ : CId → KKey} {f c comp : CId}
    {compDs : List (KExpr × BinderMeta)}
    (hC : GuessCompShape env κ f c comp compDs) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
    {xs : List V} {σ : BVarIdx → V} {R : KExpr}
    (hfit : Fits M.cval env φ ρ0 (piTele compDs (.sort .zero)) xs σ R)
    (hlen : xs.length = compDs.length) :
    (xs ++ [xs.foldl app (M.cval (κ f) φ)]).foldl app (M.cval (κ c) φ) =
      M.cval boolTrueName φ := by
  obtain ⟨hEq, hBool, ciF, ciC, cvComp, pfComp, hfF, hfC, hfComp, hlC, hlComp, htComp⟩ := hC
  obtain ⟨cvBT, hfBT, hlBT, _⟩ := hBool.bTrue
  let lps := cvComp.levelParams
  obtain ⟨TComp, hTComp, hPm⟩ := mem_key M hfComp φ ρ0
  simp only [ConstantInfo.toConstantVal] at hTComp
  rw [htComp] at hTComp
  let conclC : KExpr :=
    eqApp (.succ .zero) (.const boolKey [])
      (.app
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
        (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length)))
      (.const boolTrueName [])
  have hfitC := fits_piTele_retarget compDs compDs (.sort .zero) conclC hfit hlen rfl
  obtain ⟨TConcl, hTConcl, hPxs⟩ := fits_app_mem hfitC hTComp hPm
  obtain ⟨z, hzL, hzR⟩ := eq_of_inhabited M hEq hTConcl hPxs
  have hcDen : Denotes M.cval env φ (pushAll xs ρ0)
      (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
      (xs.foldl app (M.cval (κ c) φ)) := by
    rw [← hlen]
    refine den_mkAppN_bvars 0 xs _ _ (fun j hj => ?_)
      (den_const_self M hfC (by rw [hlC, ← hlComp]) _)
    rw [Nat.zero_add]
    exact pushAll_rev xs ρ0 j hj
  have hfDen : Denotes M.cval env φ (pushAll xs ρ0)
      (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
      (xs.foldl app (M.cval (κ f) φ)) := by
    rw [← hlen]
    refine den_mkAppN_bvars 0 xs _ _ (fun j hj => ?_)
      (den_const_self M hfF hlComp.symm _)
    rw [Nat.zero_add]
    exact pushAll_rev xs ρ0 j hj
  have hlhsDen : Denotes M.cval env φ (pushAll xs ρ0)
      (.app
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
        (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length)))
      ((xs ++ [xs.foldl app (M.cval (κ f) φ)]).foldl app (M.cval (κ c) φ)) := by
    simpa [List.foldl_append] using Denotes.app hcDen hfDen
  have hrhsDen : Denotes M.cval env φ (pushAll xs ρ0) (.const boolTrueName [])
      (M.cval boolTrueName φ) := (den_const0 hfBT hlBT).mpr rfl
  rw [Denotes_functional hlhsDen hzL, Denotes_functional hzR hrhsDen]

/-- **Completeness in `Denotes` form**: the kernel application `c.{lps} xs (f.{lps} xs)`
denotes `M.cval boolTrueName φ` at `pushAll xs ρ0`. -/
theorem guess_complete_denotes (M : Model V env) {κ : CId → KKey} {f c comp : CId}
    {compDs : List (KExpr × BinderMeta)}
    (hC : GuessCompShape env κ f c comp compDs) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
    {xs : List V} {σ : BVarIdx → V} {R : KExpr}
    (hfit : Fits M.cval env φ ρ0 (piTele compDs (.sort .zero)) xs σ R)
    (hlen : xs.length = compDs.length)
    {lps : List LevelParam}
    (hlps : ∀ ci, env.find? (κ f) = some ci → ci.toConstantVal.levelParams = lps) :
    Denotes M.cval env φ (pushAll xs ρ0)
      (.app
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
        (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length)))
      (M.cval boolTrueName φ) := by
  have heq := guess_complete M hC φ ρ0 hfit hlen
  obtain ⟨_, _, ciF, ciC, _, _, hfF, hfC, _, hlC, _, _⟩ := hC
  have hlF := hlps ciF hfF
  have hcDen : Denotes M.cval env φ (pushAll xs ρ0)
      (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
      (xs.foldl app (M.cval (κ c) φ)) := by
    rw [← hlen]
    refine den_mkAppN_bvars 0 xs _ _ (fun j hj => ?_)
      (den_const_self M hfC (by rw [hlC, hlF]) _)
    rw [Nat.zero_add]
    exact pushAll_rev xs ρ0 j hj
  have hfDen : Denotes M.cval env φ (pushAll xs ρ0)
      (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
      (xs.foldl app (M.cval (κ f) φ)) := by
    rw [← hlen]
    refine den_mkAppN_bvars 0 xs _ _ (fun j hj => ?_)
      (den_const_self M hfF hlF _)
    rw [Nat.zero_add]
    exact pushAll_rev xs ρ0 j hj
  have hden : Denotes M.cval env φ (pushAll xs ρ0)
      (.app
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 compDs.length))
        (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 compDs.length)))
      ((xs ++ [xs.foldl app (M.cval (κ f) φ)]).foldl app (M.cval (κ c) φ)) := by
    simpa [List.foldl_append] using Denotes.app hcDen hfDen
  rwa [heq] at hden

/-- **Exact biconditional characterization**: given both `GuessShape` and `GuessCompShape` over
matching argument domains, for every `xs` fitting `d.Ds` and every witness `y ∈ B(xs)`,
`c xs y = Bool.true ↔ y = f xs` in `M`. -/
theorem guess_iff (M : Model V env) {κ : CId → KKey} {f c thm comp : CId} {d : GuessData}
    {compDs : List (KExpr × BinderMeta)}
    (hS : GuessShape env κ f c thm d) (hC : GuessCompShape env κ f c comp compDs)
    (hdoms : d.Ds.map (·.1) = compDs.map (·.1))
    (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
    {xs : List V} {σ : BVarIdx → V} {R : KExpr}
    (hfit : Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) xs σ R)
    (hlen : xs.length = d.Ds.length)
    {YB y : V} (hB : Denotes M.cval env φ (pushAll xs ρ0) d.B YB) (hy : y ∈ˢ YB) :
    (xs ++ [y]).foldl app (M.cval (κ c) φ) = M.cval boolTrueName φ ↔
      y = xs.foldl app (M.cval (κ f) φ) := by
  constructor
  · exact guess_sound M hS φ ρ0 hfit hlen hB hy
  · intro hyf
    subst hyf
    have hlenC : xs.length = compDs.length := by
      have hm := congrArg List.length hdoms
      simp only [List.length_map] at hm
      omega
    have hfitC := fits_piTele_retarget d.Ds compDs (.sort .zero) (.sort .zero) hfit hlen hdoms
    exact guess_complete M hC φ ρ0 hfitC hlenC

end ModelSoundness

/-! ## Bridge from `IxCC.Src.Table.Guess.checkGuess` to `Ix.Kernel.Model` -/

section SrcBridge

private theorem univ_eq_of_beq : ∀ (u1 u2 : IxCC.Ixon.Univ), (u1 == u2) = true → u1 = u2
  | .zero, .zero, _ => rfl
  | .succ a, .succ b, h => by
    have h' : (a == b) = true := h
    rw [univ_eq_of_beq a b h']
  | .max a1 b1, .max a2 b2, h => by
    have h' : ((a1 == a2) && (b1 == b2)) = true := h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    rw [univ_eq_of_beq a1 a2 h1, univ_eq_of_beq b1 b2 h2]
  | .imax a1 b1, .imax a2 b2, h => by
    have h' : ((a1 == a2) && (b1 == b2)) = true := h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    rw [univ_eq_of_beq a1 a2 h1, univ_eq_of_beq b1 b2 h2]
  | .var i, .var j, h => by
    have h' : (i == j) = true := h
    rw [beq_iff_eq.mp h']
  | .zero, .succ _, h | .zero, .max _ _, h | .zero, .imax _ _, h | .zero, .var _, h
  | .succ _, .zero, h | .succ _, .max _ _, h | .succ _, .imax _ _, h | .succ _, .var _, h
  | .max _ _, .zero, h | .max _ _, .succ _, h | .max _ _, .imax _ _, h | .max _ _, .var _, h
  | .imax _ _, .zero, h | .imax _ _, .succ _, h | .imax _ _, .max _ _, h | .imax _ _, .var _, h
  | .var _, .zero, h | .var _, .succ _, h | .var _, .max _ _, h | .var _, .imax _ _, h =>
    nomatch h

private theorem list_univ_eq_of_beq :
    ∀ (us1 us2 : List IxCC.Ixon.Univ), (us1 == us2) = true → us1 = us2
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | u1 :: us1, u2 :: us2, h => by
    have h' : ((u1 == u2) && (us1 == us2)) = true := h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h'
    rw [univ_eq_of_beq u1 u2 h1, list_univ_eq_of_beq us1 us2 h2]

/-- `Term.eqv` preserves `TermCorr`: syntactic equality ignoring `Mode`/`Rel`/`Binder`
corresponds to the same kernel `KExpr`. -/
theorem termCorr_eqv_congr {κ : CId → KKey} {lps : List Nat} :
    ∀ {t1 t2 : Term} {e : KExpr}, TermCorr κ lps t1 e → t1.eqv t2 = true → TermCorr κ lps t2 e
  | _, t2, _, .var, h => by
    cases t2 <;> simp only [Term.eqv, beq_iff_eq, Bool.false_eq_true] at h
    subst h; exact .var
  | _, t2, _, .sort hu, h => by
    cases t2 <;> simp only [Term.eqv, Bool.false_eq_true] at h
    rw [← univ_eq_of_beq _ _ h]
    exact .sort hu
  | _, t2, _, .const hlen hu, h => by
    cases t2 <;> simp only [Term.eqv, Bool.and_eq_true, Bool.false_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rw [← beq_iff_eq.mp h1, ← list_univ_eq_of_beq _ _ h2]
    exact .const hlen hu
  | _, t2, _, .app hf ha, h => by
    cases t2 <;> simp only [Term.eqv, Bool.and_eq_true, Bool.false_eq_true] at h
    exact .app (termCorr_eqv_congr hf h.1) (termCorr_eqv_congr ha h.2)
  | _, t2, _, .lam hd hb, h => by
    cases t2 <;> simp only [Term.eqv, Bool.and_eq_true, Bool.false_eq_true] at h
    exact .lam (termCorr_eqv_congr hd h.1) (termCorr_eqv_congr hb h.2)
  | _, t2, _, .pi hd hc, h => by
    cases t2 <;> simp only [Term.eqv, Bool.and_eq_true, Bool.false_eq_true] at h
    exact .pi (termCorr_eqv_congr hd h.1) (termCorr_eqv_congr hc h.2)
  | _, t2, _, .proj he, h => by
    cases t2 <;> simp only [Term.eqv, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl⟩, h'⟩ := h
    exact .proj (termCorr_eqv_congr he h')
  | _, t2, _, .natLit, h => by
    cases t2 <;> simp only [Term.eqv, beq_iff_eq, Bool.false_eq_true] at h
    subst h; exact .natLit

theorem spine_go_mkApps : ∀ (t : Term) (acc : List Term.Arg) (h : Term) (args : List Term.Arg),
    Term.spine.go t acc = (h, args) → Term.mkApps t acc = Term.mkApps h args
  | .app f a m r, acc, h, args, hs => spine_go_mkApps f ((a, m, r) :: acc) h args hs
  | .var _, acc, h, args, hs | .sort _, acc, h, args, hs | .const _ _, acc, h, args, hs
  | .lam _ _ _, acc, h, args, hs | .pi _ _ _, acc, h, args, hs
  | .letE _ _ _ _ _ _, acc, h, args, hs | .proj _ _ _, acc, h, args, hs
  | .natLit _, acc, h, args, hs | .strLit _, acc, h, args, hs => by
    simp only [Term.spine.go, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    rfl

theorem spine_mkApps {t h : Term} {args : List Term.Arg} (hs : t.spine = (h, args)) :
    t = Term.mkApps h args :=
  spine_go_mkApps t [] h args hs

theorem termCorr_peelPis {κ : CId → KKey} {lps : List Nat} :
    ∀ (k : Nat) (t : Term) (e : KExpr) (bs : List (IxCC.Src.Binder × Term)) (body : Term),
      TermCorr κ lps t e → peelPis k t = some (bs, body) →
      ∃ (kbs : List (KExpr × BinderMeta)) (ke : KExpr),
        kbs.length = k ∧ e = piTele kbs ke ∧ TermCorr κ lps body ke ∧
        ∀ (i : Nat) (b : IxCC.Src.Binder × Term) (kb : KExpr × BinderMeta),
          bs[i]? = some b → kbs[i]? = some kb → TermCorr κ lps b.2 kb.1
  | 0, t, e, bs, body, hc, hp => by
    simp only [peelPis, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨[], e, rfl, rfl, hc, fun _ _ _ h1 => by simp at h1⟩
  | k + 1, t, e, bs, body, hc, hp => by
    cases t with
    | pi b d t' =>
      simp only [peelPis, Option.bind_eq_bind] at hp
      cases hp' : peelPis k t' with
      | none => simp [hp'] at hp
      | some pair =>
        rcases pair with ⟨bs', body'⟩
        simp only [hp', Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        cases hc with
        | @pi _ _ _ d' e' mb hcd hct =>
          obtain ⟨kbs', ke, hlen, rfl, hcb, hdoms⟩ := termCorr_peelPis k t' e' bs' body' hct hp'
          refine ⟨(d', mb) :: kbs', ke, by simp [hlen], rfl, hcb, fun i b0 kb0 hb0 hkb0 => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hb0 hkb0
            subst hb0 hkb0
            exact hcd
          | succ i =>
            exact hdoms i b0 kb0 (by simpa using hb0) (by simpa using hkb0)
    | _ => simp [peelPis] at hp

theorem termCorr_const_nil {κ : CId → KKey} {lps : List Nat} {c : CId} {e : KExpr}
    (h : TermCorr κ lps (.const c []) e) : e = .const (κ c) [] := by
  cases h with
  | @const _ _ ls hlen _ =>
    cases ls with
    | nil => rfl
    | cons _ _ => simp at hlen

theorem termCorr_const_one {κ : CId → KKey} {lps : List Nat} {c : CId} {e : KExpr}
    (h : TermCorr κ lps (.const c [.succ .zero]) e) : e = .const (κ c) [.succ .zero] := by
  cases h with
  | @const _ _ ls hlen hu =>
    cases ls with
    | nil => simp at hlen
    | cons l ls' =>
      cases ls' with
      | cons _ _ => simp at hlen
      | nil =>
        have huc := hu 0 (.succ .zero) l rfl rfl
        cases huc with
        | succ h0 =>
          cases h0
          rfl

theorem termCorr_paramUnivs {κ : CId → KKey} {lps : List Nat} {d : CId} {n : Nat} {e : KExpr}
    (hlen : lps.length = n) (hlt : n < UInt64.size)
    (h : TermCorr κ lps (.const d (paramUnivs n)) e) :
    e = .const (κ d) (lps.map Level.param) := by
  cases h with
  | @const _ _ ls hlenU hu =>
    congr 1
    have hls : ls.length = lps.length := by
      simp only [paramUnivs, List.length_map, List.length_range] at hlenU
      omega
    refine List.ext_getElem (by simp [hls]) fun i hi1 hi2 => ?_
    have hiN : i < n := by omega
    have hpu : (paramUnivs n)[i]? = some (.var i.toUInt64) := by
      simp [paramUnivs, hiN]
    have huc := hu i (.var i.toUInt64) ls[i] hpu (List.getElem?_eq_getElem hi1)
    generalize hli : ls[i] = l at huc ⊢
    cases huc with
    | var hp =>
      have htoNat : i.toUInt64.toNat = i := by
        simpa [Nat.toUInt64, UInt64.toNat_ofNat] using Nat.mod_eq_of_lt (by omega : i < UInt64.size)
      rw [htoNat, List.getElem?_eq_getElem (by omega)] at hp
      simp only [Option.some.injEq] at hp
      subst hp
      simp

theorem termCorr_mkApps {κ : CId → KKey} {lps : List Nat} :
    ∀ (args : List Term.Arg) (f : Term) (f' : KExpr) (args' : List KExpr) (e : KExpr),
      (∀ e', TermCorr κ lps f e' → e' = f') →
      args.length = args'.length →
      (∀ (i : Nat) (a : Term.Arg) (a' : KExpr),
        args[i]? = some a → args'[i]? = some a' → ∀ e', TermCorr κ lps a.1 e' → e' = a') →
      TermCorr κ lps (Term.mkApps f args) e →
      e = Expr.mkAppN f' args'
  | [], f, f', [], e, hf, _, _, hc => hf e hc
  | [], _, _, _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _, _, [], _, _, hlen, _, _ => by simp at hlen
  | (a, m, r) :: rest, f, f', a' :: rest', e, hf, hlen, ha, hc => by
    refine termCorr_mkApps rest (.app f a m r) (.app f' a') rest' e ?_ (by simpa using hlen)
      (fun i x x' hx hx' => ha (i + 1) x x' (by simpa using hx) (by simpa using hx')) hc
    intro e' hfa
    cases hfa with
    | app hf' ha' =>
      rw [hf _ hf', ha 0 (a, m, r) a' rfl rfl _ ha']

theorem termCorr_mkAppVars {κ : CId → KKey} {lps : List Nat} {d : CId} {n offset k : Nat}
    {e : KExpr} (hlen : lps.length = n) (hlt : n < UInt64.size)
    (h : TermCorr κ lps (mkAppVars d n offset k) e) :
    e = Expr.mkAppN (.const (κ d) (lps.map Level.param)) (bvarsFrom offset k) := by
  refine termCorr_mkApps _ (.const d (paramUnivs n)) (.const (κ d) (lps.map Level.param))
    (bvarsFrom offset k) e (fun _ hc => termCorr_paramUnivs hlen hlt hc)
    (by simp [boundVarsFrom, bvarsFrom]) (fun i a a' ha ha' e' he' => ?_) h
  simp only [boundVarsFrom, List.map_map, List.getElem?_map] at ha
  simp only [bvarsFrom, List.getElem?_map] at ha'
  cases hget : (List.range k).reverse[i]? with
  | none => simp [hget] at ha
  | some idx =>
    rw [hget] at ha ha'
    simp only [Option.map_some, Option.some.injEq] at ha ha'
    subst ha ha'
    cases he'
    rfl

theorem termCorr_mkEq1 {κ : CId → KKey} {lps : List Nat} {eqC boolC : CId}
    {lhs rhs : Term} {lhs' rhs' e : KExpr}
    (heq : κ eqC = eqName) (hbool : κ boolC = boolKey)
    (hlhs : ∀ e', TermCorr κ lps lhs e' → e' = lhs')
    (hrhs : ∀ e', TermCorr κ lps rhs e' → e' = rhs')
    (h : TermCorr κ lps (mkEq1 eqC (.const boolC []) lhs rhs) e) :
    e = eqApp (.succ .zero) (.const boolKey []) lhs' rhs' := by
  cases h with
  | app h1 hr =>
    cases h1 with
    | app h2 hl =>
      cases h2 with
      | app h3 hb =>
        rw [termCorr_const_one h3, heq, termCorr_const_nil hb, hbool, hlhs _ hl, hrhs _ hr]
        rfl

/-- Standard `Src`-to-`KEnv` correspondence hypotheses for a checked `guess` entry
(mirroring `IxCCGrounding.Check`'s pinned-role and stored-declaration facts):
* `EqBasis env` and `GuessBoolBasis env`;
* pinned `Eq`, `Bool`, `Bool.true` in `p.known` map via `κ` to `eqName`, `boolKey`, `boolTrueName`;
* `f`, `c`, `thm` (and `comp` if present) are stored in `env` with shared level parameters `lps`
  of length matching their `Src` declarations, and their `Src` types correspond node-for-node
  (`TermCorr κ lps`) to their stored kernel types. -/
structure GuessEnvCorr (p : Program) (env : KEnv) (κ : CId → KKey) (lps : List Nat)
    (f c thm : CId) (comp? : Option CId) : Prop where
  eqBasis : EqBasis env
  boolBasis : GuessBoolBasis env
  eqPin : ∀ eqC, p.known.eq = some eqC → κ eqC = eqName
  boolPin : ∀ boolC, p.known.bool = some boolC → κ boolC = boolKey
  boolTruePin : ∀ boolTrueC, p.known.boolTrue = some boolTrueC → κ boolTrueC = boolTrueName
  fStored : ∀ n tf vf, safeDefn? p f = some (n, tf, vf) →
    ∃ ciF : ConstantInfo .anon, env.find? (κ f) = some ciF ∧
      ciF.toConstantVal.levelParams = lps ∧ lps.length = n ∧
      TermCorr κ lps tf ciF.toConstantVal.type
  cStored : ∀ n tc vc, safeDefn? p c = some (n, tc, vc) →
    ∃ ciC : ConstantInfo .anon, env.find? (κ c) = some ciC ∧
      ciC.toConstantVal.levelParams = lps ∧
      TermCorr κ lps tc ciC.toConstantVal.type
  thmStored : ∀ n tθ vθ, p.decl? thm = some (.defn .thm .safe n tθ vθ) →
    ∃ (cvT : ConstantVal .anon) (pf : KExpr), env.find? (κ thm) = some (.thmInfo cvT pf) ∧
      cvT.levelParams = lps ∧ TermCorr κ lps tθ cvT.type
  compStored : ∀ comp, comp? = some comp →
    ∀ n tComp vComp, p.decl? comp = some (.defn .thm .safe n tComp vComp) →
      ∃ (cvComp : ConstantVal .anon) (pf : KExpr),
        env.find? (κ comp) = some (.thmInfo cvComp pf) ∧
        cvComp.levelParams = lps ∧ TermCorr κ lps tComp cvComp.type

/-- **`checkGuess` yields `GuessShape`**: every entry accepted by `Src.Table.Guess.checkGuess`
has the exact kernel soundness shape `GuessShape` in `env`. -/
theorem guessShape_of_checkGuess {p : Program} {env : KEnv} {κ : CId → KKey} {lps : List Nat}
    {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm comp? = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm comp?) :
    ∃ d : GuessData, d.Ds.length = g.arity ∧ GuessShape env κ f c thm d := by
  obtain ⟨-, -, -, n, tf, vf, tc, vc, tθ, vθ, eqC, boolC, boolTrueC,
    fBinders, fBody, cArgs, bCY, cYDom, cBody, θArgs, bY, yDom, bH, hDom, θBody,
    uB, eqTy, lhs, rhs, hlt, hsf, hsc, hthm, _, _, _, _, _, _, _,
    heqC, hboolC, hbtC, _, _, _, _, _, hpeelθ, _, _, hhDomEqv, hθEq, _, hlhsEqv, hrhsEqv, _⟩ :=
    checkGuess_ok_props hcheck
  obtain ⟨ciF, hfF, hlF, hlenLps, _⟩ := hcorr.fStored n tf vf hsf
  obtain ⟨ciC, hfC, hlC, _⟩ := hcorr.cStored n tc vc hsc
  obtain ⟨cvT, pfT, hfT, hlT, hcorrθ⟩ := hcorr.thmStored n tθ vθ hthm
  obtain ⟨kDs, ke, hlenDs, htθEq, hcorrRest, _⟩ :=
    termCorr_peelPis g.arity tθ cvT.type θArgs (.pi bY yDom (.pi bH hDom θBody)) hcorrθ hpeelθ
  cases hcorrRest with
  | @pi _ _ _ B ke1 mY _ hcorrRest2 =>
    cases hcorrRest2 with
    | @pi _ _ _ hDomK θBodyK mH hcorrHDom hcorrBody =>
      -- Match `hDomK` via `hDom.eqv ...`
      have hHDomEq : hDomK = eqApp (.succ .zero) (.const boolKey [])
          (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 (g.arity + 1)))
          (.const boolTrueName []) :=
        termCorr_mkEq1 (hcorr.eqPin eqC heqC) (hcorr.boolPin boolC hboolC)
          (fun _ hc => termCorr_mkAppVars hlenLps hlt hc)
          (fun _ hc => by rw [termCorr_const_nil hc, hcorr.boolTruePin boolTrueC hbtC])
          (termCorr_eqv_congr hcorrHDom hhDomEqv)
      -- Match `θBodyK` via `eqAppUniv?`
      unfold eqAppUniv? at hθEq
      cases hsp : θBody.spine with
      | mk spHead spArgs =>
        rw [hsp] at hθEq
        cases spHead with
        | const eqId eqUs =>
          cases eqUs with
          | cons u0 eqUs' =>
            cases eqUs' with
            | nil =>
              cases spArgs with
              | cons a1 r1 =>
                cases r1 with
                | cons a2 r2 =>
                  cases r2 with
                  | cons a3 r3 =>
                    cases r3 with
                    | nil =>
                      simp only [beq_iff_eq] at hθEq
                      split at hθEq
                      · rename_i heqId
                        simp only [Option.some.injEq, Prod.mk.injEq] at hθEq
                        obtain ⟨hu0, ha1, ha2, ha3⟩ := hθEq
                        rw [heqC, Option.some.injEq] at heqId
                        subst hu0 ha1 ha2 ha3 heqId
                        have hθBodyForm : θBody =
                            .app (.app (.app (.const eqId [u0]) a1.1 a1.2.1 a1.2.2)
                              a2.1 a2.2.1 a2.2.2) a3.1 a3.2.1 a3.2.2 := by
                          simpa [Term.mkApps] using spine_mkApps hsp
                        rw [hθBodyForm] at hcorrBody
                        cases hcorrBody with
                        | @app _ _ _ _ _ rhsK h1 hcorrRhs =>
                          cases h1 with
                          | @app _ _ _ _ _ lhsK h2 hcorrLhs =>
                            cases h2 with
                            | @app _ _ _ _ _ eqTyK h3 hcorrEqTy =>
                              cases h3 with
                              | @const _ _ eqLs hlenU _ =>
                                cases eqLs with
                                | nil => simp at hlenU
                                | cons uBK eqLs' =>
                                  cases eqLs' with
                                  | cons _ _ => simp at hlenU
                                  | nil =>
                                    have hvar : TermCorr κ lps (.var 1) lhsK :=
                                      termCorr_eqv_congr hcorrLhs hlhsEqv
                                    have hlhsK : lhsK = .bvar 1 := by
                                      cases hvar
                                      rfl
                                    have hrhsK : rhsK = Expr.mkAppN (.const (κ f)
                                        (lps.map Level.param)) (bvarsFrom 2 g.arity) :=
                                      termCorr_mkAppVars hlenLps hlt
                                        (termCorr_eqv_congr hcorrRhs hrhsEqv)
                                    let d : GuessData :=
                                      { Ds := kDs, B, mY, mH, uB := uBK, B' := eqTyK }
                                    refine ⟨d, hlenDs, hcorr.eqBasis, hcorr.boolBasis,
                                      ciF, ciC, cvT, pfT, hfF, hfC, hfT,
                                      by rw [hlC, hlF], by rw [hlT, hlF], ?_⟩
                                    rw [htθEq, hHDomEq, hlhsK, hrhsK, hcorr.eqPin eqId heqC]
                                    simp only [d, GuessData.thmType, hlT, hlenDs, eqApp,
                                      Expr.mkAppN]
                      · cases hθEq
                    | cons _ _ => simp at hθEq
                  | nil => simp at hθEq
                | nil => simp at hθEq
              | nil => simp at hθEq
            | cons _ _ => simp at hθEq
          | nil => simp at hθEq
        | _ => simp at hθEq

/-- **`checkGuess` yields `GuessCompShape`**: when `comp? = some comp`, every entry accepted by
`Src.Table.Guess.checkGuess` has the exact kernel completeness shape `GuessCompShape` in `env`. -/
theorem guessCompShape_of_checkGuess {p : Program} {env : KEnv} {κ : CId → KKey} {lps : List Nat}
    {f c thm comp : CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm (some comp) = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm (some comp)) :
    ∃ compDs : List (KExpr × BinderMeta),
      compDs.length = g.arity ∧ GuessCompShape env κ f c comp compDs := by
  obtain ⟨-, -, -, n, tf, vf, tc, vc, _, _, eqC, boolC, boolTrueC,
    fBinders, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlt, hsf, hsc, _, _, _, _, _, _, _, _,
    heqC, hboolC, hbtC, _, _, _, _, _, _, _, _, _, _, _, _, _, hcompAll⟩ :=
    checkGuess_ok_props hcheck
  obtain ⟨tComp, vComp, compBinders, compBody, hdeclComp, _, _, _, hpeelComp, _, hbodyEqv⟩ :=
    hcompAll comp rfl
  obtain ⟨ciF, hfF, hlF, hlenLps, _⟩ := hcorr.fStored n tf vf hsf
  obtain ⟨ciC, hfC, hlC, _⟩ := hcorr.cStored n tc vc hsc
  obtain ⟨cvComp, pfComp, hfComp, hlComp, hcorrComp⟩ :=
    hcorr.compStored comp rfl n tComp vComp hdeclComp
  obtain ⟨kDs, ke, hlenDs, htCompEq, hcorrBody, _⟩ :=
    termCorr_peelPis g.arity tComp cvComp.type compBinders compBody hcorrComp hpeelComp
  have hkeEq : ke = eqApp (.succ .zero) (.const boolKey [])
      (.app
        (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 g.arity))
        (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 g.arity)))
      (.const boolTrueName []) :=
    termCorr_mkEq1 (hcorr.eqPin eqC heqC) (hcorr.boolPin boolC hboolC)
      (fun e' hca => by
        cases hca with
        | app hcApp hfApp =>
          rw [termCorr_mkAppVars hlenLps hlt hcApp, termCorr_mkAppVars hlenLps hlt hfApp])
      (fun _ hc => by rw [termCorr_const_nil hc, hcorr.boolTruePin boolTrueC hbtC])
      (termCorr_eqv_congr hcorrBody hbodyEqv)
  refine ⟨kDs, hlenDs, hcorr.eqBasis, hcorr.boolBasis, ciF, ciC, cvComp, pfComp,
    hfF, hfC, hfComp, by rw [hlC, hlF], by rw [hlComp, hlF], ?_⟩
  rw [htCompEq, hkeEq]
  simp only [guessCompType, hlComp, hlenDs]

/-! ## Headline Zero-TCB Grounding Theorems for `checkGuess` -/

section EndToEnd

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **Zero-TCB soundness of `checkGuess` in any kernel model `M`**:
if `checkGuess p f c thm comp? = .ok g` and the declarations correspond to `env` (`GuessEnvCorr`),
then there exists `d : GuessData` of arity `g.arity` with `GuessShape env κ f c thm d` such that
for every level assignment `φ`, argument sets `xs` fitting `A₀ … Aₖ₋₁` (`d.Ds`), and candidate
witness `y ∈ B(xs)` (`d.B`), if `c xs y = Bool.true` in `M`, then `y = f xs` in `M`. -/
theorem checkGuess_sound (M : Model V env) {p : Program} {κ : CId → KKey} {lps : List Nat}
    {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm comp? = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm comp?) :
    ∃ d : GuessData, d.Ds.length = g.arity ∧ GuessShape env κ f c thm d ∧
      ∀ (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (xs : List V) (σ : BVarIdx → V) (R : KExpr),
        Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) xs σ R →
        xs.length = g.arity →
        ∀ (YB y : V),
          Denotes M.cval env φ (pushAll xs ρ0) d.B YB → y ∈ˢ YB →
          (xs ++ [y]).foldl app (M.cval (κ c) φ) = M.cval boolTrueName φ →
          y = xs.foldl app (M.cval (κ f) φ) := by
  obtain ⟨d, hlenD, hS⟩ := guessShape_of_checkGuess hcheck hcorr
  exact ⟨d, hlenD, hS, fun φ ρ0 xs σ R hfit hlen YB y hB hy hchk =>
    guess_sound M hS φ ρ0 hfit (by omega) hB hy hchk⟩

/-- **Zero-TCB completeness of `checkGuess` in any kernel model `M`**:
if `checkGuess p f c thm (some comp) = .ok g` and `GuessEnvCorr`, then there exists `compDs`
of arity `g.arity` with `GuessCompShape env κ f c comp compDs` such that for every level
assignment `φ` and argument sets `xs` fitting `A₀ … Aₖ₋₁` (`compDs`), `c xs (f xs) = Bool.true`
in `M` (and the kernel term `c.{lps} xs (f.{lps} xs)` denotes `M.cval boolTrueName φ`). -/
theorem checkGuess_complete (M : Model V env) {p : Program} {κ : CId → KKey} {lps : List Nat}
    {f c thm comp : CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm (some comp) = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm (some comp)) :
    ∃ compDs : List (KExpr × BinderMeta),
      compDs.length = g.arity ∧ GuessCompShape env κ f c comp compDs ∧
      ∀ (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (xs : List V) (σ : BVarIdx → V) (R : KExpr),
        Fits M.cval env φ ρ0 (piTele compDs (.sort .zero)) xs σ R →
        xs.length = g.arity →
        (xs ++ [xs.foldl app (M.cval (κ f) φ)]).foldl app (M.cval (κ c) φ) =
          M.cval boolTrueName φ ∧
        Denotes M.cval env φ (pushAll xs ρ0)
          (.app
            (Expr.mkAppN (.const (κ c) (lps.map Level.param)) (bvarsFrom 0 g.arity))
            (Expr.mkAppN (.const (κ f) (lps.map Level.param)) (bvarsFrom 0 g.arity)))
          (M.cval boolTrueName φ) := by
  obtain ⟨compDs, hlenC, hC⟩ := guessCompShape_of_checkGuess hcheck hcorr
  obtain ⟨-, -, -, n, tf, vf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, hsf, _⟩ := checkGuess_ok_props hcheck
  obtain ⟨ciF', hfF', hlF', _, _⟩ := hcorr.fStored n tf vf hsf
  have hlpsF : ∀ ci, env.find? (κ f) = some ci → ci.toConstantVal.levelParams = lps := by
    intro ci hci
    rw [hfF'] at hci
    cases hci
    exact hlF'
  refine ⟨compDs, hlenC, hC, fun φ ρ0 xs σ R hfit hlen => ?_⟩
  refine ⟨guess_complete M hC φ ρ0 hfit (by omega), ?_⟩
  rw [← hlenC]
  exact guess_complete_denotes M hC φ ρ0 hfit (by omega) hlpsF

/-- **Combined Zero-TCB Grounding of `checkGuess`**: packages both soundness (from `thm`) and
optional completeness (from `comp? = some comp`) in any kernel model `M`, using zero laws beyond
`Model.mem` and `Model.eq_equality`. -/
theorem checkGuess_ground (M : Model V env) {p : Program} {κ : CId → KKey} {lps : List Nat}
    {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm comp? = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm comp?) :
    (∃ d : GuessData, d.Ds.length = g.arity ∧ GuessShape env κ f c thm d ∧
      ∀ (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (xs : List V) (σ : BVarIdx → V) (R : KExpr),
        Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) xs σ R →
        xs.length = g.arity →
        ∀ (YB y : V),
          Denotes M.cval env φ (pushAll xs ρ0) d.B YB → y ∈ˢ YB →
          (xs ++ [y]).foldl app (M.cval (κ c) φ) = M.cval boolTrueName φ →
          y = xs.foldl app (M.cval (κ f) φ)) ∧
    (∀ comp, comp? = some comp →
      ∃ compDs : List (KExpr × BinderMeta),
        compDs.length = g.arity ∧ GuessCompShape env κ f c comp compDs ∧
        ∀ (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
          (xs : List V) (σ : BVarIdx → V) (R : KExpr),
          Fits M.cval env φ ρ0 (piTele compDs (.sort .zero)) xs σ R →
          xs.length = g.arity →
          (xs ++ [xs.foldl app (M.cval (κ f) φ)]).foldl app (M.cval (κ c) φ) =
            M.cval boolTrueName φ) := by
  refine ⟨checkGuess_sound M hcheck hcorr, fun comp hcomp => ?_⟩
  subst hcomp
  obtain ⟨compDs, hlenC, hC, hbody⟩ := checkGuess_complete M hcheck hcorr
  exact ⟨compDs, hlenC, hC, fun φ ρ0 xs σ R hfit hlen => (hbody φ ρ0 xs σ R hfit hlen).1⟩

end EndToEnd

end SrcBridge

end IxCC.Grounding.Guess
