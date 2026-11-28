import IxCC.Src.Table.Guess
import IxCC.Src.Table.Cert
import IxCC.Src.EvalG
import IxCCGrounding.Eqn
import IxCCGrounding.Fundamental
import IxCCGrounding.Tele

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

/-! ## Thin Relational `SrcG` Soundness (`S2`) -/

section SrcGSoundness

open IxCC.Src (Value Slot Levels)
open IxCC.Src.Table (domainEqv)

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- Pointwise relation between `Src.Value` list and model-element list `V` (Mathlib-free). -/
inductive ValDenList (R : Value → V → Prop) : List Value → List V → Prop where
  | nil : ValDenList R [] []
  | cons {v : Value} {vs : List Value} {X : V} {Xs : List V} :
      R v X → ValDenList R vs Xs → ValDenList R (v :: vs) (X :: Xs)

omit [Ix.Kernel.SetTheory V] in
theorem valDenList_length {R : Value → V → Prop} :
    ∀ {vs : List Value} {Xs : List V}, ValDenList R vs Xs → Xs.length = vs.length
  | [], _, .nil => rfl
  | _ :: _, _, .cons _ h => by simp [valDenList_length h]

omit [Ix.Kernel.SetTheory V] in
theorem valDenList_snoc {R : Value → V → Prop} :
    ∀ {vs : List Value} {Xs : List V} {v : Value} {X : V},
      ValDenList R vs Xs → R v X → ValDenList R (vs ++ [v]) (Xs ++ [X])
  | [], _, _, _, .nil, hv => .cons hv .nil
  | _ :: _, _, _, _, .cons h1 h', hv => .cons h1 (valDenList_snoc h' hv)

theorem valDenList_of_relVs {M : Model V env} {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop} :
    ∀ {vs : List Value} {Xs : List V},
      RelVs M p κ lpsOf S Ok vs Xs → ValDenList (RelV M p κ lpsOf S Ok) vs Xs
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by cases h with | cons h1 h' => exact .cons h1 (valDenList_of_relVs h')

theorem relVs_of_valDenList {M : Model V env} {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop} :
    ∀ {vs : List Value} {Xs : List V},
      ValDenList (RelV M p κ lpsOf S Ok) vs Xs → RelVs M p κ lpsOf S Ok vs Xs
  | [], _, .nil => .nil
  | _ :: _, _, .cons h1 h' => .cons h1 (relVs_of_valDenList h')

theorem relSlots_of_relVs {M : Model V env} {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop} :
    ∀ {vs : List Value} {Xs : List V},
      RelVs M p κ lpsOf S Ok vs Xs → RelSlots M p κ lpsOf S Ok (vs.map .val) Xs
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by cases h with | cons h1 h' => exact .cons (.val h1) (relSlots_of_relVs h')

/-! ### `Bool.true` adequacy and telescope transport helpers -/

/-- Under `GuessBoolBasis`, `M.cval boolTrueName φ` lies in `M.cval boolKey φ`. -/
theorem boolTrue_mem_bool (M : Model V env) (hBool : GuessBoolBasis env)
    (φ : LevelParam → Nat) :
    M.cval boolTrueName φ ∈ˢ M.cval boolKey φ := by
  obtain ⟨cvB, _, hfB, hlB, _⟩ := hBool.bool
  obtain ⟨cvBT, hfBT, _, htBT⟩ := hBool.bTrue
  obtain ⟨TBT, hTBT, hmBT⟩ := mem_key M hfBT φ (fun _ => empty)
  simp only [ConstantInfo.toConstantVal, htBT] at hTBT
  rwa [(den_const0 hfB hlB).mp hTBT] at hmBT

/-- Any model element `Z` related by `RelV` to the pinned `Bool.true` constructor equals
`M.cval boolTrueName φ` (uses only `GuessBoolBasis` and `Model.cval_params`). -/
theorem relV_boolTrue_eq (M : Model V env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}
    {boolTrueC : CId} (hBool : GuessBoolBasis env) (hbtPin : κ boolTrueC = boolTrueName)
    {Z : V} (h : RelV M p κ lpsOf S Ok (.con boolTrueC [] [] []) Z)
    (φ : LevelParam → Nat) :
    Z = M.cval boolTrueName φ := by
  cases h with
  | con _ _ _ _ _ hPs hFs _ _ =>
    cases hPs
    cases hFs
    obtain ⟨cvBT, hfBT, hlBT, _⟩ := hBool.bTrue
    simp only [List.append_nil, List.foldl_nil, hbtPin]
    exact M.cval_params boolTrueName (.ctorInfo cvBT 0 0) hfBT _ φ fun q hq => by
      simp [ConstantInfo.toConstantVal, hlBT] at hq

/-- The pinned `Bool.true` constructor relates to `M.cval boolTrueName φ` under `RelV`. -/
theorem relV_boolTrue_intro (M : Model V env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}
    {boolTrueC : CId} (hBool : GuessBoolBasis env) (hS : S boolTrueC)
    (hlps : lpsOf boolTrueC = []) (hbtPin : κ boolTrueC = boolTrueName)
    (φ : LevelParam → Nat) :
    RelV M p κ lpsOf S Ok (.con boolTrueC [] [] []) (M.cval boolTrueName φ) := by
  obtain ⟨cvBT, hfBT, _, _⟩ := hBool.bTrue
  have hlv : LvAt φ (lpsOf boolTrueC) [] := by
    rw [hlps]; intro i q h; simp at h
  have hcon := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok)
    (c := boolTrueC) (ls := []) (ps := []) (fs := []) (φ := φ)
    (cvC := cvBT) (np := 0) (nf := 0) (Ps := []) (Fs := [])
    (ρ := fun _ => empty) hS hlv (by rwa [hbtPin]) rfl rfl .nil .nil .nil (.inl hlps)
  simpa [hbtPin] using hcon

private theorem piTele_inj :
    ∀ (bs1 bs2 : List (KExpr × BinderMeta)) (C1 C2 : KExpr),
      piTele bs1 C1 = piTele bs2 C2 → bs1.length = bs2.length → bs1 = bs2 ∧ C1 = C2
  | [], [], C1, C2, h, _ => ⟨rfl, h⟩
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | (A1, m1) :: bs1, (A2, m2) :: bs2, C1, C2, h, hl => by
    simp only [piTele, Expr.forallE.injEq] at h
    obtain ⟨rfl, hbody, rfl⟩ := h
    obtain ⟨hbs, hC⟩ := piTele_inj bs1 bs2 C1 C2 hbody (by simpa using hl)
    exact ⟨congrArg _ hbs, hC⟩

theorem fits_piTele_sigma {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {ρ σ : BVarIdx → V} {R : KExpr} {xs : List V},
      Fits cval env φ ρ (piTele bs C) xs σ R →
      xs.length = bs.length →
      σ = pushAll xs ρ ∧ R = C
  | [], C, ρ, _, _, [], h, _ => by
    cases h with
    | nil => exact ⟨(pushAll_nil ρ).symm, rfl⟩
  | [], _, _, _, _, _ :: _, _, hl => by simp at hl
  | _ :: _, _, _, _, _, [], _, hl => by simp at hl
  | (A, m) :: bs, C, ρ, σ, R, x :: xs, h, hl => by
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons _ _ h' =>
      obtain ⟨hσ, hR⟩ := fits_piTele_sigma bs C h' (by simpa using hl)
      rw [pushAll_cons]
      exact ⟨hσ, hR⟩

theorem fits_piTele_retarget_den {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs bs' : List (KExpr × BinderMeta)) (C C' : KExpr) {ρ σ : BVarIdx → V} {R : KExpr}
      {xs : List V},
      Fits cval env φ ρ (piTele bs C) xs σ R →
      xs.length = bs.length →
      bs.length = bs'.length →
      (∀ (i : Nat) (b b' : KExpr × BinderMeta), bs[i]? = some b → bs'[i]? = some b' →
        ∀ (ρ' : BVarIdx → V) (X : V),
          Denotes cval env φ ρ' b.1 X → Denotes cval env φ ρ' b'.1 X) →
      Fits cval env φ ρ (piTele bs' C') xs (pushAll xs ρ) C'
  | [], [], _, C', ρ, _, _, [], h, _, _, _ => by
    cases h with
    | nil => rw [pushAll_nil]; exact .nil
  | [], _ :: _, _, _, _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, _, _, _, _, _, [], _, hl, _, _ => by simp at hl
  | [], [], _, _, _, _, _, _ :: _, _, hl, _, _ => by simp at hl
  | (A, m) :: bs, (A', m') :: bs', C, C', ρ, σ, R, x :: xs, h, hl, hlB, hdom => by
    have h0 : Fits cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h0 with
    | cons hA hx h' =>
      have hA' := hdom 0 (A, m) (A', m') rfl rfl ρ _ hA
      have hrest := fits_piTele_retarget_den bs bs' C C' h' (by simpa using hl)
        (by simpa using hlB) (fun i b b' hb hb' =>
          hdom (i + 1) b b' (by simpa using hb) (by simpa using hb'))
      rw [pushAll_cons]
      exact .cons hA' hx hrest

/-- Domain denotation preservation for `Src.Table.domainEqv`: two `Src` domains accepted by
`domainEqv` that correspond via `TermCorr` to kernel expressions denote the same set in `M`. -/
def DomDenEq (M : Model V env) (p : Program) (κ : CId → KKey) (lps : List Nat) : Prop :=
  ∀ (a b : Term) (a' b' : KExpr) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V),
    domainEqv p a b = true → TermCorr κ lps a a' → TermCorr κ lps b b' →
    Denotes M.cval env φ ρ a' X → Denotes M.cval env φ ρ b' X

/-- Arguments `Xs` fit the stored kernel type of `κ f` at `(φ, ρ0)`, with result domain `TR`. -/
def CallFits (M : Model V env) (κ : CId → KKey) (f : CId) (φ : LevelParam → Nat)
    (ρ0 : BVarIdx → V) (Xs : List V) (TR : V) : Prop :=
  ∃ (ciF : ConstantInfo .anon) (σ : BVarIdx → V) (R : KExpr),
    env.find? (κ f) = some ciF ∧
    Fits M.cval env φ ρ0 ciF.toConstantVal.type Xs σ R ∧
    Denotes M.cval env φ σ R TR

/-- Transport a well-typed call `(f, Xs, Y)` across a checked `guess` entry `g = (c, k, thm, comp?)`:
1. Produces `GuessData` `d` with `GuessShape env κ f c thm d` where `Xs` fits `d.Ds` and `Y ∈ d.B(Xs)`.
2. Produces `CallFits M κ c φ ρ0 (Xs ++ [Y]) (M.cval boolKey φ)` for the checker call. -/
theorem checkGuess_transfer_call (M : Model V env) {p : Program} {κ : CId → KKey}
    {lps : List Nat} {f c thm : CId} {comp? : Option CId} {g : GuessEntry}
    (hcheck : checkGuess p f c thm comp? = .ok g)
    (hcorr : GuessEnvCorr p env κ lps f c thm comp?)
    (hdom : DomDenEq M p κ lps)
    {φ : LevelParam → Nat} {ρ0 : BVarIdx → V} {Xs : List V} {TR Y : V}
    (hlen : Xs.length = g.arity)
    (hfit : CallFits M κ f φ ρ0 Xs TR) (hy : Y ∈ˢ TR) :
    (∃ d : GuessData, d.Ds.length = g.arity ∧ GuessShape env κ f c thm d ∧
      Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) Xs (pushAll Xs ρ0) (.sort .zero) ∧
      Denotes M.cval env φ (pushAll Xs ρ0) d.B TR) ∧
    CallFits M κ c φ ρ0 (Xs ++ [Y]) (M.cval boolKey φ) := by
  obtain ⟨-, -, -, n, tf, vf, tc, vc, tθ, vθ, eqC, boolC, boolTrueC,
    fBinders, fBody, cArgs, bCY, cYDom, cBody, θArgs, bY, yDom, bH, hDom, θBody,
    _, _, _, _, _, hsf, hsc, hthm, _, _, _, _, _, _, _,
    _, hboolC, _,
    hpeelF, hpeelC, hcD, hcYD, hcB, hpeelθ, hθD, hyD,
    _, _, _, _, _, _⟩ := checkGuess_ok_props hcheck
  obtain ⟨ciF, hfF, _, _, hcorrF⟩ := hcorr.fStored n tf vf hsf
  obtain ⟨ciC, hfC, _, hcorrC⟩ := hcorr.cStored n tc vc hsc
  obtain ⟨cvT, pfT, hfT, _, hcorrθ⟩ := hcorr.thmStored n tθ vθ hthm
  obtain ⟨ciF', σ, R, hfF', hfitsF, hdenR⟩ := hfit
  rw [hfF] at hfF'; cases hfF'
  obtain ⟨kfDs, kfB, hlenKf, htfEq, hcorrFB, hdomsF⟩ :=
    termCorr_peelPis g.arity tf ciF.toConstantVal.type fBinders fBody hcorrF hpeelF
  have hlenFB : fBinders.length = g.arity := peelPis_length g.arity tf fBinders fBody hpeelF
  rw [htfEq] at hfitsF
  obtain ⟨rfl, rfl⟩ := fits_piTele_sigma kfDs kfB hfitsF (by omega)
  -- 1. Build `GuessShape` and transfer `Fits` + `d.B` from `tf` to `tθ`.
  obtain ⟨d, hlenD, hShape⟩ := guessShape_of_checkGuess hcheck hcorr
  obtain ⟨kθDs, kθRest, hlenKθ, htθEq, hcorrθRest, hdomsθ⟩ :=
    termCorr_peelPis g.arity tθ cvT.type θArgs (.pi bY yDom (.pi bH hDom θBody)) hcorrθ hpeelθ
  have hlenθB : θArgs.length = g.arity := peelPis_length g.arity tθ θArgs _ hpeelθ
  cases hcorrθRest with
  | @pi _ _ _ kθB kθRest2 mY' hcorrYDom _ =>
    have hShape0 := hShape
    obtain ⟨_, _, _, _, cvT', _, _, _, hfT', _, _, htθShape⟩ := hShape0
    rw [hfT] at hfT'; cases hfT'
    unfold GuessData.thmType at htθShape
    rw [htθShape] at htθEq
    obtain ⟨hDsEq, hRestEq⟩ := piTele_inj d.Ds kθDs _ _ htθEq (by omega)
    subst hDsEq
    injection hRestEq with hBEq _ _
    subst hBEq
    have hfitθ : Fits M.cval env φ ρ0 (piTele d.Ds (.sort .zero)) Xs (pushAll Xs ρ0) (.sort .zero) := by
      refine fits_piTele_retarget_den kfDs d.Ds R (.sort .zero) hfitsF (by omega) (by omega)
        fun i bF bθ hbF hbθ ρ' X hX => ?_
      have hi : i < g.arity := by
        have := (List.getElem?_eq_some_iff.1 hbF).1; omega
      have hbf : fBinders[i]? = some fBinders[i] := List.getElem?_eq_getElem (by omega)
      have hbθ' : θArgs[i]? = some θArgs[i] := List.getElem?_eq_getElem (by omega)
      have hzip : (fBinders[i], θArgs[i]) ∈ fBinders.zip θArgs :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hbf, hbθ'⟩)
      have hdeqv : domainEqv p fBinders[i].2 θArgs[i].2 = true := List.all_eq_true.mp hθD _ hzip
      exact hdom _ _ _ _ φ ρ' X hdeqv (hdomsF i _ _ hbf hbF) (hdomsθ i _ _ hbθ' hbθ) hX
    have hdenB : Denotes M.cval env φ (pushAll Xs ρ0) d.B TR :=
      hdom _ _ _ _ φ (pushAll Xs ρ0) TR hyD hcorrFB hcorrYDom hdenR
    -- 2. Transfer `Fits` from `tf` to `tc` and extend by witness `Y ∈ˢ TR`.
    obtain ⟨kcDs, kcRest, hlenKc, htcEq, hcorrCRest, hdomsC⟩ :=
      termCorr_peelPis g.arity tc ciC.toConstantVal.type cArgs (.pi bCY cYDom cBody) hcorrC hpeelC
    have hlenCB : cArgs.length = g.arity := peelPis_length g.arity tc cArgs _ hpeelC
    cases hcorrCRest with
    | @pi _ _ _ kcYDom kcBody mCY hcorrCYDom hcorrCBody =>
      have hkcBody : kcBody = .const boolKey [] := by
        rw [termCorr_const_nil (termCorr_eqv_congr hcorrCBody hcB), hcorr.boolPin boolC hboolC]
      subst hkcBody
      have hfitC0 : Fits M.cval env φ ρ0
          (piTele kcDs (.forallE kcYDom (.const boolKey []) mCY)) Xs (pushAll Xs ρ0)
          (.forallE kcYDom (.const boolKey []) mCY) := by
        refine fits_piTele_retarget_den kfDs kcDs R (.forallE kcYDom (.const boolKey []) mCY)
          hfitsF (by omega) (by omega) fun i bF bC hbF hbC ρ' X hX => ?_
        have hi : i < g.arity := by
          have := (List.getElem?_eq_some_iff.1 hbF).1; omega
        have hbf : fBinders[i]? = some fBinders[i] := List.getElem?_eq_getElem (by omega)
        have hbc : cArgs[i]? = some cArgs[i] := List.getElem?_eq_getElem (by omega)
        have hzip : (fBinders[i], cArgs[i]) ∈ fBinders.zip cArgs :=
          List.mem_of_getElem? (List.getElem?_zip_eq_some.mpr ⟨hbf, hbc⟩)
        have hdeqv : domainEqv p fBinders[i].2 cArgs[i].2 = true := List.all_eq_true.mp hcD _ hzip
        exact hdom _ _ _ _ φ ρ' X hdeqv (hdomsF i _ _ hbf hbF) (hdomsC i _ _ hbc hbC) hX
      have hdenCY : Denotes M.cval env φ (pushAll Xs ρ0) kcYDom TR :=
        hdom _ _ _ _ φ (pushAll Xs ρ0) TR hcYD hcorrFB hcorrCYDom hdenR
      have hfitC := fits_snoc hfitC0 rfl hdenCY hy
      rw [← htcEq] at hfitC
      obtain ⟨cvB, _, hfB, hlB, _⟩ := hcorr.boolBasis.bool
      have hdenBool : Denotes M.cval env φ (push Y (pushAll Xs ρ0)) (.const boolKey [])
          (M.cval boolKey φ) := (den_const0 hfB hlB).mpr rfl
      exact ⟨⟨d, hlenD, hShape, hfitθ, hdenB⟩,
        ⟨ciC, push Y (pushAll Xs ρ0), .const boolKey [], hfC, hfitC, hdenBool⟩⟩

/-- Grounding hypotheses for a program `p` with a validated `table.guess` over `M : Model V env`
and a value-to-set relation `ValDen : Value → V → Prop` (instantiated below with `RelV`). -/
structure GuessTableGround (M : Model V env) (p : Program) (κ : CId → KKey)
    (lpsOf : CId → List Nat) (ValDen : Value → V → Prop) : Prop where
  /-- Every `guess` entry in `p.table` passes `Table.Guess.validateGuess`
  (discharged by `Table.ofCert_hardened` or `Table.validate_guess_ok`). -/
  valid : ∀ f g, p.table.guessOf f = some g → validateGuess p f g = .ok ()
  /-- Every `guess` entry in `p.table` satisfies `GuessEnvCorr` at `lpsOf f` with matching
  level parameters for `f` and `g.checker`. -/
  envCorr : ∀ f g, p.table.guessOf f = some g →
    GuessEnvCorr p env κ (lpsOf f) f g.checker g.thm g.comp? ∧
    lpsOf g.checker = lpsOf f
  /-- Domain denotation preservation for `domainEqv` at every `guess` entry. -/
  domDen : ∀ f g, p.table.guessOf f = some g → DomDenEq M p κ (lpsOf f)
  /-- `Bool.true` adequacy of `ValDen` at the pinned `Bool.true` constructor. -/
  boolTrueDen : ∀ boolTrueC Z φ, p.known.boolTrue = some boolTrueC →
    GuessBoolBasis env → κ boolTrueC = boolTrueName →
    ValDen (.con boolTrueC [] [] []) Z → Z = M.cval boolTrueName φ
  boolTrueVal : ∀ boolTrueC φ, p.known.boolTrue = some boolTrueC →
    GuessBoolBasis env → κ boolTrueC = boolTrueName →
    ValDen (.con boolTrueC [] [] []) (M.cval boolTrueName φ)
  /-- Standard `SrcEval` (`runAt`) soundness on calls fitting the stored type. -/
  srcSound : ∀ (k : Nat) (ls : Levels) (f : CId) (xs : List Value) (y : Value)
      (φ : LevelParam → Nat) (ρ0 : BVarIdx → V) (Xs : List V) (TR : V),
    IxCC.Src.runAt p k ls f xs = .ok y →
    LvAt φ (lpsOf f) ls →
    ValDenList ValDen xs Xs →
    CallFits M κ f φ ρ0 Xs TR →
    ValDen y (Xs.foldl app (M.cval (κ f) φ))

/-- **Soundness (`S2`) of the thin relational `SrcG` layer (`RunG`)**:
every `RunG p ls f xs y` derivation (of arbitrary `guess` nesting depth) over a validated
`table.guess` (`GuessTableGround`) relates `y` to `f xs` in `M` (`ValDen y (f xs)`), composing
directly with `checkGuess_ground` / `guess_sound`. -/
theorem runG_sound {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ValDen : Value → V → Prop}
    (hG : GuessTableGround M p κ lpsOf ValDen)
    {ls : Levels} {f : CId} {xs : List Value} {y : Value}
    (hRun : IxCC.Src.RunG p ls f xs y) :
    ∀ (φ : LevelParam → Nat) (ρ0 : BVarIdx → V) (Xs : List V) (TR : V),
      LvAt φ (lpsOf f) ls →
      ValDenList ValDen xs Xs →
      CallFits M κ f φ ρ0 Xs TR →
      (p.table.guessOf f ≠ none → ∃ Y, ValDen y Y ∧ Y ∈ˢ TR) →
      ValDen y (Xs.foldl app (M.cval (κ f) φ)) := by
  induction hRun with
  | src hk =>
    intro φ ρ0 Xs TR hlv hxs hfit _
    exact hG.srcSound _ _ _ _ _ φ ρ0 Xs TR hk hlv hxs hfit
  | guess hg hlen hbt hchk ih =>
    rename_i ls' f' g xs' y' boolTrueC
    intro φ ρ0 Xs TR hlv hxs hfit hwit
    obtain ⟨Y, hyV, hyM⟩ := hwit (by rw [hg]; simp)
    have hcheck : checkGuess p f' g.checker g.thm g.comp? = .ok g :=
      validateGuess_iff.mp (hG.valid f' g hg)
    obtain ⟨hcorr, hlpsC⟩ := hG.envCorr f' g hg
    have hlenXs : Xs.length = g.arity := by rw [valDenList_length hxs, hlen]
    obtain ⟨⟨d, hlenD, hShape, hfitθ, hdenB⟩, hfitC⟩ :=
      checkGuess_transfer_call M hcheck hcorr (hG.domDen f' g hg) hlenXs hfit hyM
    have hbtPin : κ boolTrueC = boolTrueName := hcorr.boolTruePin boolTrueC hbt
    have hchkDen : ValDen (.con boolTrueC [] [] [])
        ((Xs ++ [Y]).foldl app (M.cval (κ g.checker) φ)) :=
      ih φ ρ0 (Xs ++ [Y]) (M.cval boolKey φ) (by rwa [hlpsC])
        (valDenList_snoc hxs hyV) hfitC (fun _ =>
          ⟨M.cval boolTrueName φ,
            hG.boolTrueVal boolTrueC φ hbt hcorr.boolBasis hbtPin,
            boolTrue_mem_bool M hcorr.boolBasis φ⟩)
    have hchkEq : (Xs ++ [Y]).foldl app (M.cval (κ g.checker) φ) = M.cval boolTrueName φ :=
      hG.boolTrueDen boolTrueC _ φ hbt hcorr.boolBasis hbtPin hchkDen
    have hYeq : Y = Xs.foldl app (M.cval (κ f') φ) :=
      guess_sound M hShape φ ρ0 hfitθ (by omega) hdenB hyM hchkEq
    rwa [← hYeq]

/-- **Exact denotational equality (`S2`, `y = f xs`)** at any `guess` step: composing directly
with `checkGuess_ground` and `runG_sound`, any witness `Y ∈ˢ TR` validated by `RunG` on
`g.checker (xs ++ [y])` satisfies exact model equality `Y = Xs.foldl app (M.cval (κ f) φ)`. -/
theorem runG_guess_eq {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ValDen : Value → V → Prop}
    (hG : GuessTableGround M p κ lpsOf ValDen)
    {ls : Levels} {f : CId} {g : GuessEntry} {xs : List Value} {y : Value} {boolTrueC : CId}
    (hg : p.table.guessOf f = some g)
    (hlen : xs.length = g.arity)
    (hbt : p.known.boolTrue = some boolTrueC)
    (hchk : IxCC.Src.RunG p ls g.checker (xs ++ [y]) (.con boolTrueC [] [] []))
    {φ : LevelParam → Nat} {ρ0 : BVarIdx → V} {Xs : List V} {TR Y : V}
    (hlv : LvAt φ (lpsOf f) ls)
    (hxs : ValDenList ValDen xs Xs)
    (hfit : CallFits M κ f φ ρ0 Xs TR)
    (hyV : ValDen y Y) (hyM : Y ∈ˢ TR) :
    Y = Xs.foldl app (M.cval (κ f) φ) := by
  have hcheck : checkGuess p f g.checker g.thm g.comp? = .ok g :=
    validateGuess_iff.mp (hG.valid f g hg)
  obtain ⟨hcorr, hlpsC⟩ := hG.envCorr f g hg
  have hlenXs : Xs.length = g.arity := by rw [valDenList_length hxs, hlen]
  obtain ⟨⟨d, hlenD, hShape, hfitθ, hdenB⟩, hfitC⟩ :=
    checkGuess_transfer_call M hcheck hcorr (hG.domDen f g hg) hlenXs hfit hyM
  have hbtPin : κ boolTrueC = boolTrueName := hcorr.boolTruePin boolTrueC hbt
  have hchkDen : ValDen (.con boolTrueC [] [] [])
      ((Xs ++ [Y]).foldl app (M.cval (κ g.checker) φ)) :=
    runG_sound hG hchk φ ρ0 (Xs ++ [Y]) (M.cval boolKey φ) (by rwa [hlpsC])
      (valDenList_snoc hxs hyV) hfitC (fun _ =>
        ⟨M.cval boolTrueName φ,
          hG.boolTrueVal boolTrueC φ hbt hcorr.boolBasis hbtPin,
          boolTrue_mem_bool M hcorr.boolBasis φ⟩)
  have hchkEq : (Xs ++ [Y]).foldl app (M.cval (κ g.checker) φ) = M.cval boolTrueName φ :=
    hG.boolTrueDen boolTrueC _ φ hbt hcorr.boolBasis hbtPin hchkDen
  exact guess_sound M hShape φ ρ0 hfitθ (by omega) hdenB hyM hchkEq

/-! ### Concrete `IxCCGrounding.AllP` + `Table.ofCert` / `Table.validate` Composition -/

/-- Build `GuessTableGround` for `RelV M p κ lpsOf S Ok` from `AllP` and any table-validity proof
(`Table.ofCert_hardened` or `Table.validate_guess_ok`). -/
theorem guessTableGround_of_allP {M : Model V env} {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}
    (hAll : ∀ k, AllP M p κ lpsOf S Ok k)
    (hValid : ∀ f g, p.table.guessOf f = some g → validateGuess p f g = .ok ())
    (hEnvCorr : ∀ f g, p.table.guessOf f = some g →
      GuessEnvCorr p env κ (lpsOf f) f g.checker g.thm g.comp? ∧
      lpsOf g.checker = lpsOf f)
    (hDom : ∀ f g, p.table.guessOf f = some g → DomDenEq M p κ (lpsOf f))
    (hBtS : ∀ boolTrueC, p.known.boolTrue = some boolTrueC → S boolTrueC ∧ lpsOf boolTrueC = [])
    (hSrcOk : ∀ (f : CId) (ls : Levels) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (Xs : List V) (TR : V),
      LvAt φ (lpsOf f) ls → CallFits M κ f φ ρ0 Xs TR →
      S f ∧ Ok f ls ∧ AppChain (M.cval (κ f) φ) Xs) :
    GuessTableGround M p κ lpsOf (RelV M p κ lpsOf S Ok) where
  valid := hValid
  envCorr := hEnvCorr
  domDen := hDom
  boolTrueDen := fun _ _ φ _ hBool hbtPin hRel => relV_boolTrue_eq M hBool hbtPin hRel φ
  boolTrueVal := fun boolTrueC φ hbt hBool hbtPin =>
    let ⟨hS, hlps⟩ := hBtS boolTrueC hbt
    relV_boolTrue_intro M hBool hS hlps hbtPin φ
  srcSound := fun k ls f xs y φ ρ0 Xs TR hrun hlv hxs hfit => by
    obtain ⟨hSf, hOk, hchain⟩ := hSrcOk f ls φ ρ0 Xs TR hlv hfit
    unfold IxCC.Src.runAt at hrun
    cases hev : IxCC.Src.evalConst p k ls f with
    | ok fv =>
      rw [hev] at hrun
      have hfv := (hAll k).evalConst ls f fv φ hev hSf hOk hlv
      exact (hAll k).applyAll fv (xs.map .val) y (M.cval (κ f) φ) Xs hrun hfv
        (relSlots_of_relVs (relVs_of_valDenList hxs)) hchain
    | timeout => rw [hev] at hrun; cases hrun
    | resource _ => rw [hev] at hrun; cases hrun
    | trap => rw [hev] at hrun; cases hrun
    | stuck => rw [hev] at hrun; cases hrun

/-- **End-to-end `S2` Soundness over `Table.ofCert`**: any table rebuilt by `Table.ofCert`
automatically discharges `validateGuess` via `Table.ofCert_hardened`, so every `RunG`
derivation over `{ p0 with table := t }` agrees with standard `RelV` denotation in `M`. -/
theorem runG_sound_of_cert {M : Model V env} {cfg : IxCC.Src.Table.Config} {p0 : Program}
    {cert : IxCC.Src.Table.TableCert} {t : IxCC.Src.Table}
    (hCert : IxCC.Src.Table.ofCert cfg p0 cert = .ok t)
    {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}
    (hAll : ∀ k, AllP M { p0 with table := t } κ lpsOf S Ok k)
    (hEnvCorr : ∀ f g, t.guessOf f = some g →
      GuessEnvCorr { p0 with table := t } env κ (lpsOf f) f g.checker g.thm g.comp? ∧
      lpsOf g.checker = lpsOf f)
    (hDom : ∀ f g, t.guessOf f = some g → DomDenEq M { p0 with table := t } κ (lpsOf f))
    (hBtS : ∀ boolTrueC, p0.known.boolTrue = some boolTrueC → S boolTrueC ∧ lpsOf boolTrueC = [])
    (hSrcOk : ∀ (f : CId) (ls : Levels) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (Xs : List V) (TR : V),
      LvAt φ (lpsOf f) ls → CallFits M κ f φ ρ0 Xs TR →
      S f ∧ Ok f ls ∧ AppChain (M.cval (κ f) φ) Xs)
    {ls : Levels} {f : CId} {xs : List Value} {y : Value}
    (hRun : IxCC.Src.RunG { p0 with table := t } ls f xs y)
    {φ : LevelParam → Nat} {ρ0 : BVarIdx → V} {Xs : List V} {TR : V}
    (hlv : LvAt φ (lpsOf f) ls)
    (hxs : RelVs M { p0 with table := t } κ lpsOf S Ok xs Xs)
    (hfit : CallFits M κ f φ ρ0 Xs TR)
    (hwit : t.guessOf f ≠ none → ∃ Y, RelV M { p0 with table := t } κ lpsOf S Ok y Y ∧ Y ∈ˢ TR) :
    RelV M { p0 with table := t } κ lpsOf S Ok y (Xs.foldl app (M.cval (κ f) φ)) := by
  have hVal0 := (IxCC.Src.Table.ofCert_hardened hCert).2.2
  have hVal : ∀ c g, ({ p0 with table := t } : Program).table.guessOf c = some g →
      validateGuess { p0 with table := t } c g = .ok () := by
    intro c g hg
    rw [validateGuess_with_table]
    exact hVal0 c g hg
  have hG := guessTableGround_of_allP hAll hVal hEnvCorr hDom hBtS hSrcOk
  exact runG_sound hG hRun φ ρ0 Xs TR hlv (valDenList_of_relVs hxs) hfit hwit

/-- **End-to-end `S2` Soundness over `Table.validate`**: any program whose table passes
`Table.validate` automatically discharges `validateGuess` via `Table.validate_guess_ok`. -/
theorem runG_sound_of_validate {M : Model V env} {cfg : IxCC.Src.Table.Config} {p : Program}
    (hVal : IxCC.Src.Table.validate cfg p = .ok ())
    {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop} {Ok : CId → Levels → Prop}
    (hAll : ∀ k, AllP M p κ lpsOf S Ok k)
    (hEnvCorr : ∀ f g, p.table.guessOf f = some g →
      GuessEnvCorr p env κ (lpsOf f) f g.checker g.thm g.comp? ∧
      lpsOf g.checker = lpsOf f)
    (hDom : ∀ f g, p.table.guessOf f = some g → DomDenEq M p κ (lpsOf f))
    (hBtS : ∀ boolTrueC, p.known.boolTrue = some boolTrueC → S boolTrueC ∧ lpsOf boolTrueC = [])
    (hSrcOk : ∀ (f : CId) (ls : Levels) (φ : LevelParam → Nat) (ρ0 : BVarIdx → V)
        (Xs : List V) (TR : V),
      LvAt φ (lpsOf f) ls → CallFits M κ f φ ρ0 Xs TR →
      S f ∧ Ok f ls ∧ AppChain (M.cval (κ f) φ) Xs)
    {ls : Levels} {f : CId} {xs : List Value} {y : Value}
    (hRun : IxCC.Src.RunG p ls f xs y)
    {φ : LevelParam → Nat} {ρ0 : BVarIdx → V} {Xs : List V} {TR : V}
    (hlv : LvAt φ (lpsOf f) ls)
    (hxs : RelVs M p κ lpsOf S Ok xs Xs)
    (hfit : CallFits M κ f φ ρ0 Xs TR)
    (hwit : p.table.guessOf f ≠ none → ∃ Y, RelV M p κ lpsOf S Ok y Y ∧ Y ∈ˢ TR) :
    RelV M p κ lpsOf S Ok y (Xs.foldl app (M.cval (κ f) φ)) := by
  have hG := guessTableGround_of_allP hAll (IxCC.Src.Table.validate_guess_ok hVal)
    hEnvCorr hDom hBtS hSrcOk
  exact runG_sound hG hRun φ ρ0 Xs TR hlv (valDenList_of_relVs hxs) hfit hwit

/-- **Term-level `EvalG.guess` Soundness (`S2`)**: whenever a saturated call
`Term.mkApps (.const f us) args` derives `y` via `EvalG.guess` over a validated table
(`GuessTableGround`), any well-typed witness `Y ∈ˢ TR` satisfying `ValDen y Y` equals
`Xs.foldl app (M.cval (κ f) φ)` in `M`. -/
theorem evalG_guess_eq {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ValDen : Value → V → Prop}
    (hG : GuessTableGround M p κ lpsOf ValDen)
    {ls : Levels} {ρ : IxCC.Src.Env} {f : CId} {us : List IxCC.Ixon.Univ}
    {args : List Term.Arg} {xs : List Value} {y : Value} {g : GuessEntry} {boolTrueC : CId}
    (hg : p.table.guessOf f = some g)
    (hlen : args.length = g.arity)
    (hargs : IxCC.Src.EvalGArgs p ls ρ args xs)
    (hbt : p.known.boolTrue = some boolTrueC)
    (hchk : IxCC.Src.RunG p (us.map (IxCC.Src.evalUniv ls)) g.checker (xs ++ [y])
      (.con boolTrueC [] [] []))
    {φ : LevelParam → Nat} {ρ0 : BVarIdx → V} {Xs : List V} {TR Y : V}
    (hlv : LvAt φ (lpsOf f) (us.map (IxCC.Src.evalUniv ls)))
    (hxs : ValDenList ValDen xs Xs)
    (hfit : CallFits M κ f φ ρ0 Xs TR)
    (hyV : ValDen y Y) (hyM : Y ∈ˢ TR) :
    Y = Xs.foldl app (M.cval (κ f) φ) :=
  runG_guess_eq hG hg (by rw [IxCC.Src.evalGArgs_length hargs, hlen]) hbt hchk hlv hxs hfit hyV hyM

end SrcGSoundness

end IxCC.Grounding.Guess
