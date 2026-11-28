import IxCCGrounding.LimbWord
import IxCCGrounding.StrLit
import IxCC.BigNat.Basic

/-!
# `ArraySpec` & `BigNat` Layer-3 Adequacy Bridge (`IxCCGrounding.BigNatBridge`)

This module proves the Layer-3 adequacy bridge over `Ix.Kernel.Model` linking:
1. **`FalseBasis`, `bool_true_ne_false`, and `litSet_inj`**:
   directly from `M.false_empty`, `M.eq_equality`, and `M.lit_ops`, proving that
   `Bool.true ≠ Bool.false` and `litSet M φ : Nat → V` is injective in every `Ix.Kernel.Model V env`.
2. **`ListBasis`, `ArrayBasis`, `array_eta`, and `array_ext`**:
   proving `Array` structure η (`x = Array.mk A (Array.toList A x)`) and extensionality directly
   from `M.proj_law` (`entry.off ≤ 1`) and `M.defn_value` — zero new axioms, zero constructor
   canonicity.
3. **`ArraySpec` Model Adequacy over `Ix.Kernel.Model`**:
   proving model-level acceleration for `List` (`length`, `concat`, `dropLast`, `set`, `getD`) by
   induction on `List V`, and upgrading the `Array.toList` equations of `IxCC.Src.Table.Array`
   (`emptyWithCapacity`, `size`, `push`, `pop`, `setIfInBounds`, `getD`, `set`) to full `Array`
   equality in `M` via `array_eta` and `toList_arraySet`.
4. **`BigNat` Limb-Array Denotation, `toNat` Adequacy, and Layer-1 × Layer-3 Composition**:
   proving `towV_mem_of_ofNat` and `toNat_towV_of_eqn`, defining `limbArraySet M tk ak φ xs`,
   proving `app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs) = litSet M φ (IxCC.BigNat.toNat xs)`
   from stored `toNatPrefix` / `getLimb` / `toNat` equations, and composing any stored Layer-1
   correctness theorem (`toNat (op a b) = natOp (toNat a) (toNat b)`) with `litSet_inj` and
   `bool_true_ne_false` to conclude exact meta-level `Nat` / `Bool` equality directly over
   `Ix.Kernel.Model`.

## Exact Minimal Remaining Layer-3 Specification Boundary (`docs/bignum-design.md:162-167`)

Everything that belongs purely to `Ix.Kernel.Model` is proved without axioms across `LimbWord`,
`PcProp`, `StrLit`, and `BigNatBridge`:
- All 5 `IxCC.BigNat.LimbOps` word equations (`clz64`, `mulWide64`, `divWide64`, `addCarry64`,
  `subBorrow64`) and `Prod` projections (`LimbWord.lean`);
- `PUnit.casesOn` at both ordinary and `Prop` instances (`PcProp.lean`);
- `Lit.str` denotation, membership, UTF-8 readback, and root soundness (`StrLit.lean`);
- `Array` structure η/extensionality (`M.proj_law`), `ArraySpec` model adequacy, `litSet_inj`,
  `toNat` adequacy, and Layer-1 × Layer-3 composition (`BigNatBridge.lean`).

What remains for Wave 3b / Wave 4 (outside `IxCCGrounding/**`, after `arrays-wire` merges
`Resolve.array` into `IxCC/Src/` and `IxCC.BigNat.Entry` is frozen in `Ixon`) is strictly:
1. Wiring `Resolve.array` head firing in `SrcEval` (`ArrayFires` in `Hyps.lean` / `Fundamental.lean`,
   mirroring `WordFires` / `WordFire.lean`) to call `BigNatBridge`'s already-proved `ArraySpec`
   acceleration theorems (`arrayEmpty_accel`, `arraySize_accel`, `arrayPush_accel`,
   `arrayPop_accel`, `arraySetIfInBounds_accel`, `arrayGetD_accel`, `arraySet_of_toList_eqn`).
2. Wiring `IxCC.BigNat.LimbOps` 3-arg / `Prod`-returning limb entries into `WordFire` using
   `LimbWord`'s already-proved adequacy theorems (`clz64_accel`, `mulWide64_accel`,
   `divWide64_accel`, `addCarry64_accel`, `subBorrow64_accel`).
3. Freezing `IxCC.BigNat.Entry` in `Ixon` together with its Layer-1 theorem proofs and
   `ArraySpec` / `LimbOps` equation seeds, and running `groundCheckStrWPP` + `BigNatBridge`'s
   decidable basis/equation checks on the frozen closure.

Until (1)–(3) are wired on the frozen `BigNat` closure, the minimal remaining Layer-3 entry in
`trusted-externs.json` is ONLY the `SrcEval`-to-`Model` relation (`RelV` on `IxCC.BigNat` entry
calls when `Resolve.array` fires), with zero arithmetic, array-extensionality, limb-op, or `toNat`
axioms trusted.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels Width PrimOp)

universe w

/-! ## Helper syntax -/

/-- `@Eq.{u} T a b` in kernel syntax. -/
def eqE (u : Level) (T a b : KExpr) : KExpr :=
  Expr.mkAppN (.const eqName [u]) [T, a, b]

/-! ## Section 1: `FalseBasis`, `bool_true_ne_false`, and `litSet_inj` -/

/-- `False` is stored at `falseName` with no level parameters. -/
def FalseBasis (env : KEnv) : Prop :=
  ∃ ci : ConstantInfo .anon, env.find? falseName = some ci ∧ ci.toConstantVal.levelParams = []

def falseBasisB (env : KEnv) : Bool :=
  match env.find? falseName with
  | some ci => ci.toConstantVal.levelParams.isEmpty
  | none => false

theorem falseBasis_of_check {env : KEnv} (h : falseBasisB env = true) : FalseBasis env := by
  unfold falseBasisB at h
  split at h
  · rename_i ci hf; exact ⟨ci, hf, List.isEmpty_iff.mp h⟩
  · cases h

/-- `Bool : Type 0` and a stored theorem `kNe : @Eq.{1} Bool Bool.true Bool.false → False`. -/
structure BoolTrueNeFalseStored (env : KEnv) (kNe : KKey) : Prop where
  boolSort : ∃ (cv : ConstantVal .anon) (caps : IndCaps .anon),
    env.find? boolKey = some (.indInfo cv caps) ∧ cv.levelParams = [] ∧
    cv.type = .sort (.succ .zero)
  thm : ∃ (ci : ConstantInfo .anon) (mb : BinderMeta),
    env.find? kNe = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (eqE (.succ .zero) (.const boolKey []) (.const boolTrueName []) (.const boolFalseName []))
        (.const falseName []) mb

def boolTrueNeFalseB (env : KEnv) (kNe : KKey) : Bool :=
  (match env.find? boolKey with
    | some (.indInfo cv _) => cv.levelParams.isEmpty && cv.type == .sort (.succ .zero)
    | _ => false) &&
  (match env.find? kNe with
    | some ci =>
      ci.toConstantVal.levelParams.isEmpty &&
      match ci.toConstantVal.type with
      | .forallE d (.const f []) _ =>
        decide (d = eqE (.succ .zero) (.const boolKey []) (.const boolTrueName [])
          (.const boolFalseName [])) && f == falseName
      | _ => false
    | none => false)

theorem boolTrueNeFalse_of_check {env : KEnv} {kNe : KKey} (h : boolTrueNeFalseB env kNe = true) :
    BoolTrueNeFalseStored env kNe := by
  unfold boolTrueNeFalseB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hB, hK⟩ := h
  refine ⟨?_, ?_⟩
  · cases hf : env.find? boolKey with
    | none => simp [hf] at hB
    | some ci =>
      simp only [hf] at hB
      cases ci with
      | indInfo cv caps =>
        simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hB
        exact ⟨cv, caps, rfl, hB.1, hB.2⟩
      | _ => simp at hB
  · cases hf : env.find? kNe with
    | none => simp [hf] at hK
    | some ci =>
      simp only [hf, Bool.and_eq_true, List.isEmpty_iff] at hK
      obtain ⟨hlp, hty⟩ := hK
      cases ht : ci.toConstantVal.type with
      | forallE d b mb =>
        rw [ht] at hty
        cases b with
        | const f us =>
          cases us with
          | nil =>
            simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hty
            exact ⟨ci, mb, rfl, hlp, by rw [ht, hty.1, hty.2]⟩
          | cons _ _ => simp at hty
        | _ => simp at hty
      | _ => rw [ht] at hty; simp at hty

/-- `Nat.beq` is stored at `natBeqName` with no level parameters. -/
def NatBeqStored (env : KEnv) : Prop :=
  ∃ ci : ConstantInfo .anon, env.find? natBeqName = some ci ∧ ci.toConstantVal.levelParams = []

def natBeqStoredB (env : KEnv) : Bool :=
  match env.find? natBeqName with
  | some ci => ci.toConstantVal.levelParams.isEmpty
  | none => false

theorem natBeqStored_of_check {env : KEnv} (h : natBeqStoredB env = true) : NatBeqStored env := by
  unfold natBeqStoredB at h
  split at h
  · rename_i ci hf; exact ⟨ci, hf, List.isEmpty_iff.mp h⟩
  · cases h

section InjSem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- **`Bool.true ≠ Bool.false` in every `Ix.Kernel.Model`** containing `EqBasis`, `BoolBasis`,
and a stored `Bool.true = Bool.false → False` theorem (via `M.false_empty`). -/
theorem bool_true_ne_false (M : Model V env) (hE : EqBasis env) (hB : BoolBasis env)
    {kNe : KKey} (hNe : BoolTrueNeFalseStored env kNe)
    (φ : LevelParam → Nat) : M.cval boolTrueName φ ≠ M.cval boolFalseName φ := by
  intro heq
  obtain ⟨ciEq, hfEq, hlEq, _⟩ := hE
  obtain ⟨cvB, capsB, hfB, hlB, htB⟩ := hNe.boolSort
  obtain ⟨cvT, hfT, hlT, htT⟩ := hB.bTrue
  obtain ⟨cvFa, hfFa, hlFa, htFa⟩ := hB.bFalse
  obtain ⟨ciNe, mb, hfNe, _, htNe⟩ := hNe.thm
  have hB1 : M.cval boolKey φ ∈ˢ (univ 1 : V) := by
    obtain ⟨TB, hTB, hmB⟩ := mem_key M hfB φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htB] at hTB
    simpa [Level.eval] using den_sort.mp hTB ▸ hmB
  have hTm : M.cval boolTrueName φ ∈ˢ M.cval boolKey φ := by
    obtain ⟨TT, hTT, hmT⟩ := mem_key M hfT φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htT, boolK] at hTT
    rwa [(den_const0 hfB hlB).mp hTT] at hmT
  have hFm : M.cval boolFalseName φ ∈ˢ M.cval boolKey φ := by
    obtain ⟨TF, hTF, hmF⟩ := mem_key M hfFa φ (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htFa, boolK] at hTF
    rwa [(den_const0 hfB hlB).mp hTF] at hmF
  have hEqD : Denotes M.cval env φ (fun _ => empty) (.const eqName [.succ .zero])
      (M.cval eqName (Level.substFn φ [0] [.succ .zero])) := by
    have h1 := Denotes.const (cval := M.cval) (env := env) (φ := φ) (ρ := fun _ => empty)
      (us := [.succ .zero]) hfEq (by rw [hlEq]; rfl)
    rwa [hlEq] at h1
  have hDomD : Denotes M.cval env φ (fun _ => empty)
      (eqE (.succ .zero) (.const boolKey []) (.const boolTrueName []) (.const boolFalseName []))
      (eqv (M.cval boolTrueName φ) (M.cval boolFalseName φ)) := by
    have h1 := M.eq_equality (.succ .zero) φ (fun _ => empty) _ _ _ _ hEqD hB1 hTm hFm
    rw [← h1]
    exact .app (.app (.app hEqD ((den_const0 hfB hlB).mpr rfl))
      ((den_const0 hfT hlT).mpr rfl)) ((den_const0 hfFa hlFa).mpr rfl)
  have hpt : (pt : V) ∈ˢ eqv (M.cval boolTrueName φ) (M.cval boolFalseName φ) := by
    rw [heq]; exact pt_mem_eqv_self _
  obtain ⟨TN, hTN, hmN⟩ := mem_key M hfNe φ (fun _ => empty)
  rw [htNe] at hTN
  obtain ⟨BF, hBF, hmemF⟩ := app_mem_den_pi hTN hDomD hmN hpt
  have hEmpty : BF = empty := M.false_empty φ _ BF hBF
  rw [hEmpty] at hmemF
  exact not_mem_empty _ hmemF

/-- **`boolSet` is injective** once `Bool.true ≠ Bool.false`. -/
theorem boolSet_inj {M : Model V env} {φ : LevelParam → Nat}
    (hNe : M.cval boolTrueName φ ≠ M.cval boolFalseName φ) {b₁ b₂ : Bool}
    (h : boolSet M φ b₁ = boolSet M φ b₂) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · exact absurd h.symm hNe
  · exact absurd h hNe
  · rfl

/-- **`litSet` is injective** in every `Ix.Kernel.Model` with `NatAccel`, `NatBasis`, `BoolBasis`,
`NatBeqStored`, and `Bool.true ≠ Bool.false`. -/
theorem litSet_inj (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hB : BoolBasis env)
    (hBeq : NatBeqStored env) {φ : LevelParam → Nat}
    (hNe : M.cval boolTrueName φ ≠ M.cval boolFalseName φ) {m n : Nat}
    (h : litSet M φ m = litSet M φ n) : m = n := by
  obtain ⟨ciBeq, hfBeq, hlBeq⟩ := hBeq
  obtain ⟨cvT, hfT, hlT, _⟩ := hB.bTrue
  obtain ⟨cvFa, hfFa, hlFa, _⟩ := hB.bFalse
  have hF := natFacts M hN φ
  have evalBeq : ∀ a b : Nat,
      app (app (M.cval natBeqName φ) (litSet M φ a)) (litSet M φ b) = boolSet M φ (a == b) := by
    intro a b
    have hD : Denotes M.cval env φ (fun _ => empty) (primApp .beq a b)
        (app (app (M.cval natBeqName φ) (litSet M φ a)) (litSet M φ b)) := by
      simp only [primApp, PrimOp.arity, primKey]
      exact .app (.app ((den_const0 hfBeq hlBeq).mpr rfl) ((lit_den M hF _ a _).mpr rfl))
        ((lit_den M hF _ b _).mpr rfl)
    have hR := hacc .beq a b φ (fun _ => empty) _ (fun h1 => by simp [PrimOp.arity] at h1) hD
    simp only [IxCC.Src.PrimOp.eval2] at hR
    cases hbe : (a == b) with
    | true =>
      rw [hbe] at hR
      exact (den_const0 hfT hlT).mp hR
    | false =>
      rw [hbe] at hR
      exact (den_const0 hfFa hlFa).mp hR
  have h1 : boolSet M φ (m == n) = boolSet M φ (n == n) := by
    rw [← evalBeq m n, ← evalBeq n n, h]
  have h2 : (m == n) = (n == n) := boolSet_inj hNe h1
  simpa using h2

/-- Binary `Nat`-valued primitive acceleration via `NatAccel` (covers `add`, `sub`, `mul`, `div`,
`mod`, `pow`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`). -/
theorem natPrimBin_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {op : PrimOp} (har : op.arity = 2) {ci : ConstantInfo .anon}
    (hf : env.find? (primKey op) = some ci) (hlp : ci.toConstantVal.levelParams = [])
    (φ : LevelParam → Nat) {a b r : Nat} (hev : op.eval2 a b = .nat r) :
    app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b) = litSet M φ r := by
  have hF := natFacts M hN φ
  have hD : Denotes M.cval env φ (fun _ => empty) (primApp op a b)
      (app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b)) := by
    have hne : op.arity ≠ 1 := by omega
    simp only [primApp, hne, ↓reduceIte]
    exact .app (.app ((den_const0 hf hlp).mpr rfl) ((lit_den M hF _ a _).mpr rfl))
      ((lit_den M hF _ b _).mpr rfl)
  have hR := hacc op a b φ (fun _ => empty) _ (fun h1 => by omega) hD
  rw [hev] at hR
  exact (lit_den M hF _ r _).mp hR

/-- `Nat.pow` acceleration via `NatAccel`. -/
theorem natPow_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {ci : ConstantInfo .anon} (hf : env.find? natPowName = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (φ : LevelParam → Nat) (a b : Nat) :
    app (app (M.cval natPowName φ) (litSet M φ a)) (litSet M φ b) = litSet M φ (a ^ b) :=
  natPrimBin_accel M hacc hN (op := .pow) rfl hf hlp φ rfl

/-- Unary `Nat.pred` acceleration via `NatAccel`. -/
theorem natPred_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {ci : ConstantInfo .anon} (hf : env.find? natPredName = some ci)
    (hlp : ci.toConstantVal.levelParams = []) (φ : LevelParam → Nat) (a : Nat) :
    app (M.cval natPredName φ) (litSet M φ a) = litSet M φ (a - 1) := by
  have hF := natFacts M hN φ
  have hD : Denotes M.cval env φ (fun _ => empty) (primApp .pred a 0)
      (app (M.cval natPredName φ) (litSet M φ a)) := by
    simp only [primApp, PrimOp.arity, ↓reduceIte, primKey]
    exact .app ((den_const0 hf hlp).mpr rfl) ((lit_den M hF _ a _).mpr rfl)
  have hR := hacc .pred a 0 φ (fun _ => empty) _ (fun _ => rfl) hD
  exact (lit_den M hF _ (a - 1) _).mp hR

/-- Binary `Bool`-valued `Nat` comparison acceleration (`beq`, `ble`) via `NatAccel`. -/
theorem natPrimCmp_accel (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) {op : PrimOp} (har : op.arity = 2) {ci : ConstantInfo .anon}
    (hf : env.find? (primKey op) = some ci) (hlp : ci.toConstantVal.levelParams = [])
    (φ : LevelParam → Nat) {a b : Nat} {res : Bool} (hev : op.eval2 a b = .bool res) :
    app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b) = boolSet M φ res := by
  obtain ⟨cvT, hfT, hlT, _⟩ := hB.bTrue
  obtain ⟨cvFa, hfFa, hlFa, _⟩ := hB.bFalse
  have hF := natFacts M hN φ
  have hD : Denotes M.cval env φ (fun _ => empty) (primApp op a b)
      (app (app (M.cval (primKey op) φ) (litSet M φ a)) (litSet M φ b)) := by
    have hne : op.arity ≠ 1 := by omega
    simp only [primApp, hne, ↓reduceIte]
    exact .app (.app ((den_const0 hf hlp).mpr rfl) ((lit_den M hF _ a _).mpr rfl))
      ((lit_den M hF _ b _).mpr rfl)
  have hR := hacc op a b φ (fun _ => empty) _ (fun h1 => by omega) hD
  rw [hev] at hR
  cases res with
  | true => exact (den_const0 hfT hlT).mp hR
  | false => exact (den_const0 hfFa hlFa).mp hR

end InjSem

/-! ## Section 2: `ListBasis`, `ArrayBasis`, and `array_eta` / `array_ext` from `M.proj_law` -/

/-- The kernel environment stores `List`, `List.nil`, and `List.cons` with the standard 1-parameter
polymorphic shapes. -/
structure ListBasis (env : KEnv) : Prop where
  list : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb : BinderMeta),
    env.find? listName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type = .forallE (.sort (.succ (.param p))) (.sort (.succ (.param p))) mb
  listNil : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb : BinderMeta),
    env.find? listNilName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type =
      .forallE (.sort (.succ (.param p))) (.app (.const listName [.param p]) (.bvar 0)) mb
  listCons : ∃ (ci : ConstantInfo .anon) (p : LevelParam) (mb1 mb2 mb3 : BinderMeta),
    env.find? listConsName = some ci ∧ ci.toConstantVal.levelParams = [p] ∧
    ci.toConstantVal.type =
      .forallE (.sort (.succ (.param p)))
        (.forallE (.bvar 0)
          (.forallE (.app (.const listName [.param p]) (.bvar 1))
            (.app (.const listName [.param p]) (.bvar 2)) mb3) mb2) mb1

def listBasisB (env : KEnv) : Bool :=
  listTyOk (env.find? listName) &&
  listNilTyOk (env.find? listNilName) &&
  listConsTyOk (env.find? listConsName)

theorem listBasis_of_strBasis {env : KEnv} (h : StrBasis env) : ListBasis env :=
  ⟨h.list, h.listNil, h.listCons⟩

/-- Keys and universe parameter for `Array`, `Array.mk`, and `Array.toList`. -/
structure ArrayKeys where
  array : KKey
  arrayMk : KKey
  toList : KKey
  lvlParam : LevelParam := 0

/-- The kernel environment stores `Array.{p}`, its 1-field native structure constructor
`Array.mk.{p}`, its projection table entry at field 0 (`entry.off ≤ 1`), and
`Array.toList.{p} := λ α a, a.0`. -/
structure ArrayBasis (env : KEnv) (ak : ArrayKeys) : Prop where
  array : ∃ (cvA : ConstantVal .anon) (caps : IndCaps .anon) (mb : BinderMeta),
    env.find? ak.array = some (.indInfo cvA caps) ∧
    cvA.levelParams = [ak.lvlParam] ∧
    cvA.type = .forallE (.sort (.succ (.param ak.lvlParam)))
      (.sort (.succ (.param ak.lvlParam))) mb
  arrayMk : ∃ (cvM : ConstantVal .anon) (mb1 mb2 : BinderMeta),
    env.find? ak.arrayMk = some (.ctorInfo cvM 1 1) ∧
    cvM.levelParams = [ak.lvlParam] ∧
    cvM.type =
      .forallE (.sort (.succ (.param ak.lvlParam)))
        (.forallE (.app (.const listName [.param ak.lvlParam]) (.bvar 0))
          (.app (.const ak.array [.param ak.lvlParam]) (.bvar 1)) mb2) mb1
  proj : ∃ entry : ProjEntry .anon,
    env.findProj? ak.array 0 = some entry ∧
    entry.ctor = ak.arrayMk ∧ entry.numParams = 1 ∧ entry.numFields = 1 ∧
    entry.off ≤ 1 ∧ entry.levelParams = [ak.lvlParam] ∧
    entry.structSort = .succ (.param ak.lvlParam)
  toList : ∃ (cvL : ConstantVal .anon) (hint : ReducibilityHint) (mb1 mb2 : BinderMeta),
    env.find? ak.toList = some (.defnInfo cvL
      (.lam (.sort (.succ (.param ak.lvlParam)))
        (.lam (.app (.const ak.array [.param ak.lvlParam]) (.bvar 0))
          (.proj ak.array 0 (.bvar 0)) mb2) mb1)
      hint) ∧
    cvL.levelParams = [ak.lvlParam] ∧
    cvL.type =
      .forallE (.sort (.succ (.param ak.lvlParam)))
        (.forallE (.app (.const ak.array [.param ak.lvlParam]) (.bvar 0))
          (.app (.const listName [.param ak.lvlParam]) (.bvar 1)) mb2) mb1

/-- Decidable check for `ArrayBasis env ak`. -/
def arrayBasisB (env : KEnv) (ak : ArrayKeys) : Bool :=
  let p := ak.lvlParam
  let arrOk := match env.find? ak.array with
    | some (.indInfo cvA _) =>
      cvA.levelParams == [p] &&
      match cvA.type with
      | .forallE (.sort u1) (.sort u2) _ =>
        u1 == .succ (.param p) && u2 == .succ (.param p)
      | _ => false
    | _ => false
  let mkOk := match env.find? ak.arrayMk with
    | some (.ctorInfo cvM 1 1) =>
      cvM.levelParams == [p] &&
      match cvM.type with
      | .forallE (.sort u1) (.forallE (.app (.const l1 us1) (.bvar 0))
          (.app (.const a1 us2) (.bvar 1)) _) _ =>
        u1 == .succ (.param p) && l1 == listName && us1 == [.param p] &&
          a1 == ak.array && us2 == [.param p]
      | _ => false
    | _ => false
  let projOk := match env.findProj? ak.array 0 with
    | some entry =>
      decide (entry.ctor = ak.arrayMk) && entry.numParams == 1 && entry.numFields == 1 &&
      decide (entry.off ≤ 1) && entry.levelParams == [p] &&
      decide (entry.structSort = .succ (.param p))
    | none => false
  let toListOk := match env.find? ak.toList with
    | some (.defnInfo cvL val _) =>
      cvL.levelParams == [p] &&
      match val, cvL.type with
      | .lam (.sort u1) (.lam (.app (.const a1 us1) (.bvar 0)) (.proj a2 0 (.bvar 0)) mb2) mb1,
        .forallE (.sort u1') (.forallE (.app (.const a1' us1') (.bvar 0))
          (.app (.const l1' us2') (.bvar 1)) mb2') mb1' =>
        u1 == .succ (.param p) && a1 == ak.array && us1 == [.param p] && a2 == ak.array &&
        u1' == .succ (.param p) && a1' == ak.array && us1' == [.param p] &&
        l1' == listName && us2' == [.param p] && mb1 == mb1' && mb2 == mb2'
      | _, _ => false
    | _ => false
  arrOk && mkOk && projOk && toListOk

/-- **`arrayBasisB` is sound.** -/
theorem arrayBasis_of_check {env : KEnv} {ak : ArrayKeys} (h : arrayBasisB env ak = true) :
    ArrayBasis env ak := by
  unfold arrayBasisB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hArr, hMk⟩, hProj⟩, hTL⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hf : env.find? ak.array with
    | none => simp [hf] at hArr
    | some ci =>
      simp only [hf] at hArr
      cases ci with
      | indInfo cvA caps =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hArr
        obtain ⟨hlp, hty⟩ := hArr
        cases ht : cvA.type with
        | forallE d b mb =>
          rw [ht] at hty
          cases d with
          | sort u1 =>
            cases b with
            | sort u2 =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hty
              exact ⟨cvA, caps, mb, rfl, hlp, by rw [ht, hty.1, hty.2]⟩
            | _ => simp at hty
          | _ => simp at hty
        | _ => rw [ht] at hty; simp at hty
      | _ => simp at hArr
  · cases hf : env.find? ak.arrayMk with
    | none => simp [hf] at hMk
    | some ci =>
      simp only [hf] at hMk
      cases ci with
      | ctorInfo cvM np nf =>
        cases np with
        | zero => simp at hMk
        | succ np' =>
          cases np' with
          | succ _ => simp at hMk
          | zero =>
            cases nf with
            | zero => simp at hMk
            | succ nf' =>
              cases nf' with
              | succ _ => simp at hMk
              | zero =>
                simp only [Bool.and_eq_true, beq_iff_eq] at hMk
                obtain ⟨hlp, hty⟩ := hMk
                cases ht : cvM.type with
                | forallE d1 b1 mb1 =>
                  rw [ht] at hty
                  cases d1 with
                  | sort u1 =>
                    cases b1 with
                    | forallE d2 b2 mb2 =>
                      cases d2 with
                      | app f1 a1 =>
                        cases f1 with
                        | const l1 us1 =>
                          cases a1 with
                          | bvar i0 =>
                            cases i0 with
                            | zero =>
                              cases b2 with
                              | app f2 a2 =>
                                cases f2 with
                                | const a1' us2 =>
                                  cases a2 with
                                  | bvar i1 =>
                                    cases i1 with
                                    | zero => simp at hty
                                    | succ i1' =>
                                      cases i1' with
                                      | zero =>
                                        simp only [Bool.and_eq_true, beq_iff_eq] at hty
                                        obtain ⟨⟨⟨⟨hu1, hl1⟩, hus1⟩, ha1⟩, hus2⟩ := hty
                                        exact ⟨cvM, mb1, mb2, rfl, hlp, by
                                          rw [ht, hu1, hl1, hus1, ha1, hus2]⟩
                                      | succ _ => simp at hty
                                  | _ => simp at hty
                                | _ => simp at hty
                              | _ => simp at hty
                            | succ _ => simp at hty
                          | _ => simp at hty
                        | _ => simp at hty
                      | _ => simp at hty
                    | _ => simp at hty
                  | _ => simp at hty
                | _ => rw [ht] at hty; simp at hty
      | _ => simp at hMk
  · cases hf : env.findProj? ak.array 0 with
    | none => simp [hf] at hProj
    | some entry =>
      simp only [hf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hProj
      obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hProj
      exact ⟨entry, rfl, h1, h2, h3, h4, h5, h6⟩
  · cases hf : env.find? ak.toList with
    | none => simp [hf] at hTL
    | some ci =>
      simp only [hf] at hTL
      cases ci with
      | defnInfo cvL val hint =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hTL
        obtain ⟨hlp, hvt⟩ := hTL
        cases hv : val with
        | lam d1 b1 mb1 =>
          rw [hv] at hvt
          cases ht : cvL.type with
          | forallE d1' b1' mb1' =>
            rw [ht] at hvt
            cases d1 with
            | sort u1 =>
              cases b1 with
              | lam d2 b2 mb2 =>
                cases d2 with
                | app f1 a1 =>
                  cases f1 with
                  | const a1' us1 =>
                    cases a1 with
                    | bvar i0 =>
                      cases i0 with
                      | zero =>
                        cases b2 with
                        | proj a2 j e0 =>
                          cases j with
                          | zero =>
                            cases e0 with
                            | bvar i0' =>
                              cases i0' with
                              | zero =>
                                cases d1' with
                                | sort u1' =>
                                  cases b1' with
                                  | forallE d2' b2' mb2' =>
                                    cases d2' with
                                    | app f2 a2' =>
                                      cases f2 with
                                      | const a1'' us1' =>
                                        cases a2' with
                                        | bvar i0'' =>
                                          cases i0'' with
                                          | zero =>
                                            cases b2' with
                                            | app f3 a3 =>
                                              cases f3 with
                                              | const l1' us2' =>
                                                cases a3 with
                                                | bvar i1 =>
                                                  cases i1 with
                                                  | zero => simp at hvt
                                                  | succ i1' =>
                                                    cases i1' with
                                                    | zero =>
                                                      simp only [Bool.and_eq_true, beq_iff_eq] at hvt
                                                      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hu1, ha1⟩, hus1⟩, ha2⟩, hu1'⟩,
                                                        ha1'⟩, hus1'⟩, hl1'⟩, hus2'⟩, hmb1⟩,
                                                        hmb2⟩ := hvt
                                                      have htEq : cvL.type =
                                                          .forallE (.sort (.succ (.param ak.lvlParam)))
                                                            (.forallE (.app (.const ak.array
                                                              [.param ak.lvlParam]) (.bvar 0))
                                                              (.app (.const listName
                                                                [.param ak.lvlParam]) (.bvar 1))
                                                              mb2) mb1 := by
                                                        rw [ht, hu1', ha1', hus1', hl1', hus2',
                                                          ← hmb1, ← hmb2]
                                                      exact ⟨cvL, hint, mb1, mb2,
                                                        by rw [hu1, ha1, hus1, ha2], hlp, htEq⟩
                                                    | succ _ => simp at hvt
                                                | _ => simp at hvt
                                              | _ => simp at hvt
                                            | _ => simp at hvt
                                          | succ _ => simp at hvt
                                        | _ => simp at hvt
                                      | _ => simp at hvt
                                    | _ => simp at hvt
                                  | _ => simp at hvt
                                | _ => simp at hvt
                              | succ _ => simp at hvt
                            | _ => simp at hvt
                          | succ _ => simp at hvt
                        | _ => simp at hvt
                      | succ _ => simp at hvt
                    | _ => simp at hvt
                  | _ => simp at hvt
                | _ => simp at hvt
              | _ => simp at hvt
            | _ => simp at hvt
          | _ => rw [ht] at hvt; simp at hvt
        | _ => rw [hv] at hvt; simp at hvt
      | _ => simp at hTL

section ArraySem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-- The model element of a `List.{0}` over element-type set `A`. -/
noncomputable def listSet (M : Model V env) (A : V) : List V → V
  | [] => app (M.cval listNilName (fun _ => 0)) A
  | x :: xs => app (app (app (M.cval listConsName (fun _ => 0)) A) x) (listSet M A xs)

/-- The model element of an `Array.{0}` over element-type set `A`. -/
noncomputable def arraySet (M : Model V env) (ak : ArrayKeys) (A : V) (xs : List V) : V :=
  app (app (M.cval ak.arrayMk (fun _ => 0)) A) (listSet M A xs)

/-- Membership of `listSet M A xs` in `List.{0} A`. -/
theorem listSet_mem (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {A : V} (hA : A ∈ˢ (univ 1 : V)) :
    ∀ {xs : List V}, (∀ x ∈ xs, x ∈ˢ A) →
      listSet M A xs ∈ˢ app (M.cval listName (fun _ => 0)) A
  | [], _ => by
    obtain ⟨ciN, pN, _, hfN, hlpN, htyN⟩ := hL.listNil
    obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hL.list
    obtain ⟨T, hT, hm⟩ := mem_key M hfN (fun _ => 0) (fun _ => empty)
    rw [htyN] at hT
    have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.sort (.succ (.param pN))) (univ 1) := by
      rw [den_sort]; simp [Level.eval]
    obtain ⟨B, hB, hmem⟩ := app_mem_den_pi hT hU hm hA
    rw [den_app] at hB
    obtain ⟨FL, AL, hFL, hAL, rfl⟩ := hB
    have hFLe : FL = M.cval listName (fun _ => 0) := by
      cases hFL with
      | const hfL' _ =>
        rw [hfL] at hfL'; cases hfL'
        exact hcv listName ciL hfL _ _ fun q hq => by
          rw [hlpL, List.mem_singleton] at hq; subst hq
          rw [hlpL]; simp [Level.substFn, Level.eval]
    have hALe : AL = A := den_bvar.mp hAL
    rw [hFLe, hALe] at hmem
    exact hmem
  | x :: xs, hxs => by
    obtain ⟨ciK, pK, _, _, _, hfK, hlpK, htyK⟩ := hL.listCons
    obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hL.list
    have hx : x ∈ˢ A := hxs x (List.mem_cons_self ..)
    have htail := listSet_mem M hcv hL hA (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    obtain ⟨T, hT, hm⟩ := mem_key M hfK (fun _ => 0) (fun _ => empty)
    rw [htyK] at hT
    have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.sort (.succ (.param pK))) (univ 1) := by
      rw [den_sort]; simp [Level.eval]
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT hU hm hA
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 .bvar hm1 hx
    have hListA : ∀ (i : Nat) (ρ' : BVarIdx → V), ρ' i = A →
        Denotes M.cval env (fun _ => 0) ρ' (.app (.const listName [.param pK]) (.bvar i))
          (app (M.cval listName (fun _ => 0)) A) := by
      intro i ρ' hi
      refine .app ?_ (den_bvar.mpr hi.symm)
      have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0) (ρ := ρ')
        (us := [.param pK]) hfL (by rw [hlpL]; rfl)
      have heq : M.cval listName (Level.substFn (fun _ => 0) ciL.toConstantVal.levelParams [.param pK]) =
          M.cval listName (fun _ => 0) :=
        hcv listName ciL hfL _ _ fun q hq => by
          rw [hlpL, List.mem_singleton] at hq; subst hq
          rw [hlpL]; simp [Level.substFn, Level.eval]
      rwa [heq] at hconst
    obtain ⟨B3, hB3, hm3⟩ := app_mem_den_pi hB2 (hListA 1 _ rfl) hm2 htail
    have hB3e := Denotes_functional hB3 (hListA 2 _ rfl)
    rw [hB3e] at hm3
    exact hm3

/-- Membership of `arraySet M ak A xs` in `Array.{0} A`. -/
theorem arraySet_mem (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) :
    arraySet M ak A xs ∈ˢ app (M.cval ak.array (fun _ => 0)) A := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨cvM, mb1, mb2, hfM, hlpM, htyM⟩ := hA.arrayMk
  obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hL.list
  obtain ⟨T, hT, hm⟩ := mem_key M hfM (fun _ => 0) (fun _ => empty)
  simp only [ConstantInfo.toConstantVal, htyM] at hT
  have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty)
      (.sort (.succ (.param ak.lvlParam))) (univ 1) := by
    rw [den_sort]; simp [Level.eval]
  obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT hU hm hA1
  have hListA : Denotes M.cval env (fun _ => 0) (push A (fun _ => empty))
      (.app (.const listName [.param ak.lvlParam]) (.bvar 0))
      (app (M.cval listName (fun _ => 0)) A) := by
    refine .app ?_ .bvar
    have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0)
      (ρ := push A (fun _ => empty)) (us := [.param ak.lvlParam]) hfL (by rw [hlpL]; rfl)
    have heq : M.cval listName
        (Level.substFn (fun _ => 0) ciL.toConstantVal.levelParams [.param ak.lvlParam]) =
        M.cval listName (fun _ => 0) :=
      hcv listName ciL hfL _ _ fun q hq => by
        rw [hlpL, List.mem_singleton] at hq; subst hq
        rw [hlpL]; simp [Level.substFn, Level.eval]
    rwa [heq] at hconst
  obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 hListA hm1 (listSet_mem M hcv hL hA1 hxs)
  have hArrA : Denotes M.cval env (fun _ => 0) (push (listSet M A xs) (push A (fun _ => empty)))
      (.app (.const ak.array [.param ak.lvlParam]) (.bvar 1))
      (app (M.cval ak.array (fun _ => 0)) A) := by
    refine .app ?_ .bvar
    have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0)
      (ρ := push (listSet M A xs) (push A (fun _ => empty))) (us := [.param ak.lvlParam]) hfA
      (by simp [ConstantInfo.toConstantVal, hlpA])
    simp only [ConstantInfo.toConstantVal] at hconst
    have heq : M.cval ak.array (Level.substFn (fun _ => 0) cvA.levelParams [.param ak.lvlParam]) =
        M.cval ak.array (fun _ => 0) :=
      hcv ak.array (.indInfo cvA caps) hfA _ _ fun q hq => by
        simp only [ConstantInfo.toConstantVal, hlpA, List.mem_singleton] at hq; subst hq
        rw [hlpA]; simp [Level.substFn, Level.eval]
    rwa [heq] at hconst
  rwa [Denotes_functional hB2 hArrA] at hm2

/-- Evaluating `Array.toList.{0} A x` via `M.defn_value` yields `projVal M.cval ak.array 0 entry x`. -/
theorem toList_eq_projVal (M : Model V env) (hcv : CvalParams M) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {entry : ProjEntry .anon} (hproj : env.findProj? ak.array 0 = some entry)
    {A x : V} (hA1 : A ∈ˢ (univ 1 : V)) (hx : x ∈ˢ app (M.cval ak.array (fun _ => 0)) A) :
    app (app (M.cval ak.toList (fun _ => 0)) A) x = projVal M.cval ak.array 0 entry x := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨cvL, hint, mb1, mb2, hfL, _, _⟩ := hA.toList
  have hval := M.defn_value cvL _ hint (find_mem hfL) (fun _ => 0) (fun _ => empty)
  rw [show cvL.name = ak.toList from find_name hfL] at hval
  have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty)
      (.sort (.succ (.param ak.lvlParam))) (univ 1) := by
    rw [den_sort]; simp [Level.eval]
  obtain ⟨Y1, hY1, heq1⟩ := app_den_lam hval hU hA1
  have hArrA : Denotes M.cval env (fun _ => 0) (push A (fun _ => empty))
      (.app (.const ak.array [.param ak.lvlParam]) (.bvar 0))
      (app (M.cval ak.array (fun _ => 0)) A) := by
    refine .app ?_ .bvar
    have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0)
      (ρ := push A (fun _ => empty)) (us := [.param ak.lvlParam]) hfA
      (by simp [ConstantInfo.toConstantVal, hlpA])
    simp only [ConstantInfo.toConstantVal] at hconst
    have heq : M.cval ak.array (Level.substFn (fun _ => 0) cvA.levelParams [.param ak.lvlParam]) =
        M.cval ak.array (fun _ => 0) :=
      hcv ak.array (.indInfo cvA caps) hfA _ _ fun q hq => by
        simp only [ConstantInfo.toConstantVal, hlpA, List.mem_singleton] at hq; subst hq
        rw [hlpA]; simp [Level.substFn, Level.eval]
    rwa [heq] at hconst
  obtain ⟨Y2, hY2, heq2⟩ := app_den_lam hY1 hArrA hx
  rw [heq1, heq2]
  have hP : Denotes M.cval env (fun _ => 0) (push x (push A (fun _ => empty)))
      (.proj ak.array 0 (.bvar 0)) (projVal M.cval ak.array 0 entry x) :=
    .proj_table hproj .bvar
  exact Denotes_functional hY2 hP

/-- **`Array.toList.{0} A (Array.mk.{0} A L) = L`** directly from `M.defn_value` and `M.proj_law`. -/
theorem toList_mk (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {A L : V} (hA1 : A ∈ˢ (univ 1 : V))
    (hLm : L ∈ˢ app (M.cval listName (fun _ => 0)) A) :
    app (app (M.cval ak.toList (fun _ => 0)) A)
      (app (app (M.cval ak.arrayMk (fun _ => 0)) A) L) = L := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨cvM, mb1, mb2, hfM, hlpM, htyM⟩ := hA.arrayMk
  obtain ⟨entry, hproj, hPctor, hPnp, hPnf, _, hPlp, hPss⟩ := hA.proj
  obtain ⟨ciL, pL, _, hfL, hlpL, _⟩ := hL.list
  have hMkMem : app (app (M.cval ak.arrayMk (fun _ => 0)) A) L ∈ˢ
      app (M.cval ak.array (fun _ => 0)) A := by
    obtain ⟨T, hT, hm⟩ := mem_key M hfM (fun _ => 0) (fun _ => empty)
    simp only [ConstantInfo.toConstantVal, htyM] at hT
    have hU : Denotes M.cval env (fun _ => 0) (fun _ => empty)
        (.sort (.succ (.param ak.lvlParam))) (univ 1) := by
      rw [den_sort]; simp [Level.eval]
    obtain ⟨B1, hB1, hm1⟩ := app_mem_den_pi hT hU hm hA1
    have hListA : Denotes M.cval env (fun _ => 0) (push A (fun _ => empty))
        (.app (.const listName [.param ak.lvlParam]) (.bvar 0))
        (app (M.cval listName (fun _ => 0)) A) := by
      refine .app ?_ .bvar
      have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0)
        (ρ := push A (fun _ => empty)) (us := [.param ak.lvlParam]) hfL (by rw [hlpL]; rfl)
      have heq : M.cval listName
          (Level.substFn (fun _ => 0) ciL.toConstantVal.levelParams [.param ak.lvlParam]) =
          M.cval listName (fun _ => 0) :=
        hcv listName ciL hfL _ _ fun q hq => by
          rw [hlpL, List.mem_singleton] at hq; subst hq
          rw [hlpL]; simp [Level.substFn, Level.eval]
      rwa [heq] at hconst
    obtain ⟨B2, hB2, hm2⟩ := app_mem_den_pi hB1 hListA hm1 hLm
    have hArrA : Denotes M.cval env (fun _ => 0) (push L (push A (fun _ => empty)))
        (.app (.const ak.array [.param ak.lvlParam]) (.bvar 1))
        (app (M.cval ak.array (fun _ => 0)) A) := by
      refine .app ?_ .bvar
      have hconst := Denotes.const (cval := M.cval) (env := env) (φ := fun _ => 0)
        (ρ := push L (push A (fun _ => empty))) (us := [.param ak.lvlParam]) hfA
        (by simp [ConstantInfo.toConstantVal, hlpA])
      simp only [ConstantInfo.toConstantVal] at hconst
      have heq : M.cval ak.array (Level.substFn (fun _ => 0) cvA.levelParams [.param ak.lvlParam]) =
          M.cval ak.array (fun _ => 0) :=
        hcv ak.array (.indInfo cvA caps) hfA _ _ fun q hq => by
          simp only [ConstantInfo.toConstantVal, hlpA, List.mem_singleton] at hq; subst hq
          rw [hlpA]; simp [Level.substFn, Level.eval]
      rwa [heq] at hconst
    rwa [Denotes_functional hB2 hArrA] at hm2
  rw [toList_eq_projVal M hcv hA hproj hA1 hMkMem]
  obtain ⟨_, cvC, hfC, _, _, hlaw⟩ := M.proj_law ak.array 0 entry cvA caps hproj hfA
  rw [hPctor, hPnp, hPnf, hfM] at hfC
  cases hfC
  have hF : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.const ak.array [.zero])
      (M.cval ak.array (fun _ => 0)) := (den_const_zero1 hcv hfA hlpA).mpr rfl
  have hK : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.const entry.ctor [.zero])
      (M.cval ak.arrayMk (fun _ => 0)) := by
    rw [hPctor]; exact (den_const_zero1 hcv hfM hlpM).mpr rfl
  obtain ⟨hprojEq, _⟩ := hlaw [.zero] (fun _ => 0) (fun _ => empty) _ _ (by rw [hPlp]; rfl) hF hK
  have hFits : Fits M.cval env (fun _ => 0) (fun _ => empty)
      (cvM.type.instantiateLevelParams cvM.levelParams [.zero]) [A, L]
      (push L (push A (fun _ => empty)))
      (.app (.const ak.array [.zero]) (.bvar 1)) := by
    rw [htyM, hlpM]
    have hsub : Level.subst [ak.lvlParam] [.zero] (.param ak.lvlParam) = .zero := by
      simp [Level.subst, Level.subst.go]
    have hsub1 : Level.subst [ak.lvlParam] [.zero] (.succ (.param ak.lvlParam)) = .succ .zero := by
      simp [Level.subst, Level.subst.go]
    simp only [Expr.instantiateLevelParams, List.map_cons, List.map_nil, hsub, hsub1]
    refine .cons (by rw [den_sort]; rfl) hA1 (.cons ?_ hLm .nil)
    exact .app ((den_const_zero1 hcv hfL hlpL).mpr rfl) .bvar
  have hss : Level.eval (Level.substFn (fun _ => 0) entry.levelParams [.zero]) entry.structSort ≠ 0 := by
    rw [hPss, hPlp]; simp [Level.eval]
  have hres := hprojEq (fun h0 => absurd h0 hss) _ _ [A, L] (by simp [hPnp, hPnf]) hFits
  simpa [hPnp] using hres

/-- **`Array.toList.{0} A (arraySet M ak A xs) = listSet M A xs`.** -/
theorem toList_arraySet (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) :
    app (app (M.cval ak.toList (fun _ => 0)) A) (arraySet M ak A xs) = listSet M A xs :=
  toList_mk M hcv hL hA hA1 (listSet_mem M hcv hL hA1 hxs)

/-- **Structure η for `Array` directly from `M.proj_law`** (no new axioms!):
every element `x ∈ˢ Array.{0} A` equals `Array.mk.{0} A (Array.toList.{0} A x)`. -/
theorem array_eta (M : Model V env) (hcv : CvalParams M) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {A x : V} (hA1 : A ∈ˢ (univ 1 : V))
    (hx : x ∈ˢ app (M.cval ak.array (fun _ => 0)) A) :
    x = app (app (M.cval ak.arrayMk (fun _ => 0)) A)
      (app (app (M.cval ak.toList (fun _ => 0)) A) x) := by
  obtain ⟨cvA, caps, _, hfA, hlpA, htyA⟩ := hA.array
  obtain ⟨cvM, _, _, hfM, hlpM, _⟩ := hA.arrayMk
  obtain ⟨entry, hproj, hPctor, hPnp, hPnf, hPoff, hPlp, _⟩ := hA.proj
  rw [toList_eq_projVal M hcv hA hproj hA1 hx]
  obtain ⟨_, _, _, _, _, hlaw⟩ := M.proj_law ak.array 0 entry cvA caps hproj hfA
  have hF : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.const ak.array [.zero])
      (M.cval ak.array (fun _ => 0)) := (den_const_zero1 hcv hfA hlpA).mpr rfl
  have hK : Denotes M.cval env (fun _ => 0) (fun _ => empty) (.const entry.ctor [.zero])
      (M.cval ak.arrayMk (fun _ => 0)) := by
    rw [hPctor]; exact (den_const_zero1 hcv hfM hlpM).mpr rfl
  obtain ⟨_, heta⟩ := hlaw [.zero] (fun _ => 0) (fun _ => empty) _ _ (by rw [hPlp]; rfl) hF hK
  have hFits : Fits M.cval env (fun _ => 0) (fun _ => empty)
      (cvA.type.instantiateLevelParams cvA.levelParams [.zero]) [A]
      (push A (fun _ => empty)) (.sort (.succ .zero)) := by
    rw [htyA, hlpA]
    have hsub1 : Level.subst [ak.lvlParam] [.zero] (.succ (.param ak.lvlParam)) = .succ .zero := by
      simp [Level.subst, Level.subst.go]
    simp only [Expr.instantiateLevelParams, hsub1]
    exact .cons (by rw [den_sort]; rfl) hA1 .nil
  have hres := heta hPoff _ _ [A] x (by simp [hPnp]) hFits (by simpa using hx)
  simp only [hPnf, List.range_one, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.foldl_cons, List.foldl_nil] at hres
  have hpv : projVal M.cval ak.array 0 entry x = field (0 + entry.off) x := by
    simp [projVal, hPoff]
  rw [hpv]
  exact hres

/-- **Extensionality for `Array` directly from `M.proj_law`**: two elements of `Array.{0} A`
with equal `Array.toList` are equal. -/
theorem array_ext (M : Model V env) (hcv : CvalParams M) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {A x y : V} (hA1 : A ∈ˢ (univ 1 : V))
    (hx : x ∈ˢ app (M.cval ak.array (fun _ => 0)) A)
    (hy : y ∈ˢ app (M.cval ak.array (fun _ => 0)) A)
    (heq : app (app (M.cval ak.toList (fun _ => 0)) A) x =
      app (app (M.cval ak.toList (fun _ => 0)) A) y) : x = y := by
  rw [array_eta M hcv hA hA1 hx, array_eta M hcv hA hA1 hy, heq]

/-- `arraySet` is injective into `listSet`. -/
theorem arraySet_inj (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env) {ak : ArrayKeys}
    (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {xs ys : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) (hys : ∀ y ∈ ys, y ∈ˢ A)
    (heq : arraySet M ak A xs = arraySet M ak A ys) :
    listSet M A xs = listSet M A ys := by
  rw [← toList_arraySet M hcv hL hA hA1 hxs, ← toList_arraySet M hcv hL hA hA1 hys, heq]

/-! ## Section 3: `List` & `ArraySpec` Model Adequacy over `Ix.Kernel.Model` -/

/-- Model-level equations for `List` operations at universe 0 over any `A ∈ˢ univ 1`. -/
structure ListOpsModel (M : Model V env) (A : V) where
  kLength : KKey
  kConcat : KKey
  kDropLast : KKey
  kSet : KKey
  kGetD : KKey
  length_nil : app (app (M.cval kLength (fun _ => 0)) A) (listSet M A []) = litSet M (fun _ => 0) 0
  length_cons : ∀ x xs, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) →
    app (app (M.cval kLength (fun _ => 0)) A) (listSet M A (x :: xs)) =
      app (M.cval natSuccName (fun _ => 0))
        (app (app (M.cval kLength (fun _ => 0)) A) (listSet M A xs))
  concat_nil : ∀ v, v ∈ˢ A →
    app (app (app (M.cval kConcat (fun _ => 0)) A) (listSet M A [])) v = listSet M A [v]
  concat_cons : ∀ x xs v, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) → v ∈ˢ A →
    app (app (app (M.cval kConcat (fun _ => 0)) A) (listSet M A (x :: xs))) v =
      app (app (app (M.cval listConsName (fun _ => 0)) A) x)
        (app (app (app (M.cval kConcat (fun _ => 0)) A) (listSet M A xs)) v)
  dropLast_nil :
    app (app (M.cval kDropLast (fun _ => 0)) A) (listSet M A []) = listSet M A []
  dropLast_single : ∀ x, x ∈ˢ A →
    app (app (M.cval kDropLast (fun _ => 0)) A) (listSet M A [x]) = listSet M A []
  dropLast_cons2 : ∀ x y xs, x ∈ˢ A → y ∈ˢ A → (∀ z ∈ xs, z ∈ˢ A) →
    app (app (M.cval kDropLast (fun _ => 0)) A) (listSet M A (x :: y :: xs)) =
      app (app (app (M.cval listConsName (fun _ => 0)) A) x)
        (app (app (M.cval kDropLast (fun _ => 0)) A) (listSet M A (y :: xs)))
  set_nil : ∀ i v, v ∈ˢ A →
    app (app (app (app (M.cval kSet (fun _ => 0)) A) (listSet M A []))
      (litSet M (fun _ => 0) i)) v = listSet M A []
  set_zero : ∀ x xs v, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) → v ∈ˢ A →
    app (app (app (app (M.cval kSet (fun _ => 0)) A) (listSet M A (x :: xs)))
      (litSet M (fun _ => 0) 0)) v = listSet M A (v :: xs)
  set_succ : ∀ x xs i v, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) → v ∈ˢ A →
    app (app (app (app (M.cval kSet (fun _ => 0)) A) (listSet M A (x :: xs)))
      (litSet M (fun _ => 0) (i + 1))) v =
      app (app (app (M.cval listConsName (fun _ => 0)) A) x)
        (app (app (app (app (M.cval kSet (fun _ => 0)) A) (listSet M A xs))
          (litSet M (fun _ => 0) i)) v)
  getD_nil : ∀ i d, d ∈ˢ A →
    app (app (app (app (M.cval kGetD (fun _ => 0)) A) (listSet M A []))
      (litSet M (fun _ => 0) i)) d = d
  getD_zero : ∀ x xs d, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) → d ∈ˢ A →
    app (app (app (app (M.cval kGetD (fun _ => 0)) A) (listSet M A (x :: xs)))
      (litSet M (fun _ => 0) 0)) d = x
  getD_succ : ∀ x xs i d, x ∈ˢ A → (∀ y ∈ xs, y ∈ˢ A) → d ∈ˢ A →
    app (app (app (app (M.cval kGetD (fun _ => 0)) A) (listSet M A (x :: xs)))
      (litSet M (fun _ => 0) (i + 1))) d =
      app (app (app (app (M.cval kGetD (fun _ => 0)) A) (listSet M A xs))
        (litSet M (fun _ => 0) i)) d

theorem listLength_accel {M : Model V env} {A : V} (hO : ListOpsModel M A) :
    ∀ {xs : List V}, (∀ x ∈ xs, x ∈ˢ A) →
      app (app (M.cval hO.kLength (fun _ => 0)) A) (listSet M A xs) =
        litSet M (fun _ => 0) xs.length
  | [], _ => hO.length_nil
  | x :: xs, hxs => by
    rw [hO.length_cons x xs (hxs x (List.mem_cons_self ..))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)),
      listLength_accel hO (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
    rfl

theorem listConcat_accel {M : Model V env} {A : V} (hO : ListOpsModel M A) {v : V} (hv : v ∈ˢ A) :
    ∀ {xs : List V}, (∀ x ∈ xs, x ∈ˢ A) →
      app (app (app (M.cval hO.kConcat (fun _ => 0)) A) (listSet M A xs)) v =
        listSet M A (xs ++ [v])
  | [], _ => hO.concat_nil v hv
  | x :: xs, hxs => by
    rw [hO.concat_cons x xs v (hxs x (List.mem_cons_self ..))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hv,
      listConcat_accel hO hv (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
    rfl

theorem listDropLast_accel {M : Model V env} {A : V} (hO : ListOpsModel M A) :
    ∀ {xs : List V}, (∀ x ∈ xs, x ∈ˢ A) →
      app (app (M.cval hO.kDropLast (fun _ => 0)) A) (listSet M A xs) =
        listSet M A xs.dropLast
  | [], _ => hO.dropLast_nil
  | [x], hxs => hO.dropLast_single x (hxs x (List.mem_cons_self ..))
  | x :: y :: xs, hxs => by
    have hx : x ∈ˢ A := hxs x (List.mem_cons_self ..)
    have hy : y ∈ˢ A := hxs y (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hrest : ∀ z ∈ xs, z ∈ˢ A :=
      fun z hz => hxs z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
    have htail : ∀ z ∈ y :: xs, z ∈ˢ A := fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    rw [hO.dropLast_cons2 x y xs hx hy hrest, listDropLast_accel hO htail]
    rfl

theorem listSet_accel {M : Model V env} {A : V} (hO : ListOpsModel M A) {v : V} (hv : v ∈ˢ A) :
    ∀ {xs : List V} (i : Nat), (∀ x ∈ xs, x ∈ˢ A) →
      app (app (app (app (M.cval hO.kSet (fun _ => 0)) A) (listSet M A xs))
        (litSet M (fun _ => 0) i)) v = listSet M A (xs.set i v)
  | [], i, _ => hO.set_nil i v hv
  | x :: xs, 0, hxs =>
    hO.set_zero x xs v (hxs x (List.mem_cons_self ..))
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hv
  | x :: xs, i + 1, hxs => by
    rw [hO.set_succ x xs i v (hxs x (List.mem_cons_self ..))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hv,
      listSet_accel hO hv i (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
    rfl

theorem listGetD_accel {M : Model V env} {A : V} (hO : ListOpsModel M A) {d : V} (hd : d ∈ˢ A) :
    ∀ {xs : List V} (i : Nat), (∀ x ∈ xs, x ∈ˢ A) →
      app (app (app (app (M.cval hO.kGetD (fun _ => 0)) A) (listSet M A xs))
        (litSet M (fun _ => 0) i)) d = xs.getD i d
  | [], i, _ => hO.getD_nil i d hd
  | x :: xs, 0, hxs =>
    hO.getD_zero x xs d (hxs x (List.mem_cons_self ..))
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hd
  | x :: xs, i + 1, hxs => by
    rw [hO.getD_succ x xs i d (hxs x (List.mem_cons_self ..))
        (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) hd,
      listGetD_accel hO hd i (fun y hy => hxs y (List.mem_cons_of_mem _ hy))]
    rfl

/-- Model-level `Array.toList` equations matching `IxCC.Src.Table.Array.arrayEqnType` for the
core `ArraySpec` operations (`emptyWithCapacity`, `size`, `push`, `pop`, `setIfInBounds`, `getD`,
`set`). -/
structure ArraySpecEqns (M : Model V env) (ak : ArrayKeys) (A : V) (hLO : ListOpsModel M A) where
  kEmpty : KKey
  kSize : KKey
  kPush : KKey
  kPop : KKey
  kSetIfInBounds : KKey
  kGetD : KKey
  kSet : KKey
  empty_mem : ∀ c : Nat,
    app (app (M.cval kEmpty (fun _ => 0)) A) (litSet M (fun _ => 0) c) ∈ˢ
      app (M.cval ak.array (fun _ => 0)) A
  empty_toList : ∀ c : Nat,
    app (app (M.cval ak.toList (fun _ => 0)) A)
      (app (app (M.cval kEmpty (fun _ => 0)) A) (litSet M (fun _ => 0) c)) =
    listSet M A []
  size_eq : ∀ x, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A →
    app (app (M.cval kSize (fun _ => 0)) A) x =
      app (app (M.cval hLO.kLength (fun _ => 0)) A)
        (app (app (M.cval ak.toList (fun _ => 0)) A) x)
  push_mem : ∀ x v, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (app (M.cval kPush (fun _ => 0)) A) x) v ∈ˢ app (M.cval ak.array (fun _ => 0)) A
  push_toList : ∀ x v, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (M.cval ak.toList (fun _ => 0)) A)
      (app (app (app (M.cval kPush (fun _ => 0)) A) x) v) =
    app (app (app (M.cval hLO.kConcat (fun _ => 0)) A)
      (app (app (M.cval ak.toList (fun _ => 0)) A) x)) v
  pop_mem : ∀ x, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A →
    app (app (M.cval kPop (fun _ => 0)) A) x ∈ˢ app (M.cval ak.array (fun _ => 0)) A
  pop_toList : ∀ x, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A →
    app (app (M.cval ak.toList (fun _ => 0)) A) (app (app (M.cval kPop (fun _ => 0)) A) x) =
      app (app (M.cval hLO.kDropLast (fun _ => 0)) A)
        (app (app (M.cval ak.toList (fun _ => 0)) A) x)
  setIfInBounds_mem : ∀ x (i : Nat) v, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (app (app (M.cval kSetIfInBounds (fun _ => 0)) A) x) (litSet M (fun _ => 0) i)) v ∈ˢ
      app (M.cval ak.array (fun _ => 0)) A
  setIfInBounds_toList : ∀ x (i : Nat) v, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (M.cval ak.toList (fun _ => 0)) A)
      (app (app (app (app (M.cval kSetIfInBounds (fun _ => 0)) A) x) (litSet M (fun _ => 0) i)) v) =
    app (app (app (app (M.cval hLO.kSet (fun _ => 0)) A)
      (app (app (M.cval ak.toList (fun _ => 0)) A) x)) (litSet M (fun _ => 0) i)) v
  getD_eq : ∀ x (i : Nat) d, x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → d ∈ˢ A →
    app (app (app (app (M.cval kGetD (fun _ => 0)) A) x) (litSet M (fun _ => 0) i)) d =
      app (app (app (app (M.cval hLO.kGetD (fun _ => 0)) A)
        (app (app (M.cval ak.toList (fun _ => 0)) A) x)) (litSet M (fun _ => 0) i)) d
  set_mem : ∀ x (i : Nat) v (h : V), x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (app (app (app (M.cval kSet (fun _ => 0)) A) x) (litSet M (fun _ => 0) i)) v) h ∈ˢ
      app (M.cval ak.array (fun _ => 0)) A
  set_toList : ∀ x (i : Nat) v (h : V), x ∈ˢ app (M.cval ak.array (fun _ => 0)) A → v ∈ˢ A →
    app (app (M.cval ak.toList (fun _ => 0)) A)
      (app (app (app (app (app (M.cval kSet (fun _ => 0)) A) x) (litSet M (fun _ => 0) i)) v) h) =
    app (app (app (app (M.cval hLO.kSet (fun _ => 0)) A)
      (app (app (M.cval ak.toList (fun _ => 0)) A) x)) (litSet M (fun _ => 0) i)) v

private theorem mem_of_dropLast {α : Type _} : ∀ {xs : List α} {x : α}, x ∈ xs.dropLast → x ∈ xs
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: xs, x, h => by
    simp only [List.dropLast, List.mem_cons] at h
    rcases h with rfl | h'
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_dropLast h')

private theorem mem_list_set {α : Type _} {xs : List α} {i : Nat} {v x : α}
    (hx : x ∈ xs.set i v) : x ∈ xs ∨ x = v := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_of_mem _ hx)
    | succ i =>
      simp only [List.set_cons_succ, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl (List.mem_cons_self ..)
      · rcases ih hx with h1 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr h2

/-- **`Array.emptyWithCapacity` adequacy over `Ix.Kernel.Model`** (via `array_eta`). -/
theorem arrayEmpty_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO) (c : Nat) :
    app (app (M.cval hE.kEmpty (fun _ => 0)) A) (litSet M (fun _ => 0) c) =
      arraySet M ak A [] :=
  array_ext M hcv hA hA1 (hE.empty_mem c) (arraySet_mem M hcv hL hA hA1 (by simp))
    (by rw [hE.empty_toList c, toList_arraySet M hcv hL hA hA1 (by simp)])

/-- **`Array.size` adequacy over `Ix.Kernel.Model`.** -/
theorem arraySize_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) :
    app (app (M.cval hE.kSize (fun _ => 0)) A) (arraySet M ak A xs) =
      litSet M (fun _ => 0) xs.length := by
  rw [hE.size_eq _ (arraySet_mem M hcv hL hA hA1 hxs),
    toList_arraySet M hcv hL hA hA1 hxs, listLength_accel hLO hxs]

/-- **`Array.push` adequacy over `Ix.Kernel.Model`** (via `array_eta`). -/
theorem arrayPush_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) {v : V} (hv : v ∈ˢ A) :
    app (app (app (M.cval hE.kPush (fun _ => 0)) A) (arraySet M ak A xs)) v =
      arraySet M ak A (xs ++ [v]) := by
  have hxs' : ∀ y ∈ xs ++ [v], y ∈ˢ A := fun y hy => by
    rcases List.mem_append.mp hy with hy | hy
    · exact hxs y hy
    · rw [List.mem_singleton.mp hy]; exact hv
  exact array_ext M hcv hA hA1
    (hE.push_mem _ v (arraySet_mem M hcv hL hA hA1 hxs) hv)
    (arraySet_mem M hcv hL hA hA1 hxs')
    (by
      rw [hE.push_toList _ v (arraySet_mem M hcv hL hA hA1 hxs) hv,
        toList_arraySet M hcv hL hA hA1 hxs, listConcat_accel hLO hv hxs,
        toList_arraySet M hcv hL hA hA1 hxs'])

/-- **`Array.pop` adequacy over `Ix.Kernel.Model`** (via `array_eta`). -/
theorem arrayPop_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) :
    app (app (M.cval hE.kPop (fun _ => 0)) A) (arraySet M ak A xs) =
      arraySet M ak A xs.dropLast := by
  have hxs' : ∀ y ∈ xs.dropLast, y ∈ˢ A := fun y hy => hxs y (mem_of_dropLast hy)
  exact array_ext M hcv hA hA1
    (hE.pop_mem _ (arraySet_mem M hcv hL hA hA1 hxs))
    (arraySet_mem M hcv hL hA hA1 hxs')
    (by
      rw [hE.pop_toList _ (arraySet_mem M hcv hL hA hA1 hxs),
        toList_arraySet M hcv hL hA hA1 hxs, listDropLast_accel hLO hxs,
        toList_arraySet M hcv hL hA hA1 hxs'])

/-- **`Array.setIfInBounds` adequacy over `Ix.Kernel.Model`** (via `array_eta`). -/
theorem arraySetIfInBounds_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) (i : Nat) {v : V} (hv : v ∈ˢ A) :
    app (app (app (app (M.cval hE.kSetIfInBounds (fun _ => 0)) A) (arraySet M ak A xs))
      (litSet M (fun _ => 0) i)) v = arraySet M ak A (xs.set i v) := by
  have hxs' : ∀ y ∈ xs.set i v, y ∈ˢ A := fun y hy => by
    rcases mem_list_set hy with hy | rfl
    · exact hxs y hy
    · exact hv
  exact array_ext M hcv hA hA1
    (hE.setIfInBounds_mem _ i v (arraySet_mem M hcv hL hA hA1 hxs) hv)
    (arraySet_mem M hcv hL hA hA1 hxs')
    (by
      rw [hE.setIfInBounds_toList _ i v (arraySet_mem M hcv hL hA hA1 hxs) hv,
        toList_arraySet M hcv hL hA hA1 hxs, listSet_accel hLO hv i hxs,
        toList_arraySet M hcv hL hA hA1 hxs'])

/-- **`Array.getD` adequacy over `Ix.Kernel.Model`.** -/
theorem arrayGetD_accel (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) (i : Nat) {d : V} (hd : d ∈ˢ A) :
    app (app (app (app (M.cval hE.kGetD (fun _ => 0)) A) (arraySet M ak A xs))
      (litSet M (fun _ => 0) i)) d = xs.getD i d := by
  rw [hE.getD_eq _ i d (arraySet_mem M hcv hL hA hA1 hxs) hd,
    toList_arraySet M hcv hL hA hA1 hxs, listGetD_accel hLO hd i hxs]

/-- **`Array.set` adequacy over `Ix.Kernel.Model`** (via `array_eta`). -/
theorem arraySet_of_toList_eqn (M : Model V env) (hcv : CvalParams M) (hL : ListBasis env)
    {ak : ArrayKeys} (hA : ArrayBasis env ak) {A : V} (hA1 : A ∈ˢ (univ 1 : V))
    {hLO : ListOpsModel M A} (hE : ArraySpecEqns M ak A hLO)
    {xs : List V} (hxs : ∀ x ∈ xs, x ∈ˢ A) (i : Nat) {v h : V} (hv : v ∈ˢ A) :
    app (app (app (app (app (M.cval hE.kSet (fun _ => 0)) A) (arraySet M ak A xs))
      (litSet M (fun _ => 0) i)) v) h = arraySet M ak A (xs.set i v) := by
  have hxs' : ∀ y ∈ xs.set i v, y ∈ˢ A := fun y hy => by
    rcases mem_list_set hy with hy | rfl
    · exact hxs y hy
    · exact hv
  exact array_ext M hcv hA hA1
    (hE.set_mem _ i v h (arraySet_mem M hcv hL hA hA1 hxs) hv)
    (arraySet_mem M hcv hL hA hA1 hxs')
    (by
      rw [hE.set_toList _ i v h (arraySet_mem M hcv hL hA hA1 hxs) hv,
        toList_arraySet M hcv hL hA hA1 hxs, listSet_accel hLO hv i hxs,
        toList_arraySet M hcv hL hA hA1 hxs'])

/-! ## Section 4: `BigNat` Limb-Array Denotation, `toNat` Adequacy, and Layer-1 × Layer-3 Composition -/

/-- Stored `UInt64 : Type 0` and `UInt64.ofNat : Nat → UInt64` typing facts. -/
structure UInt64Basis (env : KEnv) (tk : TowKeys) : Prop where
  ty : ∃ (ci : ConstantInfo .anon), env.find? tk.ty = some ci ∧
    ci.toConstantVal.levelParams = [] ∧ ci.toConstantVal.type = .sort (.succ .zero)
  ofNat : ∃ (ci : ConstantInfo .anon) (mb : BinderMeta), env.find? tk.ofNat = some ci ∧
    ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type = .forallE (.const natName []) (.const tk.ty []) mb

/-- Every `towV M tk 64 size64 φ n` (`n < 2^64`) lies in `UInt64`, directly from `ofNat_tow` and
`M.mem` on `UInt64.ofNat : Nat → UInt64`. -/
theorem towV_mem_of_ofNat (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hE : EqBasis env) {tk : TowKeys} {kB kR kS : KKey}
    (hBr : BridgeStored env tk 64 size64 kB kR kS) (hU : UInt64Basis env tk)
    (φ : LevelParam → Nat) {n : Nat} (hn : n < size64) :
    towV M tk 64 size64 φ n ∈ˢ M.cval tk.ty φ := by
  obtain ⟨ciTy, hfTy, hlTy, _⟩ := hU.ty
  obtain ⟨ciOf, mb, hfOf, _, htOf⟩ := hU.ofNat
  have hF := natFacts M hN φ
  have hOf : app (M.cval tk.ofNat φ) (litSet M φ n) = towV M tk 64 size64 φ n := by
    rw [ofNat_tow M hacc hN hE hBr φ n, Nat.mod_eq_of_lt hn]
  rw [← hOf]
  obtain ⟨T, hT, hm⟩ := mem_key M hfOf φ (fun _ => empty)
  rw [htOf] at hT
  obtain ⟨B, hB, hmem⟩ := app_mem_den_pi hT ((hF.natD _ _).mpr rfl) hm (lit_mem M hF n)
  rwa [(den_const0 hfTy hlTy).mp hB] at hmem

/-- The model element of a little-endian `Array UInt64` limb array (`BigNat`). -/
noncomputable def limbArraySet (M : Model V env) (tk : TowKeys) (ak : ArrayKeys)
    (φ : LevelParam → Nat) (xs : Array UInt64) : V :=
  arraySet M ak (M.cval tk.ty φ) (xs.toList.map fun u => towV M tk 64 size64 φ u.toNat)

/-- Every limb element in `xs` lies in `UInt64`. -/
theorem limbElems_mem (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env) (hE : EqBasis env)
    {tk : TowKeys} {kB kR kS : KKey} (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hU : UInt64Basis env tk) (φ : LevelParam → Nat) (xs : Array UInt64) :
    ∀ x ∈ xs.toList.map (fun u => towV M tk 64 size64 φ u.toNat), x ∈ˢ M.cval tk.ty φ := by
  intro x hx
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
  exact towV_mem_of_ofNat M hacc hN hE hBr hU φ (IxCC.BigNat.uint64_toNat_lt u)

/-- `limbArraySet M tk ak φ xs` lies in `Array.{0} UInt64`. -/
theorem limbArraySet_mem (M : Model V env) (hacc : NatAccel M) (hcv : CvalParams M)
    (hN : NatBasis env) (hE : EqBasis env) (hL : ListBasis env) {tk : TowKeys} {ak : ArrayKeys}
    {kB kR kS : KKey} (hBr : BridgeStored env tk 64 size64 kB kR kS) (hU : UInt64Basis env tk)
    (hA : ArrayBasis env ak) (φ : LevelParam → Nat) (xs : Array UInt64) :
    limbArraySet M tk ak φ xs ∈ˢ app (M.cval ak.array (fun _ => 0)) (M.cval tk.ty φ) := by
  have hT1 : M.cval tk.ty φ ∈ˢ (univ 1 : V) := by
    obtain ⟨ci, hf, _, ht⟩ := hU.ty
    obtain ⟨T, hT, hm⟩ := mem_key M hf φ (fun _ => empty)
    rw [ht] at hT
    simpa [Level.eval] using den_sort.mp hT ▸ hm
  exact arraySet_mem M hcv hL hA hT1 (limbElems_mem M hacc hN hE hBr hU φ xs)

/-- Keys for the `IxCC.BigNat` specification functions (`UInt64.toNat`, `getLimb`, `toNatPrefix`,
`toNat`, `WF`). -/
structure BigNatSpecKeys where
  uint64ToNat : KKey
  getLimb : KKey
  toNatPrefix : KKey
  toNat : KKey
  wf : KKey

/-- Stored specification equations for `UInt64.toNat`, `IxCC.BigNat.getLimb`, `toNatPrefix`, and
`toNat` in `M`. -/
structure ToNatModel (M : Model V env) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (φ : LevelParam → Nat) : Prop where
  uint64ToNat_eq : ∀ n : Nat, n < size64 →
    app (M.cval bn.uint64ToNat φ) (towV M tk 64 size64 φ n) = litSet M φ n
  getLimb_eq : ∀ (xs : Array UInt64) (i : Nat),
    app (app (M.cval bn.getLimb φ) (limbArraySet M tk ak φ xs)) (litSet M φ i) =
      towV M tk 64 size64 φ (IxCC.BigNat.getLimb xs i).toNat
  toNatPrefix_zero : ∀ xs : Array UInt64,
    app (app (M.cval bn.toNatPrefix φ) (limbArraySet M tk ak φ xs)) (litSet M φ 0) =
      litSet M φ 0
  toNatPrefix_succ : ∀ (xs : Array UInt64) (k : Nat),
    app (app (M.cval bn.toNatPrefix φ) (limbArraySet M tk ak φ xs)) (litSet M φ (k + 1)) =
      app (app (M.cval natAddName φ)
        (app (app (M.cval bn.toNatPrefix φ) (limbArraySet M tk ak φ xs)) (litSet M φ k)))
        (app (app (M.cval natMulName φ)
          (app (M.cval bn.uint64ToNat φ)
            (app (app (M.cval bn.getLimb φ) (limbArraySet M tk ak φ xs)) (litSet M φ k))))
          (app (app (M.cval natPowName φ) (litSet M φ size64)) (litSet M φ k)))
  toNat_eq : ∀ xs : Array UInt64,
    app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs) =
      app (app (M.cval bn.toNatPrefix φ) (limbArraySet M tk ak φ xs)) (litSet M φ xs.size)

/-- **`IxCC.BigNat.toNatPrefix` adequacy over `Ix.Kernel.Model`**: by induction on `k`,
`toNatPrefix (limbArraySet xs) (litSet k) = litSet (IxCC.BigNat.toNatPrefix xs k)`. -/
theorem toNatPrefix_limbArraySet (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {ciAdd ciMul ciPow : ConstantInfo .anon}
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ) (xs : Array UInt64) :
    ∀ k : Nat,
      app (app (M.cval bn.toNatPrefix φ) (limbArraySet M tk ak φ xs)) (litSet M φ k) =
        litSet M φ (IxCC.BigNat.toNatPrefix xs k)
  | 0 => hTN.toNatPrefix_zero xs
  | k + 1 => by
    have hMul := natPrimBin_accel M hacc hN (op := .mul) rfl hfMul hlMul φ
      (a := (IxCC.BigNat.getLimb xs k).toNat) (b := size64 ^ k) rfl
    have hAdd := natPrimBin_accel M hacc hN (op := .add) rfl hfAdd hlAdd φ
      (a := IxCC.BigNat.toNatPrefix xs k) (b := (IxCC.BigNat.getLimb xs k).toNat * size64 ^ k) rfl
    simp only [primKey] at hMul hAdd
    rw [hTN.toNatPrefix_succ xs k, toNatPrefix_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul
      hfPow hlPow φ hTN xs k, hTN.getLimb_eq xs k,
      hTN.uint64ToNat_eq _ (IxCC.BigNat.uint64_toNat_lt (IxCC.BigNat.getLimb xs k)),
      natPow_accel M hacc hN hfPow hlPow φ size64 k, hMul, hAdd]
    rfl

/-- **`IxCC.BigNat.toNat` adequacy over `Ix.Kernel.Model`**:
`toNat (limbArraySet xs) = litSet (IxCC.BigNat.toNat xs)`. -/
theorem toNat_limbArraySet (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {ciAdd ciMul ciPow : ConstantInfo .anon}
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ) (xs : Array UInt64) :
    app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs) =
      litSet M φ (IxCC.BigNat.toNat xs) := by
  rw [hTN.toNat_eq xs, toNatPrefix_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ
    hTN xs xs.size]
  rfl

/-- A stored Layer-1 binary `BigNat` correctness theorem in `env`:
`∀ (a b : Array.{0} UInt64), @Eq.{1} Nat (toNat (kOp a b)) (natOp (toNat a) (toNat b))`. -/
def BigNatBinThmStored (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kOp kNatOp kThm : KKey) : Prop :=
  ∃ (ci : ConstantInfo .anon) (mb1 mb2 : BinderMeta),
    env.find? kThm = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
        (.forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
          (eqE (.succ .zero) (.const natName [])
            (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 1)) (.bvar 0)))
            (.app (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 1)))
              (.app (.const bn.toNat []) (.bvar 0)))) mb2) mb1

/-- Decidable check for `BigNatBinThmStored`. -/
def bigNatBinThmB (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kOp kNatOp kThm : KKey) : Bool :=
  match env.find? kThm with
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
    match ci.toConstantVal.type with
    | .forallE d1 (.forallE d2 body _) _ =>
      let arrU64 : KExpr := .app (.const ak.array [.zero]) (.const tk.ty [])
      let expected : KExpr := eqE (.succ .zero) (.const natName [])
        (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 1)) (.bvar 0)))
        (.app (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 1)))
          (.app (.const bn.toNat []) (.bvar 0)))
      decide (d1 = arrU64) && decide (d2 = arrU64) && decide (body = expected)
    | _ => false
  | none => false

theorem bigNatBinThm_of_check {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kOp kNatOp kThm : KKey} (h : bigNatBinThmB env tk ak bn kOp kNatOp kThm = true) :
    BigNatBinThmStored env tk ak bn kOp kNatOp kThm := by
  unfold bigNatBinThmB at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨hlp, hty⟩ := h
    cases ht : ci.toConstantVal.type with
    | forallE d1 b1 mb1 =>
      rw [ht] at hty
      cases b1 with
      | forallE d2 body mb2 =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hty
        obtain ⟨⟨hd1, hd2⟩, hbody⟩ := hty
        exact ⟨ci, mb1, mb2, hf, hlp, by rw [ht, hd1, hd2, hbody]⟩
      | _ => simp at hty
    | _ => rw [ht] at hty; simp at hty
  · cases h

/-- Instantiate a stored Layer-1 binary `BigNat` theorem in any `Ix.Kernel.Model` (via
`eq_of_inhabited_pt`: no separate membership premises on the two sides are needed). -/
theorem bigNatBinThm_eval (M : Model V env) (hacc : NatAccel M) (hcv : CvalParams M)
    (hN : NatBasis env) (hE : EqBasis env) (hL : ListBasis env) {tk : TowKeys} {ak : ArrayKeys}
    {bn : BigNatSpecKeys} {kB kR kS kOp kNatOp kThm : KKey}
    {ciToNat ciOp ciNatOp : ConstantInfo .anon}
    (hBr : BridgeStored env tk 64 size64 kB kR kS) (hU : UInt64Basis env tk)
    (hA : ArrayBasis env ak)
    (hfTN : env.find? bn.toNat = some ciToNat) (hlTN : ciToNat.toConstantVal.levelParams = [])
    (hfOp : env.find? kOp = some ciOp) (hlOp : ciOp.toConstantVal.levelParams = [])
    (hfNO : env.find? kNatOp = some ciNatOp) (hlNO : ciNatOp.toConstantVal.levelParams = [])
    (hThm : BigNatBinThmStored env tk ak bn kOp kNatOp kThm)
    (φ : LevelParam → Nat) (xs ys : Array UInt64) :
    app (M.cval bn.toNat φ)
      (app (app (M.cval kOp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys)) =
    app (app (M.cval kNatOp φ) (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs)))
      (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ ys)) := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨ciT, hfT, hlpT, _⟩ := hU.ty
  obtain ⟨ciThm, mb1, mb2, hfThm, _, htyThm⟩ := hThm
  have hDom : ∀ ρ' : BVarIdx → V,
      Denotes M.cval env φ ρ' (.app (.const ak.array [.zero]) (.const tk.ty []))
        (app (M.cval ak.array (fun _ => 0)) (M.cval tk.ty φ)) := fun _ =>
    .app ((den_const_zero1 hcv hfA hlpA).mpr rfl) ((den_const0 hfT hlpT).mpr rfl)
  have hxsM := limbArraySet_mem M hacc hcv hN hE hL hBr hU hA φ xs
  have hysM := limbArraySet_mem M hacc hcv hN hE hL hBr hU hA φ ys
  obtain ⟨T0, hT0, hm0⟩ := mem_key M hfThm φ (fun _ => empty)
  rw [htyThm] at hT0
  obtain ⟨T1, hT1, hm1⟩ := app_mem_den_pi hT0 (hDom _) hm0 hxsM
  obtain ⟨T2, hT2, hm2⟩ := app_mem_den_pi hT1 (hDom _) hm1 hysM
  have hLhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ ys)
      (push (limbArraySet M tk ak φ xs) (fun _ => empty)))
      (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 1)) (.bvar 0)))
      (app (M.cval bn.toNat φ)
        (app (app (M.cval kOp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys))) :=
    .app ((den_const0 hfTN hlTN).mpr rfl)
      (.app (.app ((den_const0 hfOp hlOp).mpr rfl) .bvar) .bvar)
  have hRhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ ys)
      (push (limbArraySet M tk ak φ xs) (fun _ => empty)))
      (.app (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 1)))
        (.app (.const bn.toNat []) (.bvar 0)))
      (app (app (M.cval kNatOp φ) (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs)))
        (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ ys))) :=
    .app (.app ((den_const0 hfNO hlNO).mpr rfl)
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar))
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar)
  obtain ⟨⟨x, hxL, hxR⟩, _⟩ := eq_of_inhabited_pt M hE hT2 hm2
  exact (Denotes_functional hLhsD hxL).trans (Denotes_functional hxR hRhsD)

/-- **Layer-1 × Layer-3 composition for binary `BigNat` arithmetic operations** directly over
`Ix.Kernel.Model`: if `kOp` applied to `limbArraySet xs` and `limbArraySet ys` equals
`limbArraySet zs` in `M`, then the stored Layer-1 theorem + `toNat_limbArraySet` + `NatAccel` +
`litSet_inj` imply the exact meta-level `Nat` equality `IxCC.BigNat.toNat zs = r`. -/
theorem bigNat_binop_layer3_sound (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) (hL : ListBasis env)
    (hBeq : NatBeqStored env) {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kB kR kS kNe kOp kThm : KKey} {op : PrimOp}
    {ciAdd ciMul ciPow ciToNat ciOp ciNatOp : ConstantInfo .anon}
    (hNe : BoolTrueNeFalseStored env kNe) (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hU : UInt64Basis env tk) (hA : ArrayBasis env ak) (har : op.arity = 2)
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (hfTN : env.find? bn.toNat = some ciToNat) (hlTN : ciToNat.toConstantVal.levelParams = [])
    (hfOp : env.find? kOp = some ciOp) (hlOp : ciOp.toConstantVal.levelParams = [])
    (hfNO : env.find? (primKey op) = some ciNatOp) (hlNO : ciNatOp.toConstantVal.levelParams = [])
    (hThm : BigNatBinThmStored env tk ak bn kOp (primKey op) kThm)
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ)
    {xs ys zs : Array UInt64} {r : Nat}
    (hev : op.eval2 (IxCC.BigNat.toNat xs) (IxCC.BigNat.toNat ys) = .nat r)
    (hModelEq : app (app (M.cval kOp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys) =
      limbArraySet M tk ak φ zs) :
    IxCC.BigNat.toNat zs = r := by
  have h1 := bigNatBinThm_eval M hacc M.cval_params hN hE hL hBr hU hA hfTN hlTN hfOp hlOp hfNO hlNO
    hThm φ xs ys
  rw [hModelEq,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN zs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN xs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN ys,
    natPrimBin_accel M hacc hN har hfNO hlNO φ hev] at h1
  exact litSet_inj M hacc hN hB hBeq (bool_true_ne_false M hE hB hNe φ) h1

/-- A stored `WF`-guarded Layer-1 binary `BigNat` correctness theorem in `env`:
`∀ (a b : Array.{0} UInt64), WF a → WF b → @Eq.{1} Nat (toNat (kOp a b)) (natOp (toNat a) (toNat b))`. -/
def BigNatBinWFThmStored (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kOp kNatOp kThm : KKey) : Prop :=
  ∃ (ci : ConstantInfo .anon) (mb1 mb2 mb3 mb4 : BinderMeta),
    env.find? kThm = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
        (.forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
          (.forallE (.app (.const bn.wf []) (.bvar 1))
            (.forallE (.app (.const bn.wf []) (.bvar 1))
              (eqE (.succ .zero) (.const natName [])
                (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 3)) (.bvar 2)))
                (.app (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 3)))
                  (.app (.const bn.toNat []) (.bvar 2)))) mb4) mb3) mb2) mb1

/-- Decidable check for `BigNatBinWFThmStored`. -/
def bigNatBinWFThmB (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kOp kNatOp kThm : KKey) : Bool :=
  match env.find? kThm with
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
    match ci.toConstantVal.type with
    | .forallE d1 (.forallE d2 (.forallE d3 (.forallE d4 body _) _) _) _ =>
      let arrU64 : KExpr := .app (.const ak.array [.zero]) (.const tk.ty [])
      let expected : KExpr := eqE (.succ .zero) (.const natName [])
        (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 3)) (.bvar 2)))
        (.app (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 3)))
          (.app (.const bn.toNat []) (.bvar 2)))
      decide (d1 = arrU64) && decide (d2 = arrU64) &&
      decide (d3 = .app (.const bn.wf []) (.bvar 1)) &&
      decide (d4 = .app (.const bn.wf []) (.bvar 1)) &&
      decide (body = expected)
    | _ => false
  | none => false

theorem bigNatBinWFThm_of_check {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kOp kNatOp kThm : KKey} (h : bigNatBinWFThmB env tk ak bn kOp kNatOp kThm = true) :
    BigNatBinWFThmStored env tk ak bn kOp kNatOp kThm := by
  unfold bigNatBinWFThmB at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨hlp, hty⟩ := h
    cases ht : ci.toConstantVal.type with
    | forallE d1 b1 mb1 =>
      rw [ht] at hty
      cases b1 with
      | forallE d2 b2 mb2 =>
        cases b2 with
        | forallE d3 b3 mb3 =>
          cases b3 with
          | forallE d4 body mb4 =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hty
            obtain ⟨⟨⟨⟨hd1, hd2⟩, hd3⟩, hd4⟩, hbody⟩ := hty
            exact ⟨ci, mb1, mb2, mb3, mb4, hf, hlp, by rw [ht, hd1, hd2, hd3, hd4, hbody]⟩
          | _ => simp at hty
        | _ => simp at hty
      | _ => simp at hty
    | _ => rw [ht] at hty; simp at hty
  · cases h

/-- **`WF`-guarded Layer-1 × Layer-3 composition for binary `BigNat` operations.** -/
theorem bigNat_binop_layer3_wf_sound (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) (hL : ListBasis env)
    (hBeq : NatBeqStored env) {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kB kR kS kNe kOp kThm : KKey} {op : PrimOp}
    {ciAdd ciMul ciPow ciToNat ciOp ciNatOp ciWF : ConstantInfo .anon}
    (hNe : BoolTrueNeFalseStored env kNe) (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hU : UInt64Basis env tk) (hA : ArrayBasis env ak) (har : op.arity = 2)
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (hfTN : env.find? bn.toNat = some ciToNat) (hlTN : ciToNat.toConstantVal.levelParams = [])
    (hfOp : env.find? kOp = some ciOp) (hlOp : ciOp.toConstantVal.levelParams = [])
    (hfNO : env.find? (primKey op) = some ciNatOp) (hlNO : ciNatOp.toConstantVal.levelParams = [])
    (hfWF : env.find? bn.wf = some ciWF) (hlWF : ciWF.toConstantVal.levelParams = [])
    (hThm : BigNatBinWFThmStored env tk ak bn kOp (primKey op) kThm)
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ)
    {xs ys zs : Array UInt64} {r : Nat} {px py : V}
    (hpx : px ∈ˢ app (M.cval bn.wf φ) (limbArraySet M tk ak φ xs))
    (hpy : py ∈ˢ app (M.cval bn.wf φ) (limbArraySet M tk ak φ ys))
    (hev : op.eval2 (IxCC.BigNat.toNat xs) (IxCC.BigNat.toNat ys) = .nat r)
    (hModelEq : app (app (M.cval kOp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys) =
      limbArraySet M tk ak φ zs) :
    IxCC.BigNat.toNat zs = r := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨ciT, hfT, hlpT, _⟩ := hU.ty
  obtain ⟨ciThm, mb1, mb2, mb3, mb4, hfThm, _, htyThm⟩ := hThm
  have hDom : ∀ ρ' : BVarIdx → V,
      Denotes M.cval env φ ρ' (.app (.const ak.array [.zero]) (.const tk.ty []))
        (app (M.cval ak.array (fun _ => 0)) (M.cval tk.ty φ)) := fun _ =>
    .app ((den_const_zero1 M.cval_params hfA hlpA).mpr rfl) ((den_const0 hfT hlpT).mpr rfl)
  have hxsM := limbArraySet_mem M hacc M.cval_params hN hE hL hBr hU hA φ xs
  have hysM := limbArraySet_mem M hacc M.cval_params hN hE hL hBr hU hA φ ys
  obtain ⟨T0, hT0, hm0⟩ := mem_key M hfThm φ (fun _ => empty)
  rw [htyThm] at hT0
  obtain ⟨T1, hT1, hm1⟩ := app_mem_den_pi hT0 (hDom _) hm0 hxsM
  obtain ⟨T2, hT2, hm2⟩ := app_mem_den_pi hT1 (hDom _) hm1 hysM
  obtain ⟨T3, hT3, hm3⟩ :=
    app_mem_den_pi hT2 (.app ((den_const0 hfWF hlWF).mpr rfl) .bvar) hm2 hpx
  obtain ⟨T4, hT4, hm4⟩ :=
    app_mem_den_pi hT3 (.app ((den_const0 hfWF hlWF).mpr rfl) .bvar) hm3 hpy
  let ρ4 := push py (push px (push (limbArraySet M tk ak φ ys)
    (push (limbArraySet M tk ak φ xs) (fun _ => empty))))
  have hLhsD : Denotes M.cval env φ ρ4
      (.app (.const bn.toNat []) (.app (.app (.const kOp []) (.bvar 3)) (.bvar 2)))
      (app (M.cval bn.toNat φ)
        (app (app (M.cval kOp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys))) :=
    .app ((den_const0 hfTN hlTN).mpr rfl)
      (.app (.app ((den_const0 hfOp hlOp).mpr rfl) .bvar) .bvar)
  have hRhsD : Denotes M.cval env φ ρ4
      (.app (.app (.const (primKey op) []) (.app (.const bn.toNat []) (.bvar 3)))
        (.app (.const bn.toNat []) (.bvar 2)))
      (app (app (M.cval (primKey op) φ) (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs)))
        (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ ys))) :=
    .app (.app ((den_const0 hfNO hlNO).mpr rfl)
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar))
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar)
  obtain ⟨⟨x, hxL, hxR⟩, _⟩ := eq_of_inhabited_pt M hE hT4 hm4
  have h1 := (Denotes_functional hLhsD hxL).trans (Denotes_functional hxR hRhsD)
  rw [hModelEq,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN zs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN xs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN ys,
    natPrimBin_accel M hacc hN har hfNO hlNO φ hev] at h1
  exact litSet_inj M hacc hN hB hBeq (bool_true_ne_false M hE hB hNe φ) h1

/-- A stored Layer-1 binary `BigNat` comparison theorem in `env`:
`∀ (a b : Array.{0} UInt64), @Eq.{1} Bool (kCmp a b) (kNatCmp (toNat a) (toNat b))`. -/
def BigNatCmpThmStored (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kCmp kNatCmp kThm : KKey) : Prop :=
  ∃ (ci : ConstantInfo .anon) (mb1 mb2 : BinderMeta),
    env.find? kThm = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
        (.forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
          (eqE (.succ .zero) (.const boolKey [])
            (.app (.app (.const kCmp []) (.bvar 1)) (.bvar 0))
            (.app (.app (.const kNatCmp []) (.app (.const bn.toNat []) (.bvar 1)))
              (.app (.const bn.toNat []) (.bvar 0)))) mb2) mb1

/-- Decidable check for `BigNatCmpThmStored`. -/
def bigNatCmpThmB (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kCmp kNatCmp kThm : KKey) : Bool :=
  match env.find? kThm with
  | some ci =>
    ci.toConstantVal.levelParams.isEmpty &&
    match ci.toConstantVal.type with
    | .forallE d1 (.forallE d2 body _) _ =>
      let arrU64 : KExpr := .app (.const ak.array [.zero]) (.const tk.ty [])
      let expected : KExpr := eqE (.succ .zero) (.const boolKey [])
        (.app (.app (.const kCmp []) (.bvar 1)) (.bvar 0))
        (.app (.app (.const kNatCmp []) (.app (.const bn.toNat []) (.bvar 1)))
          (.app (.const bn.toNat []) (.bvar 0)))
      decide (d1 = arrU64) && decide (d2 = arrU64) && decide (body = expected)
    | _ => false
  | none => false

theorem bigNatCmpThm_of_check {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kCmp kNatCmp kThm : KKey} (h : bigNatCmpThmB env tk ak bn kCmp kNatCmp kThm = true) :
    BigNatCmpThmStored env tk ak bn kCmp kNatCmp kThm := by
  unfold bigNatCmpThmB at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    obtain ⟨hlp, hty⟩ := h
    cases ht : ci.toConstantVal.type with
    | forallE d1 b1 mb1 =>
      rw [ht] at hty
      cases b1 with
      | forallE d2 body mb2 =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hty
        obtain ⟨⟨hd1, hd2⟩, hbody⟩ := hty
        exact ⟨ci, mb1, mb2, hf, hlp, by rw [ht, hd1, hd2, hbody]⟩
      | _ => simp at hty
    | _ => rw [ht] at hty; simp at hty
  · cases h

/-- **Layer-1 × Layer-3 composition for binary `BigNat` comparisons** (`beq`, `ble`) directly over
`Ix.Kernel.Model`: concludes the exact meta-level `Bool` equality `b = res`. -/
theorem bigNat_cmp_layer3_sound (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) (hL : ListBasis env)
    {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kB kR kS kNe kCmp kThm : KKey} {op : PrimOp}
    {ciAdd ciMul ciPow ciToNat ciCmp ciNatCmp : ConstantInfo .anon}
    (hNe : BoolTrueNeFalseStored env kNe) (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hU : UInt64Basis env tk) (hA : ArrayBasis env ak) (har : op.arity = 2)
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (hfTN : env.find? bn.toNat = some ciToNat) (hlTN : ciToNat.toConstantVal.levelParams = [])
    (hfCmp : env.find? kCmp = some ciCmp) (hlCmp : ciCmp.toConstantVal.levelParams = [])
    (hfNC : env.find? (primKey op) = some ciNatCmp) (hlNC : ciNatCmp.toConstantVal.levelParams = [])
    (hThm : BigNatCmpThmStored env tk ak bn kCmp (primKey op) kThm)
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ)
    {xs ys : Array UInt64} {b res : Bool}
    (hev : op.eval2 (IxCC.BigNat.toNat xs) (IxCC.BigNat.toNat ys) = .bool res)
    (hModelEq : app (app (M.cval kCmp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys) =
      boolSet M φ b) :
    b = res := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨ciT, hfT, hlpT, _⟩ := hU.ty
  obtain ⟨ciThm, mb1, mb2, hfThm, _, htyThm⟩ := hThm
  have hDom : ∀ ρ' : BVarIdx → V,
      Denotes M.cval env φ ρ' (.app (.const ak.array [.zero]) (.const tk.ty []))
        (app (M.cval ak.array (fun _ => 0)) (M.cval tk.ty φ)) := fun _ =>
    .app ((den_const_zero1 M.cval_params hfA hlpA).mpr rfl) ((den_const0 hfT hlpT).mpr rfl)
  have hxsM := limbArraySet_mem M hacc M.cval_params hN hE hL hBr hU hA φ xs
  have hysM := limbArraySet_mem M hacc M.cval_params hN hE hL hBr hU hA φ ys
  obtain ⟨T0, hT0, hm0⟩ := mem_key M hfThm φ (fun _ => empty)
  rw [htyThm] at hT0
  obtain ⟨T1, hT1, hm1⟩ := app_mem_den_pi hT0 (hDom _) hm0 hxsM
  obtain ⟨T2, hT2, hm2⟩ := app_mem_den_pi hT1 (hDom _) hm1 hysM
  have hLhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ ys)
      (push (limbArraySet M tk ak φ xs) (fun _ => empty)))
      (.app (.app (.const kCmp []) (.bvar 1)) (.bvar 0))
      (app (app (M.cval kCmp φ) (limbArraySet M tk ak φ xs)) (limbArraySet M tk ak φ ys)) :=
    .app (.app ((den_const0 hfCmp hlCmp).mpr rfl) .bvar) .bvar
  have hRhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ ys)
      (push (limbArraySet M tk ak φ xs) (fun _ => empty)))
      (.app (.app (.const (primKey op) []) (.app (.const bn.toNat []) (.bvar 1)))
        (.app (.const bn.toNat []) (.bvar 0)))
      (app (app (M.cval (primKey op) φ) (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs)))
        (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ ys))) :=
    .app (.app ((den_const0 hfNC hlNC).mpr rfl)
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar))
      (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar)
  obtain ⟨⟨x, hxL, hxR⟩, _⟩ := eq_of_inhabited_pt M hE hT2 hm2
  have h1 := (Denotes_functional hLhsD hxL).trans (Denotes_functional hxR hRhsD)
  rw [hModelEq,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN xs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN ys,
    natPrimCmp_accel M hacc hN hB har hfNC hlNC φ hev] at h1
  exact boolSet_inj (bool_true_ne_false M hE hB hNe φ) h1

/-- A stored Layer-1 unary `BigNat` theorem in `env` (`pred`, `log2`, `sqr`):
`∀ (a : Array.{0} UInt64), @Eq.{1} Nat (toNat (kOp a)) (kNatOp (toNat a))`. -/
def BigNatUnThmStored (env : KEnv) (tk : TowKeys) (ak : ArrayKeys) (bn : BigNatSpecKeys)
    (kOp kNatOp kThm : KKey) : Prop :=
  ∃ (ci : ConstantInfo .anon) (mb1 : BinderMeta),
    env.find? kThm = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type =
      .forallE (.app (.const ak.array [.zero]) (.const tk.ty []))
        (eqE (.succ .zero) (.const natName [])
          (.app (.const bn.toNat []) (.app (.const kOp []) (.bvar 0)))
          (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 0)))) mb1

/-- **Layer-1 × Layer-3 composition for unary `BigNat` operations** (`pred`, `log2`, `sqr`). -/
theorem bigNat_unop_layer3_sound (M : Model V env) (hacc : NatAccel M) (hN : NatBasis env)
    (hB : BoolBasis env) (hE : EqBasis env) (hL : ListBasis env)
    (hBeq : NatBeqStored env) {tk : TowKeys} {ak : ArrayKeys} {bn : BigNatSpecKeys}
    {kB kR kS kNe kOp kNatOp kThm : KKey}
    {ciAdd ciMul ciPow ciToNat ciOp ciNatOp : ConstantInfo .anon}
    (hNe : BoolTrueNeFalseStored env kNe) (hBr : BridgeStored env tk 64 size64 kB kR kS)
    (hU : UInt64Basis env tk) (hA : ArrayBasis env ak)
    (hfAdd : env.find? natAddName = some ciAdd) (hlAdd : ciAdd.toConstantVal.levelParams = [])
    (hfMul : env.find? natMulName = some ciMul) (hlMul : ciMul.toConstantVal.levelParams = [])
    (hfPow : env.find? natPowName = some ciPow) (hlPow : ciPow.toConstantVal.levelParams = [])
    (hfTN : env.find? bn.toNat = some ciToNat) (hlTN : ciToNat.toConstantVal.levelParams = [])
    (hfOp : env.find? kOp = some ciOp) (hlOp : ciOp.toConstantVal.levelParams = [])
    (hfNO : env.find? kNatOp = some ciNatOp) (hlNO : ciNatOp.toConstantVal.levelParams = [])
    (hThm : BigNatUnThmStored env tk ak bn kOp kNatOp kThm)
    (φ : LevelParam → Nat) (hTN : ToNatModel M tk ak bn φ)
    (f : Nat → Nat) (hfEval : ∀ n, app (M.cval kNatOp φ) (litSet M φ n) = litSet M φ (f n))
    {xs zs : Array UInt64}
    (hModelEq : app (M.cval kOp φ) (limbArraySet M tk ak φ xs) = limbArraySet M tk ak φ zs) :
    IxCC.BigNat.toNat zs = f (IxCC.BigNat.toNat xs) := by
  obtain ⟨cvA, caps, _, hfA, hlpA, _⟩ := hA.array
  obtain ⟨ciT, hfT, hlpT, _⟩ := hU.ty
  obtain ⟨ciThm, mb1, hfThm, _, htyThm⟩ := hThm
  have hDom : Denotes M.cval env φ (fun _ => empty)
      (.app (.const ak.array [.zero]) (.const tk.ty []))
      (app (M.cval ak.array (fun _ => 0)) (M.cval tk.ty φ)) :=
    .app ((den_const_zero1 M.cval_params hfA hlpA).mpr rfl) ((den_const0 hfT hlpT).mpr rfl)
  have hxsM := limbArraySet_mem M hacc M.cval_params hN hE hL hBr hU hA φ xs
  obtain ⟨T0, hT0, hm0⟩ := mem_key M hfThm φ (fun _ => empty)
  rw [htyThm] at hT0
  obtain ⟨T1, hT1, hm1⟩ := app_mem_den_pi hT0 hDom hm0 hxsM
  have hLhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ xs) (fun _ => empty))
      (.app (.const bn.toNat []) (.app (.const kOp []) (.bvar 0)))
      (app (M.cval bn.toNat φ) (app (M.cval kOp φ) (limbArraySet M tk ak φ xs))) :=
    .app ((den_const0 hfTN hlTN).mpr rfl) (.app ((den_const0 hfOp hlOp).mpr rfl) .bvar)
  have hRhsD : Denotes M.cval env φ (push (limbArraySet M tk ak φ xs) (fun _ => empty))
      (.app (.const kNatOp []) (.app (.const bn.toNat []) (.bvar 0)))
      (app (M.cval kNatOp φ) (app (M.cval bn.toNat φ) (limbArraySet M tk ak φ xs))) :=
    .app ((den_const0 hfNO hlNO).mpr rfl) (.app ((den_const0 hfTN hlTN).mpr rfl) .bvar)
  obtain ⟨⟨x, hxL, hxR⟩, _⟩ := eq_of_inhabited_pt M hE hT1 hm1
  have h1 := (Denotes_functional hLhsD hxL).trans (Denotes_functional hxR hRhsD)
  rw [hModelEq,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN zs,
    toNat_limbArraySet M hacc hN hfAdd hlAdd hfMul hlMul hfPow hlPow φ hTN xs,
    hfEval] at h1
  exact litSet_inj M hacc hN hB hBeq (bool_true_ne_false M hE hB hNe φ) h1

end ArraySem

end IxCC.Grounding
