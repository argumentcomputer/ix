import IxCCAiur.FieldLower
import IxCCAiur.InlineFuseProof
import IxCCAiur.TypedGadgets
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! # Certified Soundness of Phase 3.4 Ambient-Field Lowering (`IxCCAiur.FieldLowerProof`)

Proves end-to-end semantic correctness and backward `EvalFn` soundness of
`IxCC.AiurBackend.FieldLower` over **any** prime field `ZMod p` (`[Fact (Nat.Prime p)]`):

1. **Modular `Nat` ↔ `ZMod p` arithmetic identities**:
   Exact correspondence between native `ZMod p` operations (`+`, `-`, `*`,
   `0 - a`, total `a⁻¹` with `0⁻¹ = 0` and Fermat `a^(p - 2) % p`, `a = 0`,
   `a = b`) and modular natural arithmetic `(a + b) % p`, `(a + p - b) % p`,
   `(a * b) % p`, `(p - a) % p`, `if a == 0 then 0 else p - a` on canonical
   inputs `< p`. Also establishes `FieldCompatible64` for BN254 `Fr` and
   BLS12-381 `Fr` alongside Goldilocks `p_G`.
2. **`Fields::is_zero` operational contract (`FieldsIsZeroSpec`)**:
   Bidirectional soundness + completeness directly from `checkFieldsIsZero`.
3. **Exact `EvalExpr` / `EvalFn` correctness for all 8 native `FieldOp`s**:
   Proves exact `EvalExpr` characterizations (and modular `Nat` corollaries) for
   `fieldAddE`, `fieldSubE`, `fieldMulE`, `fieldNegE`, `fieldInvVarE`/`fieldInvE`,
   `fieldDivVarsE`/`fieldDivE`, `fieldIsZeroE`, and `fieldEqE` over arbitrary
   `ZMod p` (`[Fact (Nat.Prime p)]`).
4. **Backward `EvalExpr` & `EvalFn` soundness of `lowerFieldOps` + `pruneUnreachable`**:
   Proves backward simulation for `lowerCall`, `lowerProject`, `lowerLetValue`,
   `lowerMatchValue`, `lowerFieldExpr`, `lowerFieldFn`, `lowerFieldOpsCore`,
   and full `lowerFieldOps` (with `pruneUnreachable`) over arbitrary `ZMod p`.
5. **3-field concrete corollaries & axiom pins**:
   Instantiates concrete corollaries at **Goldilocks (`p_G`)**, **BN254 (`Fr`)**,
   and **BLS12-381 (`Fr`)**, pinned with `#guard_msgs in #print axioms` to
   strictly `[propext, Classical.choice, Quot.sound]`.

Strictly zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`,
zero `bv_decide`, zero `partial`, zero `unsafe`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.FieldLowerProof

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn natLimit qualified qualifyName qualifyPat qualifyExpr qualifyPatF qualifyExprF
   hasDoubleColon allDistinct allDistinct_iff_nodup isPlainExpr isPlainExpr_qualifyExprF
   vE litE letE matchE callE)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn evalFn_plain_inv evalExpr_literal_inv evalExpr_var_inv evalExpr_binary_inv
   evalExpr_call1_inv evalExpr_tuple2_inv
   evalExpr_let_bind_inv evalExpr_let_tuple2_inv)
open IxCC.AiurBackend.TypedGadgets
  (FieldCompatible64 fieldBound64 evalExpr_match_lit_wild_inv)
open IxCC.AiurBackend.InlineFuse (pruneUnreachable)
open IxCC.AiurBackend.InlineFuseProof
  (SameAuxWorld WorldHasFns WorldProvidesFns
   pruneUnreachable_backward world_transformBodies_backward
   map_qualifyExprF map_qualifyArmsF)
open IxCC.AiurBackend.FieldLower

/-! ## Section 1: Pure `ZMod p` ↔ Modular `Nat` Arithmetic Identities (`[Fact (Nat.Prime p)]`) -/

section ZModArithmetic

variable {p : Nat} [Fact (Nat.Prime p)]

theorem prime_two_le : 2 ≤ p := (Fact.out : Nat.Prime p).two_le

theorem prime_pos : 0 < p := (Fact.out : Nat.Prime p).pos

theorem zmod_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero

theorem zmod_zero_ne_one : (0 : ZMod p) ≠ (1 : ZMod p) := zero_ne_one

/-- Native `ZMod p` addition matches `(a + b) % p`. -/
theorem zmod_add_eq_mod (a b : Nat) :
    ((a : ZMod p) + (b : ZMod p)) = (((a + b) % p : Nat) : ZMod p) := by
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- Canonical `.val` of native `ZMod p` addition is `(a + b) % p`. -/
theorem zmod_add_val (a b : Nat) :
    ((a : ZMod p) + (b : ZMod p)).val = (a + b) % p := by
  rw [zmod_add_eq_mod, ZMod.val_natCast_of_lt (Nat.mod_lt _ prime_pos)]

/-- Native `ZMod p` subtraction matches `(a + p - b) % p` for any `b ≤ p`. -/
theorem zmod_sub_eq_mod {a b : Nat} (hb : b ≤ p) :
    ((a : ZMod p) - (b : ZMod p)) = (((a + p - b) % p : Nat) : ZMod p) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega : b ≤ a + p), Nat.cast_add,
      ZMod.natCast_self, add_zero]

/-- Canonical `.val` of native `ZMod p` subtraction is `(a + p - b) % p` for `b ≤ p`. -/
theorem zmod_sub_val {a b : Nat} (hb : b ≤ p) :
    ((a : ZMod p) - (b : ZMod p)).val = (a + p - b) % p := by
  rw [zmod_sub_eq_mod hb, ZMod.val_natCast_of_lt (Nat.mod_lt _ prime_pos)]

/-- Native `ZMod p` multiplication matches `(a * b) % p`. -/
theorem zmod_mul_eq_mod (a b : Nat) :
    ((a : ZMod p) * (b : ZMod p)) = (((a * b) % p : Nat) : ZMod p) := by
  rw [ZMod.natCast_mod]
  push_cast
  rfl

/-- Canonical `.val` of native `ZMod p` multiplication is `(a * b) % p`. -/
theorem zmod_mul_val (a b : Nat) :
    ((a : ZMod p) * (b : ZMod p)).val = (a * b) % p := by
  rw [zmod_mul_eq_mod, ZMod.val_natCast_of_lt (Nat.mod_lt _ prime_pos)]

/-- Native `ZMod p` negation `0 - a` matches `(p - a) % p` for any `a ≤ p`. -/
theorem zmod_neg_eq_mod {a : Nat} (ha : a ≤ p) :
    (0 - (a : ZMod p)) = (((p - a) % p : Nat) : ZMod p) := by
  have h := zmod_sub_eq_mod (p := p) (a := 0) ha
  simpa using h

/-- Native `ZMod p` negation `0 - a` matches `if a == 0 then 0 else p - a` on canonical `a < p`. -/
theorem zmod_neg_eq_ite {a : Nat} (ha : a < p) :
    (0 - (a : ZMod p)) = ((if a == 0 then 0 else p - a : Nat) : ZMod p) := by
  rw [zmod_neg_eq_mod (Nat.le_of_lt ha)]
  by_cases h0 : a = 0
  · subst h0; simp
  · have hlt : p - a < p := by omega
    simp [h0, Nat.mod_eq_of_lt hlt]

/-- Canonical `.val` of native `ZMod p` negation `0 - a` is `(p - a) % p` for `a ≤ p`. -/
theorem zmod_neg_val {a : Nat} (ha : a ≤ p) :
    (0 - (a : ZMod p)).val = (p - a) % p := by
  rw [zmod_neg_eq_mod ha, ZMod.val_natCast_of_lt (Nat.mod_lt _ prime_pos)]

/-- Total inverse branch `if x = 0 then 0 else 1 / x` equals Lean's `x⁻¹` (with `0⁻¹ = 0`). -/
theorem zmod_inv_total (x : ZMod p) :
    (if x = 0 then (0 : ZMod p) else (1 : ZMod p) / x) = x⁻¹ := by
  by_cases h : x = 0
  · subst h; simp
  · simp [h, one_div]

/-- Total division branch `if y = 0 then 0 else x / y` equals Lean's `x / y` (with `x / 0 = 0`). -/
theorem zmod_div_total (x y : ZMod p) :
    (if y = 0 then (0 : ZMod p) else x / y) = x / y := by
  by_cases h : y = 0
  · subst h; simp
  · simp [h]

/-- Fermat's Little Theorem correspondence: for any odd prime `p ≥ 3`,
`a^(p - 2) % p` in `ZMod p` equals Lean's total inverse `(a : ZMod p)⁻¹` (including `0 ↦ 0`). -/
theorem zmod_inv_eq_fermat (hp3 : 3 ≤ p) (a : Nat) :
    ((a ^ (p - 2) % p : Nat) : ZMod p) = (a : ZMod p)⁻¹ := by
  rw [ZMod.natCast_mod, Nat.cast_pow]
  by_cases h0 : (a : ZMod p) = 0
  · rw [h0, inv_zero, zero_pow (by omega : p - 2 ≠ 0)]
  · have hfermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
    have hexp : p - 1 = (p - 2) + 1 := by omega
    rw [hexp, pow_succ] at hfermat
    exact mul_right_cancel₀ h0 (by rw [hfermat, inv_mul_cancel₀ h0])

/-- Canonical zero-test correspondence: `(a : ZMod p) = 0 ↔ a = 0` for `a < p`. -/
theorem zmod_isZero_iff {a : Nat} (ha : a < p) :
    ((a : ZMod p) = 0) ↔ a = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv
    exact hv
  · intro h; subst h; simp

/-- Canonical zero-test indicator: `(if (a : ZMod p) = 0 then 1 else 0)` matches `a == 0`. -/
theorem zmod_isZero_nat {a : Nat} (ha : a < p) :
    (if (a : ZMod p) = 0 then (1 : ZMod p) else 0) = ((if a == 0 then 1 else 0 : Nat) : ZMod p) := by
  by_cases h0 : a = 0
  · subst h0; simp
  · have hne : (a : ZMod p) ≠ 0 := fun hz => h0 ((zmod_isZero_iff ha).mp hz)
    simp [h0, hne]

/-- Canonical equality correspondence: `(a : ZMod p) = (b : ZMod p) ↔ a = b` for `a, b < p`. -/
theorem zmod_eq_iff {a b : Nat} (ha : a < p) (hb : b < p) :
    ((a : ZMod p) = (b : ZMod p)) ↔ a = b := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
    exact hv
  · intro h; subst h; rfl

/-- Canonical equality indicator: `(if (a : ZMod p) = (b : ZMod p) then 1 else 0)` matches `a == b`. -/
theorem zmod_eq_nat {a b : Nat} (ha : a < p) (hb : b < p) :
    (if (a : ZMod p) = (b : ZMod p) then (1 : ZMod p) else 0) =
      ((if a == b then 1 else 0 : Nat) : ZMod p) := by
  by_cases hab : a = b
  · subst hab; simp
  · have hne : (a : ZMod p) ≠ (b : ZMod p) := fun heq => hab ((zmod_eq_iff ha hb).mp heq)
    simp [hab, hne]

/-- Positive naturals strictly below `p` are nonzero in `ZMod p`. -/
theorem zmod_natCast_ne_zero {n : Nat} (hpos : 0 < n) (hlt : n < p) :
    (n : ZMod p) ≠ 0 := by
  intro hz
  have h0 := (zmod_isZero_iff hlt).mp hz
  omega

end ZModArithmetic

/-! ### 3-Field Compatibility (`Goldilocks`, `BN254`, `BLS12-381`) -/

/-- BN254 scalar field `Fr` satisfies `FieldCompatible64`. -/
theorem fieldCompatible64_bn254 : FieldCompatible64 Aiur.Library.Field.BN254.F :=
  FieldCompatible64.of_charP Aiur.Library.Field.BN254.F Aiur.Library.Field.BN254.modulus (by
    unfold fieldBound64 Aiur.Library.Field.BN254.modulus; norm_num)

/-- BLS12-381 scalar field `Fr` satisfies `FieldCompatible64`. -/
theorem fieldCompatible64_bls12381 : FieldCompatible64 Aiur.Library.Field.BLS12381.F :=
  FieldCompatible64.of_charP Aiur.Library.Field.BLS12381.F Aiur.Library.Field.BLS12381.modulus (by
    unfold fieldBound64 Aiur.Library.Field.BLS12381.modulus; norm_num)

/-! ## Section 2: `Fields::is_zero` Operational Contract (`FieldsIsZeroSpec`) -/

section FieldsIsZero

variable {F : Type} [Field F] [DecidableEq F]

@[simp] theorem qualifyName_fields_is_zero :
    qualifyName "Fields::is_zero" = "Fields::is_zero" := rfl

/-- Bidirectional operational contract for `Fields::is_zero(x : Field) -> Field`:
1. Soundness: any `EvalFn` on `[v]` forces `v = .field x`, leaves heap unchanged,
   and returns `.field (if x = 0 then 1 else 0)`.
2. Completeness: every `.field x` evaluates to `.field (if x = 0 then 1 else 0)`
   with unchanged heap. -/
def FieldsIsZeroSpec (world : World F) : Prop :=
  (∀ (v : SourceValue F) (h r h'),
    EvalFn world "Fields::is_zero" [v] h r h' →
      ∃ x : F, v = .field x ∧ r = .field (if x = 0 then (1 : F) else 0) ∧ h' = h) ∧
  (∀ (x : F) (h : Heap F),
    EvalFn world "Fields::is_zero" [.field x] h (.field (if x = 0 then (1 : F) else 0)) h)

/-- Soundness + completeness of `checkFieldsIsZero` over any `[Field F] [DecidableEq F]`. -/
theorem fieldsIsZeroSpec_of_check {s : Generic.Source F}
    (h : checkFieldsIsZero s = true) : FieldsIsZeroSpec s.world := by
  unfold checkFieldsIsZero at h
  cases hf : s.program.findFunction? "Fields::is_zero" with
  | none => rw [hf] at h; simp at h
  | some f =>
    rw [hf] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨htp, hparams⟩, hbody⟩ := h
    have hsym : Instance.ofSymbol "Fields::is_zero" = .ok ⟨"Fields::is_zero", []⟩ := by
      unfold Instance.ofSymbol; rfl
    have hsf : s.program.sourceFunction? "Fields::is_zero" =
        some { types := [], params := [("x", Aiur.Ty.field)],
               body := Aiur.Generic.Expr.matchValue (.var "x")
                 [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))] } := by
      unfold Generic.Program.sourceFunction?
      rw [hsym]
      simp [Except.toOption, hf, Generic.arguments, htp, hparams, hbody,
        Aiur.Generic.Ty.subst, Aiur.Generic.Ty.toCore, pure, Except.pure, bind, Except.bind]
    constructor
    · intro v heap r heap' ev
      have hplain : isPlainExpr (Aiur.Generic.Expr.matchValue (.var "x")
          [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))]) = true := rfl
      cases ev with
      | intro prep body =>
        simp only [Generic.Source.world, sourceWorld, hsf, SourceFunction.prepare] at prep
        split at prep
        · next hcond =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at prep
          obtain ⟨rfl, rfl, rfl⟩ := prep
          have hvty : v.type = Aiur.Ty.field := (by simpa using hcond.1.symm)
          cases v with
          | field x =>
            obtain ⟨vm, hm, evx, hbr⟩ := evalExpr_match_lit_wild_inv body
            obtain ⟨hlx, rfl⟩ := evalExpr_var_inv evx
            simp at hlx
            subst hlx
            rcases hbr with ⟨hx0, ev0⟩ | ⟨hxne, ev1⟩
            · injection hx0 with hx0'
              subst hx0'
              obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
              exact ⟨0, rfl, by simp, rfl⟩
            · have hne : x ≠ 0 := fun h0 => hxne (congrArg Value.field h0)
              obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
              exact ⟨x, rfl, by simp [hne], rfl⟩
          | tuple _ | ptr _ _ | construct _ _ _ =>
            simp [Value.type] at hvty
        · simp at prep
      | returned prep body =>
        simp only [Generic.Source.world, sourceWorld, hsf, SourceFunction.prepare] at prep
        split at prep
        · simp only [Except.ok.injEq, Prod.mk.injEq] at prep
          obtain ⟨rfl, rfl, rfl⟩ := prep
          exact False.elim (Gadgets.no_evalExit_of_plain hplain body)
        · simp at prep
    · intro x heap
      have hprep : s.world.prepare "Fields::is_zero" [.field x] =
          .ok ([], [("x", .field x)],
            Aiur.Generic.Expr.matchValue (.var "x")
              [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))]) := by
        simp [Generic.Source.world, sourceWorld, hsf, SourceFunction.prepare,
          Value.type, Generic.wellFormed]
      apply EvalFn.intro hprep
      have evx : EvalExpr s.world [] [("x", .field x)] (.var "x") heap (.field x) heap :=
        EvalExpr.var (by simp)
      by_cases hx : x = 0
      · subst hx
        have hsel : SourceSemantics.selectArm s.world [] heap (.field (0 : F))
            [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))] =
            .ok (some ([], .literal (1 : F))) := by
          simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings]
        simpa using EvalExpr.matchValue evx hsel EvalExpr.literal
      · have h0x : (0 : F) ≠ x := Ne.symm hx
        have hsel : SourceSemantics.selectArm s.world [] heap (.field x)
            [(.literal (0 : F), .literal (1 : F)), (.wildcard, .literal (0 : F))] =
            .ok (some ([], .literal (0 : F))) := by
          simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
            Aiur.Pattern.bindings, h0x]
        simpa [hx] using EvalExpr.matchValue evx hsel EvalExpr.literal

end FieldsIsZero

/-! ## Section 3: Exact `EvalExpr` / `EvalFn` Correctness for All 8 Native Field Ops -/

section NativeFieldOpCorrectness

variable {p : Nat} [Fact (Nat.Prime p)]

/-- Exact `EvalExpr` inversion for `fieldAddE ea eb`. -/
theorem evalExpr_fieldAdd_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldAddE ea eb)) h r h') :
    ∃ (x y : ZMod p) (hm : Heap (ZMod p)),
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) hm ∧
      EvalExpr world [] locals (qualifyExprF (ZMod p) eb) hm (.field y) h' ∧
      r = .field (x + y) := by
  simp only [fieldAddE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  obtain ⟨vx, vy, hm, evx, evy, hop⟩ := evalExpr_binary_inv ev
  cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hop
  subst hop
  exact ⟨_, _, hm, evx, evy, rfl⟩

/-- Exact modular `Nat` correspondence for `fieldAddE`: evaluates to `(a + b) % p`. -/
theorem evalExpr_fieldAdd_mod {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {a b : Nat} {h h1 h2 : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h1)
    (evb : EvalExpr world [] locals (qualifyExprF (ZMod p) eb) h1 (.field (b : ZMod p)) h2) :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldAddE ea eb)) h
      (.field (((a + b) % p : Nat) : ZMod p)) h2 := by
  simp only [fieldAddE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
  rw [← zmod_add_eq_mod]
  exact .binary eva evb rfl

/-- Exact `EvalExpr` inversion for `fieldSubE ea eb`. -/
theorem evalExpr_fieldSub_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldSubE ea eb)) h r h') :
    ∃ (x y : ZMod p) (hm : Heap (ZMod p)),
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) hm ∧
      EvalExpr world [] locals (qualifyExprF (ZMod p) eb) hm (.field y) h' ∧
      r = .field (x - y) := by
  simp only [fieldSubE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  obtain ⟨vx, vy, hm, evx, evy, hop⟩ := evalExpr_binary_inv ev
  cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hop
  subst hop
  exact ⟨_, _, hm, evx, evy, rfl⟩

/-- Exact modular `Nat` correspondence for `fieldSubE`: evaluates to `(a + p - b) % p` for `b ≤ p`. -/
theorem evalExpr_fieldSub_mod {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {a b : Nat} (hb : b ≤ p) {h h1 h2 : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h1)
    (evb : EvalExpr world [] locals (qualifyExprF (ZMod p) eb) h1 (.field (b : ZMod p)) h2) :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldSubE ea eb)) h
      (.field (((a + p - b) % p : Nat) : ZMod p)) h2 := by
  simp only [fieldSubE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
  rw [← zmod_sub_eq_mod hb]
  exact .binary eva evb rfl

/-- Exact `EvalExpr` inversion for `fieldMulE ea eb`. -/
theorem evalExpr_fieldMul_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldMulE ea eb)) h r h') :
    ∃ (x y : ZMod p) (hm : Heap (ZMod p)),
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) hm ∧
      EvalExpr world [] locals (qualifyExprF (ZMod p) eb) hm (.field y) h' ∧
      r = .field (x * y) := by
  simp only [fieldMulE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  obtain ⟨vx, vy, hm, evx, evy, hop⟩ := evalExpr_binary_inv ev
  cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hop
  subst hop
  exact ⟨_, _, hm, evx, evy, rfl⟩

/-- Exact modular `Nat` correspondence for `fieldMulE`: evaluates to `(a * b) % p`. -/
theorem evalExpr_fieldMul_mod {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea eb : Expr} {a b : Nat} {h h1 h2 : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h1)
    (evb : EvalExpr world [] locals (qualifyExprF (ZMod p) eb) h1 (.field (b : ZMod p)) h2) :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldMulE ea eb)) h
      (.field (((a * b) % p : Nat) : ZMod p)) h2 := by
  simp only [fieldMulE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
  rw [← zmod_mul_eq_mod]
  exact .binary eva evb rfl

/-- Exact `EvalExpr` inversion for `fieldNegE ea` (`0 - ea`). -/
theorem evalExpr_fieldNeg_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea : Expr} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldNegE ea)) h r h') :
    ∃ x : ZMod p,
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) h' ∧
      r = .field (0 - x) := by
  simp only [fieldNegE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  obtain ⟨v0, vx, _, ev0, evx, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
  cases vx <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hop
  subst hop
  exact ⟨_, evx, by simp⟩

/-- Exact modular `Nat` correspondence for `fieldNegE`: evaluates to `(p - a) % p` for `a ≤ p`. -/
theorem evalExpr_fieldNeg_mod {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea : Expr} {a : Nat} (ha : a ≤ p) {h h' : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h') :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldNegE ea)) h
      (.field (((p - a) % p : Nat) : ZMod p)) h' := by
  simp only [fieldNegE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, Nat.cast_zero]
  rw [← zmod_neg_eq_mod ha]
  exact .binary .literal eva rfl

/-- Exact branchless `if a == 0 then 0 else p - a` correspondence for `fieldNegE` on `a < p`. -/
theorem evalExpr_fieldNeg_ite {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {ea : Expr} {a : Nat} (ha : a < p) {h h' : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h') :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldNegE ea)) h
      (.field ((if a == 0 then 0 else p - a : Nat) : ZMod p)) h' := by
  simp only [fieldNegE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, Nat.cast_zero]
  rw [← zmod_neg_eq_ite ha]
  exact .binary .literal eva rfl

/-- Exact `EvalExpr` inversion for `fieldIsZeroE ea` (`Fields::is_zero(ea)`). -/
theorem evalExpr_fieldIsZero_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea : Expr} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldIsZeroE ea)) h r h') :
    ∃ x : ZMod p,
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) h' ∧
      r = .field (if x = 0 then (1 : ZMod p) else 0) := by
  simp only [fieldIsZeroE, callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
    List.map, qualifyName_fields_is_zero] at ev
  obtain ⟨vx, hm, evx, hcal⟩ := evalExpr_call1_inv ev
  obtain ⟨x, rfl, rfl, rfl⟩ := hiz.1 vx hm r h' hcal
  exact ⟨x, evx, rfl⟩

/-- Exact modular `Nat` correspondence for `fieldIsZeroE` on canonical `a < p`. -/
theorem evalExpr_fieldIsZero_nat {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea : Expr} {a : Nat} (ha : a < p)
    {h h' : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h') :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldIsZeroE ea)) h
      (.field ((if a == 0 then 1 else 0 : Nat) : ZMod p)) h' := by
  simp only [fieldIsZeroE, callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
    List.map, qualifyName_fields_is_zero]
  rw [← zmod_isZero_nat ha]
  exact .call (.cons eva .nil) (hiz.2 (a : ZMod p) h')

/-- Exact `EvalExpr` inversion for `fieldEqE ea eb` (`Fields::is_zero(ea - eb)`). -/
theorem evalExpr_fieldEq_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea eb : Expr} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldEqE ea eb)) h r h') :
    ∃ (x y : ZMod p) (hm : Heap (ZMod p)),
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) hm ∧
      EvalExpr world [] locals (qualifyExprF (ZMod p) eb) hm (.field y) h' ∧
      r = .field (if x = y then (1 : ZMod p) else 0) := by
  have ev' : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldIsZeroE (fieldSubE ea eb))) h r h' := ev
  obtain ⟨d, evd, rfl⟩ := evalExpr_fieldIsZero_inv hiz ev'
  obtain ⟨x, y, hm, eva, evb, hd⟩ := evalExpr_fieldSub_inv evd
  injection hd with hd'
  subst hd'
  have hiff : (x - y = 0) ↔ (x = y) := sub_eq_zero
  exact ⟨x, y, hm, eva, evb, by simp [hiff]⟩

/-- Exact modular `Nat` correspondence for `fieldEqE` on canonical `a, b < p`. -/
theorem evalExpr_fieldEq_nat {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea eb : Expr} {a b : Nat} (ha : a < p) (hb : b < p)
    {h h1 h2 : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h1)
    (evb : EvalExpr world [] locals (qualifyExprF (ZMod p) eb) h1 (.field (b : ZMod p)) h2) :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldEqE ea eb)) h
      (.field ((if a == b then 1 else 0 : Nat) : ZMod p)) h2 := by
  simp only [fieldEqE, callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
    List.map, qualifyName_fields_is_zero]
  have heq : (if (a : ZMod p) - (b : ZMod p) = 0 then (1 : ZMod p) else 0) =
      ((if a == b then 1 else 0 : Nat) : ZMod p) := by
    rw [← zmod_eq_nat ha hb]
    simp [sub_eq_zero]
  rw [← heq]
  exact .call (.cons (.binary eva evb rfl) .nil) (hiz.2 ((a : ZMod p) - (b : ZMod p)) h2)

/-- Exact `EvalExpr` inversion for `fieldInvVarE v`: forces `v` to bind `.field x`,
leaves heap unchanged, and returns total inverse `.field x⁻¹` (`0 ↦ 0`, `x ≠ 0 ↦ x⁻¹`). -/
theorem evalExpr_fieldInvVar_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {v : String} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldInvVarE v)) h r h') :
    ∃ x : ZMod p,
      locals.find? (·.1 == v) = some (v, .field x) ∧
      r = .field x⁻¹ ∧ h' = h := by
  simp only [fieldInvVarE, matchE, fieldIsZeroE, callE, vE, litE,
    qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map, qualifyName_fields_is_zero,
    Nat.cast_zero, Nat.cast_one] at ev
  obtain ⟨viz, hm, eviz, hbr⟩ := evalExpr_match_lit_wild_inv ev
  obtain ⟨vx, hm1, evv, hcal⟩ := evalExpr_call1_inv eviz
  obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evv
  obtain ⟨x, rfl, rfl, rfl⟩ := hiz.1 vx hm1 viz hm hcal
  rcases hbr with ⟨h1, ev0⟩ | ⟨hne1, evdiv⟩
  · injection h1 with h1'
    by_cases hx : x = 0
    · subst hx
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
      exact ⟨0, hlook, by simp, rfl⟩
    · simp only [hx, ↓reduceIte] at h1'
      exact False.elim (zmod_zero_ne_one h1')
  · by_cases hx : x = 0
    · subst hx
      simp only [↓reduceIte] at hne1
      exact False.elim (hne1 rfl)
    · obtain ⟨v1, vx2, _, ev1, evv2, hop⟩ := evalExpr_binary_inv evdiv
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
      obtain ⟨hlook2, rfl⟩ := evalExpr_var_inv evv2
      rw [hlook, Option.some.injEq, Prod.mk.injEq] at hlook2
      have hvx2 : vx2 = .field x := hlook2.2.symm
      subst hvx2
      simp only [evalBinOp, hx, ↓reduceIte, Except.ok.injEq] at hop
      subst hop
      exact ⟨x, hlook, by simp [one_div], rfl⟩

/-- Constructive evaluation of `fieldInvVarE v` for any `x : ZMod p` (both `x = 0` and `x ≠ 0`). -/
theorem evalExpr_fieldInvVar_mk {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {v : String} {x : ZMod p} {h : Heap (ZMod p)}
    (hlook : locals.find? (·.1 == v) = some (v, .field x)) :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldInvVarE v)) h (.field x⁻¹) h := by
  simp only [fieldInvVarE, matchE, fieldIsZeroE, callE, vE, litE,
    qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map, qualifyName_fields_is_zero,
    Nat.cast_zero, Nat.cast_one]
  have eviz : EvalExpr world [] locals (.call "Fields::is_zero" (some []) [.var v]) h
      (.field (if x = 0 then (1 : ZMod p) else 0)) h :=
    .call (.cons (.var hlook) .nil) (hiz.2 x h)
  by_cases hx : x = 0
  · subst hx
    simp only [↓reduceIte] at eviz
    have hsel : SourceSemantics.selectArm world [] h (.field (1 : ZMod p))
        [(.literal (1 : ZMod p), .literal (0 : ZMod p)),
         (.wildcard, .binary .div (.literal (1 : ZMod p)) (.var v))] =
        .ok (some ([], .literal (0 : ZMod p))) := by
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith, Aiur.Pattern.bindings]
    simpa using EvalExpr.matchValue eviz hsel EvalExpr.literal
  · simp only [hx, ↓reduceIte] at eviz
    have h10 : (1 : ZMod p) ≠ 0 := zmod_one_ne_zero
    have hsel : SourceSemantics.selectArm world [] h (.field (0 : ZMod p))
        [(.literal (1 : ZMod p), .literal (0 : ZMod p)),
         (.wildcard, .binary .div (.literal (1 : ZMod p)) (.var v))] =
        .ok (some ([], .binary .div (.literal (1 : ZMod p)) (.var v))) := by
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings, h10]
    have evdiv : EvalExpr world [] locals (.binary .div (.literal (1 : ZMod p)) (.var v)) h
        (.field x⁻¹) h := by
      refine .binary .literal (.var hlook) ?_
      simp [evalBinOp, hx, one_div]
    exact EvalExpr.matchValue eviz hsel evdiv

/-- Exact `EvalExpr` inversion for `fieldInvE ea` (`let _fi_x := ea; fieldInvVarE "_fi_x"`). -/
theorem evalExpr_fieldInv_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea : Expr} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldInvE ea)) h r h') :
    ∃ x : ZMod p,
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) h' ∧
      r = .field x⁻¹ := by
  simp only [fieldInvE, letE, qualifyExprF, qualifyExpr, qualifyPat,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map] at ev
  obtain ⟨va, hm, eva, evb⟩ := evalExpr_let_bind_inv ev
  obtain ⟨x, hlook, rfl, rfl⟩ := evalExpr_fieldInvVar_inv hiz evb
  simp at hlook
  subst hlook
  exact ⟨x, eva, rfl⟩

/-- Exact Fermat correspondence for `fieldInvE`: for any odd prime `p ≥ 3`, `fieldInvE ea`
evaluates to `(a^(p - 2) % p : ZMod p) = (a : ZMod p)⁻¹` (including `0 ↦ 0`). -/
theorem evalExpr_fieldInv_fermat {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    (hp3 : 3 ≤ p) {locals : Environment (ZMod p) Nat} {ea : Expr} {a : Nat}
    {h h' : Heap (ZMod p)}
    (eva : EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field (a : ZMod p)) h') :
    EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldInvE ea)) h
      (.field (((a ^ (p - 2) % p : Nat) : ZMod p))) h' := by
  rw [zmod_inv_eq_fermat hp3]
  simp only [fieldInvE, letE, qualifyExprF, qualifyExpr, qualifyPat,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map]
  exact EvalExpr.letValue (bindings := [("_fi_x", .field (a : ZMod p))]) eva
    (by simp [World.matchPattern, matchPatternWith])
    (evalExpr_fieldInvVar_mk hiz (by simp))

/-- Exact `EvalExpr` inversion for `fieldDivVarsE a b`. -/
theorem evalExpr_fieldDivVars_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {a b : String} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldDivVarsE a b)) h r h') :
    ∃ x y : ZMod p,
      locals.find? (·.1 == a) = some (a, .field x) ∧
      locals.find? (·.1 == b) = some (b, .field y) ∧
      r = .field (x / y) ∧ h' = h := by
  simp only [fieldDivVarsE, matchE, fieldIsZeroE, fieldMulE, callE, vE, litE,
    qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
    Aiur.Generic.Pattern.map, List.map, qualifyName_fields_is_zero,
    Nat.cast_zero, Nat.cast_one] at ev
  obtain ⟨viz, hm, eviz, hbr⟩ := evalExpr_match_lit_wild_inv ev
  obtain ⟨vb, hm1, evb, hcal⟩ := evalExpr_call1_inv eviz
  obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
  obtain ⟨y, rfl, rfl, rfl⟩ := hiz.1 vb hm1 viz hm hcal
  rcases hbr with ⟨h1, ev0⟩ | ⟨hne1, evdiv⟩
  · injection h1 with h1'
    by_cases hy : y = 0
    · subst hy
      obtain ⟨v0, va, _, evLit0, eva, hop⟩ := evalExpr_binary_inv ev0
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit0
      obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
      cases va <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hop
      subst hop
      exact ⟨_, 0, hla, hlb, by simp, rfl⟩
    · simp only [hy, ↓reduceIte] at h1'
      exact False.elim (zmod_zero_ne_one h1')
  · by_cases hy : y = 0
    · subst hy
      simp only [↓reduceIte] at hne1
      exact False.elim (hne1 rfl)
    · obtain ⟨va, vb2, _, eva, evb2, hop⟩ := evalExpr_binary_inv evdiv
      obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
      obtain ⟨hlb2, rfl⟩ := evalExpr_var_inv evb2
      rw [hlb, Option.some.injEq, Prod.mk.injEq] at hlb2
      have hvb2 : vb2 = .field y := hlb2.2.symm
      subst hvb2
      cases va <;> simp only [evalBinOp, hy, ↓reduceIte, Except.ok.injEq, reduceCtorEq] at hop
      subst hop
      exact ⟨_, y, hla, hlb, rfl, rfl⟩

/-- Exact `EvalExpr` inversion for `fieldDivE ea eb` (capture-free outer tuple binding). -/
theorem evalExpr_fieldDiv_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {ea eb : Expr} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (fieldDivE ea eb)) h r h') :
    ∃ (x y : ZMod p) (hm : Heap (ZMod p)),
      EvalExpr world [] locals (qualifyExprF (ZMod p) ea) h (.field x) hm ∧
      EvalExpr world [] locals (qualifyExprF (ZMod p) eb) hm (.field y) h' ∧
      r = .field (x / y) := by
  simp only [fieldDivE, qualifyExprF, qualifyExpr, qualifyPat,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at ev
  obtain ⟨va, vb, hm, evtup, evb⟩ := evalExpr_let_tuple2_inv ev
  obtain ⟨va', vb', hm1, eva, evb', htup⟩ := evalExpr_tuple2_inv evtup
  injection htup with hcons
  injection hcons with h1 hcons2
  injection hcons2 with h2 _
  subst h1; subst h2
  obtain ⟨x, y, hla, hlb, rfl, rfl⟩ := evalExpr_fieldDivVars_inv hiz evb
  simp at hla hlb
  subst hla; subst hlb
  exact ⟨x, y, hm1, eva, evb', rfl⟩

/-- Unified inversion lemma for `fieldOpExpr op args` across all 8 native `FieldOp`s. -/
theorem evalExpr_fieldOpExpr_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {op : FieldOp} {args : List Expr} {e : Expr}
    (hop : fieldOpExpr op args = some e)
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) e) h r h') :
    ∃ (xs : List (ZMod p)) (res : ZMod p),
      EvalArgs world [] locals (args.map (qualifyExprF (ZMod p))) h (xs.map .field) h' ∧
      op.eval xs = some res ∧
      r = .field res := by
  cases op <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
    simp only [fieldOpExpr, Option.some.injEq, reduceCtorEq] at hop
  · subst hop
    obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldAdd_inv ev
    exact ⟨[x, y], x + y, .cons eva (.cons evb .nil), rfl, rfl⟩
  · subst hop
    obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldSub_inv ev
    exact ⟨[x, y], x - y, .cons eva (.cons evb .nil), rfl, rfl⟩
  · subst hop
    obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldMul_inv ev
    exact ⟨[x, y], x * y, .cons eva (.cons evb .nil), rfl, rfl⟩
  · subst hop
    obtain ⟨x, eva, rfl⟩ := evalExpr_fieldNeg_inv ev
    exact ⟨[x], 0 - x, .cons eva .nil, rfl, rfl⟩
  · subst hop
    obtain ⟨x, eva, rfl⟩ := evalExpr_fieldInv_inv hiz ev
    exact ⟨[x], x⁻¹, .cons eva .nil, rfl, rfl⟩
  · subst hop
    obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldDiv_inv hiz ev
    exact ⟨[x, y], x / y, .cons eva (.cons evb .nil), rfl, rfl⟩
  · subst hop
    obtain ⟨x, eva, rfl⟩ := evalExpr_fieldIsZero_inv hiz ev
    exact ⟨[x], if x = 0 then 1 else 0, .cons eva .nil, rfl, rfl⟩
  · subst hop
    obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldEq_inv hiz ev
    exact ⟨[x, y], if x = y then 1 else 0, .cons eva (.cons evb .nil), rfl, rfl⟩

private theorem evalExpr_vE_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {nm : String} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) (vE nm)) h r h') :
    locals.find? (·.1 == nm) = some (nm, r) ∧ h' = h := by
  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  exact evalExpr_var_inv ev

/-- Unified inversion lemma for `fieldOpBody op opParams` (both `dropFirstParam = false`
and `dropFirstParam = true`) under distinct parameter names. -/
theorem evalExpr_fieldOpBody_inv {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {op : FieldOp} {dropFirst : Bool} {pNames : List String} {args : List (SourceValue (ZMod p))}
    {body : Expr}
    (hnd : pNames.Nodup)
    (hlen : args.length = pNames.length)
    (hbody : fieldOpBody op (if dropFirst then pNames.drop 1 else pNames) = some body)
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] (pNames.zip args) (qualifyExprF (ZMod p) body) h r h') :
    ∃ (xs : List (ZMod p)) (res : ZMod p),
      (if dropFirst then ∃ pVal, args = pVal :: xs.map .field else args = xs.map .field) ∧
      op.eval xs = some res ∧
      r = .field res ∧ h' = h := by
  have find1 : ∀ (a : String) (va : SourceValue (ZMod p)),
      ([a].zip [va] : Environment (ZMod p) Nat).find? (·.1 == a) = some (a, va) := by
    intro a va; simp
  have find2 : ∀ (a b : String) (va vb : SourceValue (ZMod p)), a ≠ b →
      ([a, b].zip [va, vb] : Environment (ZMod p) Nat).find? (·.1 == a) = some (a, va) ∧
      ([a, b].zip [va, vb] : Environment (ZMod p) Nat).find? (·.1 == b) = some (b, vb) := by
    intro a b va vb hne
    have hba : (a == b) = false := beq_false_of_ne hne
    simp [hba]
  have find3 : ∀ (m a b : String) (vm va vb : SourceValue (ZMod p)),
      m ≠ a → m ≠ b → a ≠ b →
      ([m, a, b].zip [vm, va, vb] : Environment (ZMod p) Nat).find? (·.1 == a) = some (a, va) ∧
      ([m, a, b].zip [vm, va, vb] : Environment (ZMod p) Nat).find? (·.1 == b) = some (b, vb) := by
    intro m a b vm va vb hma hmb hab
    have h1 : (m == a) = false := beq_false_of_ne hma
    have h2 : (m == b) = false := beq_false_of_ne hmb
    have h3 : (a == b) = false := beq_false_of_ne hab
    simp [h1, h2, h3]
  cases dropFirst
  · simp only [Bool.false_eq_true, ↓reduceIte] at hbody ⊢
    cases op <;> rcases pNames with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
      simp only [fieldOpBody, Option.some.injEq, reduceCtorEq] at hbody
    · subst hbody
      rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldAdd_inv ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
      rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
      rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
      exact ⟨[x, y], x + y, by simp [hla.2, hlb.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldSub_inv ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
      rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
      rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
      exact ⟨[x, y], x - y, by simp [hla.2, hlb.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldMul_inv ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
      rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
      rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
      exact ⟨[x, y], x * y, by simp [hla.2, hlb.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, eva, rfl⟩ := evalExpr_fieldNeg_inv ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      rw [find1 a va, Option.some.injEq, Prod.mk.injEq] at hla
      exact ⟨[x], 0 - x, by simp [hla.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, hla, rfl, rfl⟩ := evalExpr_fieldInvVar_inv hiz ev
      rw [find1 a va, Option.some.injEq, Prod.mk.injEq] at hla
      exact ⟨[x], x⁻¹, by simp [hla.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, hla, hlb, rfl, rfl⟩ := evalExpr_fieldDivVars_inv hiz ev
      rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
      rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
      exact ⟨[x, y], x / y, by simp [hla.2, hlb.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, eva, rfl⟩ := evalExpr_fieldIsZero_inv hiz ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      rw [find1 a va, Option.some.injEq, Prod.mk.injEq] at hla
      exact ⟨[x], if x = 0 then 1 else 0, by simp [hla.2], rfl, rfl, rfl⟩
    · subst hbody
      rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldEq_inv hiz ev
      obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
      obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
      rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
      rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
      exact ⟨[x, y], if x = y then 1 else 0, by simp [hla.2, hlb.2], rfl, rfl, rfl⟩
  · simp only [↓reduceIte] at hbody ⊢
    rcases pNames with _ | ⟨m, rest⟩
    · cases op <;> simp [fieldOpBody] at hbody
    · simp only [List.drop_succ_cons, List.drop_zero] at hbody
      cases op <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
        simp only [fieldOpBody, Option.some.injEq, reduceCtorEq] at hbody
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldAdd_inv ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
        exact ⟨[x, y], x + y, ⟨vm, by simp [hla.2, hlb.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldSub_inv ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
        exact ⟨[x, y], x - y, ⟨vm, by simp [hla.2, hlb.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldMul_inv ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
        exact ⟨[x, y], x * y, ⟨vm, by simp [hla.2, hlb.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, eva, rfl⟩ := evalExpr_fieldNeg_inv ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        exact ⟨[x], 0 - x, ⟨vm, by simp [hla.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, hla, rfl, rfl⟩ := evalExpr_fieldInvVar_inv hiz ev
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        exact ⟨[x], x⁻¹, ⟨vm, by simp [hla.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, hla, hlb, rfl, rfl⟩ := evalExpr_fieldDivVars_inv hiz ev
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
        exact ⟨[x, y], x / y, ⟨vm, by simp [hla.2, hlb.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, eva, rfl⟩ := evalExpr_fieldIsZero_inv hiz ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        exact ⟨[x], if x = 0 then 1 else 0, ⟨vm, by simp [hla.2]⟩, rfl, rfl, rfl⟩
      · subst hbody
        rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, hm, eva, evb, rfl⟩ := evalExpr_fieldEq_inv hiz ev
        obtain ⟨hla, rfl⟩ := evalExpr_vE_inv eva
        obtain ⟨hlb, rfl⟩ := evalExpr_vE_inv evb
        rw [ha, Option.some.injEq, Prod.mk.injEq] at hla
        rw [hb, Option.some.injEq, Prod.mk.injEq] at hlb
        exact ⟨[x, y], if x = y then 1 else 0, ⟨vm, by simp [hla.2, hlb.2]⟩, rfl, rfl, rfl⟩

/-- `EvalFn` correctness for a lowered ambient-field helper function over `ZMod p`. -/
theorem evalFn_fieldOpBody_sound {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {nm : String} {op : FieldOp} {dropFirst : Bool} {pNames : List String} {body : Expr}
    (hfn : WorldHasFn world nm pNames (qualifyExprF (ZMod p) body))
    (hnd : pNames.Nodup)
    (hbody : fieldOpBody op (if dropFirst then pNames.drop 1 else pNames) = some body)
    {args : List (SourceValue (ZMod p))} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalFn world nm args h r h') :
    ∃ (xs : List (ZMod p)) (res : ZMod p),
      (if dropFirst then ∃ pVal, args = pVal :: xs.map .field else args = xs.map .field) ∧
      op.eval xs = some res ∧
      r = .field res ∧ h' = h := by
  have hplain : isPlainExpr (qualifyExprF (ZMod p) body) = true := by
    rw [isPlainExpr_qualifyExprF]
    exact isPlainExpr_fieldOpBody hbody
  obtain ⟨hlen, evBody⟩ := evalFn_plain_inv hfn hplain ev
  exact evalExpr_fieldOpBody_inv hiz hnd hlen hbody evBody

end NativeFieldOpCorrectness

/-! ## Section 4: Backward `EvalExpr` & `EvalFn` Soundness of `lowerFieldOps` + `pruneUnreachable` -/

section BackwardSoundness

variable {p : Nat} [Fact (Nat.Prime p)]

/-- Specification of a single bound ambient-field function `b` in the reference
world `wOrig`: calling `Prog::<b.fnName>` on field arguments evaluates cleanly to
`b.op.eval` with unchanged heap. -/
def FieldBindingSpec (wOrig : World (ZMod p)) (b : FieldBinding) : Prop :=
  hasDoubleColon b.fnName.toList = false ∧
  if b.dropFirstParam then
    ∀ (pVal : SourceValue (ZMod p)) (xs : List (ZMod p)) (res : ZMod p) (h : Heap (ZMod p)),
      b.op.eval xs = some res →
      EvalFn wOrig (qualified b.fnName) (pVal :: xs.map .field) h (.field res) h
  else
    ∀ (xs : List (ZMod p)) (res : ZMod p) (h : Heap (ZMod p)),
      b.op.eval xs = some res →
      EvalFn wOrig (qualified b.fnName) (xs.map .field) h (.field res) h

/-- Admissibility of stripping `check_u56` wrappers in an ambient-field specification world. -/
def CheckU56Admissible (wOrig : World (ZMod p)) : Prop :=
  ∀ (v : SourceValue (ZMod p)) (h : Heap (ZMod p)),
    EvalFn wOrig (qualified "check_u56") [v] h (.tuple []) h

/-- Exact literal-argument operational contract for constant-folded 56-bit arithmetic helpers. -/
structure ConstHelperSpec (wOrig : World (ZMod p)) : Prop where
  check_u56 : ∀ n < natLimit, ∀ h,
    EvalFn wOrig (qualified "check_u56") [.field (n : ZMod p)] h (.tuple []) h
  sub_borrow_56 : ∀ a < natLimit, ∀ b < natLimit, ∀ h,
    EvalFn wOrig (qualified "sub_borrow_56") [.field (a : ZMod p), .field (b : ZMod p)] h
      (.tuple [.field ((a - b : Nat) : ZMod p),
               .field ((if a ≥ b then 1 else 0 : Nat) : ZMod p)]) h
  mul_56 : ∀ a < natLimit, ∀ b < natLimit, a * b < natLimit → ∀ h,
    EvalFn wOrig (qualified "mul_56") [.field (a : ZMod p), .field (b : ZMod p)] h
      (.field ((a * b : Nat) : ZMod p)) h
  divmod_56 : ∀ a < natLimit, ∀ b < natLimit, 0 < b → ∀ h,
    EvalFn wOrig (qualified "divmod_56") [.field (a : ZMod p), .field (b : ZMod p)] h
      (.tuple [.field ((a / b : Nat) : ZMod p), .field ((a % b : Nat) : ZMod p)]) h

/-- Combined reference-world specification for `FieldLower.lowerFieldOps`. -/
structure FieldLowerSpec (wOrig : World (ZMod p)) (bindings : List FieldBinding)
    (stripCheckU56 foldConst : Bool) : Prop where
  fieldsIsZero : FieldsIsZeroSpec wOrig
  bindings_ok : ∀ b ∈ bindings, FieldBindingSpec wOrig b
  checkU56_ok : stripCheckU56 = true → CheckU56Admissible wOrig
  constHelpers_ok : foldConst = true → ConstHelperSpec wOrig

private theorem qualifyName_eq_qualified {nm : String} (h : hasDoubleColon nm.toList = false) :
    qualifyName nm = qualified nm := by
  simp [qualifyName, h]

private theorem evalArgs_of_forall2 {wOrig : World (ZMod p)} {locals : Environment (ZMod p) Nat} :
    ∀ {xs xs' : List Expr}
      (_hrel : List.Forall₂ (fun x x' =>
        ∀ h h' r,
          EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h r h' →
          EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x) h r h') xs xs')
      {h h' : Heap (ZMod p)} {vs : List (SourceValue (ZMod p))},
      EvalArgs wOrig [] locals (xs'.map (qualifyExprF (ZMod p))) h vs h' →
      EvalArgs wOrig [] locals (xs.map (qualifyExprF (ZMod p))) h vs h'
  | [], [], .nil, _, _, _, ev => by cases ev; exact .nil
  | _ :: _, _ :: _, .cons hhd htl, _, _, _, ev => by
    cases ev with
    | cons evhd evtl => exact .cons (hhd _ _ _ evhd) (evalArgs_of_forall2 htl evtl)

private theorem evalExpr_foldConstCall_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst)
    {locals : Environment (ZMod p) Nat} {nm : String} {targs : Option (List Lower.Ty)}
    {xs : List Expr} {e : Expr}
    (hfold : foldConstCall foldConst nm targs xs = some e)
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr wOrig [] locals (qualifyExprF (ZMod p) e) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.call nm targs xs)) h r h' := by
  unfold foldConstCall at hfold
  split at hfold
  · next hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hfc, rfl⟩ := hcond
    have hch := hspec.constHelpers_ok hfc
    split at hfold
    · next n =>
      split at hfold
      · next hlt =>
        injection hfold with he; subst he
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev ⊢
        obtain ⟨rfl, rfl⟩ := TypedGadgets.evalExpr_tuple0_inv ev
        exact .call (.cons .literal .nil) (hch.check_u56 n hlt h')
      · cases hfold
    · next a b =>
      split at hfold
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        injection hfold with he; subst he
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev ⊢
        obtain ⟨v0, v1, _, ev0, ev1, rfl⟩ := evalExpr_tuple2_inv ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
        exact .call (.cons .literal (.cons .literal .nil)) (hch.sub_borrow_56 a hlt.1 b hlt.2 h')
      · cases hfold
    · next a b =>
      split at hfold
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        injection hfold with he; subst he
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev ⊢
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
        exact .call (.cons .literal (.cons .literal .nil))
          (hch.mul_56 a hlt.1.1 b hlt.1.2 hlt.2 h')
      · cases hfold
    · next a b =>
      split at hfold
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        injection hfold with he; subst he
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev ⊢
        obtain ⟨v0, v1, _, ev0, ev1, rfl⟩ := evalExpr_tuple2_inv ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
        exact .call (.cons .literal (.cons .literal .nil))
          (hch.divmod_56 a hlt.1.1 b hlt.1.2 hlt.2 h')
      · cases hfold
    · cases hfold
  · cases hfold

private theorem evalExpr_lowerCall_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {inlineFieldOps stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst)
    {locals : Environment (ZMod p) Nat} {nm : String} {targs : Option (List Lower.Ty)}
    {xs xs' : List Expr}
    (hrel : List.Forall₂ (fun x x' =>
      ∀ h h' r,
        EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h r h' →
        EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x) h r h') xs xs')
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr wOrig [] locals
      (qualifyExprF (ZMod p) (lowerCall bindings inlineFieldOps foldConst nm targs xs xs')) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.call nm targs xs)) h r h' := by
  have hfallback :
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.call nm targs xs')) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.call nm targs xs)) h r h' := by
    intro evc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF] at evc ⊢
    cases evc with
    | call ea ef => exact .call (evalArgs_of_forall2 hrel ea) ef
  unfold lowerCall at ev
  cases hfold : foldConstCall foldConst nm targs xs with
  | some e =>
    rw [hfold] at ev
    exact evalExpr_foldConstCall_backward hspec hfold ev
  | none =>
    rw [hfold] at ev
    dsimp only at ev
    by_cases hcond : (inlineFieldOps && targs == some []) = true
    · simp only [hcond, ↓reduceIte] at ev
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨_, rfl⟩ := hcond
      cases hfind : bindings.find? (·.fnName == nm) with
      | none =>
        rw [hfind] at ev
        exact hfallback ev
      | some b =>
        rw [hfind] at ev
        have hbMem : b ∈ bindings := List.mem_of_find?_eq_some hfind
        have hbNm : b.fnName = nm := by
          have := List.find?_some hfind
          simpa [beq_iff_eq] using this
        have hbSpec := hspec.bindings_ok b hbMem
        have hqn : qualifyName nm = qualified b.fnName := by
          rw [← hbNm]; exact qualifyName_eq_qualified hbSpec.1
        cases hdrop : b.dropFirstParam
        · simp only [hdrop, Bool.not_false, ↓reduceIte] at ev
          cases hop : fieldOpExpr b.op xs' with
          | none =>
            rw [hop] at ev
            exact hfallback ev
          | some e =>
            rw [hop] at ev
            obtain ⟨vs, res, eva', hev, rfl⟩ := evalExpr_fieldOpExpr_inv hspec.fieldsIsZero hop ev
            have eva := evalArgs_of_forall2 hrel eva'
            have hfn := hbSpec.2
            simp only [hdrop, Bool.false_eq_true, ↓reduceIte] at hfn
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF, hqn]
            exact .call eva (hfn vs res h' hev)
        · simp only [hdrop, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ev
          cases hrel with
          | nil => exact hfallback ev
          | cons _hhd htl =>
            rename_i hd hd' tl rest'
            cases hd with
            | literal n =>
              dsimp only at ev
              cases hop : fieldOpExpr b.op rest' with
              | none =>
                rw [hop] at ev
                exact hfallback ev
              | some e =>
                rw [hop] at ev
                obtain ⟨vs, res, evaRest', hev, rfl⟩ :=
                  evalExpr_fieldOpExpr_inv hspec.fieldsIsZero hop ev
                have evaRest := evalArgs_of_forall2 htl evaRest'
                have hfn := hbSpec.2
                simp only [hdrop, ↓reduceIte] at hfn
                simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
                  List.map, map_qualifyExprF, hqn]
                exact .call (.cons .literal evaRest) (hfn (.field (n : ZMod p)) vs res h' hev)
            | _ =>
              dsimp only at ev
              exact hfallback ev
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev

private theorem evalExpr_lowerProject_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst)
    {locals : Environment (ZMod p) Nat} {x x' : Expr} {i : Nat}
    (hx : ∀ h h' r,
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x) h r h')
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (lowerProject foldConst x x' i)) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.project x i)) h r h' := by
  have hfallback :
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.project x' i)) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.project x i)) h r h' := by
    intro evp
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evp ⊢
    cases evp with
    | project evx hp => exact .project (hx _ _ _ evx) hp
  unfold lowerProject at ev
  cases hfc : foldConst
  · simp only [hfc, Bool.false_eq_true, ↓reduceIte] at ev; exact hfallback ev
  · simp only [hfc, ↓reduceIte] at ev
    have hch := hspec.constHelpers_ok hfc
    split at ev
    · next a b =>
      split at ev
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
        exact .project
          (.call (.cons .literal (.cons .literal .nil)) (hch.sub_borrow_56 a hlt.1 b hlt.2 h'))
          rfl
      · exact hfallback ev
    · next a b =>
      split at ev
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
        exact .project
          (.call (.cons .literal (.cons .literal .nil)) (hch.sub_borrow_56 a hlt.1 b hlt.2 h'))
          rfl
      · exact hfallback ev
    · next a b =>
      split at ev
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
        exact .project
          (.call (.cons .literal (.cons .literal .nil))
            (hch.divmod_56 a hlt.1.1 b hlt.1.2 hlt.2 h'))
          rfl
      · exact hfallback ev
    · next a b =>
      split at ev
      · next hlt =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
        exact .project
          (.call (.cons .literal (.cons .literal .nil))
            (hch.divmod_56 a hlt.1.1 b hlt.1.2 hlt.2 h'))
          rfl
      · exact hfallback ev
    · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
      exact .project (.tuple (.cons .literal (.cons .literal .nil))) rfl
    · simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map]
      exact .project (.tuple (.cons .literal (.cons .literal .nil))) rfl
    · exact hfallback ev

private theorem evalExpr_lowerLetValue_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst)
    {locals : Environment (ZMod p) Nat} {pat : Pat} {x x' b b' : Expr}
    (hx : ∀ h h' r,
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x) h r h')
    (hb : ∀ bs h h' r,
      EvalExpr wOrig [] (bs ++ locals) (qualifyExprF (ZMod p) b') h r h' →
      EvalExpr wOrig [] (bs ++ locals) (qualifyExprF (ZMod p) b) h r h')
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr wOrig [] locals
      (qualifyExprF (ZMod p) (lowerLetValue stripCheckU56 foldConst pat x x' b')) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.letValue pat x b)) h r h' := by
  have hfallback :
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.letValue pat x' b')) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.letValue pat x b)) h r h' := by
    intro evl
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at evl ⊢
    cases evl with
    | letValue evx hm evb => exact .letValue (hx _ _ _ evx) hm (hb _ _ _ _ evb)
  unfold lowerLetValue at ev
  split at ev
  · next _ v v' =>
    by_cases hcond : (stripCheckU56 && v == v') = true
    · simp only [hcond, ↓reduceIte] at ev
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hstrip, rfl⟩ := hcond
      have hcu := hspec.checkU56_ok hstrip
      simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
      obtain ⟨hlook, rfl⟩ := evalExpr_var_inv ev
      have evb' : EvalExpr wOrig [] ([] ++ locals) (qualifyExprF (ZMod p) (.var v)) h' r h' := by
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.nil_append]
        exact .var hlook
      have evb := hb [] h' h' r evb'
      simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map, List.map]
      exact .letValue (.call (.cons (.var hlook) .nil) (hcu r h'))
        (by simp [World.matchPattern, matchPatternWith]) evb
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev
  · next _ body n =>
    by_cases hcond : ((stripCheckU56 || foldConst) && decide (n < natLimit)) = true
    · simp only [hcond, ↓reduceIte] at ev
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcond
      have hfn : SourceSemantics.EvalFn wOrig (qualified "check_u56") [.field (n : ZMod p)] h (.tuple []) h := by
        rcases hcond.1 with hs | hf
        · exact hspec.checkU56_ok hs (.field (n : ZMod p)) h
        · exact (hspec.constHelpers_ok hf).check_u56 n hcond.2 h
      have evb := hb [] h h' r ev
      simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map, List.map]
      exact .letValue (.call (.cons .literal .nil) hfn)
        (by simp [World.matchPattern, matchPatternWith]) evb
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev
  · next _ body =>
    by_cases hcond : (stripCheckU56 || foldConst) = true
    · simp only [hcond, ↓reduceIte] at ev
      have evb := hb [] h h' r ev
      simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map, List.map]
      exact .letValue (.tuple .nil) (by simp [World.matchPattern, matchPatternWith]) evb
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev
  · next _ _ v v' body =>
    by_cases hcond : (stripCheckU56 && v == v') = true
    · simp only [hcond, ↓reduceIte] at ev
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hstrip, rfl⟩ := hcond
      have hcu := hspec.checkU56_ok hstrip
      have hfinish :
          ∀ {val : SourceValue (ZMod p)} {hm : Heap (ZMod p)},
            EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h val hm →
            EvalExpr wOrig [] ((v, val) :: locals) (qualifyExprF (ZMod p) body) hm r h' →
            EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.letValue (.bind v) x b)) h r h' := by
        intro val hm evr evbd
        have evx := hx h hm val evr
        have evbd' : EvalExpr wOrig [] ([] ++ ((v, val) :: locals))
            (qualifyExprF (ZMod p) body) hm r h' := evbd
        have evInner : EvalExpr wOrig [] ([(v, val)] ++ locals)
            (qualifyExprF (ZMod p) (.letValue .wildcard (.call "check_u56" (some []) [.var v]) body))
            hm r h' := by
          simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
            Aiur.Generic.Pattern.map, List.map]
          exact .letValue (.call (.cons (.var (by simp)) .nil) (hcu val hm))
            (by simp [World.matchPattern, matchPatternWith]) evbd'
        have evb := hb [(v, val)] hm h' r evInner
        simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
          Aiur.Generic.Pattern.map]
        exact .letValue evx (by simp [World.matchPattern, matchPatternWith]) evb
      have hqLet : ∀ b0 : Expr,
          qualifyExprF (ZMod p) (.letValue (.bind v) x' b0) =
          .letValue (.bind v) (qualifyExprF (ZMod p) x') (qualifyExprF (ZMod p) b0) := fun b0 => by
        simp [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map]
      cases body with
      | var w =>
        dsimp only at ev
        by_cases hvw : (w == v) = true
        · simp only [hvw, ↓reduceIte] at ev
          simp only [beq_iff_eq] at hvw; subst hvw
          exact hfinish ev (by
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
            exact .var (by simp))
        · simp only [hvw, Bool.false_eq_true, ↓reduceIte] at ev
          rw [hqLet] at ev
          obtain ⟨val, hm, evr, evbd⟩ := evalExpr_let_bind_inv ev
          exact hfinish evr evbd
      | _ =>
        dsimp only at ev
        rw [hqLet] at ev
        obtain ⟨val, hm, evr, evbd⟩ := evalExpr_let_bind_inv ev
        exact hfinish evr evbd
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev
  · next _ _ v w =>
    by_cases hcond : (stripCheckU56 && v == w) = true
    · simp only [hcond, ↓reduceIte] at ev
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨_, rfl⟩ := hcond
      have evx := hx h h' r ev
      have evb' : EvalExpr wOrig [] ([(v, r)] ++ locals) (qualifyExprF (ZMod p) (.var v)) h' r h' := by
        simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map]
        exact .var (by simp)
      have evb := hb [(v, r)] h' h' r evb'
      simp only [qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map]
      exact .letValue evx (by simp [World.matchPattern, matchPatternWith]) evb
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
      exact hfallback ev
  · exact hfallback ev

private theorem selectArm_map_backward {wOrig : World (ZMod p)} {h : Heap (ZMod p)}
    {v : SourceValue (ZMod p)} :
    ∀ {arms arms' : List (Pat × Expr)}
      (_hrel : List.Forall₂ (fun a a' => a.1 = a'.1 ∧
        ∀ bs h1 h2 r,
          EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a'.2) h1 r h2 →
          EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a.2) h1 r h2) arms arms')
      {bs : Environment (ZMod p) Nat} {body' : Aiur.Generic.Expr (ZMod p)},
      SourceSemantics.selectArm wOrig [] h v
        (arms'.map fun a => (qualifyPatF (ZMod p) a.1, qualifyExprF (ZMod p) a.2)) =
        .ok (some (bs, body')) →
      ∃ body : Aiur.Generic.Expr (ZMod p),
        SourceSemantics.selectArm wOrig [] h v
          (arms.map fun a => (qualifyPatF (ZMod p) a.1, qualifyExprF (ZMod p) a.2)) =
          .ok (some (bs, body)) ∧
        ∀ loc h1 h2 r,
          EvalExpr wOrig [] loc body' h1 r h2 →
          EvalExpr wOrig [] loc body h1 r h2
  | [], [], .nil, _, _, hsel => by simp [SourceSemantics.selectArm] at hsel
  | (p1, b1) :: tl, (p2, b2) :: tl', .cons hhd htl, bs, body', hsel => by
    obtain ⟨rfl, hb⟩ := hhd
    simp only [List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel ⊢
    cases hm : wOrig.matchPattern [] h (qualifyPatF (ZMod p) p1) v with
    | error e => rw [hm] at hsel; cases hsel
    | ok o =>
      rw [hm] at hsel
      cases o with
      | some binds =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨qualifyExprF (ZMod p) b1, rfl, fun loc h1 h2 r ev => hb loc h1 h2 r ev⟩
      | none =>
        exact selectArm_map_backward htl hsel

private theorem evalExpr_lowerMatchValue_backward {wOrig : World (ZMod p)}
    {foldConst : Bool} {locals : Environment (ZMod p) Nat}
    {s s' : Expr} {arms arms' : List (Pat × Expr)}
    (hs : ∀ h h' r,
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) s') h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) s) h r h')
    (harms : List.Forall₂ (fun a a' => a.1 = a'.1 ∧
      ∀ bs h1 h2 r,
        EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a'.2) h1 r h2 →
        EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a.2) h1 r h2) arms arms')
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr wOrig [] locals
      (qualifyExprF (ZMod p) (lowerMatchValue p foldConst s s' arms')) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.matchValue s arms)) h r h' := by
  have hfallback :
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.matchValue s' arms')) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) (.matchValue s arms)) h r h' := by
    intro evm
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyArmsF] at evm ⊢
    cases evm with
    | matchValue evs hsel evbr =>
      obtain ⟨body, hsel', hbr⟩ := selectArm_map_backward harms hsel
      exact .matchValue (hs _ _ _ evs) hsel' (hbr _ _ _ _ evbr)
  unfold lowerMatchValue at ev
  cases hfc : foldConst
  · simp only [hfc, Bool.false_eq_true, ↓reduceIte] at ev; exact hfallback ev
  · simp only [hfc, ↓reduceIte] at ev
    cases s with
    | literal n =>
      cases arms' with
      | nil => exact hfallback ev
      | cons a0 rest1 =>
        cases a0 with
        | mk p0 e0' =>
          cases p0 with
          | literal k0 =>
            cases k0 with
            | zero =>
              cases rest1 with
              | nil => exact hfallback ev
              | cons a1 rest2 =>
                cases a1 with
                | mk p1 e1' =>
                  cases p1 with
                  | wildcard =>
                    cases rest2 with
                    | nil =>
                      cases harms with
                      | cons h0 harms1 =>
                        cases harms1 with
                        | cons h1 harms2 =>
                          cases harms2
                          rename_i arm0 arm1
                          rcases arm0 with ⟨pa0, e0⟩
                          rcases arm1 with ⟨pa1, e1⟩
                          obtain ⟨rfl, he0⟩ := h0
                          obtain ⟨rfl, he1⟩ := h1
                          by_cases hn0 : n = 0
                          · subst hn0
                            simp only [beq_self_eq_true, ↓reduceIte] at ev
                            have ev0 : EvalExpr wOrig [] ([] ++ locals)
                                (qualifyExprF (ZMod p) e0) h r h' := he0 locals h h' r ev
                            simp only [qualifyExprF, qualifyExpr, qualifyPat,
                              Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
                              Nat.cast_zero]
                            refine .matchValue .literal ?_ ev0
                            simp [SourceSemantics.selectArm, World.matchPattern,
                              matchPatternWith, Aiur.Pattern.bindings, qualifyExprF]
                          · have hn0b : (n == 0) = false := beq_false_of_ne hn0
                            simp only [hn0b, Bool.false_eq_true, ↓reduceIte] at ev
                            by_cases hnlt : n < p
                            · simp only [hnlt, ↓reduceIte] at ev
                              have ev1 : EvalExpr wOrig [] ([] ++ locals)
                                  (qualifyExprF (ZMod p) e1) h r h' := he1 locals h h' r ev
                              have h0n : (0 : ZMod p) ≠ (n : ZMod p) :=
                                Ne.symm (zmod_natCast_ne_zero (by omega) hnlt)
                              simp only [qualifyExprF, qualifyExpr, qualifyPat,
                                Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
                                Nat.cast_zero]
                              refine .matchValue .literal ?_ ev1
                              simp [SourceSemantics.selectArm, World.matchPattern,
                                matchPatternWith, Aiur.Pattern.bindings, h0n, qualifyExprF]
                            · simp only [hnlt, ↓reduceIte] at ev
                              exact hfallback ev
                    | cons _ _ => exact hfallback ev
                  | _ => exact hfallback ev
            | succ _ => exact hfallback ev
          | _ => exact hfallback ev
    | _ => exact hfallback ev

mutual

/-- **Core Expression Backward Simulation for `lowerFieldExpr`**:
Any `EvalExpr` derivation of `lowerFieldExpr p bindings ... e` in `wOrig` lifts
back to `EvalExpr` of `e` in `wOrig`. -/
theorem evalExpr_lowerFieldExpr_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {inlineFieldOps stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst) :
    ∀ (e : Expr) (locals : Environment (ZMod p) Nat) (h h' : Heap (ZMod p))
      (r : SourceValue (ZMod p)),
      EvalExpr wOrig [] locals
        (qualifyExprF (ZMod p) (lowerFieldExpr p bindings inlineFieldOps stripCheckU56 foldConst e))
        h r h' →
      EvalExpr wOrig [] locals (qualifyExprF (ZMod p) e) h r h'
  | .call nm targs xs, locals, h, h', r, ev =>
    evalExpr_lowerCall_backward hspec
      (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ev
  | .project x i, locals, h, h', r, ev =>
    evalExpr_lowerProject_backward hspec
      (fun h1 h2 r1 ev1 => evalExpr_lowerFieldExpr_backward hspec x locals h1 h2 r1 ev1) ev
  | .letValue pat x b, locals, h, h', r, ev =>
    evalExpr_lowerLetValue_backward hspec
      (fun h1 h2 r1 ev1 => evalExpr_lowerFieldExpr_backward hspec x locals h1 h2 r1 ev1)
      (fun bs h1 h2 r1 ev1 => evalExpr_lowerFieldExpr_backward hspec b (bs ++ locals) h1 h2 r1 ev1)
      ev
  | .matchValue s arms, locals, h, h', r, ev =>
    evalExpr_lowerMatchValue_backward
      (fun h1 h2 r1 ev1 => evalExpr_lowerFieldExpr_backward hspec s locals h1 h2 r1 ev1)
      (evalExpr_lowerFieldArms_forall2 hspec arms) ev
  | .tuple xs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | tuple ea =>
      exact .tuple (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ea)
  | .array xs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | array ea =>
      exact .array (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ea)
  | .construct ty targs nm xs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | construct ea =>
      exact .construct (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ea)
  | .constructAs ty targs nm xs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | constructAs ea =>
      exact .constructAs (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ea)
  | .record ty fs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | record ea =>
      exact .record (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec fs locals) ea)
  | .update ty fs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | update ea hu =>
      exact .update (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec fs locals) ea) hu
  | .builtin op xs, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | builtin ea ha =>
      exact .builtin (evalArgs_of_forall2 (evalExpr_lowerFieldExprList_forall2 hspec xs locals) ea) ha
  | .repeat x n, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | «repeat» evx => exact .«repeat» (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx)
  | .index x i, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | index evx hp => exact .index (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) hp
  | .slice x a b, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | slice evx hs => exact .slice (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) hs
  | .member x f, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | member evx hm => exact .member (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) hm
  | .store x, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | store evx => exact .store (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx)
  | .load x, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | load evx hl => exact .load (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) hl
  | .hint ty x ch, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | hint evx ht => exact .hint (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) ht
  | .neg x, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | neg evx ho => exact .neg (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evx) ho
  | .binary op x y, locals, h, h', r, ev => by
    simp only [lowerFieldExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary evl evr ho =>
      exact .binary (evalExpr_lowerFieldExpr_backward hspec x locals _ _ _ evl)
        (evalExpr_lowerFieldExpr_backward hspec y locals _ _ _ evr) ho
  | .literal _, _, _, _, _, ev => ev
  | .var _, _, _, _, _, ev => ev
  | .global _ _, _, _, _, _, ev => ev
  | .control _ _, _, _, _, _, ev => ev

theorem evalExpr_lowerFieldExprList_forall2 {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {inlineFieldOps stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst) :
    ∀ (xs : List Expr) (locals : Environment (ZMod p) Nat),
      List.Forall₂ (fun x x' =>
        ∀ h h' r,
          EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x') h r h' →
          EvalExpr wOrig [] locals (qualifyExprF (ZMod p) x) h r h')
        xs (lowerFieldExprList p bindings inlineFieldOps stripCheckU56 foldConst xs)
  | [], _ => .nil
  | x :: xs, locals =>
    .cons (fun h h' r ev => evalExpr_lowerFieldExpr_backward hspec x locals h h' r ev)
      (evalExpr_lowerFieldExprList_forall2 hspec xs locals)

theorem evalExpr_lowerFieldArms_forall2 {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {inlineFieldOps stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst) :
    ∀ (arms : List (Pat × Expr)),
      List.Forall₂ (fun a a' => a.1 = a'.1 ∧
        ∀ bs h1 h2 r,
          EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a'.2) h1 r h2 →
          EvalExpr wOrig [] bs (qualifyExprF (ZMod p) a.2) h1 r h2)
        arms (lowerFieldArms p bindings inlineFieldOps stripCheckU56 foldConst arms)
  | [] => .nil
  | (_, b) :: rest =>
    .cons ⟨rfl, fun bs h1 h2 r ev => evalExpr_lowerFieldExpr_backward hspec b bs h1 h2 r ev⟩
      (evalExpr_lowerFieldArms_forall2 hspec rest)

end

/-- Per-function body backward simulation for `lowerFieldFn`. -/
theorem evalExpr_lowerFieldFn_backward {wOrig : World (ZMod p)}
    {bindings : List FieldBinding} {inlineFieldOps stripCheckU56 foldConst : Bool}
    (hspec : FieldLowerSpec wOrig bindings stripCheckU56 foldConst)
    {f : Fn}
    (hOrigHas : WorldHasFn wOrig (qualified f.name) (f.params.map Prod.fst) (qualifyExprF (ZMod p) f.body))
    (hOrigPlain : isPlainExpr f.body = true)
    (hnd : (f.params.map Prod.fst).Nodup)
    {args : List (SourceValue (ZMod p))} {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (hlen : args.length = f.params.length)
    (ev : EvalExpr wOrig [] ((f.params.map Prod.fst).zip args)
      (qualifyExprF (ZMod p)
        (lowerFieldFn p bindings inlineFieldOps stripCheckU56 foldConst f).body) h r h') :
    EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF (ZMod p) f.body) h r h' := by
  unfold lowerFieldFn at ev
  cases hfind : bindings.find? (·.fnName == f.name) with
  | none =>
    rw [hfind] at ev
    exact evalExpr_lowerFieldExpr_backward hspec f.body _ h h' r ev
  | some b =>
    rw [hfind] at ev
    dsimp only at ev
    by_cases hsig : (allFieldParams f && (f.params.length == b.paramCount)) = true
    · simp only [hsig, ↓reduceIte] at ev
      cases hbody : fieldOpBody b.op
          (if b.dropFirstParam then (f.params.map Prod.fst).drop 1 else f.params.map Prod.fst) with
      | none =>
        rw [hbody] at ev
        exact evalExpr_lowerFieldExpr_backward hspec f.body _ h h' r ev
      | some nativeBody =>
        rw [hbody] at ev
        have hlen' : args.length = (f.params.map Prod.fst).length := by simpa using hlen
        obtain ⟨xs, res, hargs, heval, rfl, rfl⟩ :=
          evalExpr_fieldOpBody_inv hspec.fieldsIsZero hnd hlen' hbody ev
        have hbMem : b ∈ bindings := List.mem_of_find?_eq_some hfind
        have hbNm : b.fnName = f.name := by
          have := List.find?_some hfind
          simpa [beq_iff_eq] using this
        have hbSpec := hspec.bindings_ok b hbMem
        have hfnOrig : SourceSemantics.EvalFn wOrig (qualified f.name) args h' (.field res) h' := by
          rw [← hbNm]
          have h2 := hbSpec.2
          cases hdrop : b.dropFirstParam
          · simp only [hdrop, Bool.false_eq_true, ↓reduceIte] at hargs h2
            rw [hargs]
            exact h2 xs res h' heval
          · simp only [hdrop, ↓reduceIte] at hargs h2
            obtain ⟨pVal, rfl⟩ := hargs
            exact h2 pVal xs res h' heval
        have hplainQ : isPlainExpr (qualifyExprF (ZMod p) f.body) = true := by
          rw [isPlainExpr_qualifyExprF]; exact hOrigPlain
        exact (evalFn_plain_inv hOrigHas hplainQ hfnOrig).2
    · simp only [hsig] at ev
      exact evalExpr_lowerFieldExpr_backward hspec f.body _ h h' r ev

private theorem lowerFieldFn_name_params (ambientModulus : Nat) (bindings : List FieldBinding)
    (inlineFieldOps stripCheckU56 foldConst : Bool) (f : Fn) :
    (lowerFieldFn ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f).name = f.name ∧
    (lowerFieldFn ambientModulus bindings inlineFieldOps stripCheckU56 foldConst f).params = f.params := by
  unfold lowerFieldFn
  cases bindings.find? (·.fnName == f.name) with
  | none => exact ⟨rfl, rfl⟩
  | some b =>
    dsimp only
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- **Program-Level Backward Soundness for `lowerFieldOpsCore`** (over arbitrary prime `ZMod p`):
Every `EvalFn` derivation in the ambient-field-lowered world `wOpt` lifts back to
`EvalFn` in the reference world `wOrig`. -/
theorem lowerFieldOpsCore_backward {wOpt wOrig : World (ZMod p)}
    {cfg : Config} {fns : List Fn}
    (hpEq : cfg.ambientModulus = p)
    (haux : SameAuxWorld wOpt wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hOptHas : WorldHasFns wOpt (lowerFieldOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExt : ∀ nm args res,
      (∀ f' ∈ lowerFieldOpsCore cfg fns, qualified f'.name ≠ nm) →
      wOpt.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : FieldLowerSpec wOrig (effectiveBindings cfg fns) cfg.stripCheckU56 cfg.foldConstHelpers)
    {nm : String} {args : List (SourceValue (ZMod p))} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalFn wOpt nm args h r h') :
    EvalFn wOrig nm args h r h' := by
  have hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params)
      fns (lowerFieldOpsCore cfg fns) := by
    unfold lowerFieldOpsCore
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun f _ => ?_
    exact lowerFieldFn_name_params _ _ _ _ _ f
  have hPlainOpt : ∀ f' ∈ lowerFieldOpsCore cfg fns, isPlainExpr f'.body = true := by
    intro f' hf'
    unfold lowerFieldOpsCore at hf'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
    exact isPlainExpr_lowerFieldFn _ _ _ _ _ (hPlain f hf)
  have hUnique : ∀ f g, f ∈ fns → g ∈ fns → f.name = g.name → f = g := by
    clear hrel hPlainOpt hOptHas hOrigHas hOrigProv hExt hspec ev hpEq haux hndParams hPlain
    induction fns with
    | nil => intro _ _ h; cases h
    | cons hd tl ih =>
      simp only [List.map_cons, List.nodup_cons] at hndNames
      intro f g hf hg hnm
      rcases List.mem_cons.mp hf with rfl | hft <;> rcases List.mem_cons.mp hg with rfl | hgt
      · rfl
      · exfalso; exact hndNames.1 (hnm ▸ List.mem_map.mpr ⟨g, hgt, rfl⟩)
      · exfalso; exact hndNames.1 (hnm.symm ▸ List.mem_map.mpr ⟨f, hft, rfl⟩)
      · exact ih hndNames.2 f g hft hgt hnm
  refine world_transformBodies_backward haux hrel hOptHas hOrigProv hExt hPlainOpt ?_ ev
  intro f f' hf hf' hnm _ args' h1 r1 h2 hlen evBody
  unfold lowerFieldOpsCore at hf'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
  have hgnm : g.name = f.name := by
    have hnp := (lowerFieldFn_name_params cfg.ambientModulus (effectiveBindings cfg fns)
      cfg.inlineFieldOps cfg.stripCheckU56 cfg.foldConstHelpers g).1
    exact hnp.symm.trans hnm
  have hgf : g = f := hUnique g f hg hf hgnm
  subst hgf
  rw [hpEq] at evBody
  exact evalExpr_lowerFieldFn_backward hspec (hOrigHas g hg) (hPlain g hg) (hndParams g hg)
    hlen evBody

/-- **End-to-End Backward Soundness of `lowerFieldOps` + `pruneUnreachable`**
over **any** prime field `ZMod p` (`[Fact (Nat.Prime p)]`):
Composes `pruneUnreachable_backward` with `lowerFieldOpsCore_backward`, lifting
every `EvalFn` derivation in the final pruned ambient-field world `wPruned` back
to `EvalFn` in the reference world `wOrig`. -/
theorem lowerFieldOps_backward {wPruned wMid wOrig : World (ZMod p)}
    {cfg : Config} {fns : List Fn}
    (hpEq : cfg.ambientModulus = p)
    (hauxPM : SameAuxWorld wPruned wMid)
    (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerFieldOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerFieldOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerFieldOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerFieldOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerFieldOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : FieldLowerSpec wOrig (effectiveBindings cfg fns) cfg.stripCheckU56 cfg.foldConstHelpers)
    {nm : String} {args : List (SourceValue (ZMod p))} {h h' : Heap (ZMod p)}
    {r : SourceValue (ZMod p)}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' := by
  have evMid : EvalFn wMid nm args h r h' := by
    unfold lowerFieldOps at hPrunedHas hExtPM
    cases hroots : cfg.pruneRoots with
    | none =>
      rw [hroots] at hPrunedHas hExtPM
      have hsub : InlineFuseProof.WorldSub wPruned wMid := by
        refine ⟨hauxPM, fun nm' args' res hprep => ?_⟩
        by_cases hex : ∃ f ∈ lowerFieldOpsCore cfg fns, qualified f.name = nm'
        · obtain ⟨f, hf, rfl⟩ := hex
          rcases res with ⟨types, locals, body⟩
          obtain ⟨rfl, hlen, rfl, rfl⟩ := hPrunedHas f hf args' types locals body hprep
          exact hMidProv f hf args' hlen
        · exact hExtPM nm' args' res (fun f hf heq => hex ⟨f, hf, heq⟩) hprep
      exact InlineFuseProof.evalFn_of_worldSub hsub ev
    | some roots =>
      rw [hroots] at hPrunedHas hExtPM
      exact pruneUnreachable_backward hauxPM hPrunedHas hMidProv hExtPM ev
  exact lowerFieldOpsCore_backward hpEq hauxMO hndNames hndParams hPlain
    hMidHas hOrigHas hOrigProv hExtMO hspec evMid

end BackwardSoundness

/-! ## Section 5: 3-Field Concrete Corollaries (`Goldilocks`, `BN254`, `BLS12-381`) & Axiom Pins -/

section ThreeFieldCorollaries

/-- Concrete Goldilocks (`p_G = 2^64 - 2^32 + 1`) modular arithmetic & Fermat inverse soundness. -/
theorem goldilocks_fieldOps_sound (a b : Nat) (ha : a < goldilocksModulus)
    (hb : b < goldilocksModulus) :
    ((a : ZMod goldilocksModulus) + (b : ZMod goldilocksModulus) =
      (((a + b) % goldilocksModulus : Nat) : ZMod goldilocksModulus)) ∧
    ((a : ZMod goldilocksModulus) - (b : ZMod goldilocksModulus) =
      (((a + goldilocksModulus - b) % goldilocksModulus : Nat) : ZMod goldilocksModulus)) ∧
    ((a : ZMod goldilocksModulus) * (b : ZMod goldilocksModulus) =
      (((a * b) % goldilocksModulus : Nat) : ZMod goldilocksModulus)) ∧
    ((0 - (a : ZMod goldilocksModulus)) =
      (((goldilocksModulus - a) % goldilocksModulus : Nat) : ZMod goldilocksModulus)) ∧
    ((((a ^ (goldilocksModulus - 2) % goldilocksModulus : Nat) : ZMod goldilocksModulus)) =
      (a : ZMod goldilocksModulus)⁻¹) :=
  ⟨zmod_add_eq_mod a b,
   zmod_sub_eq_mod (Nat.le_of_lt hb),
   zmod_mul_eq_mod a b,
   zmod_neg_eq_mod (Nat.le_of_lt ha),
   zmod_inv_eq_fermat (by unfold goldilocksModulus Aiur.Library.U32.Goldilocks.modulus; norm_num) a⟩

/-- Concrete BN254 scalar field (`Fr`) modular arithmetic & Fermat inverse soundness. -/
theorem bn254_fieldOps_sound (a b : Nat) (ha : a < bn254Modulus)
    (hb : b < bn254Modulus) :
    ((a : ZMod bn254Modulus) + (b : ZMod bn254Modulus) =
      (((a + b) % bn254Modulus : Nat) : ZMod bn254Modulus)) ∧
    ((a : ZMod bn254Modulus) - (b : ZMod bn254Modulus) =
      (((a + bn254Modulus - b) % bn254Modulus : Nat) : ZMod bn254Modulus)) ∧
    ((a : ZMod bn254Modulus) * (b : ZMod bn254Modulus) =
      (((a * b) % bn254Modulus : Nat) : ZMod bn254Modulus)) ∧
    ((0 - (a : ZMod bn254Modulus)) =
      (((bn254Modulus - a) % bn254Modulus : Nat) : ZMod bn254Modulus)) ∧
    ((((a ^ (bn254Modulus - 2) % bn254Modulus : Nat) : ZMod bn254Modulus)) =
      (a : ZMod bn254Modulus)⁻¹) :=
  ⟨zmod_add_eq_mod a b,
   zmod_sub_eq_mod (Nat.le_of_lt hb),
   zmod_mul_eq_mod a b,
   zmod_neg_eq_mod (Nat.le_of_lt ha),
   zmod_inv_eq_fermat (by unfold bn254Modulus Aiur.Library.Field.BN254.modulus; norm_num) a⟩

/-- Concrete BLS12-381 scalar field (`Fr`) modular arithmetic & Fermat inverse soundness. -/
theorem bls12381_fieldOps_sound (a b : Nat) (ha : a < bls12381Modulus)
    (hb : b < bls12381Modulus) :
    ((a : ZMod bls12381Modulus) + (b : ZMod bls12381Modulus) =
      (((a + b) % bls12381Modulus : Nat) : ZMod bls12381Modulus)) ∧
    ((a : ZMod bls12381Modulus) - (b : ZMod bls12381Modulus) =
      (((a + bls12381Modulus - b) % bls12381Modulus : Nat) : ZMod bls12381Modulus)) ∧
    ((a : ZMod bls12381Modulus) * (b : ZMod bls12381Modulus) =
      (((a * b) % bls12381Modulus : Nat) : ZMod bls12381Modulus)) ∧
    ((0 - (a : ZMod bls12381Modulus)) =
      (((bls12381Modulus - a) % bls12381Modulus : Nat) : ZMod bls12381Modulus)) ∧
    ((((a ^ (bls12381Modulus - 2) % bls12381Modulus : Nat) : ZMod bls12381Modulus)) =
      (a : ZMod bls12381Modulus)⁻¹) :=
  ⟨zmod_add_eq_mod a b,
   zmod_sub_eq_mod (Nat.le_of_lt hb),
   zmod_mul_eq_mod a b,
   zmod_neg_eq_mod (Nat.le_of_lt ha),
   zmod_inv_eq_fermat (by unfold bls12381Modulus Aiur.Library.Field.BLS12381.modulus; norm_num) a⟩

/-- End-to-end backward `EvalFn` soundness of `lowerFieldOps` + `pruneUnreachable`
instantiated at **Goldilocks (`p_G`)**. -/
theorem lowerFieldOps_backward_goldilocks
    {wPruned wMid wOrig : World Aiur.Library.U32.Goldilocks.F}
    {cfg : Config} {fns : List Fn}
    (hpEq : cfg.ambientModulus = goldilocksModulus)
    (hauxPM : SameAuxWorld wPruned wMid)
    (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerFieldOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerFieldOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerFieldOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerFieldOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerFieldOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : FieldLowerSpec wOrig (effectiveBindings cfg fns) cfg.stripCheckU56 cfg.foldConstHelpers)
    {nm : String} {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)}
    {h h' : Heap Aiur.Library.U32.Goldilocks.F} {r : SourceValue Aiur.Library.U32.Goldilocks.F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerFieldOps_backward (p := goldilocksModulus) hpEq hauxPM hauxMO hndNames hndParams
    hPlain hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

/-- End-to-end backward `EvalFn` soundness of `lowerFieldOps` + `pruneUnreachable`
instantiated at **BN254 (`Fr`)**. -/
theorem lowerFieldOps_backward_bn254
    {wPruned wMid wOrig : World Aiur.Library.Field.BN254.F}
    {cfg : Config} {fns : List Fn}
    (hpEq : cfg.ambientModulus = bn254Modulus)
    (hauxPM : SameAuxWorld wPruned wMid)
    (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerFieldOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerFieldOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerFieldOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerFieldOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerFieldOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : FieldLowerSpec wOrig (effectiveBindings cfg fns) cfg.stripCheckU56 cfg.foldConstHelpers)
    {nm : String} {args : List (SourceValue Aiur.Library.Field.BN254.F)}
    {h h' : Heap Aiur.Library.Field.BN254.F} {r : SourceValue Aiur.Library.Field.BN254.F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerFieldOps_backward (p := bn254Modulus) hpEq hauxPM hauxMO hndNames hndParams
    hPlain hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

/-- End-to-end backward `EvalFn` soundness of `lowerFieldOps` + `pruneUnreachable`
instantiated at **BLS12-381 (`Fr`)**. -/
theorem lowerFieldOps_backward_bls12381
    {wPruned wMid wOrig : World Aiur.Library.Field.BLS12381.F}
    {cfg : Config} {fns : List Fn}
    (hpEq : cfg.ambientModulus = bls12381Modulus)
    (hauxPM : SameAuxWorld wPruned wMid)
    (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerFieldOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerFieldOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerFieldOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerFieldOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerFieldOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : FieldLowerSpec wOrig (effectiveBindings cfg fns) cfg.stripCheckU56 cfg.foldConstHelpers)
    {nm : String} {args : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    {h h' : Heap Aiur.Library.Field.BLS12381.F} {r : SourceValue Aiur.Library.Field.BLS12381.F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerFieldOps_backward (p := bls12381Modulus) hpEq hauxPM hauxMO hndNames hndParams
    hPlain hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

end ThreeFieldCorollaries

/-! ## Section 6: Kernel-Checked Axiom Pins (Strictly `[propext, Classical.choice, Quot.sound]`) -/

/-- info: 'IxCC.AiurBackend.FieldLowerProof.fieldsIsZeroSpec_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fieldsIsZeroSpec_of_check

/-- info: 'IxCC.AiurBackend.FieldLowerProof.evalExpr_fieldInv_fermat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms evalExpr_fieldInv_fermat

/-- info: 'IxCC.AiurBackend.FieldLowerProof.lowerFieldOps_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerFieldOps_backward

/-- info: 'IxCC.AiurBackend.FieldLowerProof.goldilocks_fieldOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms goldilocks_fieldOps_sound

/-- info: 'IxCC.AiurBackend.FieldLowerProof.bn254_fieldOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bn254_fieldOps_sound

/-- info: 'IxCC.AiurBackend.FieldLowerProof.bls12381_fieldOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bls12381_fieldOps_sound

/--
info: 'IxCC.AiurBackend.FieldLowerProof.lowerFieldOps_backward_goldilocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms lowerFieldOps_backward_goldilocks

/--
info: 'IxCC.AiurBackend.FieldLowerProof.lowerFieldOps_backward_bn254' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms lowerFieldOps_backward_bn254

/--
info: 'IxCC.AiurBackend.FieldLowerProof.lowerFieldOps_backward_bls12381' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms lowerFieldOps_backward_bls12381

end IxCC.AiurBackend.FieldLowerProof
