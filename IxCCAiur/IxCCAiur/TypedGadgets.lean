import IxCCAiur.TypedWorld
import Aiur.Library.U32.Correctness

/-! # Certified Operational Contracts for Typed 56-bit and `UInt32` Gadgets (`IxCCAiur.TypedGadgets`)

Proves exact operational contracts over `Aiur.Generic.SourceSemantics.EvalFn` for the
demand-linked typed gadgets emitted by `IxCCAiur.TypedLower`:

1. **`FieldCompatible64 F`**: injectivity of `Nat.cast : Nat → F` below
   `fieldBound64 = 2^64 - 2^32 + 1` (the Goldilocks prime), discharged for
   `Aiur.Library.U32.Goldilocks.F`, with projections to `Gadgets.FieldCompatible F`,
   `Aiur.Library.U32.Compatible F`, and `Aiur.Library.U64.Compatible F`.
2. **Unified `ByteCheckSpec world usePair`**: abstracts over both the slim 256-row
   `U8Byte::check` table (`usePair = false`) and `UInt8::from_fields` backed by
   `UInt8::range_pair` (`usePair = true`), yielding unified soundness contracts
   `eval_check_u8`, `eval_check_u16`, `eval_check_u24`, and `eval_check_u56`.
3. **All core 56-bit arithmetic gadgets**:
   `eval_sub_borrow_56`, `eval_split_32_24` (+ `_any`), `eval_mul_56` (+ `_any`),
   `eval_divmod_56`, `eval_pow_56_loop`, `eval_pow_56`, `eval_gcd_56`,
   `eval_shl_56`, and `eval_shr_56`.
4. **Sound `UInt32` helpers under `FieldCompatible64`**:
   `U32Contracts`, `eval_u32_complement`, `eval_u32_div`, `eval_u32_mod`,
   `eval_u32_shr`, and `eval_u32_of_field`.
5. **Plainness lemmas**: `isPlainExpr` proved for every gadget body and for
   `demandedHelpers d usePair`.

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedGadgets

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.World
open IxCC.AiurBackend.TypedRep IxCC.AiurBackend.TypedLower IxCC.AiurBackend.TypedWorld

/-! ## Field Compatibility Below Goldilocks (`2^64 - 2^32 + 1`) -/

/-- Exact Goldilocks modulus bound `2^64 - 2^32 + 1 = 18446744069414584321`. -/
def fieldBound64 : Nat := 2 ^ 64 - 2 ^ 32 + 1

/-- Natural casts are injective below `2^64 - 2^32 + 1` (the Goldilocks prime),
ensuring exact 32×32 products (`(2^32 - 1)^2 = 2^64 - 2^33 + 1 < fieldBound64`)
and exact 56-bit arithmetic (`sub_borrow_56`, `mul_56`, `divmod_56`, `pow_56`,
`gcd_56`, `shl_56`, `shr_56`) with zero field wraparound. -/
def FieldCompatible64 (F : Type) [NatCast F] : Prop :=
  Set.InjOn (Nat.cast : Nat → F) (Set.Iio fieldBound64)

theorem FieldCompatible64.of_charP (F : Type) [AddGroupWithOne F] (p : Nat) [CharP F p]
    (large : fieldBound64 ≤ p) : FieldCompatible64 F := by
  intro a ha b hb equal
  exact CharP.natCast_injOn_Iio F p (lt_of_lt_of_le ha large) (lt_of_lt_of_le hb large) equal

theorem FieldCompatible64.of_charZero (F : Type) [AddMonoidWithOne F] [CharZero F] :
    FieldCompatible64 F := by
  intro a _ b _ equal
  exact Nat.cast_injective equal

/-- Goldilocks (`ZMod 18446744069414584321`) satisfies `FieldCompatible64`. -/
theorem fieldCompatible64_goldilocks : FieldCompatible64 U32.Goldilocks.F :=
  FieldCompatible64.of_charP U32.Goldilocks.F U32.Goldilocks.modulus (by decide)

theorem FieldCompatible64.toFieldCompatible {F : Type} [NatCast F] (fc : FieldCompatible64 F) :
    FieldCompatible F := by
  intro a ha b hb equal
  have hlt : 2 ^ 57 < fieldBound64 := by decide
  exact fc (lt_trans ha hlt) (lt_trans hb hlt) equal

theorem FieldCompatible64.toU32Compatible {F : Type} [NatCast F] (fc : FieldCompatible64 F) :
    U32.Compatible F := by
  intro a ha b hb equal
  have hlt : 3 * U32.base < fieldBound64 := by decide
  exact fc (lt_trans ha hlt) (lt_trans hb hlt) equal

theorem FieldCompatible64.toU64Compatible {F : Type} [NatCast F] (fc : FieldCompatible64 F) :
    U64.Compatible F :=
  fc.toFieldCompatible.u64

section Field64Facts

variable {F : Type} [Field F]

theorem FieldCompatible64.natCast_inj (fc : FieldCompatible64 F) {a b : Nat}
    (ha : a < fieldBound64) (hb : b < fieldBound64) (heq : (a : F) = (b : F)) : a = b :=
  fc ha hb heq

theorem FieldCompatible64.natCast_inj56 (fc : FieldCompatible64 F) {a b : Nat}
    (ha : a < natLimit) (hb : b < natLimit) (heq : (a : F) = (b : F)) : a = b :=
  fc.toFieldCompatible.natCast_inj56 ha hb heq

theorem FieldCompatible64.ne_zero_of_pos (fc : FieldCompatible64 F) {a : Nat}
    (hpos : 0 < a) (hlt : a < fieldBound64) : (a : F) ≠ 0 := by
  intro h
  have h0 : a = 0 := fc.natCast_inj hlt (by unfold fieldBound64; omega) (by simp [h])
  omega

theorem FieldCompatible64.ne_zero_of_pos56 (fc : FieldCompatible64 F) {a : Nat}
    (hpos : 0 < a) (hlt : a < natLimit) : (a : F) ≠ 0 :=
  fc.toFieldCompatible.ne_zero_of_pos hpos (lt_trans hlt (by unfold natLimit; omega))

end Field64Facts

/-! ## Qualification and Plainness Lemmas for All Typed Gadgets -/

section PlainAndQualify

@[simp] theorem qualifyName_u8Byte_check : qualifyName "U8Byte::check" = "U8Byte::check" := rfl
@[simp] theorem qualifyName_u8_from_fields :
    qualifyName "UInt8::from_fields" = "UInt8::from_fields" := rfl
@[simp] theorem qualifyName_u8_to_field :
    qualifyName "UInt8::to_field" = "UInt8::to_field" := rfl
@[simp] theorem qualifyName_u32_compact :
    qualifyName "UInt32::compact" = "UInt32::compact" := rfl
@[simp] theorem qualifyName_u32_compact_field :
    qualifyName "UInt32::compact_field" = "UInt32::compact_field" := rfl
@[simp] theorem qualifyName_u32_from_fields :
    qualifyName "UInt32::from_fields" = "UInt32::from_fields" := rfl
@[simp] theorem qualifyName_u32_from_field :
    qualifyName "UInt32::from_field" = "UInt32::from_field" := rfl
@[simp] theorem qualifyName_u32_to_bytes :
    qualifyName "UInt32::to_bytes" = "UInt32::to_bytes" := rfl
@[simp] theorem qualifyName_check_u8 : qualifyName "check_u8" = qualified "check_u8" := rfl
@[simp] theorem qualifyName_check_u16 : qualifyName "check_u16" = qualified "check_u16" := rfl
@[simp] theorem qualifyName_check_u24 : qualifyName "check_u24" = qualified "check_u24" := rfl
@[simp] theorem qualifyName_check_u56 : qualifyName "check_u56" = qualified "check_u56" := rfl
@[simp] theorem qualifyName_sub_borrow_56 :
    qualifyName "sub_borrow_56" = qualified "sub_borrow_56" := rfl
@[simp] theorem qualifyName_split_32_24 :
    qualifyName "split_32_24" = qualified "split_32_24" := rfl
@[simp] theorem qualifyName_mul_56 : qualifyName "mul_56" = qualified "mul_56" := rfl
@[simp] theorem qualifyName_divmod_56 : qualifyName "divmod_56" = qualified "divmod_56" := rfl
@[simp] theorem qualifyName_pow_56_loop :
    qualifyName "pow_56_loop" = qualified "pow_56_loop" := rfl
@[simp] theorem qualifyName_pow_56 : qualifyName "pow_56" = qualified "pow_56" := rfl
@[simp] theorem qualifyName_gcd_56 : qualifyName "gcd_56" = qualified "gcd_56" := rfl
@[simp] theorem qualifyName_shl_56 : qualifyName "shl_56" = qualified "shl_56" := rfl
@[simp] theorem qualifyName_shr_56 : qualifyName "shr_56" = qualified "shr_56" := rfl
@[simp] theorem qualifyName_u32_mul : qualifyName "u32_mul" = qualified "u32_mul" := rfl
@[simp] theorem qualifyName_u32_complement :
    qualifyName "u32_complement" = qualified "u32_complement" := rfl
@[simp] theorem qualifyName_u32_div : qualifyName "u32_div" = qualified "u32_div" := rfl
@[simp] theorem qualifyName_u32_mod : qualifyName "u32_mod" = qualified "u32_mod" := rfl
@[simp] theorem qualifyName_u32_shl : qualifyName "u32_shl" = qualified "u32_shl" := rfl
@[simp] theorem qualifyName_u32_shr : qualifyName "u32_shr" = qualified "u32_shr" := rfl
@[simp] theorem qualifyName_u32_of_field :
    qualifyName "u32_of_field" = qualified "u32_of_field" := rfl

theorem isPlainExpr_checkU8Fn (usePair : Bool) : isPlainExpr (checkU8Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_checkU16Fn (usePair : Bool) : isPlainExpr (checkU16Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_checkU24Fn (usePair : Bool) : isPlainExpr (checkU24Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_checkU56Fn (usePair : Bool) : isPlainExpr (checkU56Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_subBorrow56Fn (usePair : Bool) :
    isPlainExpr (subBorrow56Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_split32_24Fn (usePair : Bool) :
    isPlainExpr (split32_24Fn usePair).body = true := by
  cases usePair <;> rfl

theorem isPlainExpr_mul56Fn : isPlainExpr mul56Fn.body = true := rfl
theorem isPlainExpr_divmod56Fn : isPlainExpr divmod56Fn.body = true := rfl
theorem isPlainExpr_pow56LoopFn : isPlainExpr pow56LoopFn.body = true := rfl
theorem isPlainExpr_pow56Fn : isPlainExpr pow56Fn.body = true := rfl
theorem isPlainExpr_gcd56Fn : isPlainExpr gcd56Fn.body = true := rfl
theorem isPlainExpr_shl56Fn : isPlainExpr shl56Fn.body = true := rfl
theorem isPlainExpr_shr56Fn : isPlainExpr shr56Fn.body = true := rfl
theorem isPlainExpr_u32MulFn : isPlainExpr u32MulFn.body = true := rfl
theorem isPlainExpr_u32ComplementFn : isPlainExpr u32ComplementFn.body = true := rfl
theorem isPlainExpr_u32DivFn : isPlainExpr u32DivFn.body = true := rfl
theorem isPlainExpr_u32ModFn : isPlainExpr u32ModFn.body = true := rfl
theorem isPlainExpr_u32ShlFn : isPlainExpr u32ShlFn.body = true := rfl
theorem isPlainExpr_u32ShrFn : isPlainExpr u32ShrFn.body = true := rfl
theorem isPlainExpr_u32OfFieldFn : isPlainExpr u32OfFieldFn.body = true := rfl
theorem isPlainExpr_u64ShlFn : isPlainExpr u64ShlFn.body = true := by
  simp [u64ShlFn, letE, matchE, callE, vE, litE, subE, isPlainExpr, isPlainList, isPlainArms]
  rfl
theorem isPlainExpr_u64ShrFn : isPlainExpr u64ShrFn.body = true := by
  simp [u64ShrFn, letE, matchE, callE, vE, litE, addE, subE, isPlainExpr, isPlainList, isPlainArms]
  exact ⟨rfl, rfl⟩

theorem isPlainExpr_demandedHelpers (d : Demand) (usePair : Bool) :
    ∀ f ∈ demandedHelpers d usePair, isPlainExpr f.body = true := by
  have happ : ∀ {xs ys : List Fn},
      (∀ f ∈ xs, isPlainExpr f.body = true) → (∀ f ∈ ys, isPlainExpr f.body = true) →
      ∀ f ∈ xs ++ ys, isPlainExpr f.body = true := by
    intro xs ys hxs hys f hf
    rcases List.mem_append.mp hf with h | h
    · exact hxs f h
    · exact hys f h
  have h1 : ∀ (c : Bool) (g : Fn),
      isPlainExpr g.body = true → ∀ f ∈ (if c then [g] else []), isPlainExpr f.body = true := by
    intro c g hg f h; split at h
    · simp only [List.mem_singleton] at h; subst h; exact hg
    · simp at h
  have h2 : ∀ (c : Bool) (g1 g2 : Fn),
      isPlainExpr g1.body = true → isPlainExpr g2.body = true →
      ∀ f ∈ (if c then [g1, g2] else []), isPlainExpr f.body = true := by
    intro c g1 g2 hg1 hg2 f h; split at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> assumption
    · simp at h
  unfold demandedHelpers
  refine happ (happ (happ (happ (happ (happ (happ (happ (happ (happ
    (happ (happ (happ (happ (happ (happ (happ (happ (happ
      (h2 _ _ _ (isPlainExpr_checkU8Fn usePair) (isPlainExpr_checkU56Fn usePair))
      (h1 _ _ (isPlainExpr_checkU16Fn usePair)))
      (h1 _ _ (isPlainExpr_checkU24Fn usePair)))
      (h1 _ _ (isPlainExpr_subBorrow56Fn usePair)))
      (h1 _ _ (isPlainExpr_split32_24Fn usePair)))
      (h1 _ _ isPlainExpr_mul56Fn))
      (h1 _ _ isPlainExpr_divmod56Fn))
      (h2 _ _ _ isPlainExpr_pow56LoopFn isPlainExpr_pow56Fn))
      (h1 _ _ isPlainExpr_gcd56Fn))
      (h1 _ _ isPlainExpr_shl56Fn))
      (h1 _ _ isPlainExpr_shr56Fn))
      (h1 _ _ isPlainExpr_u32MulFn))
      (h1 _ _ isPlainExpr_u32ComplementFn))
      (h1 _ _ isPlainExpr_u32DivFn))
      (h1 _ _ isPlainExpr_u32ModFn))
      (h1 _ _ isPlainExpr_u32ShlFn))
      (h1 _ _ isPlainExpr_u32ShrFn))
      (h1 _ _ isPlainExpr_u32OfFieldFn))
      (h1 _ _ isPlainExpr_u64ShlFn))
      (h1 _ _ isPlainExpr_u64ShrFn)

end PlainAndQualify

/-! ## Additional Straight-Line `EvalExpr` Inversion Helpers -/

section EvalHelpers

variable {F : Type} [Field F] [DecidableEq F]

theorem evalExpr_tuple0_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.tuple []) h r h') :
    r = .tuple [] ∧ h' = h := by
  cases ev with
  | tuple hargs =>
    cases hargs
    exact ⟨rfl, rfl⟩

theorem evalExpr_call3_inv {world : World F} {locals : Environment F Nat}
    {name : String} {a b c : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.call name (some []) [a, b, c]) h r h') :
    ∃ va vb vc h1 h2 hm,
      EvalExpr world [] locals a h va h1 ∧
      EvalExpr world [] locals b h1 vb h2 ∧
      EvalExpr world [] locals c h2 vc hm ∧
      EvalFn world name [va, vb, vc] hm r h' := by
  obtain ⟨vs, hm, hargs, hcal⟩ := evalExpr_call_inv ev
  cases hargs with
  | cons ha ht1 =>
    cases ht1 with
    | cons hb ht2 =>
      cases ht2 with
      | cons hc ht3 =>
        cases ht3
        exact ⟨_, _, _, _, _, _, ha, hb, hc, hcal⟩

theorem evalExpr_array4_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {e0 e1 e2 e3 : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.array [e0, e1, e2, e3]) h r h') :
    ∃ v0 v1 v2 v3 h1 h2 h3,
      EvalExpr world types locals e0 h v0 h1 ∧
      EvalExpr world types locals e1 h1 v1 h2 ∧
      EvalExpr world types locals e2 h2 v2 h3 ∧
      EvalExpr world types locals e3 h3 v3 h' ∧
      r = .tuple [v0, v1, v2, v3] := by
  cases ev with
  | array hargs =>
    cases hargs with | cons h0 t0 =>
    cases t0 with | cons h1 t1 =>
    cases t1 with | cons h2 t2 =>
    cases t2 with | cons h3 t3 =>
    cases t3
    exact ⟨_, _, _, _, _, _, _, h0, h1, h2, h3, rfl⟩

theorem evalExpr_let_wild_tuple2_inv {world : World F} {types : Types} {locals : Environment F Nat}
    {y : String} {e b : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world types locals (.letValue (.tuple [.wildcard, .bind y]) e b) h r h') :
    ∃ vx vy hm,
      EvalExpr world types locals e h (.tuple [vx, vy]) hm ∧
      EvalExpr world types ((y, vy) :: locals) b hm r h' := by
  cases ev with
  | letValue hv hm hb =>
    rename_i inp _ bindings
    cases inp with
    | tuple vs =>
      rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;>
        simp [World.matchPattern, matchPatternWith, matchListWith] at hm
      subst hm
      exact ⟨v0, v1, _, hv, hb⟩
    | field _ | ptr _ _ | construct _ _ _ => simp [World.matchPattern, matchPatternWith] at hm

theorem evalExpr_match_lit_wild_inv {world : World F} {locals : Environment F Nat}
    {scrut e0 e1 : Aiur.Generic.Expr F} {c : F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (.matchValue scrut [(.literal c, e0), (.wildcard, e1)]) h r h') :
    ∃ v hm,
      EvalExpr world [] locals scrut h v hm ∧
      ((v = .field c ∧ EvalExpr world [] locals e0 hm r h') ∨
       (v ≠ .field c ∧ EvalExpr world [] locals e1 hm r h')) := by
  cases ev with
  | matchValue evs hsel hbr =>
    rename_i v hm bindings body
    cases v with
    | field x =>
      by_cases hxc : x = c
      · subst hxc
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨.field x, hm, evs, Or.inl ⟨rfl, hbr⟩⟩
      · have hcx : c ≠ x := Ne.symm hxc
        simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
          Aiur.Pattern.bindings, hcx] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨.field x, hm, evs, Or.inr ⟨fun h => hxc (Value.field.inj h), hbr⟩⟩
    | tuple vs =>
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact ⟨.tuple vs, hm, evs, Or.inr ⟨by simp, hbr⟩⟩
    | ptr p a =>
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact ⟨.ptr p a, hm, evs, Or.inr ⟨by simp, hbr⟩⟩
    | construct en ctor xs =>
      simp [SourceSemantics.selectArm, World.matchPattern, matchPatternWith,
        Aiur.Pattern.bindings] at hsel
      obtain ⟨rfl, rfl⟩ := hsel
      exact ⟨.construct en ctor xs, hm, evs, Or.inr ⟨by simp, hbr⟩⟩

private theorem evalExpr_var_eq {world : World F} {locals : Environment F Nat}
    {nm : String} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.var nm) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨hl, rfl⟩ := evalExpr_var_inv ev
  rw [hlook, Option.some.injEq, Prod.mk.injEq] at hl
  exact ⟨hl.2.symm, rfl⟩

private theorem evalExpr_mul_lit_var_eq {world : World F} {locals : Environment F Nat}
    {c b : Nat} {nm : String} {r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, .field (b : F)))
    (ev : EvalExpr world [] locals (.binary .mul (.literal (c : F)) (.var nm)) h r h') :
    r = .field ((c * b : Nat) : F) ∧ h' = h := by
  obtain ⟨vl, vr, _, evl, evr, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evl
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evr
  simp only [evalBinOp, Except.ok.injEq] at hop
  subst hop
  exact ⟨by push_cast; rfl, rfl⟩

private theorem evalExpr_add_fields {world : World F} {locals : Environment F Nat}
    {e1 e2 : Aiur.Generic.Expr F} {a b : Nat} {r : SourceValue F} {h h' : Heap F}
    (h1 : ∀ r1 h1, EvalExpr world [] locals e1 h r1 h1 → r1 = .field (a : F) ∧ h1 = h)
    (h2 : ∀ r2 h2, EvalExpr world [] locals e2 h r2 h2 → r2 = .field (b : F) ∧ h2 = h)
    (ev : EvalExpr world [] locals (.binary .add e1 e2) h r h') :
    r = .field ((a + b : Nat) : F) ∧ h' = h := by
  obtain ⟨vl, vr, hm, evl, evr, hop⟩ := evalExpr_binary_inv ev
  obtain ⟨rfl, rfl⟩ := h1 vl hm evl
  obtain ⟨rfl, rfl⟩ := h2 vr h' evr
  simp only [evalBinOp, Except.ok.injEq] at hop
  subst hop
  exact ⟨by push_cast; rfl, rfl⟩

private theorem evalExpr_assertVarZero_seq_inv {world : World F} {locals : Environment F Nat}
    {nm : String} {a : Aiur.Assertion} {v : SourceValue F} {body : Aiur.Generic.Expr F}
    {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals
      (.letValue .wildcard (.builtin (.assertEq a) [.var nm, .literal (0 : F)]) body) h r h') :
    v = .field (0 : F) ∧ EvalExpr world [] locals body h r h' := by
  obtain ⟨_, _, hass, hrest⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evl
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evr
  exact ⟨heq, hrest⟩

end EvalHelpers

/-! ## Unified Byte-Check Hypothesis (`ByteCheckSpec world usePair`) -/

section ByteCheck

variable {F : Type} [Field F] [DecidableEq F]

/-- Operational contract for `UInt8::from_fields(a, b) -> (U8, U8)`: verifies both
arguments are `< 256` field elements and leaves the heap unchanged. -/
def U8FromFieldsSpec (world : World F) : Prop :=
  ∀ v1 v2 h r h',
    EvalFn world "UInt8::from_fields" [v1, v2] h r h' →
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)

/-- Expected elaborated body of `UInt8::from_fields`. -/
def u8FromFieldsBody : Aiur.Generic.Expr F :=
  .letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
    (.tuple [.var "a", .var "b"])

/-- Computable check that `UInt8::from_fields` is installed with its exact library body. -/
def checkU8FromFields (s : Generic.Source F) : Bool :=
  match s.program.findFunction? "UInt8::from_fields" with
  | some f => f.typeParams.isEmpty && (f.params.map Prod.fst == ["a", "b"]) &&
      (f.body == u8FromFieldsBody)
  | none => false

theorem u8FromFieldsSpec_of_mapSpec {world : World F}
    (maps : U8MapSpec world)
    (hfn : WorldHasFn world "UInt8::from_fields" ["a", "b"] u8FromFieldsBody) :
    U8FromFieldsSpec world := by
  intro v1 v2 h r h' ev
  obtain ⟨_, b⟩ := evalFn_plain_inv hfn (by rfl) ev
  obtain ⟨_, _, hcall, hret⟩ := evalExpr_let_wildcard_inv b
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
  obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := maps.range_pair _ _ _ _ _ hcal
  obtain ⟨va', vb', _, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  exact ⟨rfl, rfl, a, b', ha, hb, rfl, rfl⟩

theorem u8FromFieldsSpec_of_u64LibraryWorld {world : World F} (lib : U64LibraryWorld world) :
    U8FromFieldsSpec world :=
  fun _ _ _ _ _ ev => Gadgets.u8_from_fields_spec lib ev

/-- Unified byte range-check hypothesis parameterized by `TypedLower`'s `usePair : Bool`:
* `false` (`TableTier.byte256`): slim 256-row `U8Byte::check` map (`TypedWorld.U8ByteSpec`);
* `true` (`TableTier.u32` / `TableTier.u64`): `UInt8::from_fields` backed by `UInt8::range_pair`. -/
def ByteCheckSpec (world : World F) : Bool → Prop
  | false => TypedWorld.U8ByteSpec world
  | true => U8FromFieldsSpec world

theorem byteCheckSpec_false_of_check {s : Generic.Source F}
    (h : checkU8ByteTable s = true) : ByteCheckSpec s.world false :=
  TypedWorld.u8ByteSpec_of_check h

theorem byteCheckSpec_true_of_check {s : Generic.Source F}
    (ht : checkTables s = true) (hf : checkU8FromFields s = true) :
    ByteCheckSpec s.world true :=
  u8FromFieldsSpec_of_mapSpec
    (u8MapSpec_of_source s (u8TablesMatch_of_check ht))
    (worldHasFn_of_check s (by decide) hf)

theorem byteCheckSpec_true_of_u64LibraryWorld {world : World F}
    (lib : U64LibraryWorld world) : ByteCheckSpec world true :=
  u8FromFieldsSpec_of_u64LibraryWorld lib

/-! ### Reusable Byte-Sequence Inversion Helpers -/

private theorem eval_u8Byte_seq_var {world : World F} {locals : Environment F Nat}
    (hspec : U8ByteSpec world) {nm : String} {v : SourceValue F}
    {body : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals
      (.letValue .wildcard (.call "U8Byte::check" (some []) [.var nm]) body) h r h') :
    ∃ b : Nat, b < 256 ∧ v = .field (b : F) ∧ EvalExpr world [] locals body h r h' := by
  obtain ⟨_, _, hcall, hrest⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨va, _, eva, hcal⟩ := evalExpr_call1_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook eva
  obtain ⟨_, rfl, b, hb, rfl⟩ := hspec _ _ _ _ hcal
  exact ⟨b, hb, rfl, hrest⟩

private theorem eval_pair_seq_vars {world : World F} {locals : Environment F Nat}
    (hspec : U8FromFieldsSpec world) {n1 n2 : String} {v1 v2 : SourceValue F}
    {body : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hl1 : locals.find? (·.1 == n1) = some (n1, v1))
    (hl2 : locals.find? (·.1 == n2) = some (n2, v2))
    (ev : EvalExpr world [] locals
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var n1, .var n2]) body) h r h') :
    ∃ b1 b2 : Nat, b1 < 256 ∧ b2 < 256 ∧ v1 = .field (b1 : F) ∧ v2 = .field (b2 : F) ∧
      EvalExpr world [] locals body h r h' := by
  obtain ⟨_, _, hcall, hrest⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl1 eva
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl2 evb
  obtain ⟨_, rfl, b1, b2, hb1, hb2, rfl, rfl⟩ := hspec _ _ _ _ _ hcal
  exact ⟨b1, b2, hb1, hb2, rfl, rfl, hrest⟩

private theorem eval_pair_seq_var0 {world : World F} {locals : Environment F Nat}
    (hspec : U8FromFieldsSpec world) {n1 : String} {v1 : SourceValue F}
    {body : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (hl1 : locals.find? (·.1 == n1) = some (n1, v1))
    (ev : EvalExpr world [] locals
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var n1, .literal (0 : F)]) body)
      h r h') :
    ∃ b1 : Nat, b1 < 256 ∧ v1 = .field (b1 : F) ∧ EvalExpr world [] locals body h r h' := by
  obtain ⟨_, _, hcall, hrest⟩ := evalExpr_let_wildcard_inv ev
  obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hl1 eva
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evb
  obtain ⟨_, rfl, b1, _, hb1, _, rfl, _⟩ := hspec _ _ _ _ _ hcal
  exact ⟨b1, hb1, rfl, hrest⟩

private theorem eval_recompose7 {world : World F} {locals : Environment F Nat}
    {b0 b1 b2 b3 b4 b5 b6 : Nat} {r : SourceValue F} {h h' : Heap F}
    (l0 : locals.find? (·.1 == "b0") = some ("b0", .field (b0 : F)))
    (l1 : locals.find? (·.1 == "b1") = some ("b1", .field (b1 : F)))
    (l2 : locals.find? (·.1 == "b2") = some ("b2", .field (b2 : F)))
    (l3 : locals.find? (·.1 == "b3") = some ("b3", .field (b3 : F)))
    (l4 : locals.find? (·.1 == "b4") = some ("b4", .field (b4 : F)))
    (l5 : locals.find? (·.1 == "b5") = some ("b5", .field (b5 : F)))
    (l6 : locals.find? (·.1 == "b6") = some ("b6", .field (b6 : F)))
    (ev : EvalExpr world [] locals
      (.binary .add (.var "b0")
        (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1"))
          (.binary .add (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b2"))
            (.binary .add (.binary .mul (.literal ((16777216 : Nat) : F)) (.var "b3"))
              (.binary .add (.binary .mul (.literal ((4294967296 : Nat) : F)) (.var "b4"))
                (.binary .add (.binary .mul (.literal ((1099511627776 : Nat) : F)) (.var "b5"))
                  (.binary .mul (.literal ((281474976710656 : Nat) : F)) (.var "b6"))))))))
      h r h') :
    r = .field ((b0 + (256 * b1 + (65536 * b2 + (16777216 * b3 +
      (4294967296 * b4 + (1099511627776 * b5 + 281474976710656 * b6))))) : Nat) : F) ∧
    h' = h := by
  apply evalExpr_add_fields (fun _ _ e => evalExpr_var_eq l0 e) _ ev
  intro _ _ e1
  apply evalExpr_add_fields (fun _ _ e => evalExpr_mul_lit_var_eq l1 e) _ e1
  intro _ _ e2
  apply evalExpr_add_fields (fun _ _ e => evalExpr_mul_lit_var_eq l2 e) _ e2
  intro _ _ e3
  apply evalExpr_add_fields (fun _ _ e => evalExpr_mul_lit_var_eq l3 e) _ e3
  intro _ _ e4
  apply evalExpr_add_fields (fun _ _ e => evalExpr_mul_lit_var_eq l4 e) _ e4
  intro _ _ e5
  exact evalExpr_add_fields (fun _ _ e => evalExpr_mul_lit_var_eq l5 e)
    (fun _ _ e => evalExpr_mul_lit_var_eq l6 e) e5

private theorem eval_byteCheck7_false {world : World F} {locals : Environment F Nat}
    (hspec : U8ByteSpec world) {v0 v1 v2 v3 v4 v5 v6 v7 : SourceValue F}
    {body : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world []
      ([("b0", v0), ("b1", v1), ("b2", v2), ("b3", v3),
        ("b4", v4), ("b5", v5), ("b6", v6), ("b7", v7)] ++ locals)
      (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                    body)))))))
      h r h') :
    ∃ b0 b1 b2 b3 b4 b5 b6 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧ b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧
      v0 = .field (b0 : F) ∧ v1 = .field (b1 : F) ∧ v2 = .field (b2 : F) ∧
      v3 = .field (b3 : F) ∧ v4 = .field (b4 : F) ∧ v5 = .field (b5 : F) ∧
      v6 = .field (b6 : F) ∧
      EvalExpr world []
        ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
          ("b3", .field (b3 : F)), ("b4", .field (b4 : F)), ("b5", .field (b5 : F)),
          ("b6", .field (b6 : F)), ("b7", v7)] ++ locals)
        body h r h' := by
  obtain ⟨b0, hb0, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b1, hb1, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b2, hb2, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b3, hb3, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b4, hb4, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b5, hb5, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  obtain ⟨b6, hb6, rfl, ev⟩ := eval_u8Byte_seq_var hspec (by simp; rfl) ev
  exact ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ev⟩

private theorem eval_byteCheck7_true {world : World F} {locals : Environment F Nat}
    (hspec : U8FromFieldsSpec world) {v0 v1 v2 v3 v4 v5 v6 v7 : SourceValue F}
    {body : Aiur.Generic.Expr F} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world []
      ([("b0", v0), ("b1", v1), ("b2", v2), ("b3", v3),
        ("b4", v4), ("b5", v5), ("b6", v6), ("b7", v7)] ++ locals)
      (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal (0 : F)])
              body))))
      h r h') :
    ∃ b0 b1 b2 b3 b4 b5 b6 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧ b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧
      v0 = .field (b0 : F) ∧ v1 = .field (b1 : F) ∧ v2 = .field (b2 : F) ∧
      v3 = .field (b3 : F) ∧ v4 = .field (b4 : F) ∧ v5 = .field (b5 : F) ∧
      v6 = .field (b6 : F) ∧
      EvalExpr world []
        ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
          ("b3", .field (b3 : F)), ("b4", .field (b4 : F)), ("b5", .field (b5 : F)),
          ("b6", .field (b6 : F)), ("b7", v7)] ++ locals)
        body h r h' := by
  obtain ⟨b0, b1, hb0, hb1, rfl, rfl, ev⟩ :=
    eval_pair_seq_vars hspec (by simp; rfl) (by simp; rfl) ev
  obtain ⟨b2, b3, hb2, hb3, rfl, rfl, ev⟩ :=
    eval_pair_seq_vars hspec (by simp; rfl) (by simp; rfl) ev
  obtain ⟨b4, b5, hb4, hb5, rfl, rfl, ev⟩ :=
    eval_pair_seq_vars hspec (by simp; rfl) (by simp; rfl) ev
  obtain ⟨b6, hb6, rfl, ev⟩ := eval_pair_seq_var0 hspec (by simp; rfl) ev
  exact ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ev⟩

/-! ### Unified Range-Check Contracts: `check_u8`, `check_u16`, `check_u24`, `check_u56` -/

theorem eval_check_u8 {world : World F} {usePair : Bool}
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "check_u8") ["x"]
      (qualifyExprF F (checkU8Fn usePair).body))
    {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "check_u8") [v] h r h') :
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 8 ∧ v = .field (n : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_checkU8Fn usePair) ev
  cases usePair with
  | false =>
    simp only [checkU8Fn, callE, vE, qualifyExprF, qualifyExpr, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, List.map, Bool.false_eq_true, ↓reduceIte] at body
    obtain ⟨va, _, eva, hcal⟩ := evalExpr_call1_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva
    obtain ⟨rfl, rfl, b, hb, rfl⟩ := hbc _ _ _ _ hcal
    exact ⟨rfl, rfl, b, by omega, rfl⟩
  | true =>
    simp only [checkU8Fn, seqE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
      qualifyName_u8_from_fields, Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map,
      List.map, ↓reduceIte, Nat.cast_zero] at body
    obtain ⟨b, hb, rfl, hret⟩ := eval_pair_seq_var0 hbc (by simp; rfl) body
    obtain ⟨rfl, rfl⟩ := evalExpr_tuple0_inv hret
    exact ⟨rfl, rfl, b, by omega, rfl⟩

private theorem body_checkU16Fn_false :
    (checkU16Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b2", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b3", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b4", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b5", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b6", .literal 0])
                      (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b7", .literal 0])
                        (.letValue .wildcard
                          (.builtin (.assertEq (assertion "u16: bytes do not recompose"))
                            [.binary .add (.var "b0") (.binary .mul (.literal 256) (.var "b1")), .var "x"])
                          (.tuple [])))))))))) := rfl

private theorem body_checkU16Fn_true :
    (checkU16Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b2", .literal 0])
            (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b3", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b4", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b5", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b6", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b7", .literal 0])
                      (.letValue .wildcard
                        (.builtin (.assertEq (assertion "u16: bytes do not recompose"))
                          [.binary .add (.var "b0") (.binary .mul (.literal 256) (.var "b1")), .var "x"])
                        (.tuple []))))))))) := rfl

theorem eval_check_u16 {world : World F} {usePair : Bool}
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "check_u16") ["x"]
      (qualifyExprF F (checkU16Fn usePair).body))
    {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "check_u16") [v] h r h') :
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 16 ∧ v = .field (n : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_checkU16Fn usePair) ev
  have htail :
      ∀ (b0 b1 : Nat) (v2 v3 v4 v5 v6 v7 : SourceValue F),
        b0 < 256 → b1 < 256 →
        EvalExpr world []
          ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", v2), ("b3", v3),
            ("b4", v4), ("b5", v5), ("b6", v6), ("b7", v7)] ++ [("x", v)])
          (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b2", .literal (0 : F)])
            (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b3", .literal (0 : F)])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b4", .literal (0 : F)])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b5", .literal (0 : F)])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b6", .literal (0 : F)])
                    (.letValue .wildcard (.builtin (.assertEq (assertion "u16: high bytes must be zero")) [.var "b7", .literal (0 : F)])
                      (.letValue .wildcard
                        (.builtin (.assertEq (assertion "u16: bytes do not recompose"))
                          [.binary .add (.var "b0") (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1")), .var "x"])
                        (.tuple []))))))))
          h r h' →
        r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 16 ∧ v = .field (n : F) := by
    intro b0 b1 v2 v3 v4 v5 v6 v7 hb0 hb1 k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, _, hass, hret⟩ := evalExpr_let_wildcard_inv k
    obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv hass
    obtain ⟨rfl, rfl⟩ := evalExpr_add_fields
      (fun _ _ e => evalExpr_var_eq (by simp; rfl) e)
      (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e) evl
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
    obtain ⟨rfl, rfl⟩ := evalExpr_tuple0_inv hret
    exact ⟨rfl, rfl, b0 + 256 * b1, by omega, heq.symm⟩
  cases usePair with
  | false =>
    rw [body_checkU16Fn_false] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, hb0, rfl, k⟩ := eval_u8Byte_seq_var hbc (by simp; rfl) k
    obtain ⟨b1, hb1, rfl, k⟩ := eval_u8Byte_seq_var hbc (by simp; rfl) k
    exact htail b0 b1 v2 v3 v4 v5 v6 v7 hb0 hb1 k
  | true =>
    rw [body_checkU16Fn_true] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, hb0, hb1, rfl, rfl, k⟩ :=
      eval_pair_seq_vars hbc (by simp; rfl) (by simp; rfl) k
    exact htail b0 b1 v2 v3 v4 v5 v6 v7 hb0 hb1 k

private theorem body_checkU24Fn_false :
    (checkU24Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b3", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b4", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b5", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b6", .literal 0])
                      (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b7", .literal 0])
                        (.letValue .wildcard
                          (.builtin (.assertEq (assertion "u24: bytes do not recompose"))
                            [.binary .add (.var "b0")
                              (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                                (.binary .mul (.literal 65536) (.var "b2"))),
                             .var "x"])
                          (.tuple [])))))))))) := rfl

private theorem body_checkU24Fn_true :
    (checkU24Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .literal 0])
            (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b3", .literal 0])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b4", .literal 0])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b5", .literal 0])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b6", .literal 0])
                    (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b7", .literal 0])
                      (.letValue .wildcard
                        (.builtin (.assertEq (assertion "u24: bytes do not recompose"))
                          [.binary .add (.var "b0")
                            (.binary .add (.binary .mul (.literal 256) (.var "b1"))
                              (.binary .mul (.literal 65536) (.var "b2"))),
                           .var "x"])
                        (.tuple []))))))))) := rfl

theorem eval_check_u24 {world : World F} {usePair : Bool}
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "check_u24") [v] h r h') :
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 24 ∧ v = .field (n : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_checkU24Fn usePair) ev
  have htail :
      ∀ (b0 b1 b2 : Nat) (v3 v4 v5 v6 v7 : SourceValue F),
        b0 < 256 → b1 < 256 → b2 < 256 →
        EvalExpr world []
          ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
            ("b3", v3), ("b4", v4), ("b5", v5), ("b6", v6), ("b7", v7)] ++ [("x", v)])
          (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b3", .literal (0 : F)])
            (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b4", .literal (0 : F)])
              (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b5", .literal (0 : F)])
                (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b6", .literal (0 : F)])
                  (.letValue .wildcard (.builtin (.assertEq (assertion "u24: high bytes must be zero")) [.var "b7", .literal (0 : F)])
                    (.letValue .wildcard
                      (.builtin (.assertEq (assertion "u24: bytes do not recompose"))
                        [.binary .add (.var "b0")
                          (.binary .add (.binary .mul (.literal ((256 : Nat) : F)) (.var "b1"))
                            (.binary .mul (.literal ((65536 : Nat) : F)) (.var "b2"))),
                         .var "x"])
                      (.tuple [])))))))
          h r h' →
        r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < 2 ^ 24 ∧ v = .field (n : F) := by
    intro b0 b1 b2 v3 v4 v5 v6 v7 hb0 hb1 hb2 k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, _, hass, hret⟩ := evalExpr_let_wildcard_inv k
    obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv hass
    obtain ⟨rfl, rfl⟩ := evalExpr_add_fields
      (fun _ _ e => evalExpr_var_eq (by simp; rfl) e)
      (fun _ _ e => evalExpr_add_fields
        (fun _ _ e1 => evalExpr_mul_lit_var_eq (by simp; rfl) e1)
        (fun _ _ e2 => evalExpr_mul_lit_var_eq (by simp; rfl) e2) e) evl
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
    obtain ⟨rfl, rfl⟩ := evalExpr_tuple0_inv hret
    exact ⟨rfl, rfl, b0 + (256 * b1 + 65536 * b2), by omega, heq.symm⟩
  cases usePair with
  | false =>
    rw [body_checkU24Fn_false] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, hb0, rfl, k⟩ := eval_u8Byte_seq_var hbc (by simp; rfl) k
    obtain ⟨b1, hb1, rfl, k⟩ := eval_u8Byte_seq_var hbc (by simp; rfl) k
    obtain ⟨b2, hb2, rfl, k⟩ := eval_u8Byte_seq_var hbc (by simp; rfl) k
    exact htail b0 b1 b2 v3 v4 v5 v6 v7 hb0 hb1 hb2 k
  | true =>
    rw [body_checkU24Fn_true] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, hb0, hb1, rfl, rfl, k⟩ :=
      eval_pair_seq_vars hbc (by simp; rfl) (by simp; rfl) k
    obtain ⟨b2, hb2, rfl, k⟩ := eval_pair_seq_var0 hbc (by simp; rfl) k
    exact htail b0 b1 b2 v3 v4 v5 v6 v7 hb0 hb1 hb2 k

private def recompose7NatExpr : Lower.Expr :=
  .binary .add (.var "b0")
    (.binary .add (.binary .mul (.literal 256) (.var "b1"))
      (.binary .add (.binary .mul (.literal 65536) (.var "b2"))
        (.binary .add (.binary .mul (.literal 16777216) (.var "b3"))
          (.binary .add (.binary .mul (.literal 4294967296) (.var "b4"))
            (.binary .add (.binary .mul (.literal 1099511627776) (.var "b5"))
              (.binary .mul (.literal 281474976710656) (.var "b6")))))))

private def checkU56TailNatExpr : Lower.Expr :=
  .letValue .wildcard
    (.builtin (.assertEq (assertion "u56: top byte must be zero")) [.var "b7", .literal 0])
    (.letValue .wildcard
      (.builtin (.assertEq (assertion "u56: bytes do not recompose")) [recompose7NatExpr, .var "x"])
      (.tuple []))

private theorem body_checkU56Fn_false :
    (checkU56Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                      checkU56TailNatExpr))))))) := rfl

private theorem body_checkU56Fn_true :
    (checkU56Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                checkU56TailNatExpr)))) := rfl

theorem eval_check_u56 {world : World F} {usePair : Bool}
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "check_u56") [v] h r h') :
    r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < natLimit ∧ v = .field (n : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_checkU56Fn usePair) ev
  have htail :
      ∀ (b0 b1 b2 b3 b4 b5 b6 : Nat) (v7 : SourceValue F),
        b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 → b4 < 256 → b5 < 256 → b6 < 256 →
        EvalExpr world []
          ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
            ("b3", .field (b3 : F)), ("b4", .field (b4 : F)), ("b5", .field (b5 : F)),
            ("b6", .field (b6 : F)), ("b7", v7)] ++ [("x", v)])
          (qualifyExprF F checkU56TailNatExpr) h r h' →
        r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < natLimit ∧ v = .field (n : F) := by
    intro b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k
    simp only [checkU56TailNatExpr, recompose7NatExpr, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero] at k
    obtain ⟨_, k⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨_, _, hass, hret⟩ := evalExpr_let_wildcard_inv k
    obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv hass
    obtain ⟨rfl, rfl⟩ := eval_recompose7 (by simp; rfl) (by simp; rfl) (by simp; rfl)
      (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp; rfl) evl
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
    obtain ⟨rfl, rfl⟩ := evalExpr_tuple0_inv hret
    refine ⟨rfl, rfl, b0 + (256 * b1 + (65536 * b2 + (16777216 * b3 +
      (4294967296 * b4 + (1099511627776 * b5 + 281474976710656 * b6))))), ?_, heq.symm⟩
    unfold natLimit; omega
  cases usePair with
  | false =>
    rw [body_checkU56Fn_false] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_false hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1
  | true =>
    rw [body_checkU56Fn_true] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_true hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1

end ByteCheck

/-! ## Core 56-bit Arithmetic Gadgets -/

section Core56

variable {F : Type} [Field F] [DecidableEq F]

/-! ### `sub_borrow_56` -/

private def subBorrow56TailNatExpr : Lower.Expr :=
  .letValue .wildcard
    (.builtin (.assertEq (assertion "sub_borrow_56: b7 not boolean"))
      [.binary .mul (.var "b7") (.binary .sub (.var "b7") (.literal 1)), .literal 0])
    (.letValue (.bind "lo") recompose7NatExpr
      (.letValue .wildcard
        (.builtin (.assertEq (assertion "sub_borrow_56: recomposition failed"))
          [.binary .add (.var "lo") (.binary .mul (.literal natLimit) (.var "b7")), .var "z"])
        (.tuple [.binary .mul (.var "b7") (.var "lo"), .var "b7"])))

private theorem body_subBorrow56Fn_false :
    (subBorrow56Fn false).body =
      .letValue (.bind "z")
        (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal natLimit))
        (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                            .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
          (.hint (.array .field 8) (.var "z") "bytes_le")
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                      (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                        subBorrow56TailNatExpr)))))))) := rfl

private theorem body_subBorrow56Fn_true :
    (subBorrow56Fn true).body =
      .letValue (.bind "z")
        (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal natLimit))
        (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                            .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
          (.hint (.array .field 8) (.var "z") "bytes_le")
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
                (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                  subBorrow56TailNatExpr))))) := rfl

/-- Exact operational soundness of `Prog::sub_borrow_56`:
for `x, y < 2^56`, returns `(x - y, 1)` when `y ≤ x` and `(0, 0)` when `x < y`,
i.e., `(.field ((x - y : Nat) : F), .field (if y ≤ x then 1 else 0))`, leaving the heap unchanged. -/
theorem eval_sub_borrow_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h') :
    h' = h ∧
    r = .tuple [.field ((x - y : Nat) : F), .field (if y ≤ x then (1 : F) else 0)] := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_subBorrow56Fn usePair) ev
  have htail :
      ∀ (b0 b1 b2 b3 b4 b5 b6 : Nat) (v7 : SourceValue F),
        b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 → b4 < 256 → b5 < 256 → b6 < 256 →
        EvalExpr world []
          ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
            ("b3", .field (b3 : F)), ("b4", .field (b4 : F)), ("b5", .field (b5 : F)),
            ("b6", .field (b6 : F)), ("b7", v7)] ++
           [("z", .field ((x : F) - (y : F) + (natLimit : F))),
            ("x", .field (x : F)), ("y", .field (y : F))])
          (qualifyExprF F subBorrow56TailNatExpr) h r h' →
        h' = h ∧
        r = .tuple [.field ((x - y : Nat) : F), .field (if y ≤ x then (1 : F) else 0)] := by
    intro b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k
    simp only [subBorrow56TailNatExpr, recompose7NatExpr, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero, Nat.cast_one] at k
    -- 1. `b7 * (b7 - 1) = 0`
    obtain ⟨_, _, hbool, k1⟩ := evalExpr_let_wildcard_inv k
    obtain ⟨vlb, vrb, _, evlb, evrb, hboolEq, _⟩ := evalExpr_assertEq_inv hbool
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evrb
    obtain ⟨v7l, v7r, _, ev7l, ev7r, hmulb⟩ := evalExpr_binary_inv evlb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev7l
    obtain ⟨v7s, v1s, _, ev7s, ev1s, hsubb⟩ := evalExpr_binary_inv ev7r
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev7s
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1s
    cases v7s with
    | tuple _ | ptr _ _ | construct _ _ _ => simp [evalBinOp] at hsubb
    | field b7f =>
      simp only [evalBinOp, Except.ok.injEq] at hsubb; subst hsubb
      simp only [evalBinOp, Except.ok.injEq] at hmulb; subst hmulb
      have hb7bool : b7f = 0 ∨ b7f = 1 := by
        have h0 : b7f * (b7f - 1) = 0 := Value.field.inj hboolEq
        exact (U32.binary_carry b7f).mp h0
      -- 2. `lo = recompose7`
      obtain ⟨vlo, _, evlo, k2⟩ := evalExpr_let_bind_inv k1
      obtain ⟨rfl, rfl⟩ := eval_recompose7 (by simp; rfl) (by simp; rfl) (by simp; rfl)
        (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp; rfl) evlo
      set lo : Nat := b0 + (256 * b1 + (65536 * b2 + (16777216 * b3 +
        (4294967296 * b4 + (1099511627776 * b5 + 281474976710656 * b6)))))
      have hloLt : lo < natLimit := by unfold natLimit; omega
      -- 3. `lo + natLimit * b7 = z`
      obtain ⟨_, _, hrec, k3⟩ := evalExpr_let_wildcard_inv k2
      obtain ⟨vlr, vrr, _, evlr, evrr, hrecEq, _⟩ := evalExpr_assertEq_inv hrec
      obtain ⟨va1, va2, _, eva1, eva2, haddr⟩ := evalExpr_binary_inv evlr
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva1
      obtain ⟨vm1, vm2, _, evm1, evm2, hmulr⟩ := evalExpr_binary_inv eva2
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evm1
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evm2
      simp only [evalBinOp, Except.ok.injEq] at hmulr; subst hmulr
      simp only [evalBinOp, Except.ok.injEq] at haddr; subst haddr
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evrr
      have hrecF : (lo : F) + (natLimit : F) * b7f = (x : F) - (y : F) + (natLimit : F) :=
        Value.field.inj hrecEq
      -- 4. Return tuple `(b7 * lo, b7)`
      obtain ⟨vr0, vr1, _, evr0, evr1, rfl⟩ := evalExpr_tuple2_inv k3
      obtain ⟨vrm1, vrm2, _, evrm1, evrm2, hmulret⟩ := evalExpr_binary_inv evr0
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evrm1
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evrm2
      simp only [evalBinOp, Except.ok.injEq] at hmulret; subst hmulret
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr1
      -- 5. Lift equality to `ℕ`
      have hzCast : ((x + natLimit - y : Nat) : F) = (x : F) - (y : F) + (natLimit : F) := by
        have hle : y ≤ x + natLimit := by omega
        rw [Nat.cast_sub hle, Nat.cast_add]
        ring
      rcases hb7bool with rfl | rfl
      · have hloEq : lo = x + natLimit - y := by
          apply fc.natCast_inj
            (lt_trans hloLt (by unfold natLimit fieldBound64; omega))
            (by unfold natLimit fieldBound64 at *; omega)
          rw [hzCast]
          simpa using hrecF
        have hnle : ¬ y ≤ x := by omega
        have hsub0 : x - y = 0 := by omega
        simp [hnle, hsub0]
      · have hloEq : lo + natLimit = x + natLimit - y := by
          apply fc.natCast_inj
            (by unfold natLimit fieldBound64 at *; omega)
            (by unfold natLimit fieldBound64 at *; omega)
          rw [hzCast, Nat.cast_add]
          simpa using hrecF
        have hle : y ≤ x := by omega
        have hloSub : lo = x - y := by omega
        simp [hle, hloSub]
  have hzStep :
      ∀ (cont : Aiur.Generic.Expr F),
        EvalExpr world [] [("x", .field (x : F)), ("y", .field (y : F))]
          (.letValue (.bind "z")
            (.binary .add (.binary .sub (.var "x") (.var "y")) (.literal (natLimit : F)))
            (.letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                                .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
              (.hint (.array .field 8) (.var "z") "bytes_le")
              cont))
          h r h' →
        ∃ v0 v1 v2 v3 v4 v5 v6 v7,
          EvalExpr world []
            ([("b0", v0), ("b1", v1), ("b2", v2), ("b3", v3),
              ("b4", v4), ("b5", v5), ("b6", v6), ("b7", v7)] ++
             [("z", .field ((x : F) - (y : F) + (natLimit : F))),
              ("x", .field (x : F)), ("y", .field (y : F))])
            cont h r h' := by
    intro cont ev0
    obtain ⟨vz, _, evz, k0⟩ := evalExpr_let_bind_inv ev0
    obtain ⟨vsub, vlim, _, evsub, evlim, haddz⟩ := evalExpr_binary_inv evz
    obtain ⟨vx, vy, _, evx, evy, hsubz⟩ := evalExpr_binary_inv evsub
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evy
    simp only [evalBinOp, Except.ok.injEq] at hsubz; subst hsubz
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evlim
    simp only [evalBinOp, Except.ok.injEq] at haddz; subst haddz
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k1⟩ := evalExpr_let_array8_inv k0
    obtain ⟨_, evkz⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evkz
    exact ⟨v0, v1, v2, v3, v4, v5, v6, v7, k1⟩
  cases usePair with
  | false =>
    rw [body_subBorrow56Fn_false] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, k⟩ := hzStep _ body
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_false hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1
  | true =>
    rw [body_subBorrow56Fn_true] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, k⟩ := hzStep _ body
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_true hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1

theorem eval_sub_borrow_56_ge {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit) (hge : y ≤ x)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h') :
    h' = h ∧ r = .tuple [.field ((x - y : Nat) : F), .field (1 : F)] := by
  obtain ⟨rfl, hr⟩ := eval_sub_borrow_56 fc hbc hfn hx hy ev
  exact ⟨rfl, by simpa [hge] using hr⟩

theorem eval_sub_borrow_56_lt {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit) (hlt : x < y)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h') :
    h' = h ∧ r = .tuple [.field (0 : F), .field (0 : F)] := by
  obtain ⟨rfl, hr⟩ := eval_sub_borrow_56 fc hbc hfn hx hy ev
  have hnle : ¬ y ≤ x := by omega
  have hsub : x - y = 0 := by omega
  exact ⟨rfl, by simpa [hnle, hsub] using hr⟩

/-! ### `split_32_24` -/

private def split32_24TailNatExpr : Lower.Expr :=
  .letValue .wildcard
    (.builtin (.assertEq (assertion "split_32_24: top byte must be zero"))
      [.var "b7", .literal 0])
    (.letValue (.bind "lo")
      (.binary .add (.var "b0")
        (.binary .add (.binary .mul (.literal 256) (.var "b1"))
          (.binary .add (.binary .mul (.literal 65536) (.var "b2"))
            (.binary .mul (.literal 16777216) (.var "b3")))))
      (.letValue (.bind "hi")
        (.binary .add (.var "b4")
          (.binary .add (.binary .mul (.literal 256) (.var "b5"))
            (.binary .mul (.literal 65536) (.var "b6"))))
        (.letValue .wildcard
          (.builtin (.assertEq (assertion "split_32_24: recomposition failed"))
            [.binary .add (.var "lo") (.binary .mul (.literal (2 ^ 32)) (.var "hi")), .var "x"])
          (.tuple [.var "lo", .var "hi"]))))

private theorem body_split32_24Fn_false :
    (split32_24Fn false).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b0"])
          (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b1"])
            (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b2"])
              (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b3"])
                (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b4"])
                  (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b5"])
                    (.letValue .wildcard (.call "U8Byte::check" (some []) [.var "b6"])
                      split32_24TailNatExpr))))))) := rfl

private theorem body_split32_24Fn_true :
    (split32_24Fn true).body =
      .letValue (.array [.bind "b0", .bind "b1", .bind "b2", .bind "b3",
                         .bind "b4", .bind "b5", .bind "b6", .bind "b7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b0", .var "b1"])
          (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b2", .var "b3"])
            (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b4", .var "b5"])
              (.letValue .wildcard (.call "UInt8::from_fields" (some []) [.var "b6", .literal 0])
                split32_24TailNatExpr)))) := rfl

/-- Unconditional soundness of `Prog::split_32_24`: proves for ANY argument `v` that
`v = .field (lo + 2^32 * hi)` with `lo < 2^32`, `hi < 2^24`, and returns `(lo, hi)`. -/
theorem eval_split_32_24_any {world : World F} {usePair : Bool}
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    {v r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "split_32_24") [v] h r h') :
    h' = h ∧
    ∃ lo hi : Nat, lo < 2 ^ 32 ∧ hi < 2 ^ 24 ∧
      v = .field ((lo + 2 ^ 32 * hi : Nat) : F) ∧
      r = .tuple [.field (lo : F), .field (hi : F)] := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_split32_24Fn usePair) ev
  have htail :
      ∀ (b0 b1 b2 b3 b4 b5 b6 : Nat) (v7 : SourceValue F),
        b0 < 256 → b1 < 256 → b2 < 256 → b3 < 256 → b4 < 256 → b5 < 256 → b6 < 256 →
        EvalExpr world []
          ([("b0", .field (b0 : F)), ("b1", .field (b1 : F)), ("b2", .field (b2 : F)),
            ("b3", .field (b3 : F)), ("b4", .field (b4 : F)), ("b5", .field (b5 : F)),
            ("b6", .field (b6 : F)), ("b7", v7)] ++ [("x", v)])
          (qualifyExprF F split32_24TailNatExpr) h r h' →
        h' = h ∧
        ∃ lo hi : Nat, lo < 2 ^ 32 ∧ hi < 2 ^ 24 ∧
          v = .field ((lo + 2 ^ 32 * hi : Nat) : F) ∧
          r = .tuple [.field (lo : F), .field (hi : F)] := by
    intro b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k
    simp only [split32_24TailNatExpr, qualifyExprF, qualifyExpr, qualifyPat,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero] at k
    obtain ⟨_, k1⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k
    obtain ⟨vlo, _, evlo, k2⟩ := evalExpr_let_bind_inv k1
    obtain ⟨rfl, rfl⟩ := evalExpr_add_fields
      (fun _ _ e => evalExpr_var_eq (by simp; rfl) e)
      (fun _ _ e1 => evalExpr_add_fields
        (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e)
        (fun _ _ e2 => evalExpr_add_fields
          (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e)
          (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e) e2) e1) evlo
    set lo : Nat := b0 + (256 * b1 + (65536 * b2 + 16777216 * b3))
    obtain ⟨vhi, _, evhi, k3⟩ := evalExpr_let_bind_inv k2
    obtain ⟨rfl, rfl⟩ := evalExpr_add_fields
      (fun _ _ e => evalExpr_var_eq (by simp; rfl) e)
      (fun _ _ e1 => evalExpr_add_fields
        (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e)
        (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e) e1) evhi
    set hi : Nat := b4 + (256 * b5 + 65536 * b6)
    obtain ⟨_, _, hass, k4⟩ := evalExpr_let_wildcard_inv k3
    obtain ⟨vl, vr, _, evl, evr, heq, _⟩ := evalExpr_assertEq_inv hass
    obtain ⟨rfl, rfl⟩ := evalExpr_add_fields
      (fun _ _ e => evalExpr_var_eq (by simp; rfl) e)
      (fun _ _ e => evalExpr_mul_lit_var_eq (by simp; rfl) e) evl
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
    obtain ⟨vr0, vr1, _, evr0, evr1, rfl⟩ := evalExpr_tuple2_inv k4
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr1
    exact ⟨rfl, lo, hi, by omega, by omega, heq.symm, rfl⟩
  cases usePair with
  | false =>
    rw [body_split32_24Fn_false] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8Byte_check,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_false hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1
  | true =>
    rw [body_split32_24Fn_true] at body
    simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u8_from_fields,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero] at body
    obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, _, evh, k⟩ := evalExpr_let_array8_inv body
    obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
    obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, hb0, hb1, hb2, hb3, hb4, hb5, hb6,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, k1⟩ := eval_byteCheck7_true hbc k
    exact htail b0 b1 b2 b3 b4 b5 b6 v7 hb0 hb1 hb2 hb3 hb4 hb5 hb6 k1

/-- Operational soundness of `Prog::split_32_24` on a known `< 2^56` natural `x`. -/
theorem eval_split_32_24 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hfn : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    {x : Nat} (hx : x < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "split_32_24") [.field (x : F)] h r h') :
    h' = h ∧
    ∃ lo hi : Nat, lo < 2 ^ 32 ∧ hi < 2 ^ 24 ∧
      x = lo + 2 ^ 32 * hi ∧
      r = .tuple [.field (lo : F), .field (hi : F)] := by
  obtain ⟨rfl, lo, hi, hlo, hhi, hveq, rfl⟩ := eval_split_32_24_any hbc hfn ev
  have hxEq : x = lo + 2 ^ 32 * hi :=
    fc.natCast_inj56 hx (by unfold natLimit; omega) (Value.field.inj hveq)
  exact ⟨rfl, lo, hi, hlo, hhi, hxEq, rfl⟩

/-! ### `mul_56` -/

/-- Unconditional soundness of `Prog::mul_56` over any `FieldCompatible64` field:
even on arbitrary (untrusted/hinted) inputs `vx, vy`, verifies both are `< 2^56` naturals
whose exact product `x * y < 2^56`, and returns `.field ((x * y : Nat) : F)`. -/
theorem eval_mul_56_any {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    {vx vy r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "mul_56") [vx, vy] h r h') :
    h' = h ∧
    ∃ x y : Nat, x < natLimit ∧ y < natLimit ∧
      vx = .field (x : F) ∧ vy = .field (y : F) ∧
      x * y < natLimit ∧ r = .field ((x * y : Nat) : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hmul
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_mul56Fn) ev
  simp only [mul56Fn, letE, seqE, callE, addE, mulE, vE, litE, qualifyExprF, qualifyExpr,
    qualifyPat, qualifyName_split_32_24, qualifyName_check_u24, qualifyName_check_u56,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero] at body
  -- 1. `(xlo, xhi) = split_32_24(x)`
  obtain ⟨vxlo, vxhi, _, evsx, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨vx', _, evx', csx⟩ := evalExpr_call1_inv evsx
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx'
  obtain ⟨rfl, xlo, xhi, hxlo, hxhi, rfl, hxeq⟩ := eval_split_32_24_any hbc hsplit csx
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hxeq
  obtain ⟨rfl, rfl⟩ := hxeq
  -- 2. `(ylo, yhi) = split_32_24(y)`
  obtain ⟨vylo, vyhi, _, evsy, k2⟩ := evalExpr_let_tuple2_inv k1
  obtain ⟨vy', _, evy', csy⟩ := evalExpr_call1_inv evsy
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evy'
  obtain ⟨rfl, ylo, yhi, hylo, hyhi, rfl, hyeq⟩ := eval_split_32_24_any hbc hsplit csy
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hyeq
  obtain ⟨rfl, rfl⟩ := hyeq
  -- 3. `assertEq(xhi * yhi, 0)`
  obtain ⟨_, _, hhiAss, k3⟩ := evalExpr_let_wildcard_inv k2
  obtain ⟨vlhi, vrhi, _, evlhi, evrhi, hhiEq, _⟩ := evalExpr_assertEq_inv hhiAss
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evrhi
  obtain ⟨vxhi', vyhi', _, evxhi', evyhi', hmulhi⟩ := evalExpr_binary_inv evlhi
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evxhi'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evyhi'
  simp only [evalBinOp, Except.ok.injEq] at hmulhi; subst hmulhi
  have hxhiyhi0 : xhi * yhi = 0 := by
    have hlt : xhi * yhi < fieldBound64 := by
      have h1 : xhi * yhi < 2 ^ 24 * 2 ^ 24 := Nat.mul_lt_mul'' hxhi hyhi
      exact lt_trans h1 (by decide)
    apply fc.natCast_inj hlt (by unfold fieldBound64; omega)
    simpa [Nat.cast_mul] using Value.field.inj hhiEq
  -- 4. `mid = xlo * yhi + xhi * ylo` and `check_u24(mid)`
  obtain ⟨vmid, _, evmid, k4⟩ := evalExpr_let_bind_inv k3
  obtain ⟨vm1, vm2, _, evm1, evm2, haddm⟩ := evalExpr_binary_inv evmid
  obtain ⟨v1a, v1b, _, ev1a, ev1b, hmul1⟩ := evalExpr_binary_inv evm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev1a
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev1b
  simp only [evalBinOp, Except.ok.injEq] at hmul1; subst hmul1
  obtain ⟨v2a, v2b, _, ev2a, ev2b, hmul2⟩ := evalExpr_binary_inv evm2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2a
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2b
  simp only [evalBinOp, Except.ok.injEq] at hmul2; subst hmul2
  simp only [evalBinOp, Except.ok.injEq] at haddm; subst haddm
  obtain ⟨_, _, evcu24, k5⟩ := evalExpr_let_wildcard_inv k4
  obtain ⟨vmid', _, evmid', ccu24⟩ := evalExpr_call1_inv evcu24
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evmid'
  obtain ⟨_, rfl, midN, hmidN, hmidEq⟩ := eval_check_u24 hbc hu24 ccu24
  have hmidVal : xlo * yhi + xhi * ylo = midN := by
    have hlt : xlo * yhi + xhi * ylo < fieldBound64 := by
      have h1 : xlo * yhi < 2 ^ 32 * 2 ^ 24 := Nat.mul_lt_mul'' hxlo hyhi
      have h2 : xhi * ylo < 2 ^ 24 * 2 ^ 32 := Nat.mul_lt_mul'' hxhi hylo
      have h3 : 2 ^ 32 * 2 ^ 24 + 2 ^ 24 * 2 ^ 32 < fieldBound64 := by decide
      omega
    apply fc.natCast_inj hlt (lt_trans hmidN (by decide))
    simpa [Nat.cast_add, Nat.cast_mul] using Value.field.inj hmidEq
  have hmidLt : xlo * yhi + xhi * ylo < 2 ^ 24 := hmidVal ▸ hmidN
  -- 5. `lo = xlo * ylo` and `check_u56(lo)`
  obtain ⟨vlo, _, evlo, k6⟩ := evalExpr_let_bind_inv k5
  obtain ⟨vla, vlb, _, evla, evlb, hmullo⟩ := evalExpr_binary_inv evlo
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evla
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlb
  simp only [evalBinOp, Except.ok.injEq] at hmullo; subst hmullo
  obtain ⟨_, _, evcu56lo, k7⟩ := evalExpr_let_wildcard_inv k6
  obtain ⟨vlo', _, evlo', ccu56lo⟩ := evalExpr_call1_inv evcu56lo
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evlo'
  obtain ⟨_, rfl, loN, hloN, hloEq⟩ := eval_check_u56 hbc hu56 ccu56lo
  have hloVal : xlo * ylo = loN := by
    have hlt : xlo * ylo < fieldBound64 := by
      have h1 : xlo ≤ 2 ^ 32 - 1 := by omega
      have h2 : ylo ≤ 2 ^ 32 - 1 := by omega
      have h3 : xlo * ylo ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul h1 h2
      have h4 : (2 ^ 32 - 1) * (2 ^ 32 - 1) < fieldBound64 := by decide
      exact lt_of_le_of_lt h3 h4
    apply fc.natCast_inj hlt (lt_trans hloN (by decide))
    simpa [Nat.cast_mul] using Value.field.inj hloEq
  have hloLt : xlo * ylo < natLimit := hloVal ▸ hloN
  -- 6. `prod = lo + 2^32 * mid` and `check_u56(prod)`
  obtain ⟨vprod, _, evprod, k8⟩ := evalExpr_let_bind_inv k7
  obtain ⟨vpa, vpb, _, evpa, evpb, haddp⟩ := evalExpr_binary_inv evprod
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evpa
  obtain ⟨vp1, vp2, _, evp1, evp2, hmulp⟩ := evalExpr_binary_inv evpb
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evp1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp2
  simp only [evalBinOp, Except.ok.injEq] at hmulp; subst hmulp
  simp only [evalBinOp, Except.ok.injEq] at haddp; subst haddp
  obtain ⟨_, _, evcu56p, k9⟩ := evalExpr_let_wildcard_inv k8
  obtain ⟨vprod', _, evprod', ccu56p⟩ := evalExpr_call1_inv evcu56p
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evprod'
  obtain ⟨_, rfl, prodN, hprodN, hprodEq⟩ := eval_check_u56 hbc hu56 ccu56p
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k9
  -- 7. Exact algebraic identity `(xlo + 2^32 * xhi) * (ylo + 2^32 * yhi) = xlo*ylo + 2^32 * mid`
  set x := xlo + 2 ^ 32 * xhi
  set y := ylo + 2 ^ 32 * yhi
  have hxyEq : x * y = xlo * ylo + 2 ^ 32 * (xlo * yhi + xhi * ylo) := by
    have : x * y = xlo * ylo + 2 ^ 32 * (xlo * yhi + xhi * ylo) + 2 ^ 64 * (xhi * yhi) := by
      dsimp only [x, y]; ring
    rw [this, hxhiyhi0, Nat.mul_zero, Nat.add_zero]
  have hprodVal : x * y = prodN := by
    rw [hxyEq]
    have hlt : xlo * ylo + 2 ^ 32 * (xlo * yhi + xhi * ylo) < fieldBound64 := by
      unfold natLimit fieldBound64 at *; omega
    apply fc.natCast_inj hlt (lt_trans hprodN (by decide))
    simpa [Nat.cast_add, Nat.cast_mul] using Value.field.inj hprodEq
  refine ⟨rfl, x, y, by unfold natLimit; omega, by unfold natLimit; omega, rfl, rfl,
    hprodVal ▸ hprodN, ?_⟩
  rw [hprodVal]
  exact hprodEq

/-- Operational soundness of `Prog::mul_56` on known `< 2^56` naturals `x, y`. -/
theorem eval_mul_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    {x y : Nat} (hx : x < natLimit) (hy : y < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "mul_56") [.field (x : F), .field (y : F)] h r h') :
    h' = h ∧ x * y < natLimit ∧ r = .field ((x * y : Nat) : F) := by
  obtain ⟨rfl, x', y', hx', hy', hxe, hye, hprod, rfl⟩ :=
    eval_mul_56_any fc hbc hsplit hu24 hu56 hmul ev
  have hxx : x = x' := fc.natCast_inj56 hx hx' (Value.field.inj hxe)
  have hyy : y = y' := fc.natCast_inj56 hy hy' (Value.field.inj hye)
  subst hxx hyy
  exact ⟨rfl, hprod, rfl⟩

/-! ### `divmod_56` -/

/-- Contract-parameterized soundness of `Prog::divmod_56`. -/
theorem eval_divmod_56_of_contracts {world : World F}
    (fc : FieldCompatible64 F)
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hmulSpec : ∀ vx vy h r h',
      EvalFn world (qualified "mul_56") [vx, vy] h r h' →
      h' = h ∧ ∃ x y : Nat, x < natLimit ∧ y < natLimit ∧
        vx = .field (x : F) ∧ vy = .field (y : F) ∧
        x * y < natLimit ∧ r = .field ((x * y : Nat) : F))
    (hu56Spec : ∀ v h r h',
      EvalFn world (qualified "check_u56") [v] h r h' →
      r = .tuple [] ∧ h' = h ∧ ∃ n : Nat, n < natLimit ∧ v = .field (n : F))
    (hsubSpec : ∀ x y h r h', x < natLimit → y < natLimit →
      EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h' →
      h' = h ∧ r = .tuple [.field ((x - y : Nat) : F), .field (if y ≤ x then (1 : F) else 0)])
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ 0 < b ∧
    r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)] := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hdivmod
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_divmod56Fn) ev
  simp only [divmod56Fn, letE, seqE, callE, addE, vE, litE, qualifyExprF, qualifyExpr,
    qualifyPat, qualifyTy, qualifyName_mul_56, qualifyName_check_u56, qualifyName_sub_borrow_56,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero] at body
  -- 1. `(q, r) = hint("ixcc.divmod", (x, y))`
  obtain ⟨vq, vr, _, evh, k1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨_, evkey⟩ := evalExpr_hint_inv evh
  obtain ⟨_, _, _, ekx, eky, _⟩ := evalExpr_tuple2_inv evkey
  obtain ⟨_, rfl⟩ := evalExpr_var_inv ekx
  obtain ⟨_, rfl⟩ := evalExpr_var_inv eky
  -- 2. `p = mul_56(q, y)`
  obtain ⟨vp, _, evp, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨vq', vy', _, _, evq', evy', cmul⟩ := evalExpr_call2_inv evp
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evy'
  obtain ⟨rfl, q, b', hqLt, hb'Lt, rfl, hbe, hqbLt, rfl⟩ := hmulSpec _ _ _ _ _ cmul
  have hbb : b = b' := fc.natCast_inj56 hb hb'Lt (Value.field.inj hbe)
  subst hbb
  -- 3. `check_u56(r)`
  obtain ⟨_, _, evcr, k3⟩ := evalExpr_let_wildcard_inv k2
  obtain ⟨vr', _, evr', ccr⟩ := evalExpr_call1_inv evcr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
  obtain ⟨_, rfl, rem, hremLt, rfl⟩ := hu56Spec _ _ _ _ ccr
  -- 4. `assertEq(p + r, x)`
  obtain ⟨_, _, hass1, k4⟩ := evalExpr_let_wildcard_inv k3
  obtain ⟨vl1, vr1, _, evl1, evr1, heq1, _⟩ := evalExpr_assertEq_inv hass1
  obtain ⟨vp', vr'', _, evp', evr'', hadd1⟩ := evalExpr_binary_inv evl1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr''
  simp only [evalBinOp, Except.ok.injEq] at hadd1; subst hadd1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr1
  have hqrEq : q * b + rem = a := by
    apply fc.natCast_inj
      (by unfold natLimit fieldBound64 at *; omega)
      (lt_trans ha (by unfold natLimit fieldBound64; omega))
    simpa [Nat.cast_add] using Value.field.inj heq1
  -- 5. `(_, ge) = sub_borrow_56(r, y)` and `assertEq(ge, 0)`
  obtain ⟨_, vge, _, evsub, k5⟩ := evalExpr_let_wild_tuple2_inv k4
  obtain ⟨vr3, vy3, _, _, evr3, evy3, csub⟩ := evalExpr_call2_inv evsub
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evy3
  obtain ⟨rfl, hsubEq⟩ := hsubSpec rem b _ _ _ hremLt hb csub
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hsubEq
  obtain ⟨_, rfl⟩ := hsubEq
  obtain ⟨hge0, k6⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k5
  have hremLtB : rem < b := by
    by_contra hnot
    have hle : b ≤ rem := Nat.le_of_not_lt hnot
    simp only [hle, ↓reduceIte, Value.field.injEq] at hge0
    exact one_ne_zero hge0
  have hbPos : 0 < b := by omega
  -- 6. Return `(q, r)`
  obtain ⟨vqout, vrout, _, evqo, evro, rfl⟩ := evalExpr_tuple2_inv k6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evqo
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evro
  have hqEq : q = a / b := by
    rw [← hqrEq, Nat.mul_comm q b, Nat.mul_add_div hbPos, Nat.div_eq_of_lt hremLtB, Nat.add_zero]
  have hremEq : rem = a % b := by
    rw [← hqrEq, Nat.mul_comm q b, Nat.mul_add_mod, Nat.mod_eq_of_lt hremLtB]
  subst hqEq hremEq
  exact ⟨rfl, hbPos, rfl⟩

/-- Operational soundness of `Prog::divmod_56` directly from `WorldHasFn` bindings. -/
theorem eval_divmod_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ 0 < b ∧
    r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)] :=
  eval_divmod_56_of_contracts fc hdivmod
    (fun _ _ _ _ _ e => eval_mul_56_any fc hbc hsplit hu24 hu56 hmul e)
    (fun _ _ _ _ e => eval_check_u56 hbc hu56 e)
    (fun _ _ _ _ _ hx hy e => eval_sub_borrow_56 fc hbc hsub hx hy e)
    ha hb ev

/-! ### `pow_56_loop` and `pow_56` -/

/-- Contract-parameterized soundness of `Prog::pow_56_loop(base, exp, acc)`:
returns `acc * base ^ exp < 2^56` and leaves the heap unchanged. -/
theorem eval_pow_56_loop_of_contracts {world : World F}
    (fc : FieldCompatible64 F)
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hmulSpec : ∀ x y h r h', x < natLimit → y < natLimit →
      EvalFn world (qualified "mul_56") [.field (x : F), .field (y : F)] h r h' →
      h' = h ∧ x * y < natLimit ∧ r = .field ((x * y : Nat) : F))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)]) :
    ∀ (exp : Nat) {base acc : Nat},
      base < natLimit → exp < natLimit → acc < natLimit →
      ∀ {r : SourceValue F} {h h' : Heap F},
        EvalFn world (qualified "pow_56_loop")
          [.field (base : F), .field (exp : F), .field (acc : F)] h r h' →
        h' = h ∧ acc * base ^ exp < natLimit ∧ r = .field ((acc * base ^ exp : Nat) : F) := by
  intro exp
  induction exp using Nat.strongRecOn with
  | _ exp ih =>
    intro base acc hbase hexp hacc r h h' ev
    obtain ⟨_, body⟩ := evalFn_plain_inv hloop
      (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_pow56LoopFn) ev
    simp only [pow56LoopFn, matchE, letE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
      qualifyName_divmod_56, qualifyName_mul_56, qualifyName_pow_56_loop,
      Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
      Nat.cast_zero, Nat.cast_ofNat] at body
    obtain ⟨vexp, _, evexp, hbr⟩ := evalExpr_match_lit_wild_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evexp
    rcases hbr with ⟨hexp0F, hzero⟩ | ⟨hexpNeF, hpos⟩
    · have hexp0 : exp = 0 :=
        fc.natCast_inj56 hexp (by unfold natLimit; omega) (by simpa using Value.field.inj hexp0F)
      subst hexp0
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hzero
      simp [hacc]
    · have hexpNe : exp ≠ 0 := by
        intro h0; subst h0; exact hexpNeF (by simp)
      -- `(half, bit) = divmod_56(exp, 2)`
      obtain ⟨vhalf, vbit, _, evdm, k1⟩ := evalExpr_let_tuple2_inv hpos
      obtain ⟨ve1, ve2, _, _, eve1, eve2, cdm⟩ := evalExpr_call2_inv evdm
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eve1
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv eve2
      have h2lt : (2 : Nat) < natLimit := by unfold natLimit; omega
      obtain ⟨rfl, _, hdmEq⟩ := hdivmodSpec exp 2 _ _ _ hexp h2lt (by simpa using cdm)
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
      obtain ⟨rfl, rfl⟩ := hdmEq
      -- `acc2 = match bit { 0 => acc, _ => mul_56(acc, base) }`
      obtain ⟨vacc2, hm2, evacc2, k2⟩ := evalExpr_let_bind_inv k1
      obtain ⟨vbit', hm1, evbit', hbitBr⟩ := evalExpr_match_lit_wild_inv evacc2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evbit'
      have hacc2 :
          hm2 = hm1 ∧ acc * base ^ (exp % 2) < natLimit ∧
            vacc2 = .field ((acc * base ^ (exp % 2) : Nat) : F) := by
        rcases hbitBr with ⟨hbit0F, hb0⟩ | ⟨hbitNeF, hb1⟩
        · have hbit0 : exp % 2 = 0 :=
            fc.natCast_inj56 (by omega) (by unfold natLimit; omega)
              (by simpa using Value.field.inj hbit0F)
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hb0
          exact ⟨rfl, by simpa [hbit0] using hacc, by simp [hbit0]⟩
        · have hbit1 : exp % 2 = 1 := by
            have hlt2 : exp % 2 < 2 := Nat.mod_lt exp (by omega)
            have hne0 : exp % 2 ≠ 0 := fun h0 => hbitNeF (by simp [h0])
            omega
          obtain ⟨va', vb', _, _, eva', evb', cmul⟩ := evalExpr_call2_inv hb1
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
          obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
          obtain ⟨rfl, hprodLt, rfl⟩ := hmulSpec acc base _ _ _ hacc hbase cmul
          exact ⟨rfl, by simpa [hbit1] using hprodLt, by simp [hbit1]⟩
      obtain ⟨rfl, hacc2Lt, rfl⟩ := hacc2
      set acc2N := acc * base ^ (exp % 2)
      -- `match half { 0 => acc2, _ => let b2 = mul_56(base, base); pow_56_loop(b2, half, acc2) }`
      obtain ⟨vhalf', _, evhalf', hhalfBr⟩ := evalExpr_match_lit_wild_inv k2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evhalf'
      rcases hhalfBr with ⟨hhalf0F, hh0⟩ | ⟨hhalfNeF, hh1⟩
      · have hhalf0 : exp / 2 = 0 :=
          fc.natCast_inj56 (by omega) (by unfold natLimit; omega)
            (by simpa using Value.field.inj hhalf0F)
        have hexp1 : exp = 1 := by omega
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hh0
        have hEq : acc * base ^ exp = acc2N := by
          simp [acc2N, hexp1]
        rw [hEq]
        exact ⟨rfl, hacc2Lt, rfl⟩
      · obtain ⟨vb2, _, evb2, k3⟩ := evalExpr_let_bind_inv hh1
        obtain ⟨vb1', vb2', _, _, evb1', evb2', cmulb⟩ := evalExpr_call2_inv evb2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb1'
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb2'
        obtain ⟨rfl, hb2Lt, rfl⟩ := hmulSpec base base _ _ _ hbase hbase cmulb
        obtain ⟨vc1, vc2, vc3, _, _, _, evc1, evc2, evc3, crec⟩ := evalExpr_call3_inv k3
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc2
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evc3
        have hhalfLtExp : exp / 2 < exp := Nat.div_lt_self (Nat.pos_of_ne_zero hexpNe) (by omega)
        have hhalfLtLim : exp / 2 < natLimit := lt_trans hhalfLtExp hexp
        obtain ⟨rfl, hrecLt, rfl⟩ :=
          ih (exp / 2) hhalfLtExp hb2Lt hhalfLtLim hacc2Lt (by simpa [Nat.cast_mul] using crec)
        have hpowId : acc2N * (base * base) ^ (exp / 2) = acc * base ^ exp := by
          dsimp only [acc2N]
          rw [mul_assoc, ← sq, ← pow_mul, ← pow_add]
          have hdecomp : exp % 2 + 2 * (exp / 2) = exp := by omega
          rw [hdecomp]
        rw [hpowId] at hrecLt ⊢
        exact ⟨rfl, hrecLt, rfl⟩

/-- Operational soundness of `Prog::pow_56_loop` directly from `WorldHasFn` bindings. -/
theorem eval_pow_56_loop {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    {base exp acc : Nat} (hbase : base < natLimit) (hexp : exp < natLimit) (hacc : acc < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "pow_56_loop")
      [.field (base : F), .field (exp : F), .field (acc : F)] h r h') :
    h' = h ∧ acc * base ^ exp < natLimit ∧ r = .field ((acc * base ^ exp : Nat) : F) :=
  eval_pow_56_loop_of_contracts fc hloop
    (fun _ _ _ _ _ hx hy e => eval_mul_56 fc hbc hsplit hu24 hu56 hmul hx hy e)
    (fun _ _ _ _ _ ha hb e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod ha hb e)
    exp hbase hexp hacc ev

/-- Contract-parameterized soundness of `Prog::pow_56(a, b)`. -/
theorem eval_pow_56_of_contracts {world : World F}
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    (hloopSpec : ∀ base exp acc h r h', base < natLimit → exp < natLimit → acc < natLimit →
      EvalFn world (qualified "pow_56_loop")
        [.field (base : F), .field (exp : F), .field (acc : F)] h r h' →
      h' = h ∧ acc * base ^ exp < natLimit ∧ r = .field ((acc * base ^ exp : Nat) : F))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hpow
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_pow56Fn) ev
  simp only [pow56Fn, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyName_pow_56_loop,
    Option.map_some, Aiur.Generic.Expr.map, List.map, Nat.cast_one] at body
  obtain ⟨v1, v2, v3, _, _, _, ev1, ev2, ev3, cloop⟩ := evalExpr_call3_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev3
  have h1lt : (1 : Nat) < natLimit := by unfold natLimit; omega
  obtain ⟨rfl, hlt, rfl⟩ := hloopSpec a b 1 _ _ _ ha hb h1lt (by simpa using cloop)
  exact ⟨rfl, by simpa using hlt, by simp⟩

/-- Operational soundness of `Prog::pow_56(a, b)` directly from `WorldHasFn` bindings. -/
theorem eval_pow_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F) :=
  eval_pow_56_of_contracts hpow
    (fun _ _ _ _ _ _ hb' he' ha' e =>
      eval_pow_56_loop fc hbc hsplit hu24 hu56 hsub hmul hdivmod hloop hb' he' ha' e)
    ha hb ev

/-! ### `gcd_56` -/

/-- Contract-parameterized soundness of `Prog::gcd_56(a, b)`. -/
theorem eval_gcd_56_of_contracts {world : World F}
    (fc : FieldCompatible64 F)
    (hgcd : WorldHasFn world (qualified "gcd_56") ["a", "b"]
      (qualifyExprF F gcd56Fn.body))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)]) :
    ∀ (b : Nat) {a : Nat}, a < natLimit → b < natLimit →
      ∀ {r : SourceValue F} {h h' : Heap F},
        EvalFn world (qualified "gcd_56") [.field (a : F), .field (b : F)] h r h' →
        h' = h ∧ Nat.gcd a b < natLimit ∧ r = .field ((Nat.gcd a b : Nat) : F) := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro a ha hb r h h' ev
    obtain ⟨_, body⟩ := evalFn_plain_inv hgcd
      (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_gcd56Fn) ev
    simp only [gcd56Fn, matchE, callE, vE, qualifyExprF, qualifyExpr, qualifyPat,
      qualifyName_divmod_56, qualifyName_gcd_56, Option.map_some,
      Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero] at body
    obtain ⟨vb, _, evb, hbr⟩ := evalExpr_match_lit_wild_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb
    rcases hbr with ⟨hb0F, hzero⟩ | ⟨_, hpos⟩
    · have hb0 : b = 0 :=
        fc.natCast_inj56 hb (by unfold natLimit; omega) (by simpa using Value.field.inj hb0F)
      subst hb0
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hzero
      simp [ha]
    · obtain ⟨_, vr, _, evdm, k1⟩ := evalExpr_let_wild_tuple2_inv hpos
      obtain ⟨va', vb', _, _, eva', evb', cdm⟩ := evalExpr_call2_inv evdm
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
      obtain ⟨rfl, hbPos, hdmEq⟩ := hdivmodSpec a b _ _ _ ha hb cdm
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
      obtain ⟨_, rfl⟩ := hdmEq
      obtain ⟨vb2, vr2, _, _, evb2, evr2, crec⟩ := evalExpr_call2_inv k1
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr2
      have hmodLtB : a % b < b := Nat.mod_lt a hbPos
      have hmodLtLim : a % b < natLimit := lt_trans hmodLtB hb
      obtain ⟨rfl, hrecLt, rfl⟩ := ih (a % b) hmodLtB hb hmodLtLim crec
      have hgcdEq : Nat.gcd b (a % b) = Nat.gcd a b := by
        rw [Nat.gcd_comm a b, Nat.gcd_rec b a, Nat.gcd_comm]
      rw [hgcdEq] at hrecLt ⊢
      exact ⟨rfl, hrecLt, rfl⟩

/-- Operational soundness of `Prog::gcd_56(a, b)` directly from `WorldHasFn` bindings. -/
theorem eval_gcd_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hgcd : WorldHasFn world (qualified "gcd_56") ["a", "b"]
      (qualifyExprF F gcd56Fn.body))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "gcd_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ Nat.gcd a b < natLimit ∧ r = .field ((Nat.gcd a b : Nat) : F) :=
  eval_gcd_56_of_contracts fc hgcd
    (fun _ _ _ _ _ hx hy e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    b ha hb ev

/-! ### `shl_56` and `shr_56` -/

/-- Contract-parameterized soundness of `Prog::shl_56(a, b)`:
verifies `Nat.shiftLeft a b < natLimit` and returns `.field ((Nat.shiftLeft a b : Nat) : F)`. -/
theorem eval_shl_56_of_contracts {world : World F}
    (fc : FieldCompatible64 F)
    (hshl : WorldHasFn world (qualified "shl_56") ["x", "k"]
      (qualifyExprF F shl56Fn.body))
    (hmulSpec : ∀ x y h r h', x < natLimit → y < natLimit →
      EvalFn world (qualified "mul_56") [.field (x : F), .field (y : F)] h r h' →
      h' = h ∧ x * y < natLimit ∧ r = .field ((x * y : Nat) : F))
    (hpowSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "shl_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ Nat.shiftLeft a b < natLimit ∧ r = .field ((Nat.shiftLeft a b : Nat) : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hshl
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_shl56Fn) ev
  simp only [shl56Fn, matchE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_mul_56, qualifyName_pow_56, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero, Nat.cast_ofNat] at body
  obtain ⟨vx, _, evx, hbr⟩ := evalExpr_match_lit_wild_inv body
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx
  rcases hbr with ⟨ha0F, hzero⟩ | ⟨_, hpos⟩
  · have ha0 : a = 0 :=
      fc.natCast_inj56 ha (by unfold natLimit; omega) (by simpa using Value.field.inj ha0F)
    subst ha0
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hzero
    simp [Nat.shiftLeft_eq, natLimit]
  · obtain ⟨vx', vp, _, _, evx', evp, cmul⟩ := evalExpr_call2_inv hpos
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx'
    obtain ⟨v2, vk, _, _, ev2, evk, cpow⟩ := evalExpr_call2_inv evp
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk
    have h2lt : (2 : Nat) < natLimit := by unfold natLimit; omega
    obtain ⟨rfl, hpowLt, rfl⟩ := hpowSpec 2 b _ _ _ h2lt hb (by simpa using cpow)
    obtain ⟨rfl, hmulLt, rfl⟩ := hmulSpec a (2 ^ b) _ _ _ ha hpowLt cmul
    have hshlEq : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
    rw [hshlEq]
    exact ⟨rfl, hmulLt, rfl⟩

/-- Operational soundness of `Prog::shl_56(a, b)` directly from `WorldHasFn` bindings. -/
theorem eval_shl_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    (hshl : WorldHasFn world (qualified "shl_56") ["x", "k"]
      (qualifyExprF F shl56Fn.body))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "shl_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ Nat.shiftLeft a b < natLimit ∧ r = .field ((Nat.shiftLeft a b : Nat) : F) :=
  eval_shl_56_of_contracts fc hshl
    (fun _ _ _ _ _ hx hy e => eval_mul_56 fc hbc hsplit hu24 hu56 hmul hx hy e)
    (fun _ _ _ _ _ hx hy e =>
      eval_pow_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hloop hpow hx hy e)
    ha hb ev

/-- Contract-parameterized soundness of `Prog::shr_56(a, b)`:
returns `.field ((Nat.shiftRight a b : Nat) : F)` (`= a / 2^b`) and leaves the heap unchanged. -/
theorem eval_shr_56_of_contracts {world : World F}
    (hshr : WorldHasFn world (qualified "shr_56") ["x", "k"]
      (qualifyExprF F shr56Fn.body))
    (hsubSpec : ∀ x y h r h', x < natLimit → y < natLimit →
      EvalFn world (qualified "sub_borrow_56") [.field (x : F), .field (y : F)] h r h' →
      h' = h ∧ r = .tuple [.field ((x - y : Nat) : F), .field (if y ≤ x then (1 : F) else 0)])
    (hpowSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)])
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "shr_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ Nat.shiftRight a b < natLimit ∧ r = .field ((Nat.shiftRight a b : Nat) : F) := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hshr
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_shr56Fn) ev
  simp only [shr56Fn, matchE, callE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_sub_borrow_56, qualifyName_divmod_56, qualifyName_pow_56, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at body
  obtain ⟨_, vge, _, evsub, k1⟩ := evalExpr_let_wild_tuple2_inv body
  obtain ⟨vk, v56, _, _, evk, ev56, csub⟩ := evalExpr_call2_inv evsub
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev56
  have h56lt : (56 : Nat) < natLimit := by unfold natLimit; omega
  obtain ⟨rfl, hsubEq⟩ := hsubSpec b 56 _ _ _ hb h56lt (by simpa using csub)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hsubEq
  obtain ⟨_, rfl⟩ := hsubEq
  obtain ⟨vge', _, evge', hbr⟩ := evalExpr_match_lit_wild_inv k1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evge'
  rcases hbr with ⟨hge1, hlarge⟩ | ⟨_, hsmall⟩
  · have h56le : 56 ≤ b := by
      by_contra hnot
      simp only [hnot, ↓reduceIte, Value.field.injEq] at hge1
      exact zero_ne_one hge1
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv hlarge
    have hpowGe : natLimit ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) h56le
    have hshr0 : Nat.shiftRight a b = 0 := by
      have hshrEq : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
      rw [hshrEq]
      exact Nat.div_eq_of_lt (lt_of_lt_of_le ha hpowGe)
    rw [hshr0]
    exact ⟨rfl, by unfold natLimit; omega, by simp⟩
  · obtain ⟨vq, _, _, evdm, k2⟩ := evalExpr_let_tuple2_wild_inv hsmall
    obtain ⟨vx', vp, _, _, evx', evp, cdm⟩ := evalExpr_call2_inv evdm
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evx'
    obtain ⟨v2, vk', _, _, ev2, evk', cpow⟩ := evalExpr_call2_inv evp
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk'
    have h2lt : (2 : Nat) < natLimit := by unfold natLimit; omega
    obtain ⟨rfl, hpowLt, rfl⟩ := hpowSpec 2 b _ _ _ h2lt hb (by simpa using cpow)
    obtain ⟨rfl, _, hdmEq⟩ := hdivmodSpec a (2 ^ b) _ _ _ ha hpowLt cdm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
    obtain ⟨rfl, _⟩ := hdmEq
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k2
    have hshrEq : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b
    rw [hshrEq]
    exact ⟨rfl, lt_of_le_of_lt (Nat.div_le_self a (2 ^ b)) ha, rfl⟩

/-- Operational soundness of `Prog::shr_56(a, b)` directly from `WorldHasFn` bindings. -/
theorem eval_shr_56 {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F)
    (hbc : ByteCheckSpec world usePair)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    (hshr : WorldHasFn world (qualified "shr_56") ["x", "k"]
      (qualifyExprF F shr56Fn.body))
    {a b : Nat} (ha : a < natLimit) (hb : b < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "shr_56") [.field (a : F), .field (b : F)] h r h') :
    h' = h ∧ Nat.shiftRight a b < natLimit ∧ r = .field ((Nat.shiftRight a b : Nat) : F) :=
  eval_shr_56_of_contracts hshr
    (fun _ _ _ _ _ hx hy e => eval_sub_borrow_56 fc hbc hsub hx hy e)
    (fun _ _ _ _ _ hx hy e =>
      eval_pow_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hloop hpow hx hy e)
    (fun _ _ _ _ _ hx hy e =>
      eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    ha hb ev

end Core56

/-! ## `UInt32` Value Predicate, Library Contracts, and Sound `u32_*` Gadgets -/

section U32Gadgets

variable {F : Type} [Field F] [DecidableEq F]

/-- Checked 32-bit word value: 4 little-endian byte fields `< 256` packing to `n`. -/
def isU32Val (n : Nat) (v : SourceValue F) : Prop :=
  ∃ b0 b1 b2 b3 : Nat,
    b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
    n = U32.pack b0 b1 b2 b3 ∧
    v = .tuple [.field (b0 : F), .field (b1 : F), .field (b2 : F), .field (b3 : F)]

omit [DecidableEq F] in
theorem isU32Val_lt {n : Nat} {v : SourceValue F} (hv : isU32Val n v) : n < U32.base := by
  obtain ⟨b0, b1, b2, b3, h0, h1, h2, h3, rfl, _⟩ := hv
  exact U32.pack_lt h0 h1 h2 h3

omit [DecidableEq F] in
theorem isU32Val_lt_natLimit {n : Nat} {v : SourceValue F} (hv : isU32Val n v) : n < natLimit :=
  lt_trans (isU32Val_lt hv) (by decide)

/-- Operational contracts for the `UInt8`/`UInt32` library functions used by
`TypedLower`'s `u32_*` gadgets. -/
structure U32Contracts (world : World F) : Prop where
  u8_to_field : ∀ v h r h',
    EvalFn world "UInt8::to_field" [v] h r h' → r = v ∧ h' = h
  to_bytes : ∀ n w h r h', isU32Val n w →
    EvalFn world "UInt32::to_bytes" [w] h r h' → r = w ∧ h' = h
  compact : ∀ n w h r h', isU32Val n w →
    EvalFn world "UInt32::compact" [w] h r h' → r = .field (n : F) ∧ h' = h
  compact_field : ∀ v h r h',
    EvalFn world "UInt32::compact_field" [v] h r h' → r = v ∧ h' = h
  from_fields : ∀ v0 v1 v2 v3 h r h',
    EvalFn world "UInt32::from_fields" [.tuple [v0, v1, v2, v3]] h r h' →
    ∃ b0 b1 b2 b3 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      v0 = .field (b0 : F) ∧ v1 = .field (b1 : F) ∧
      v2 = .field (b2 : F) ∧ v3 = .field (b3 : F) ∧
      isU32Val (U32.pack b0 b1 b2 b3) r ∧ h' = h
  from_field : ∀ v h r h',
    EvalFn world "UInt32::from_field" [v] h r h' →
    ∃ n, n < U32.base ∧ v = .field (n : F) ∧ isU32Val n r ∧ h' = h

/-- Close `TypedGadgets.U32Contracts s.world` directly from `World.checkTables` and
`TypedWorld.checkU32Functions` under `FieldCompatible64 F`. -/
theorem U32Contracts.ofCheck {s : Generic.Source F}
    (fc : FieldCompatible64 F) (ht : checkTables s = true) (h : checkU32Functions s = true) :
    U32Contracts s.world :=
  let c := TypedWorld.u32Contracts_of_check fc.toU32Compatible ht h
  { u8_to_field := c.u8_to_field
    to_bytes := c.to_bytes
    compact := c.compact
    compact_field := c.compact_field
    from_fields := c.from_fields
    from_field := c.from_field }

private theorem eval_u32ToField_var {world : World F} (u32 : U32Contracts world)
    {locals : Environment F Nat} {nm : String} {n : Nat} {w r : SourceValue F}
    {h h' : Heap F} (hw : isU32Val n w)
    (hlook : locals.find? (·.1 == nm) = some (nm, w))
    (ev : EvalExpr world [] locals
      (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var nm]])
      h r h') :
    r = .field (n : F) ∧ h' = h := by
  obtain ⟨vc, _, evc, ccf⟩ := evalExpr_call1_inv ev
  obtain ⟨vw, _, evw, cc⟩ := evalExpr_call1_inv evc
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evw
  obtain ⟨rfl, rfl⟩ := u32.compact _ _ _ _ _ hw cc
  exact u32.compact_field _ _ _ _ ccf

private theorem body_u32OfFieldFn :
    u32OfFieldFn.body =
      .letValue (.array [.bind "h0", .bind "h1", .bind "h2", .bind "h3",
                         .bind "h4", .bind "h5", .bind "h6", .bind "h7"])
        (.hint (.array .field 8) (.var "x") "bytes_le")
        (.letValue (.bind "lo")
          (.call "UInt32::from_fields" (some []) [.array [.var "h0", .var "h1", .var "h2", .var "h3"]])
          (.letValue (.bind "hi")
            (.call "UInt32::from_fields" (some []) [.array [.var "h4", .var "h5", .var "h6", .var "h7"]])
            (.letValue .wildcard
              (.builtin (.assertEq (assertion "u32_of_field: top byte zero")) [.var "h7", .literal 0])
              (.letValue .wildcard
                (.builtin (.assertEq (assertion "u32_of_field: recomposition"))
                  [.binary .add
                    (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "lo"]])
                    (.binary .mul (.literal (2 ^ 32))
                      (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "hi"]])),
                   .var "x"])
                (.var "lo"))))) := rfl

/-- Soundness of `Prog::u32_of_field`: reduces any `< 2^56` natural `x` modulo `2^32`. -/
theorem eval_u32_of_field {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_of_field") ["x"]
      (qualifyExprF F u32OfFieldFn.body))
    {x : Nat} (hx : x < natLimit)
    {r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world (qualified "u32_of_field") [.field (x : F)] h r h') :
    h' = h ∧ isU32Val (x % U32.base) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32OfFieldFn) ev
  rw [body_u32OfFieldFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyTy, qualifyName_u32_from_fields,
    qualifyName_u32_compact_field, qualifyName_u32_compact, Option.map_some,
    Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map, Nat.cast_zero] at body
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, _, evh, k1⟩ := evalExpr_let_array8_inv body
  obtain ⟨_, evx⟩ := evalExpr_hint_inv evh
  obtain ⟨_, rfl⟩ := evalExpr_var_inv evx
  obtain ⟨vlo, _, evlo, k2⟩ := evalExpr_let_bind_inv k1
  obtain ⟨va1, _, eva1, cff1⟩ := evalExpr_call1_inv evlo
  obtain ⟨u0, u1, u2, u3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv eva1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e3
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl, rfl, rfl, hloVal, rfl⟩ :=
    u32.from_fields _ _ _ _ _ _ _ cff1
  obtain ⟨vhi, _, evhi, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨va2, _, eva2, cff2⟩ := evalExpr_call1_inv evhi
  obtain ⟨u4, u5, u6, u7, _, _, _, e4, e5, e6, e7, rfl⟩ := evalExpr_array4_inv eva2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e5
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) e7
  obtain ⟨b4, b5, b6, b7, hb4, hb5, hb6, hb7, rfl, rfl, rfl, rfl, hhiVal, rfl⟩ :=
    u32.from_fields _ _ _ _ _ _ _ cff2
  obtain ⟨hb7Zero, k4⟩ := evalExpr_assertVarZero_seq_inv (by simp; rfl) k3
  have hb7_0 : b7 = 0 :=
    fc.natCast_inj (by unfold fieldBound64; omega) (by unfold fieldBound64; omega)
      (by simpa using Value.field.inj hb7Zero)
  obtain ⟨_, _, hass, k5⟩ := evalExpr_let_wildcard_inv k4
  obtain ⟨vl, vr, _, evl, evr, hrecEq, _⟩ := evalExpr_assertEq_inv hass
  obtain ⟨va, vb, _, eva, evb, hadd⟩ := evalExpr_binary_inv evl
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hloVal (by simp) eva
  obtain ⟨vc, vd, _, evc, evd, hmul⟩ := evalExpr_binary_inv evb
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evc
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hhiVal (by simp) evd
  simp only [evalBinOp, Except.ok.injEq] at hmul; subst hmul
  simp only [evalBinOp, Except.ok.injEq] at hadd; subst hadd
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) k5
  have hloLt : U32.pack b0 b1 b2 b3 < U32.base := U32.pack_lt hb0 hb1 hb2 hb3
  have hhiLt : U32.pack b4 b5 b6 b7 < 2 ^ 24 := by
    unfold U32.pack; subst hb7_0; omega
  have hlift : U32.pack b0 b1 b2 b3 + 2 ^ 32 * U32.pack b4 b5 b6 b7 = x := by
    apply fc.natCast_inj
      (by unfold U32.base fieldBound64 at *; omega)
      (lt_trans hx (by unfold natLimit fieldBound64; omega))
    simpa [Nat.cast_add, Nat.cast_mul] using Value.field.inj hrecEq
  have hmod : U32.pack b0 b1 b2 b3 = x % U32.base := by
    have hbase : (2 ^ 32 : Nat) = U32.base := rfl
    rw [← hlift, hbase, Nat.mul_comm U32.base, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hloLt]
  rw [← hmod]
  exact ⟨rfl, hloVal⟩

/-- Soundness of `Prog::u32_complement`: bitwise complement `(2^32 - 1) - a` on a `U32`. -/
theorem eval_u32_complement {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_complement") ["a"]
      (qualifyExprF F u32ComplementFn.body))
    {a : Nat} {wa r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa)
    (ev : EvalFn world (qualified "u32_complement") [wa] h r h') :
    h' = h ∧ isU32Val (U32.base - 1 - a) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32ComplementFn) ev
  simp only [u32ComplementFn, letE, callE, subE, vE, litE, qualifyExprF, qualifyExpr, qualifyPat,
    qualifyName_u32_to_bytes, qualifyName_u32_from_fields, qualifyName_u8_to_field,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ := hwa
  obtain ⟨vbs, _, evbs, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨va', _, eva', ctb⟩ := evalExpr_call1_inv evbs
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eva'
  obtain ⟨rfl, rfl⟩ := u32.to_bytes _ _ _ _ _ ⟨a0, a1, a2, a3, ha0, ha1, ha2, ha3, rfl, rfl⟩ ctb
  obtain ⟨varr, _, evarr, cff⟩ := evalExpr_call1_inv k1
  obtain ⟨v0, v1, v2, v3, _, _, _, e0, e1, e2, e3, rfl⟩ := evalExpr_array4_inv evarr
  have step :
      ∀ (idx ai : Nat) {v : SourceValue F} {h1 h2 : Heap F},
        ai < 256 →
        ([.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F)] :
          List (SourceValue F))[idx]? = some (.field (ai : F)) →
        EvalExpr world []
          [("bs", .tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F)]),
           ("a", .tuple [.field (a0 : F), .field (a1 : F), .field (a2 : F), .field (a3 : F)])]
          (.binary .sub (.literal ((255 : Nat) : F))
            (.call "UInt8::to_field" (some []) [.index (.var "bs") idx])) h1 v h2 →
        v = .field ((255 - ai : Nat) : F) ∧ h2 = h1 := by
    intro idx ai v h1 h2 hai hidx evi
    obtain ⟨vl, vr, _, evl, evr, hsub⟩ := evalExpr_binary_inv evi
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evl
    obtain ⟨vb, _, evb, cu8⟩ := evalExpr_call1_inv evr
    obtain ⟨vt, evt, hproj⟩ := evalExpr_index_inv evb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evt
    simp only [projectValue, hidx, pure, Except.pure, Except.ok.injEq] at hproj
    subst hproj
    obtain ⟨rfl, rfl⟩ := u32.u8_to_field _ _ _ _ cu8
    simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
    exact ⟨by rw [Nat.cast_sub (by omega)], rfl⟩
  obtain ⟨rfl, rfl⟩ := step 0 a0 ha0 (by simp) e0
  obtain ⟨rfl, rfl⟩ := step 1 a1 ha1 (by simp) e1
  obtain ⟨rfl, rfl⟩ := step 2 a2 ha2 (by simp) e2
  obtain ⟨rfl, rfl⟩ := step 3 a3 ha3 (by simp) e3
  obtain ⟨c0, c1, c2, c3, hc0, hc1, hc2, hc3, eq0, eq1, eq2, eq3, hres, rfl⟩ :=
    u32.from_fields _ _ _ _ _ _ _ cff
  have h0 : 255 - a0 = c0 :=
    fc.natCast_inj (by unfold fieldBound64; omega) (by unfold fieldBound64; omega) (Value.field.inj eq0)
  have h1 : 255 - a1 = c1 :=
    fc.natCast_inj (by unfold fieldBound64; omega) (by unfold fieldBound64; omega) (Value.field.inj eq1)
  have h2 : 255 - a2 = c2 :=
    fc.natCast_inj (by unfold fieldBound64; omega) (by unfold fieldBound64; omega) (Value.field.inj eq2)
  have h3 : 255 - a3 = c3 :=
    fc.natCast_inj (by unfold fieldBound64; omega) (by unfold fieldBound64; omega) (Value.field.inj eq3)
  subst h0 h1 h2 h3
  have hpack : U32.pack (255 - a0) (255 - a1) (255 - a2) (255 - a3) =
      U32.base - 1 - U32.pack a0 a1 a2 a3 := by
    unfold U32.pack U32.base; omega
  rw [hpack] at hres
  exact ⟨rfl, hres⟩

private theorem body_u32DivFn :
    u32DivFn.body =
      .letValue (.bind "bf")
        (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "b"]])
        (.matchValue (.var "bf")
          [(.literal 0, .call "UInt32::from_field" (some []) [.literal 0]),
           (.wildcard,
            .letValue (.tuple [.bind "q", .wildcard])
              (.call "divmod_56" (some [])
                [.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "a"]],
                 .var "bf"])
              (.call "UInt32::from_field" (some []) [.var "q"]))]) := rfl

/-- Soundness of `Prog::u32_div`: exact unsigned division `a / b` (with `a / 0 = 0`). -/
theorem eval_u32_div_of_contracts {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_div") ["a", "b"]
      (qualifyExprF F u32DivFn.body))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)])
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_div") [wa, wb] h r h') :
    h' = h ∧ isU32Val (a / b) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32DivFn) ev
  rw [body_u32DivFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyName_u32_compact_field,
    qualifyName_u32_compact, qualifyName_u32_from_field, qualifyName_divmod_56,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero] at body
  obtain ⟨vbf, _, evbf, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwb (by simp) evbf
  obtain ⟨vbf', _, evbf', hbr⟩ := evalExpr_match_lit_wild_inv k1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evbf'
  rcases hbr with ⟨hb0F, hzero⟩ | ⟨_, hpos⟩
  · have hb0 : b = 0 :=
      fc.natCast_inj56 (isU32Val_lt_natLimit hwb) (by unfold natLimit; omega)
        (by simpa using Value.field.inj hb0F)
    subst hb0
    obtain ⟨v0, _, ev0, cff⟩ := evalExpr_call1_inv hzero
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
    obtain ⟨n, hn, h0eq, hnVal, rfl⟩ := u32.from_field _ _ _ _ cff
    have hn0 : n = 0 :=
      fc.natCast_inj (lt_trans hn (by decide)) (by unfold fieldBound64; omega)
        (by simpa using (Value.field.inj h0eq).symm)
    subst hn0
    exact ⟨rfl, by simpa using hnVal⟩
  · obtain ⟨vq, _, _, evdm, k2⟩ := evalExpr_let_tuple2_wild_inv hpos
    obtain ⟨vaf, vbf'', _, _, evaf, evbf'', cdm⟩ := evalExpr_call2_inv evdm
    obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwa (by simp) evaf
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evbf''
    obtain ⟨rfl, _, hdmEq⟩ :=
      hdivmodSpec a b _ _ _ (isU32Val_lt_natLimit hwa) (isU32Val_lt_natLimit hwb) cdm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
    obtain ⟨rfl, _⟩ := hdmEq
    obtain ⟨vq', _, evq', cff⟩ := evalExpr_call1_inv k2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
    obtain ⟨n, hn, hqeq, hnVal, rfl⟩ := u32.from_field _ _ _ _ cff
    have hqlt : a / b < U32.base := lt_of_le_of_lt (Nat.div_le_self a b) (isU32Val_lt hwa)
    have hqn : a / b = n :=
      fc.natCast_inj (lt_trans hqlt (by decide)) (lt_trans hn (by decide)) (Value.field.inj hqeq)
    subst hqn
    exact ⟨rfl, hnVal⟩

private theorem body_u32ModFn :
    u32ModFn.body =
      .letValue (.bind "bf")
        (.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "b"]])
        (.matchValue (.var "bf")
          [(.literal 0, .var "a"),
           (.wildcard,
            .letValue (.tuple [.wildcard, .bind "r"])
              (.call "divmod_56" (some [])
                [.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "a"]],
                 .var "bf"])
              (.call "UInt32::from_field" (some []) [.var "r"]))]) := rfl

/-- Soundness of `Prog::u32_mod`: exact unsigned remainder `a % b` (with `a % 0 = a`). -/
theorem eval_u32_mod_of_contracts {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_mod") ["a", "b"]
      (qualifyExprF F u32ModFn.body))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)])
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_mod") [wa, wb] h r h') :
    h' = h ∧ isU32Val (a % b) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32ModFn) ev
  rw [body_u32ModFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyName_u32_compact_field,
    qualifyName_u32_compact, qualifyName_u32_from_field, qualifyName_divmod_56,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map,
    Nat.cast_zero] at body
  obtain ⟨vbf, _, evbf, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwb (by simp) evbf
  obtain ⟨vbf', _, evbf', hbr⟩ := evalExpr_match_lit_wild_inv k1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evbf'
  rcases hbr with ⟨hb0F, hzero⟩ | ⟨_, hpos⟩
  · have hb0 : b = 0 :=
      fc.natCast_inj56 (isU32Val_lt_natLimit hwb) (by unfold natLimit; omega)
        (by simpa using Value.field.inj hb0F)
    subst hb0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) hzero
    exact ⟨rfl, by simpa using hwa⟩
  · obtain ⟨_, vr, _, evdm, k2⟩ := evalExpr_let_wild_tuple2_inv hpos
    obtain ⟨vaf, vbf'', _, _, evaf, evbf'', cdm⟩ := evalExpr_call2_inv evdm
    obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwa (by simp) evaf
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evbf''
    obtain ⟨rfl, _, hdmEq⟩ :=
      hdivmodSpec a b _ _ _ (isU32Val_lt_natLimit hwa) (isU32Val_lt_natLimit hwb) cdm
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdmEq
    obtain ⟨_, rfl⟩ := hdmEq
    obtain ⟨vr', _, evr', cff⟩ := evalExpr_call1_inv k2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evr'
    obtain ⟨n, hn, hreq, hnVal, rfl⟩ := u32.from_field _ _ _ _ cff
    have hrlt : a % b < U32.base := lt_of_le_of_lt (Nat.mod_le a b) (isU32Val_lt hwa)
    have hrn : a % b = n :=
      fc.natCast_inj (lt_trans hrlt (by decide)) (lt_trans hn (by decide)) (Value.field.inj hreq)
    subst hrn
    exact ⟨rfl, hnVal⟩

private theorem body_u32ShrFn :
    u32ShrFn.body =
      .letValue (.bind "s")
        (.call "UInt8::to_field" (some [])
          [.index (.call "UInt32::to_bytes" (some []) [.var "b"]) 0])
        (.letValue (.tuple [.wildcard, .bind "k"])
          (.call "divmod_56" (some []) [.var "s", .literal 32])
          (.letValue (.bind "p")
            (.call "pow_56" (some []) [.literal 2, .var "k"])
            (.letValue (.tuple [.bind "q", .wildcard])
              (.call "divmod_56" (some [])
                [.call "UInt32::compact_field" (some []) [.call "UInt32::compact" (some []) [.var "a"]],
                 .var "p"])
              (.call "UInt32::from_field" (some []) [.var "q"])))) := rfl

/-- Soundness of `Prog::u32_shr`: logical right shift `a >>> (b % 32)`. -/
theorem eval_u32_shr_of_contracts {world : World F}
    (fc : FieldCompatible64 F) (u32 : U32Contracts world)
    (hfn : WorldHasFn world (qualified "u32_shr") ["a", "b"]
      (qualifyExprF F u32ShrFn.body))
    (hdivmodSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "divmod_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ 0 < b ∧ r = .tuple [.field ((a / b : Nat) : F), .field ((a % b : Nat) : F)])
    (hpowSpec : ∀ a b h r h', a < natLimit → b < natLimit →
      EvalFn world (qualified "pow_56") [.field (a : F), .field (b : F)] h r h' →
      h' = h ∧ a ^ b < natLimit ∧ r = .field ((a ^ b : Nat) : F))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_shr") [wa, wb] h r h') :
    h' = h ∧ isU32Val (Nat.shiftRight a (b % 32)) r := by
  obtain ⟨_, body⟩ := evalFn_plain_inv hfn
    (by rw [isPlainExpr_qualifyExprF]; exact isPlainExpr_u32ShrFn) ev
  rw [body_u32ShrFn] at body
  simp only [qualifyExprF, qualifyExpr, qualifyPat, qualifyName_u8_to_field,
    qualifyName_u32_to_bytes, qualifyName_divmod_56, qualifyName_pow_56,
    qualifyName_u32_compact_field, qualifyName_u32_compact, qualifyName_u32_from_field,
    Option.map_some, Aiur.Generic.Expr.map, Aiur.Generic.Pattern.map, List.map] at body
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ := hwb
  obtain ⟨vs, _, evs, k1⟩ := evalExpr_let_bind_inv body
  obtain ⟨vi, _, evi, cu8⟩ := evalExpr_call1_inv evs
  obtain ⟨vt, evt, hproj⟩ := evalExpr_index_inv evi
  obtain ⟨vb', _, evb', ctb⟩ := evalExpr_call1_inv evt
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evb'
  obtain ⟨rfl, rfl⟩ := u32.to_bytes _ _ _ _ _ ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, rfl, rfl⟩ ctb
  simp only [projectValue, List.getElem?_cons_zero, pure, Except.pure, Except.ok.injEq] at hproj
  subst hproj
  obtain ⟨rfl, rfl⟩ := u32.u8_to_field _ _ _ _ cu8
  obtain ⟨_, vk, _, evdm1, k2⟩ := evalExpr_let_wild_tuple2_inv k1
  obtain ⟨vs', v32, _, _, evs', ev32, cdm1⟩ := evalExpr_call2_inv evdm1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evs'
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev32
  obtain ⟨rfl, _, hdm1Eq⟩ :=
    hdivmodSpec b0 32 _ _ _ (by unfold natLimit; omega) (by unfold natLimit; omega) cdm1
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdm1Eq
  obtain ⟨_, rfl⟩ := hdm1Eq
  have hkMod : b0 % 32 = U32.pack b0 b1 b2 b3 % 32 := by
    unfold U32.pack; omega
  obtain ⟨vp, _, evp, k3⟩ := evalExpr_let_bind_inv k2
  obtain ⟨v2, vk', _, _, ev2, evk', cpow⟩ := evalExpr_call2_inv evp
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evk'
  obtain ⟨rfl, hpowLt, rfl⟩ :=
    hpowSpec 2 (b0 % 32) _ _ _ (by unfold natLimit; omega) (by unfold natLimit; omega) cpow
  obtain ⟨vq, _, _, evdm2, k4⟩ := evalExpr_let_tuple2_wild_inv k3
  obtain ⟨vaf, vp', _, _, evaf, evp', cdm2⟩ := evalExpr_call2_inv evdm2
  obtain ⟨rfl, rfl⟩ := eval_u32ToField_var u32 hwa (by simp) evaf
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evp'
  obtain ⟨rfl, _, hdm2Eq⟩ :=
    hdivmodSpec a (2 ^ (b0 % 32)) _ _ _ (isU32Val_lt_natLimit hwa) hpowLt
      (by simpa [Nat.cast_pow] using cdm2)
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hdm2Eq
  obtain ⟨rfl, _⟩ := hdm2Eq
  obtain ⟨vq', _, evq', cff⟩ := evalExpr_call1_inv k4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evq'
  obtain ⟨n, hn, hqeq, hnVal, rfl⟩ := u32.from_field _ _ _ _ cff
  have hqlt : a / 2 ^ (b0 % 32) < U32.base :=
    lt_of_le_of_lt (Nat.div_le_self a _) (isU32Val_lt hwa)
  have hqn : a / 2 ^ (b0 % 32) = n :=
    fc.natCast_inj (lt_trans hqlt (by decide)) (lt_trans hn (by decide)) (Value.field.inj hqeq)
  subst hqn
  have hshrEq : Nat.shiftRight a (U32.pack b0 b1 b2 b3 % 32) =
      a / 2 ^ (U32.pack b0 b1 b2 b3 % 32) := Nat.shiftRight_eq_div_pow a _
  rw [hshrEq, ← hkMod]
  exact ⟨rfl, hnVal⟩

/-- Operational soundness of `Prog::u32_div` directly from `WorldHasFn` bindings. -/
theorem eval_u32_div {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair) (u32 : U32Contracts world)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hfn : WorldHasFn world (qualified "u32_div") ["a", "b"]
      (qualifyExprF F u32DivFn.body))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_div") [wa, wb] h r h') :
    h' = h ∧ isU32Val (a / b) r :=
  eval_u32_div_of_contracts fc u32 hfn
    (fun _ _ _ _ _ hx hy e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    hwa hwb ev

/-- Operational soundness of `Prog::u32_mod` directly from `WorldHasFn` bindings. -/
theorem eval_u32_mod {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair) (u32 : U32Contracts world)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hfn : WorldHasFn world (qualified "u32_mod") ["a", "b"]
      (qualifyExprF F u32ModFn.body))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_mod") [wa, wb] h r h') :
    h' = h ∧ isU32Val (a % b) r :=
  eval_u32_mod_of_contracts fc u32 hfn
    (fun _ _ _ _ _ hx hy e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    hwa hwb ev

/-- Operational soundness of `Prog::u32_shr` directly from `WorldHasFn` bindings. -/
theorem eval_u32_shr {world : World F} {usePair : Bool}
    (fc : FieldCompatible64 F) (hbc : ByteCheckSpec world usePair) (u32 : U32Contracts world)
    (hsplit : WorldHasFn world (qualified "split_32_24") ["x"]
      (qualifyExprF F (split32_24Fn usePair).body))
    (hu24 : WorldHasFn world (qualified "check_u24") ["x"]
      (qualifyExprF F (checkU24Fn usePair).body))
    (hu56 : WorldHasFn world (qualified "check_u56") ["x"]
      (qualifyExprF F (checkU56Fn usePair).body))
    (hsub : WorldHasFn world (qualified "sub_borrow_56") ["x", "y"]
      (qualifyExprF F (subBorrow56Fn usePair).body))
    (hmul : WorldHasFn world (qualified "mul_56") ["x", "y"]
      (qualifyExprF F mul56Fn.body))
    (hdivmod : WorldHasFn world (qualified "divmod_56") ["x", "y"]
      (qualifyExprF F divmod56Fn.body))
    (hloop : WorldHasFn world (qualified "pow_56_loop") ["base", "exp", "acc"]
      (qualifyExprF F pow56LoopFn.body))
    (hpow : WorldHasFn world (qualified "pow_56") ["base", "exp"]
      (qualifyExprF F pow56Fn.body))
    (hfn : WorldHasFn world (qualified "u32_shr") ["a", "b"]
      (qualifyExprF F u32ShrFn.body))
    {a b : Nat} {wa wb r : SourceValue F} {h h' : Heap F}
    (hwa : isU32Val a wa) (hwb : isU32Val b wb)
    (ev : EvalFn world (qualified "u32_shr") [wa, wb] h r h') :
    h' = h ∧ isU32Val (Nat.shiftRight a (b % 32)) r :=
  eval_u32_shr_of_contracts fc u32 hfn
    (fun _ _ _ _ _ hx hy e => eval_divmod_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hx hy e)
    (fun _ _ _ _ _ hx hy e =>
      eval_pow_56 fc hbc hsplit hu24 hu56 hsub hmul hdivmod hloop hpow hx hy e)
    hwa hwb ev

end U32Gadgets

end IxCC.AiurBackend.TypedGadgets
