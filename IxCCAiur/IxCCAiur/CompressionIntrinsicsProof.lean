import IxCCAiur.CompressionIntrinsics
import IxCCAiur.FieldLowerProof
import IxCCAiur.InlineFuseProof
import IxCCAiur.Blake3Spec
import IxCCAiur.WitnessIO
import IxCCAiur.CompiledCert
import IxCCAiur.TypedClaim

/-! # Certified Backward Soundness of Compression Intrinsic Lowering (`IxCCAiur.CompressionIntrinsicsProof`)

Establishes end-to-end certified backward soundness for
`IxCC.AiurBackend.CompressionIntrinsics.lowerCompressionOps`, multi-field linking,
custom entry aliasing, and existential witness-stream ingress over arbitrary prime
fields `[Field F] [DecidableEq F]` and concretely over **Goldilocks (`p_G`)**,
**BN254 (`Fr`)**, and **BLS12-381 (`Fr`)**:

1. **Pure Goldilocks (`GLF`) & Cubic Extension (`ExtGL = GLF[X]/(X^3 - X - 1)`) Algebra &
   Emulated No-Wrap Arithmetic**:
   - Exact ring and adjugate-inverse specifications for `ExtGL` matching Karatsuba
     multiplication (`eg_mul`) and adjugate inversion (`eg_inverse`).
   - Generic no-wrap emulated reduction theorems (`EmulatedGLBounds p`) instantiated
     at `BN254 Fr` and `BLS12-381 Fr` using `bn254_emulated_*_bound` and
     `bls12381_emulated_*_bound`.
2. **Unified `GoldilocksContracts` for Both Native and Emulated `Goldilocks` Libraries**:
   - Operational `EvalFn` contracts for all 11 `GoldilocksOp`s (`gl_add`, `gl_sub`,
     `gl_mul`, `gl_neg`, `gl_inverse`, `gl_is_zero`, `gl_eq`, `eg_add`, `eg_sub`,
     `eg_mul`, `eg_inverse`), sharing a single value encoding `glVal F` / `egVal F`.
   - Computable world checkers and soundness proofs discharging `GoldilocksContracts`
     from BOTH native `Aiur.Library.Field.Goldilocks` (over `GLF`) AND emulated
     `Aiur.Library.Field.Goldilocks.Emulated` (over `BN254 Fr`, `BLS12-381 Fr`, and
     any prime `ZMod p` satisfying `EmulatedGLBounds p`).
3. **Per-Op `CompressionOp` Backward Soundness (`field`, `goldilocks`, `blake3`, `witness`)**:
   - `CompressionOp.field`: delegated to `FieldLowerProof` over `ZMod p` and generalized
     to arbitrary `[Field F] [DecidableEq F]`.
   - `CompressionOp.goldilocks`: connected to `GoldilocksContracts` across all scalar,
     `[Field; 3]`, and `(Field, Field, Field)` parameter/return adapter shapes.
   - `CompressionOp.blake3`: connected directly to `Blake3Spec.Blake3Contracts`
     (`compress_init`, `hash`, `pack_digest`).
   - `CompressionOp.witness`: connected directly to `WitnessIO` (`StarkIO::read_channel`,
     `StarkIO::read_byte_stream`, `KzgIO::read_stream`, `KzgIO::sized_channel`),
     yielding unconditional heap extension and existential valid byte streams.
4. **Whole-Program Backward Simulation for `lowerCompressionOps`**:
   - Proves `evalExpr_lowerCompressionExpr_backward`, `evalExpr_lowerCompressionFn_backward`,
     `lowerCompressionOpsCore_backward`, and `lowerCompressionOps_backward` (reusing
     `InlineFuseProof.world_transformBodies_backward` and `pruneUnreachable_backward`)
     under a demand-gated `CompressionIntrinsicWorld`.
5. **End-to-End Composition (`CompressionCert`) with `aliasEntry_sound`, `CompiledCert` /
   `TypedClaim`, and `WitnessIO`**:
   - Composes `plan.checkMemo (rawROM rom) root rows = .ok ()` →
     `Aiur.Modules.Prepared.depth_grouped_activated_heap_sound` →
     `aliasEntry_sound_of_check` → `lowerCompressionOps_backward` →
     `TypedClaim` / `Progress.checkShape` and `WitnessIO.witness_wrapper_*_sound`,
     instantiated for Goldilocks, BN254 `Fr`, and BLS12-381 `Fr`.

Strictly pure Lean 4, total (zero `partial`), zero `sorry`, zero `admit`, zero `axiom`,
zero `native_decide`, zero `bv_decide`, strictly `[propext, Classical.choice, Quot.sound]`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.CompressionIntrinsicsProof

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.AiurBackend.Lower
  (Expr Pat Fn natLimit moduleName qualified qualifyName qualifyPat qualifyExpr
   qualifyPatF qualifyExprF hasDoubleColon allDistinct allDistinct_iff_nodup
   isPlainExpr isPlainList isPlainArms isPlainExpr_qualifyExprF
   vE litE letE matchE callE entryName)
open IxCC.AiurBackend.Gadgets
  (WorldHasFn evalFn_plain_inv evalExpr_literal_inv evalExpr_var_inv evalExpr_binary_inv
   evalExpr_index_inv evalExpr_call_inv evalExpr_call1_inv evalExpr_call2_inv
   evalExpr_tuple2_inv evalExpr_array3_inv evalExpr_array8_inv
   evalExpr_let_wildcard_inv evalExpr_let_bind_inv evalExpr_let_tuple2_inv
   evalExpr_assertEq_inv evalExpr_hint_inv)
open IxCC.AiurBackend.TypedGadgets
  (FieldCompatible64 fieldBound64 fieldCompatible64_goldilocks
   evalExpr_call3_inv evalExpr_match_lit_wild_inv)
open IxCC.AiurBackend.InlineFuse (pruneUnreachable)
open IxCC.AiurBackend.InlineFuseProof
  (SameAuxWorld WorldHasFns WorldProvidesFns WorldSub
   evalFn_of_worldSub pruneUnreachable_backward world_transformBodies_backward
   map_qualifyExprF map_qualifyArmsF)
open IxCC.AiurBackend.FieldLower
  (FieldOp fieldAddE fieldSubE fieldMulE fieldNegE fieldIsZeroE fieldEqE
   fieldInvVarE fieldInvE fieldDivVarsE fieldDivE fieldOpExpr fieldOpBody
   goldilocksModulus bn254Modulus bls12381Modulus checkFieldsIsZero)
open IxCC.AiurBackend.FieldLowerProof
  (FieldsIsZeroSpec fieldsIsZeroSpec_of_check
   fieldCompatible64_bn254 fieldCompatible64_bls12381
   zmod_natCast_ne_zero)
open IxCC.AiurBackend.Blake3Spec
  (hasNoControl no_evalExit_of_noControl evalFn_noControl_inv
   evalExpr_var_eq evalExpr_global_literal_inv evalExpr_project_inv evalExpr_call5_inv
   vecV u64v Stream Blake3LibraryWorld Blake3Contracts
   checkBlake3World blake3LibraryWorld_of_check)
open IxCC.AiurBackend.WitnessIO
  (isValidByteList isValidByteList_ofUInt8List ByteStreamRel KzgInputRel
   WitnessByteContracts WitnessWordContracts StarkIOWorld KzgIOWorld
   checkStarkIOFunctions checkKzgIOFunctions
   starkIOWorld_of_check kzgIOWorld_of_check
   witnessByteContracts_of_blake3 witnessWordContracts_of_blake3
   starkIo_read_byte_stream_sound starkIo_read_channel_sound
   kzgIo_read_stream_sound kzgIo_sized_channel_sound
   WitnessChannelKind witnessVarName witnessWrapperBody
   witness_wrapper_sound witness_wrapper_assertOk_sound)
open IxCC.AiurBackend.CompressionIntrinsics

/-! ## Section 1: Pure Goldilocks (`GLF`) & Cubic Extension (`ExtGL`) Algebra + No-Wrap Bounds -/

section GoldilocksAlgebra

/-- Canonical Goldilocks prime modulus `2^64 - 2^32 + 1 = 18446744069414584321`. -/
abbrev glModulus : Nat := Aiur.Library.U32.Goldilocks.modulus

/-- Native Goldilocks prime field `ZMod (2^64 - 2^32 + 1)`. -/
abbrev GLF := Aiur.Library.U32.Goldilocks.F

theorem glModulus_eq_emulated : glModulus = Aiur.Library.Field.Goldilocks.Emulated.modulus := rfl

theorem glModulus_pos : 0 < glModulus := by
  unfold glModulus Aiur.Library.U32.Goldilocks.modulus; omega

/-- Cubic extension element of `GLF[X] / (X^3 - X - 1)` represented by its
coefficient triple `(c0, c1, c2)` denoting `c0 + c1 * X + c2 * X^2`. -/
structure ExtGL where
  c0 : GLF
  c1 : GLF
  c2 : GLF
  deriving DecidableEq, Repr

namespace ExtGL

/-- Additive identity `0` in `ExtGL`. -/
def zero : ExtGL := ⟨0, 0, 0⟩

/-- Multiplicative identity `1` in `ExtGL`. -/
def one : ExtGL := ⟨1, 0, 0⟩

/-- Componentwise addition in `ExtGL`. -/
def add (a b : ExtGL) : ExtGL :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩

/-- Componentwise subtraction in `ExtGL`. -/
def sub (a b : ExtGL) : ExtGL :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩

/-- Componentwise negation in `ExtGL`. -/
def neg (a : ExtGL) : ExtGL :=
  ⟨-a.c0, -a.c1, -a.c2⟩

/-- Direct polynomial multiplication in `GLF[X] / (X^3 - X - 1)` using `X^3 = 1 + X`,
`X^4 = X + X^2`. -/
def mul (a b : ExtGL) : ExtGL :=
  ⟨a.c0 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1,
   a.c0 * b.c1 + a.c1 * b.c0 + a.c1 * b.c2 + a.c2 * b.c1 + a.c2 * b.c2,
   a.c0 * b.c2 + a.c2 * b.c0 + a.c1 * b.c1 + a.c2 * b.c2⟩

/-- Karatsuba multiplication matching `Goldilocks::eg_mul`. -/
def karatsubaMul (a b : ExtGL) : ExtGL :=
  let v0 := a.c0 * b.c0
  let v1 := a.c1 * b.c1
  let v2 := a.c2 * b.c2
  let m01 := ((a.c0 + a.c1) * (b.c0 + b.c1) - v0) - v1
  let m02 := ((a.c0 + a.c2) * (b.c0 + b.c2) - v0) - v2
  let m12 := ((a.c1 + a.c2) * (b.c1 + b.c2) - v1) - v2
  ⟨v0 + m12, (m01 + m12) + v2, (m02 + v1) + v2⟩

/-- Exact equivalence between Karatsuba multiplication (`Goldilocks::eg_mul`) and
polynomial multiplication modulo `X^3 - X - 1`. -/
theorem karatsubaMul_eq_mul (a b : ExtGL) : karatsubaMul a b = mul a b := by
  cases a; cases b
  simp only [karatsubaMul, mul, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Adjugate cofactor triple `(d0, d1, d2)` in `GLF[X] / (X^3 - X - 1)` used by
`Goldilocks::eg_inverse`. -/
def adj (a : ExtGL) : ExtGL :=
  let s := a.c0 + a.c2
  ⟨s * s - a.c1 * (a.c1 + a.c2),
   a.c2 * a.c2 - a.c0 * a.c1,
   a.c1 * a.c1 - a.c2 * s⟩

/-- Cubic field norm `N(a) = a0 * d0 + a2 * d1 + a1 * d2` matching `Goldilocks::eg_inverse`. -/
def norm (a : ExtGL) : GLF :=
  let d := adj a
  (a.c0 * d.c0 + a.c2 * d.c1) + a.c1 * d.c2

/-- Total inverse in `GLF[X] / (X^3 - X - 1)` (mapping zero-norm elements to `0`),
matching `Goldilocks::eg_inverse`. -/
def inv (a : ExtGL) : ExtGL :=
  let d := adj a
  let ninv := (norm a)⁻¹
  ⟨d.c0 * ninv, d.c1 * ninv, d.c2 * ninv⟩

theorem mul_comm (a b : ExtGL) : mul a b = mul b a := by
  cases a; cases b
  simp only [mul, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem mul_assoc (a b c : ExtGL) : mul (mul a b) c = mul a (mul b c) := by
  cases a; cases b; cases c
  simp only [mul, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem one_mul (a : ExtGL) : mul one a = a := by
  cases a
  simp only [mul, one, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem mul_one (a : ExtGL) : mul a one = a := by
  rw [mul_comm, one_mul]

theorem mul_add (a b c : ExtGL) : mul a (add b c) = add (mul a b) (mul a c) := by
  cases a; cases b; cases c
  simp only [mul, add, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Algebraic adjugate identity: `a * adj(a) = (norm(a), 0, 0)` in `GLF[X]/(X^3 - X - 1)`. -/
theorem mul_adj (a : ExtGL) : mul a (adj a) = ⟨norm a, 0, 0⟩ := by
  cases a
  simp only [mul, adj, norm, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- Whenever `norm a ≠ 0`, `a * inv(a) = 1` in `GLF[X] / (X^3 - X - 1)`. -/
theorem mul_inv_of_norm_ne_zero {a : ExtGL} (hn : norm a ≠ 0) :
    mul a (inv a) = one := by
  have hadj := mul_adj a
  have hc0 : a.c0 * (adj a).c0 + a.c1 * (adj a).c2 + a.c2 * (adj a).c1 = norm a :=
    (ExtGL.mk.inj hadj).1
  have hc1 : a.c0 * (adj a).c1 + a.c1 * (adj a).c0 + a.c1 * (adj a).c2 +
      a.c2 * (adj a).c1 + a.c2 * (adj a).c2 = 0 :=
    (ExtGL.mk.inj hadj).2.1
  have hc2 : a.c0 * (adj a).c2 + a.c2 * (adj a).c0 + a.c1 * (adj a).c1 +
      a.c2 * (adj a).c2 = 0 :=
    (ExtGL.mk.inj hadj).2.2
  simp only [mul, inv, one, ExtGL.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · have h1 : a.c0 * ((adj a).c0 * (norm a)⁻¹) + a.c1 * ((adj a).c2 * (norm a)⁻¹) +
        a.c2 * ((adj a).c1 * (norm a)⁻¹) =
        (a.c0 * (adj a).c0 + a.c1 * (adj a).c2 + a.c2 * (adj a).c1) * (norm a)⁻¹ := by ring
    rw [h1, hc0, mul_inv_cancel₀ hn]
  · have h2 : a.c0 * ((adj a).c1 * (norm a)⁻¹) + a.c1 * ((adj a).c0 * (norm a)⁻¹) +
        a.c1 * ((adj a).c2 * (norm a)⁻¹) + a.c2 * ((adj a).c1 * (norm a)⁻¹) +
        a.c2 * ((adj a).c2 * (norm a)⁻¹) =
        (a.c0 * (adj a).c1 + a.c1 * (adj a).c0 + a.c1 * (adj a).c2 +
          a.c2 * (adj a).c1 + a.c2 * (adj a).c2) * (norm a)⁻¹ := by ring
    rw [h2, hc1, zero_mul]
  · have h3 : a.c0 * ((adj a).c2 * (norm a)⁻¹) + a.c2 * ((adj a).c0 * (norm a)⁻¹) +
        a.c1 * ((adj a).c1 * (norm a)⁻¹) + a.c2 * ((adj a).c2 * (norm a)⁻¹) =
        (a.c0 * (adj a).c2 + a.c2 * (adj a).c0 + a.c1 * (adj a).c1 +
          a.c2 * (adj a).c2) * (norm a)⁻¹ := by ring
    rw [h3, hc2, zero_mul]

/-- Total inverse maps `0` to `0`. -/
theorem inv_zero : inv zero = zero := by
  simp [inv, norm, adj, zero]

end ExtGL

/-- Canonical Formal Aiur encoding of a Goldilocks base element `x : GLF` in any
ambient field `F` (`[NatCast F]`): `.field (x.val : F)`.
* Over native `GLF`: `(x.val : GLF) = x`, so `glVal GLF x = .field x`.
* Over `BN254 Fr` / `BLS12-381 Fr`: canonical residue `< glModulus` in `ZMod p`. -/
abbrev glVal (F : Type) [NatCast F] (x : GLF) : SourceValue F :=
  .field (x.val : F)

/-- Canonical Formal Aiur encoding of a cubic extension element `a : ExtGL` in any
ambient field `F`: `.tuple [glVal F a.c0, glVal F a.c1, glVal F a.c2]`. -/
abbrev egVal (F : Type) [NatCast F] (a : ExtGL) : SourceValue F :=
  .tuple [glVal F a.c0, glVal F a.c1, glVal F a.c2]

theorem glVal_native (x : GLF) : glVal GLF x = .field x := by
  simp [glVal]

theorem egVal_native (a : ExtGL) : egVal GLF a = .tuple [.field a.c0, .field a.c1, .field a.c2] := by
  simp [egVal, glVal_native]

/-- Injectivity of the canonical Goldilocks residue embedding `GLF → F`. -/
def GLInjective (F : Type) [NatCast F] : Prop :=
  ∀ a b : GLF, (a.val : F) = (b.val : F) → a = b

theorem glVal_inj {F : Type} [NatCast F] (hinj : GLInjective F) {a b : GLF}
    (h : glVal F a = glVal F b) : a = b :=
  hinj a b (Value.field.inj h)

theorem glInjective_goldilocks : GLInjective GLF := by
  intro a b h
  simpa [ZMod.natCast_zmod_val] using h

theorem glInjective_of_zmod (p : Nat) [Fact (Nat.Prime p)] (hp : glModulus ≤ p) :
    GLInjective (ZMod p) := by
  intro a b h
  have ha : a.val < p := lt_of_lt_of_le a.val_lt hp
  have hb : b.val < p := lt_of_lt_of_le b.val_lt hp
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  exact ZMod.val_injective glModulus hv

theorem glInjective_bn254 : GLInjective Aiur.Library.Field.BN254.F :=
  glInjective_of_zmod bn254Modulus (by unfold glModulus bn254Modulus Aiur.Library.U32.Goldilocks.modulus Aiur.Library.Field.BN254.modulus; norm_num)

theorem glInjective_bls12381 : GLInjective Aiur.Library.Field.BLS12381.F :=
  glInjective_of_zmod bls12381Modulus (by unfold glModulus bls12381Modulus Aiur.Library.U32.Goldilocks.modulus Aiur.Library.Field.BLS12381.modulus; norm_num)

/-! ### Emulated Goldilocks No-Wrap Bounds & Pure Modular Reduction Theorems -/

/-- Sufficient no-wrap bounds for `Aiur.Library.Field.Goldilocks.Emulated` over a prime
field `ZMod p`: both `(p_G - 1)^2 < p` and `(2^64 - 1) * p_G + (p_G - 1) < p`. -/
structure EmulatedGLBounds (p : Nat) [Fact (Nat.Prime p)] : Prop where
  product_lt : (glModulus - 1) ^ 2 < p
  reduction_lt : (2 ^ 64 - 1) * glModulus + (glModulus - 1) < p

/-- `BN254 Fr` satisfies `EmulatedGLBounds` via `CompressionIntrinsics.bn254_emulated_*_bound`. -/
theorem emulatedGLBounds_bn254 : EmulatedGLBounds bn254Modulus where
  product_lt := bn254_emulated_product_bound
  reduction_lt := bn254_emulated_reduction_bound

/-- `BLS12-381 Fr` satisfies `EmulatedGLBounds` via `CompressionIntrinsics.bls12381_emulated_*_bound`. -/
theorem emulatedGLBounds_bls12381 : EmulatedGLBounds bls12381Modulus where
  product_lt := bls12381_emulated_product_bound
  reduction_lt := bls12381_emulated_reduction_bound

section EmulatedBoundsFacts

variable {p : Nat} [Fact (Nat.Prime p)]

theorem EmulatedGLBounds.glModulus_lt (hb : EmulatedGLBounds p) : glModulus < p := by
  have h1 : glModulus ≤ (2 ^ 64 - 1) * glModulus + (glModulus - 1) := by
    unfold glModulus Aiur.Library.U32.Goldilocks.modulus; omega
  exact lt_of_le_of_lt h1 hb.reduction_lt

theorem EmulatedGLBounds.two_mul_glModulus_lt (hb : EmulatedGLBounds p) : 2 * glModulus < p := by
  have h1 : 2 * glModulus ≤ (2 ^ 64 - 1) * glModulus + (glModulus - 1) := by
    unfold glModulus Aiur.Library.U32.Goldilocks.modulus; omega
  exact lt_of_le_of_lt h1 hb.reduction_lt

theorem EmulatedGLBounds.lit1020_lt (hb : EmulatedGLBounds p) : 1020 < p := by
  have h := hb.glModulus_lt
  unfold glModulus Aiur.Library.U32.Goldilocks.modulus at h
  omega

theorem EmulatedGLBounds.glInjective (hb : EmulatedGLBounds p) : GLInjective (ZMod p) :=
  glInjective_of_zmod p (Nat.le_of_lt hb.glModulus_lt)

theorem EmulatedGLBounds.depth_characteristic (hb : EmulatedGLBounds p) :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : ZMod p) ≠ 0 := by
  intro n hpos hle
  have hgl := hb.glModulus_lt
  unfold glModulus Aiur.Library.U32.Goldilocks.modulus at hgl
  exact zmod_natCast_ne_zero hpos (by omega)

theorem EmulatedGLBounds.fieldCompatible64 (hb : EmulatedGLBounds p) :
    FieldCompatible64 (ZMod p) := by
  apply FieldCompatible64.of_charP (ZMod p) p
  have hgl := hb.glModulus_lt
  unfold glModulus Aiur.Library.U32.Goldilocks.modulus at hgl
  unfold fieldBound64
  omega

/-- Little-endian packing of 8 natural bytes into a 64-bit natural number. -/
def packBytes8 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 +
    1099511627776 * b5 + 281474976710656 * b6 + 72057594037927936 * b7

theorem packBytes8_lt {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    packBytes8 b0 b1 b2 b3 b4 b5 b6 b7 < 2 ^ 64 := by
  unfold packBytes8; omega

/-- Exact arithmetic soundness of `Goldilocks::gl_lt_p`: on 8 bytes `< 256`, the
branchless test `1 - hi_max * (1 - lo_zero) = 1` holds in `ZMod p` (`1020 < p`)
iff `packBytes8 b0..b7 < glModulus`. -/
theorem gl_lt_p_eq_one_iff (hp : 1020 < p) {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256) :
    let hiSum : ZMod p := (b4 : ZMod p) + b5 + b6 + b7 - 1020
    let loSum : ZMod p := (b0 : ZMod p) + b1 + b2 + b3
    let hiMax : ZMod p := if hiSum = 0 then 1 else 0
    let loZero : ZMod p := if loSum = 0 then 1 else 0
    ((1 : ZMod p) - hiMax * (1 - loZero) = 1) ↔
      packBytes8 b0 b1 b2 b3 b4 b5 b6 b7 < glModulus := by
  have hpPos : 0 < p := by omega
  have h1ne0 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hhi_iff : ((b4 : ZMod p) + b5 + b6 + b7 - 1020 = 0) ↔ b4 + b5 + b6 + b7 = 1020 := by
    rw [sub_eq_zero]
    have hcast : ((b4 : ZMod p) + b5 + b6 + b7) = (((b4 + b5 + b6 + b7 : Nat) : ZMod p)) := by
      push_cast; rfl
    have h1020 : (1020 : ZMod p) = ((1020 : Nat) : ZMod p) := by norm_num
    rw [hcast, h1020]
    have hlt1 : b4 + b5 + b6 + b7 < p := by omega
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hp] at hv
      exact hv
    · intro h; rw [h]
  have hlo_iff : ((b0 : ZMod p) + b1 + b2 + b3 = 0) ↔ b0 + b1 + b2 + b3 = 0 := by
    have hcast : ((b0 : ZMod p) + b1 + b2 + b3) = (((b0 + b1 + b2 + b3 : Nat) : ZMod p)) := by
      push_cast; rfl
    rw [hcast]
    have hlt : b0 + b1 + b2 + b3 < p := by omega
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
      exact hv
    · intro h; rw [h]; simp
  dsimp only
  simp only [hhi_iff, hlo_iff]
  by_cases hhi : b4 + b5 + b6 + b7 = 1020
  · by_cases hlo : b0 + b1 + b2 + b3 = 0
    · simp only [hhi, hlo, ↓reduceIte, sub_self, mul_zero, sub_zero, true_iff]
      unfold packBytes8 glModulus Aiur.Library.U32.Goldilocks.modulus; omega
    · simp only [hhi, hlo, ↓reduceIte, sub_zero, mul_one, sub_self, false_iff,
        (Ne.symm h1ne0)]
      unfold packBytes8 glModulus Aiur.Library.U32.Goldilocks.modulus; omega
  · simp only [hhi, ↓reduceIte, zero_mul, sub_zero, true_iff]
    unfold packBytes8 glModulus Aiur.Library.U32.Goldilocks.modulus; omega

/-- Soundness of emulated Goldilocks addition: no-wrap lift from `ZMod p` to `GLF`. -/
theorem emulated_gl_add_sound (hb : EmulatedGLBounds p)
    {na nb nr : Nat} (ha : na < glModulus) (hnb : nb < glModulus) (hr : nr < glModulus)
    {carry : ZMod p} (hbool : carry * (carry - 1) = 0)
    (hrel : (na : ZMod p) + (nb : ZMod p) = (nr : ZMod p) + carry * (glModulus : ZMod p)) :
    (nr : GLF) = (na : GLF) + (nb : GLF) := by
  have h2 := hb.two_mul_glModulus_lt
  have hcases : carry = 0 ∨ carry = 1 := by
    rcases mul_eq_zero.mp hbool with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hnat : ∃ c : Nat, c ≤ 1 ∧ na + nb = nr + c * glModulus := by
    rcases hcases with rfl | rfl
    · refine ⟨0, by omega, ?_⟩
      simp only [zero_mul, add_zero] at hrel ⊢
      have hcast : ((na + nb : Nat) : ZMod p) = (nr : ZMod p) := by push_cast; exact hrel
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
      exact hv
    · refine ⟨1, by omega, ?_⟩
      simp only [one_mul] at hrel ⊢
      have hcast : ((na + nb : Nat) : ZMod p) = ((nr + glModulus : Nat) : ZMod p) := by
        push_cast; exact hrel
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
      exact hv
  obtain ⟨c, _, hEq⟩ := hnat
  have hgl := congrArg (Nat.cast : Nat → GLF) hEq
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero] at hgl
  exact hgl.symm

/-- Soundness of emulated Goldilocks subtraction: no-wrap lift from `ZMod p` to `GLF`. -/
theorem emulated_gl_sub_sound (hb : EmulatedGLBounds p)
    {na nb nr : Nat} (ha : na < glModulus) (hnb : nb < glModulus) (hr : nr < glModulus)
    {borrow : ZMod p} (hbool : borrow * (borrow - 1) = 0)
    (hrel : (na : ZMod p) + borrow * (glModulus : ZMod p) = (nb : ZMod p) + (nr : ZMod p)) :
    (nr : GLF) = (na : GLF) - (nb : GLF) := by
  have h2 := hb.two_mul_glModulus_lt
  have hcases : borrow = 0 ∨ borrow = 1 := by
    rcases mul_eq_zero.mp hbool with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hnat : ∃ c : Nat, c ≤ 1 ∧ na + c * glModulus = nb + nr := by
    rcases hcases with rfl | rfl
    · refine ⟨0, by omega, ?_⟩
      simp only [zero_mul, add_zero] at hrel ⊢
      have hcast : (na : ZMod p) = ((nb + nr : Nat) : ZMod p) := by push_cast; exact hrel
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
      exact hv
    · refine ⟨1, by omega, ?_⟩
      simp only [one_mul] at hrel ⊢
      have hcast : ((na + glModulus : Nat) : ZMod p) = ((nb + nr : Nat) : ZMod p) := by
        push_cast; exact hrel
      have hv := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
      exact hv
  obtain ⟨c, _, hEq⟩ := hnat
  have hgl := congrArg (Nat.cast : Nat → GLF) hEq
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero] at hgl
  exact eq_sub_of_add_eq' hgl.symm

/-- Soundness of emulated Goldilocks multiplication: no-wrap Euclidean lift from
`ZMod p` to `GLF` using `product_lt` and `reduction_lt`. -/
theorem emulated_gl_mul_sound (hb : EmulatedGLBounds p)
    {na nb nq nr : Nat}
    (ha : na < glModulus) (hnb : nb < glModulus) (hq : nq < 2 ^ 64) (hr : nr < glModulus)
    (hrel : (na : ZMod p) * (nb : ZMod p) = (nq : ZMod p) * (glModulus : ZMod p) + (nr : ZMod p)) :
    (nr : GLF) = (na : GLF) * (nb : GLF) := by
  have hlhs_le : na * nb ≤ (glModulus - 1) ^ 2 := by
    have ha' : na ≤ glModulus - 1 := by omega
    have hb' : nb ≤ glModulus - 1 := by omega
    rw [sq]
    exact Nat.mul_le_mul ha' hb'
  have hlhs_lt : na * nb < p := lt_of_le_of_lt hlhs_le hb.product_lt
  have hrhs_le : nq * glModulus + nr ≤ (2 ^ 64 - 1) * glModulus + (glModulus - 1) :=
    Nat.add_le_add (Nat.mul_le_mul_right glModulus (by omega)) (by omega)
  have hrhs_lt : nq * glModulus + nr < p := lt_of_le_of_lt hrhs_le hb.reduction_lt
  have hcast : ((na * nb : Nat) : ZMod p) = ((nq * glModulus + nr : Nat) : ZMod p) := by
    push_cast; exact hrel
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hlhs_lt, ZMod.val_natCast_of_lt hrhs_lt] at hv
  have hgl := congrArg (Nat.cast : Nat → GLF) hv
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add] at hgl
  exact hgl.symm

/-- Soundness of emulated Goldilocks total inverse (`0 ↦ 0`, `a ≠ 0 ↦ a⁻¹`). -/
theorem emulated_gl_inv_sound (hb : EmulatedGLBounds p)
    {na ninv nprod : Nat}
    (ha : na < glModulus) (hinv : ninv < glModulus) (hprod : nprod < glModulus)
    (hmul : (nprod : GLF) = (na : GLF) * (ninv : GLF))
    (hrel1 : (nprod : ZMod p) = (1 : ZMod p) - (if (na : ZMod p) = 0 then 1 else 0))
    (hrel2 : (if (na : ZMod p) = 0 then (1 : ZMod p) else 0) * (ninv : ZMod p) = 0) :
    (ninv : GLF) = (na : GLF)⁻¹ := by
  have hpgl := hb.glModulus_lt
  have h1lt : 1 < p := lt_trans (by unfold glModulus Aiur.Library.U32.Goldilocks.modulus; omega) hpgl
  have hzero_iff : ((na : ZMod p) = 0) ↔ na = 0 := by
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt (lt_trans ha hpgl), ZMod.val_zero] at hv
      exact hv
    · intro h; subst h; simp
  by_cases ha0 : na = 0
  · subst ha0
    simp only [Nat.cast_zero, ↓reduceIte, one_mul] at hrel2
    have hv := congrArg ZMod.val hrel2
    rw [ZMod.val_natCast_of_lt (lt_trans hinv hpgl), ZMod.val_zero] at hv
    subst hv
    simp
  · have hneP : (na : ZMod p) ≠ 0 := fun h => ha0 (hzero_iff.mp h)
    simp only [hneP, ↓reduceIte, sub_zero] at hrel1
    have hv := congrArg ZMod.val hrel1
    rw [ZMod.val_natCast_of_lt (lt_trans hprod hpgl), ZMod.val_one] at hv
    have hprod1 : (nprod : GLF) = 1 := by rw [hv]; simp
    have hneGL : (na : GLF) ≠ 0 := by
      intro h0
      have hv0 := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv0
      exact ha0 hv0
    rw [hprod1] at hmul
    exact mul_left_cancel₀ hneGL (by rw [← hmul, mul_inv_cancel₀ hneGL])

end EmulatedBoundsFacts

end GoldilocksAlgebra

/-! ## Section 2: Unified `GoldilocksContracts` (Native `Goldilocks` & Emulated `Goldilocks.Emulated`) -/

section GoldilocksWorldContracts

variable {F : Type} [Field F] [DecidableEq F]

/-- Typed variant of `Gadgets.WorldHasFn`: records both parameter names AND core parameter
types enforced by `SourceFunction.prepare`. -/
def WorldHasTypedFn (world : World F) (name : String) (params : List (String × Aiur.Ty))
    (body : Aiur.Generic.Expr F) : Prop :=
  ∀ args types locals expr,
    world.prepare name args = .ok (types, locals, expr) →
    types = [] ∧
    args.map Value.type = params.map Prod.snd ∧
    locals = (params.map Prod.fst).zip args ∧
    expr = body

omit [Field F] [DecidableEq F] in
theorem WorldHasTypedFn.toWorldHasFn {world : World F} {name : String}
    {params : List (String × Aiur.Ty)} {body : Aiur.Generic.Expr F}
    (h : WorldHasTypedFn world name params body) :
    WorldHasFn world name (params.map Prod.fst) body := by
  intro args types locals expr hprep
  obtain ⟨rfl, hty, rfl, rfl⟩ := h args types locals expr hprep
  have hlen : args.length = (params.map Prod.fst).length := by
    have := congrArg List.length hty
    simpa using this
  exact ⟨rfl, hlen, rfl, rfl⟩

/-- Executable check that `s` binds monomorphic function `name` with exact typed
parameters `rawParams` and elaborated body `body`. -/
def checkTypedFn {F : Type} [DecidableEq F] (s : Generic.Source F) (name : String)
    (rawParams : List (String × Generic.Ty)) (body : Aiur.Generic.Expr F) : Bool :=
  match s.program.findFunction? name with
  | some f => f.typeParams.isEmpty && (f.params == rawParams) && (f.body == body)
  | none => false

omit [Field F] in
/-- Construct `WorldHasTypedFn` directly from `checkTypedFn`, normalizing `rawParams` to core types. -/
theorem worldHasTypedFn_of_check (s : Generic.Source F) (name : String)
    (rawParams : List (String × Generic.Ty)) (body : Aiur.Generic.Expr F)
    {coreParams : List (String × Aiur.Ty)}
    (hnoDollar : name.toList.head? ≠ some '$')
    (h : checkTypedFn s name rawParams body = true)
    (hCore : rawParams.map (fun (n, t) => (n, (t.subst []).toCore)) = coreParams :=
      by simp [Generic.Ty.subst, Generic.Ty.toCore, List.replicate]) :
    WorldHasTypedFn s.world name coreParams body := by
  subst hCore
  unfold checkTypedFn at h
  cases hf : s.program.findFunction? name with
  | none => rw [hf] at h; simp at h
  | some f =>
    rw [hf] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    obtain ⟨⟨htp, hparams⟩, hbody⟩ := h
    have hsym : Instance.ofSymbol name = .ok ⟨name, []⟩ := by
      unfold Instance.ofSymbol
      cases hl : name.toList with
      | nil => rfl
      | cons c cs =>
        rw [hl] at hnoDollar
        have hc : c ≠ '$' := by simpa using hnoDollar
        simp [hc]
    have hsf : s.program.sourceFunction? name =
        some { types := [],
               params := rawParams.map fun (n, t) => (n, (t.subst []).toCore),
               body := body } := by
      unfold Generic.Program.sourceFunction?
      rw [hsym]
      simp [Except.toOption, hf, Generic.arguments, htp, hparams, hbody,
        pure, Except.pure, bind, Except.bind]
    intro args types locals expr hprep
    simp only [Generic.Source.world, sourceWorld, hsf, SourceFunction.prepare] at hprep
    split at hprep
    · next hcond =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at hprep
      obtain ⟨rfl, rfl, rfl⟩ := hprep
      exact ⟨rfl, hcond.1.symm, rfl, rfl⟩
    · simp at hprep

/-- Inversion of `EvalFn` on a control-free typed function: yields both core argument
types and `EvalExpr` on the body. -/
theorem evalFn_noControl_typed_inv {world : World F} {name : String}
    {params : List (String × Aiur.Ty)} {body : Aiur.Generic.Expr F}
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hfn : WorldHasTypedFn world name params body) (hnc : hasNoControl body = true)
    (ev : EvalFn world name args h r h') :
    args.map Value.type = params.map Prod.snd ∧
    EvalExpr world [] ((params.map Prod.fst).zip args) body h r h' := by
  cases ev with
  | intro prep b =>
    obtain ⟨rfl, hty, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact ⟨hty, b⟩
  | returned prep b =>
    obtain ⟨rfl, _, rfl, rfl⟩ := hfn _ _ _ _ prep
    exact False.elim (no_evalExit_of_noControl hnc b)

omit [Field F] [DecidableEq F] in
private theorem value_field_of_type {v : SourceValue F} (ht : v.type = .field) :
    ∃ x : F, v = .field x := by
  cases v with
  | field x => exact ⟨x, rfl⟩
  | tuple _ | ptr _ _ | construct _ _ _ => simp [Value.type] at ht

omit [Field F] [DecidableEq F] in
private theorem value_array3_of_type {v : SourceValue F}
    (ht : v.type = .tuple [.field, .field, .field]) :
    ∃ x0 x1 x2 : F, v = .tuple [.field x0, .field x1, .field x2] := by
  cases v with
  | tuple xs =>
    rcases xs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩⟩ <;> simp at ht
    obtain ⟨x0, rfl⟩ := value_field_of_type ht.1
    obtain ⟨x1, rfl⟩ := value_field_of_type ht.2.1
    obtain ⟨x2, rfl⟩ := value_field_of_type ht.2.2
    exact ⟨x0, x1, x2, rfl⟩
  | field _ | ptr _ _ | construct _ _ _ => simp [Value.type] at ht

omit [Field F] [DecidableEq F] in
private theorem value_array8_of_type {v : SourceValue F}
    (ht : v.type = .tuple (List.replicate 8 .field)) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 : F,
      v = .tuple [.field x0, .field x1, .field x2, .field x3,
                  .field x4, .field x5, .field x6, .field x7] := by
  cases v with
  | tuple xs =>
    rcases xs with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | ⟨v4, _ | ⟨v5, _ | ⟨v6, _ | ⟨v7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [List.replicate] at ht
    obtain ⟨x0, rfl⟩ := value_field_of_type ht.1
    obtain ⟨x1, rfl⟩ := value_field_of_type ht.2.1
    obtain ⟨x2, rfl⟩ := value_field_of_type ht.2.2.1
    obtain ⟨x3, rfl⟩ := value_field_of_type ht.2.2.2.1
    obtain ⟨x4, rfl⟩ := value_field_of_type ht.2.2.2.2.1
    obtain ⟨x5, rfl⟩ := value_field_of_type ht.2.2.2.2.2.1
    obtain ⟨x6, rfl⟩ := value_field_of_type ht.2.2.2.2.2.2.1
    obtain ⟨x7, rfl⟩ := value_field_of_type ht.2.2.2.2.2.2.2
    exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩
  | field _ | ptr _ _ | construct _ _ _ => simp [Value.type] at ht

/-! ### Unified `GoldilocksBaseContracts` & `GoldilocksContracts` -/

/-- Operational `EvalFn` contracts for the 7 Goldilocks base-field operations,
parameterized by ambient field `F` via `glVal F`. -/
structure GoldilocksBaseContracts (world : World F) : Prop where
  gl_add : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::gl_add" [va, vb] h r h' →
    ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a + b) ∧ h' = h
  gl_sub : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::gl_sub" [va, vb] h r h' →
    ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a - b) ∧ h' = h
  gl_mul : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::gl_mul" [va, vb] h r h' →
    ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a * b) ∧ h' = h
  gl_neg : ∀ {va r h h'},
    EvalFn world "Goldilocks::gl_neg" [va] h r h' →
    ∃ a : GLF, va = glVal F a ∧ r = glVal F (-a) ∧ h' = h
  gl_inverse : ∀ {va r h h'},
    EvalFn world "Goldilocks::gl_inverse" [va] h r h' →
    ∃ a : GLF, va = glVal F a ∧ r = glVal F a⁻¹ ∧ h' = h
  gl_is_zero : ∀ {va r h h'},
    EvalFn world "Goldilocks::gl_is_zero" [va] h r h' →
    ∃ a : GLF, va = glVal F a ∧ r = .field (if a = 0 then (1 : F) else 0) ∧ h' = h
  gl_eq : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::gl_eq" [va, vb] h r h' →
    ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧
      r = .field (if a = b then (1 : F) else 0) ∧ h' = h

/-- Complete operational `EvalFn` contracts for all 11 `GoldilocksOp`s (7 base + 4
cubic extension ops), shared uniformly by native `Aiur.Library.Field.Goldilocks`
and emulated `Aiur.Library.Field.Goldilocks.Emulated`. -/
structure GoldilocksContracts (world : World F) : Prop extends GoldilocksBaseContracts world where
  eg_add : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::eg_add" [va, vb] h r h' →
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.add a b) ∧ h' = h
  eg_sub : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::eg_sub" [va, vb] h r h' →
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.sub a b) ∧ h' = h
  eg_mul : ∀ {va vb r h h'},
    EvalFn world "Goldilocks::eg_mul" [va, vb] h r h' →
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.mul a b) ∧ h' = h
  eg_inverse : ∀ {va r h h'},
    EvalFn world "Goldilocks::eg_inverse" [va] h r h' →
    ∃ a : ExtGL, va = egVal F a ∧ r = egVal F (ExtGL.inv a) ∧ h' = h

/-! ### Shared Cubic-Extension Bodies & Lifting from `GoldilocksBaseContracts` -/

private abbrev glCall (nm : String) (xs : List (Aiur.Generic.Expr F)) : Aiur.Generic.Expr F :=
  .call nm (some []) xs

/-- Exact elaborated body of `Goldilocks::eg_add(a, b)` (identical in native & emulated). -/
def egAddBody : Aiur.Generic.Expr F :=
  .array [
    glCall "Goldilocks::gl_add" [.index (.var "a") 0, .index (.var "b") 0],
    glCall "Goldilocks::gl_add" [.index (.var "a") 1, .index (.var "b") 1],
    glCall "Goldilocks::gl_add" [.index (.var "a") 2, .index (.var "b") 2]]

/-- Exact elaborated body of `Goldilocks::eg_sub(a, b)` (identical in native & emulated). -/
def egSubBody : Aiur.Generic.Expr F :=
  .array [
    glCall "Goldilocks::gl_sub" [.index (.var "a") 0, .index (.var "b") 0],
    glCall "Goldilocks::gl_sub" [.index (.var "a") 1, .index (.var "b") 1],
    glCall "Goldilocks::gl_sub" [.index (.var "a") 2, .index (.var "b") 2]]

/-- Exact elaborated body of `Goldilocks::eg_mul(a, b)` (identical in native & emulated). -/
def egMulBody : Aiur.Generic.Expr F :=
  .letValue (.bind "v0") (glCall "Goldilocks::gl_mul" [.index (.var "a") 0, .index (.var "b") 0]) <|
  .letValue (.bind "v1") (glCall "Goldilocks::gl_mul" [.index (.var "a") 1, .index (.var "b") 1]) <|
  .letValue (.bind "v2") (glCall "Goldilocks::gl_mul" [.index (.var "a") 2, .index (.var "b") 2]) <|
  .letValue (.bind "m01")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_sub"
        [glCall "Goldilocks::gl_mul"
          [glCall "Goldilocks::gl_add" [.index (.var "a") 0, .index (.var "a") 1],
           glCall "Goldilocks::gl_add" [.index (.var "b") 0, .index (.var "b") 1]],
         .var "v0"],
       .var "v1"]) <|
  .letValue (.bind "m02")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_sub"
        [glCall "Goldilocks::gl_mul"
          [glCall "Goldilocks::gl_add" [.index (.var "a") 0, .index (.var "a") 2],
           glCall "Goldilocks::gl_add" [.index (.var "b") 0, .index (.var "b") 2]],
         .var "v0"],
       .var "v2"]) <|
  .letValue (.bind "m12")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_sub"
        [glCall "Goldilocks::gl_mul"
          [glCall "Goldilocks::gl_add" [.index (.var "a") 1, .index (.var "a") 2],
           glCall "Goldilocks::gl_add" [.index (.var "b") 1, .index (.var "b") 2]],
         .var "v1"],
       .var "v2"]) <|
  .array [
    glCall "Goldilocks::gl_add" [.var "v0", .var "m12"],
    glCall "Goldilocks::gl_add" [glCall "Goldilocks::gl_add" [.var "m01", .var "m12"], .var "v2"],
    glCall "Goldilocks::gl_add" [glCall "Goldilocks::gl_add" [.var "m02", .var "v1"], .var "v2"]]

/-- Exact elaborated body of `Goldilocks::eg_inverse(a)` parameterized by the inverse
local binder name (`"ninv"` in native `Goldilocks`, `"inverse"` in `Goldilocks.Emulated`). -/
def egInverseBody (invVar : String) : Aiur.Generic.Expr F :=
  .letValue (.bind "s") (glCall "Goldilocks::gl_add" [.index (.var "a") 0, .index (.var "a") 2]) <|
  .letValue (.bind "d0")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_mul" [.var "s", .var "s"],
       glCall "Goldilocks::gl_mul"
        [.index (.var "a") 1,
         glCall "Goldilocks::gl_add" [.index (.var "a") 1, .index (.var "a") 2]]]) <|
  .letValue (.bind "d1")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_mul" [.index (.var "a") 2, .index (.var "a") 2],
       glCall "Goldilocks::gl_mul" [.index (.var "a") 0, .index (.var "a") 1]]) <|
  .letValue (.bind "d2")
    (glCall "Goldilocks::gl_sub"
      [glCall "Goldilocks::gl_mul" [.index (.var "a") 1, .index (.var "a") 1],
       glCall "Goldilocks::gl_mul" [.index (.var "a") 2, .var "s"]]) <|
  .letValue (.bind "norm")
    (glCall "Goldilocks::gl_add"
      [glCall "Goldilocks::gl_add"
        [glCall "Goldilocks::gl_mul" [.index (.var "a") 0, .var "d0"],
         glCall "Goldilocks::gl_mul" [.index (.var "a") 2, .var "d1"]],
       glCall "Goldilocks::gl_mul" [.index (.var "a") 1, .var "d2"]]) <|
  .letValue (.bind invVar) (glCall "Goldilocks::gl_inverse" [.var "norm"]) <|
  .array [
    glCall "Goldilocks::gl_mul" [.var "d0", .var invVar],
    glCall "Goldilocks::gl_mul" [.var "d1", .var invVar],
    glCall "Goldilocks::gl_mul" [.var "d2", .var invVar]]

private abbrev arr3CoreTy : Aiur.Ty := .tuple [.field, .field, .field]

private theorem evalExpr_idx_var_inv {world : World F} {locals : Environment F Nat}
    {nm : String} {i : Nat} {v r : SourceValue F} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.index (.var nm) i) h r h') :
    projectValue v i = .ok r ∧ h' = h := by
  obtain ⟨v', evv, hp⟩ := evalExpr_index_inv ev
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evv
  exact ⟨hp, rfl⟩

/-- Lift `GoldilocksBaseContracts` to `Goldilocks::eg_add`. -/
theorem eval_eg_add_of_base {world : World F} (base : GoldilocksBaseContracts world)
    (hfn : WorldHasTypedFn world "Goldilocks::eg_add" [("a", arr3CoreTy), ("b", arr3CoreTy)] egAddBody)
    {va vb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Goldilocks::eg_add" [va, vb] h r h') :
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.add a b) ∧ h' = h := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv hfn rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨xa0, xa1, xa2, rfl⟩ := value_array3_of_type hty.1
  obtain ⟨xb0, xb1, xb2, rfl⟩ := value_array3_of_type hty.2
  obtain ⟨r0, r1, r2, h1, h2, e0, e1, e2, rfl⟩ := evalExpr_array3_inv body
  obtain ⟨u0, v0, _, _, eu0, ev0, hc0⟩ := evalExpr_call2_inv e0
  obtain ⟨hp0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu0
  obtain ⟨hq0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev0
  injection hp0 with hp0; subst hp0; injection hq0 with hq0; subst hq0
  obtain ⟨a0, b0, ha0, hb0, rfl, rfl⟩ := base.gl_add hc0
  obtain ⟨u1, v1, _, _, eu1, ev1, hc1⟩ := evalExpr_call2_inv e1
  obtain ⟨hp1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu1
  obtain ⟨hq1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev1
  injection hp1 with hp1; subst hp1; injection hq1 with hq1; subst hq1
  obtain ⟨a1, b1, ha1, hb1, rfl, rfl⟩ := base.gl_add hc1
  obtain ⟨u2, v2, _, _, eu2, ev2, hc2⟩ := evalExpr_call2_inv e2
  obtain ⟨hp2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu2
  obtain ⟨hq2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev2
  injection hp2 with hp2; subst hp2; injection hq2 with hq2; subst hq2
  obtain ⟨a2, b2, ha2, hb2, rfl, rfl⟩ := base.gl_add hc2
  exact ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, by simp [egVal, ha0, ha1, ha2],
    by simp [egVal, hb0, hb1, hb2], rfl, rfl⟩

/-- Lift `GoldilocksBaseContracts` to `Goldilocks::eg_sub`. -/
theorem eval_eg_sub_of_base {world : World F} (base : GoldilocksBaseContracts world)
    (hfn : WorldHasTypedFn world "Goldilocks::eg_sub" [("a", arr3CoreTy), ("b", arr3CoreTy)] egSubBody)
    {va vb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Goldilocks::eg_sub" [va, vb] h r h') :
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.sub a b) ∧ h' = h := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv hfn rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨xa0, xa1, xa2, rfl⟩ := value_array3_of_type hty.1
  obtain ⟨xb0, xb1, xb2, rfl⟩ := value_array3_of_type hty.2
  obtain ⟨r0, r1, r2, h1, h2, e0, e1, e2, rfl⟩ := evalExpr_array3_inv body
  obtain ⟨u0, v0, _, _, eu0, ev0, hc0⟩ := evalExpr_call2_inv e0
  obtain ⟨hp0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu0
  obtain ⟨hq0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev0
  injection hp0 with hp0; subst hp0; injection hq0 with hq0; subst hq0
  obtain ⟨a0, b0, ha0, hb0, rfl, rfl⟩ := base.gl_sub hc0
  obtain ⟨u1, v1, _, _, eu1, ev1, hc1⟩ := evalExpr_call2_inv e1
  obtain ⟨hp1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu1
  obtain ⟨hq1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev1
  injection hp1 with hp1; subst hp1; injection hq1 with hq1; subst hq1
  obtain ⟨a1, b1, ha1, hb1, rfl, rfl⟩ := base.gl_sub hc1
  obtain ⟨u2, v2, _, _, eu2, ev2, hc2⟩ := evalExpr_call2_inv e2
  obtain ⟨hp2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eu2
  obtain ⟨hq2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ev2
  injection hp2 with hp2; subst hp2; injection hq2 with hq2; subst hq2
  obtain ⟨a2, b2, ha2, hb2, rfl, rfl⟩ := base.gl_sub hc2
  exact ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩, by simp [egVal, ha0, ha1, ha2],
    by simp [egVal, hb0, hb1, hb2], rfl, rfl⟩

/-- Helper lemma inverting the Karatsuba cross-term
`gl_sub(gl_sub(gl_mul(gl_add(a[i], a[j]), gl_add(b[i], b[j])), vi), vj)`. -/
private theorem eval_karatsuba_cross {world : World F}
    (hinj : GLInjective F) (base : GoldilocksBaseContracts world)
    {locals : Environment F Nat} {a b : ExtGL} {i j : Nat} {ai aj bi bj : GLF}
    {viName vjName : String} {viVal vjVal : GLF} {r : SourceValue F} {h h' : Heap F}
    (ha : locals.find? (·.1 == "a") = some ("a", egVal F a))
    (hb : locals.find? (·.1 == "b") = some ("b", egVal F b))
    (hvi : locals.find? (·.1 == viName) = some (viName, glVal F viVal))
    (hvj : locals.find? (·.1 == vjName) = some (vjName, glVal F vjVal))
    (hai : projectValue (egVal F a) i = .ok (glVal F ai))
    (haj : projectValue (egVal F a) j = .ok (glVal F aj))
    (hbi : projectValue (egVal F b) i = .ok (glVal F bi))
    (hbj : projectValue (egVal F b) j = .ok (glVal F bj))
    (ev : EvalExpr world [] locals
      (glCall "Goldilocks::gl_sub"
        [glCall "Goldilocks::gl_sub"
          [glCall "Goldilocks::gl_mul"
            [glCall "Goldilocks::gl_add" [.index (.var "a") i, .index (.var "a") j],
             glCall "Goldilocks::gl_add" [.index (.var "b") i, .index (.var "b") j]],
           .var viName],
         .var vjName]) h r h') :
    r = glVal F (((ai + aj) * (bi + bj) - viVal) - vjVal) ∧ h' = h := by
  obtain ⟨_, _, _, _, eSub1, eVj, hcSub2⟩ := evalExpr_call2_inv ev
  obtain ⟨_, _, _, _, eMul, eVi, hcSub1⟩ := evalExpr_call2_inv eSub1
  obtain ⟨_, _, _, _, eAddA, eAddB, hcMul⟩ := evalExpr_call2_inv eMul
  obtain ⟨_, _, _, _, eAi, eAj, hcAddA⟩ := evalExpr_call2_inv eAddA
  obtain ⟨hpAi, rfl⟩ := evalExpr_idx_var_inv ha eAi
  obtain ⟨hpAj, rfl⟩ := evalExpr_idx_var_inv ha eAj
  rw [hai, Except.ok.injEq] at hpAi; subst hpAi
  rw [haj, Except.ok.injEq] at hpAj; subst hpAj
  obtain ⟨ai', aj', hai', haj', rfl, rfl⟩ := base.gl_add hcAddA
  have h1 := glVal_inj hinj hai'; subst h1
  have h2 := glVal_inj hinj haj'; subst h2
  obtain ⟨_, _, _, _, eBi, eBj, hcAddB⟩ := evalExpr_call2_inv eAddB
  obtain ⟨hpBi, rfl⟩ := evalExpr_idx_var_inv hb eBi
  obtain ⟨hpBj, rfl⟩ := evalExpr_idx_var_inv hb eBj
  rw [hbi, Except.ok.injEq] at hpBi; subst hpBi
  rw [hbj, Except.ok.injEq] at hpBj; subst hpBj
  obtain ⟨bi', bj', hbi', hbj', rfl, rfl⟩ := base.gl_add hcAddB
  have h3 := glVal_inj hinj hbi'; subst h3
  have h4 := glVal_inj hinj hbj'; subst h4
  obtain ⟨ma, mb, hma, hmb, rfl, rfl⟩ := base.gl_mul hcMul
  have h5 := glVal_inj hinj hma; subst h5
  have h6 := glVal_inj hinj hmb; subst h6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hvi eVi
  obtain ⟨sa, sb, hsa, hsb, rfl, rfl⟩ := base.gl_sub hcSub1
  have h7 := glVal_inj hinj hsa; subst h7
  have h8 := glVal_inj hinj hsb; subst h8
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hvj eVj
  obtain ⟨ta, tb, hta, htb, rfl, rfl⟩ := base.gl_sub hcSub2
  have h9 := glVal_inj hinj hta; subst h9
  have h10 := glVal_inj hinj htb; subst h10
  exact ⟨rfl, rfl⟩

/-- Lift `GoldilocksBaseContracts` + `GLInjective F` to `Goldilocks::eg_mul`
(Karatsuba multiplication = `ExtGL.mul` in `GLF[X]/(X^3 - X - 1)`). -/
theorem eval_eg_mul_of_base {world : World F}
    (hinj : GLInjective F) (base : GoldilocksBaseContracts world)
    (hfn : WorldHasTypedFn world "Goldilocks::eg_mul" [("a", arr3CoreTy), ("b", arr3CoreTy)] egMulBody)
    {va vb r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Goldilocks::eg_mul" [va, vb] h r h') :
    ∃ a b : ExtGL, va = egVal F a ∧ vb = egVal F b ∧ r = egVal F (ExtGL.mul a b) ∧ h' = h := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv hfn rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨xa0, xa1, xa2, rfl⟩ := value_array3_of_type hty.1
  obtain ⟨xb0, xb1, xb2, rfl⟩ := value_array3_of_type hty.2
  -- v0 = a[0] * b[0]
  obtain ⟨rv0, _, ev0, body1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, _, _, _, ea0, eb0, hc0⟩ := evalExpr_call2_inv ev0
  obtain ⟨hp0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea0
  obtain ⟨hq0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eb0
  injection hp0 with hp0; subst hp0; injection hq0 with hq0; subst hq0
  obtain ⟨a0, b0, ha0, hb0, rfl, rfl⟩ := base.gl_mul hc0
  -- v1 = a[1] * b[1]
  obtain ⟨rv1, _, ev1, body2⟩ := evalExpr_let_bind_inv body1
  obtain ⟨_, _, _, _, ea1, eb1, hc1⟩ := evalExpr_call2_inv ev1
  obtain ⟨hp1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea1
  obtain ⟨hq1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eb1
  injection hp1 with hp1; subst hp1; injection hq1 with hq1; subst hq1
  obtain ⟨a1, b1, ha1, hb1, rfl, rfl⟩ := base.gl_mul hc1
  -- v2 = a[2] * b[2]
  obtain ⟨rv2, _, ev2, body3⟩ := evalExpr_let_bind_inv body2
  obtain ⟨_, _, _, _, ea2, eb2, hc2⟩ := evalExpr_call2_inv ev2
  obtain ⟨hp2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea2
  obtain ⟨hq2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) eb2
  injection hp2 with hp2; subst hp2; injection hq2 with hq2; subst hq2
  obtain ⟨a2, b2, ha2, hb2, rfl, rfl⟩ := base.gl_mul hc2
  -- Rewrite input tuples as `egVal F a` and `egVal F b`
  have hxa0 : xa0 = (a0.val : F) := Value.field.inj ha0
  have hxa1 : xa1 = (a1.val : F) := Value.field.inj ha1
  have hxa2 : xa2 = (a2.val : F) := Value.field.inj ha2
  have hxb0 : xb0 = (b0.val : F) := Value.field.inj hb0
  have hxb1 : xb1 = (b1.val : F) := Value.field.inj hb1
  have hxb2 : xb2 = (b2.val : F) := Value.field.inj hb2
  subst hxa0 hxa1 hxa2 hxb0 hxb1 hxb2
  let a : ExtGL := ⟨a0, a1, a2⟩
  let b : ExtGL := ⟨b0, b1, b2⟩
  -- m01, m02, m12
  obtain ⟨rm01, _, em01, body4⟩ := evalExpr_let_bind_inv body3
  obtain ⟨rfl, rfl⟩ := eval_karatsuba_cross hinj base (a := a) (b := b)
    (i := 0) (j := 1) (ai := a0) (aj := a1) (bi := b0) (bj := b1)
    (viVal := a0 * b0) (vjVal := a1 * b1)
    (by simp [a, egVal]) (by simp [b, egVal]) (by simp) (by simp) rfl rfl rfl rfl em01
  obtain ⟨rm02, _, em02, body5⟩ := evalExpr_let_bind_inv body4
  obtain ⟨rfl, rfl⟩ := eval_karatsuba_cross hinj base (a := a) (b := b)
    (i := 0) (j := 2) (ai := a0) (aj := a2) (bi := b0) (bj := b2)
    (viVal := a0 * b0) (vjVal := a2 * b2)
    (by simp [a, egVal]) (by simp [b, egVal]) (by simp) (by simp) rfl rfl rfl rfl em02
  obtain ⟨rm12, _, em12, body6⟩ := evalExpr_let_bind_inv body5
  obtain ⟨rfl, rfl⟩ := eval_karatsuba_cross hinj base (a := a) (b := b)
    (i := 1) (j := 2) (ai := a1) (aj := a2) (bi := b1) (bj := b2)
    (viVal := a1 * b1) (vjVal := a2 * b2)
    (by simp [a, egVal]) (by simp [b, egVal]) (by simp) (by simp) rfl rfl rfl rfl em12
  -- Final 3-element output array
  obtain ⟨c0, c1, c2, _, _, ec0, ec1, ec2, rfl⟩ := evalExpr_array3_inv body6
  -- c0 = gl_add(v0, m12)
  obtain ⟨_, _, _, _, ev0', em12', hcc0⟩ := evalExpr_call2_inv ec0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev0'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) em12'
  obtain ⟨u0, w0, hu0, hw0, rfl, rfl⟩ := base.gl_add hcc0
  have hu0' := glVal_inj hinj hu0; subst hu0'
  have hw0' := glVal_inj hinj hw0; subst hw0'
  -- c1 = gl_add(gl_add(m01, m12), v2)
  obtain ⟨_, _, _, _, ec1a, ev2', hcc1⟩ := evalExpr_call2_inv ec1
  obtain ⟨_, _, _, _, em01', em12'', hcc1a⟩ := evalExpr_call2_inv ec1a
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) em01'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) em12''
  obtain ⟨u1a, w1a, hu1a, hw1a, rfl, rfl⟩ := base.gl_add hcc1a
  have hu1a' := glVal_inj hinj hu1a; subst hu1a'
  have hw1a' := glVal_inj hinj hw1a; subst hw1a'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2'
  obtain ⟨u1, w1, hu1, hw1, rfl, rfl⟩ := base.gl_add hcc1
  have hu1' := glVal_inj hinj hu1; subst hu1'
  have hw1' := glVal_inj hinj hw1; subst hw1'
  -- c2 = gl_add(gl_add(m02, v1), v2)
  obtain ⟨_, _, _, _, ec2a, ev2'', hcc2⟩ := evalExpr_call2_inv ec2
  obtain ⟨_, _, _, _, em02', ev1', hcc2a⟩ := evalExpr_call2_inv ec2a
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) em02'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev1'
  obtain ⟨u2a, w2a, hu2a, hw2a, rfl, rfl⟩ := base.gl_add hcc2a
  have hu2a' := glVal_inj hinj hu2a; subst hu2a'
  have hw2a' := glVal_inj hinj hw2a; subst hw2a'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2''
  obtain ⟨u2, w2, hu2, hw2, rfl, rfl⟩ := base.gl_add hcc2
  have hu2' := glVal_inj hinj hu2; subst hu2'
  have hw2' := glVal_inj hinj hw2; subst hw2'
  refine ⟨a, b, rfl, rfl, ?_, rfl⟩
  rw [← ExtGL.karatsubaMul_eq_mul]
  rfl

/-- Lift `GoldilocksBaseContracts` + `GLInjective F` to `Goldilocks::eg_inverse`
(both native `"ninv"` and emulated `"inverse"`). -/
theorem eval_eg_inverse_of_base {world : World F}
    (hinj : GLInjective F) (base : GoldilocksBaseContracts world)
    {invVar : String}
    (hDistinct : invVar ≠ "d0" ∧ invVar ≠ "d1" ∧ invVar ≠ "d2")
    (hfn : WorldHasTypedFn world "Goldilocks::eg_inverse" [("a", arr3CoreTy)] (egInverseBody invVar))
    {va r : SourceValue F} {h h' : Heap F}
    (ev : EvalFn world "Goldilocks::eg_inverse" [va] h r h') :
    ∃ a : ExtGL, va = egVal F a ∧ r = egVal F (ExtGL.inv a) ∧ h' = h := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv hfn rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨x0, x1, x2, rfl⟩ := value_array3_of_type hty
  -- s = a[0] + a[2]
  obtain ⟨vs, _, evs, body1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, _, _, _, ea0, ea2, hcs⟩ := evalExpr_call2_inv evs
  obtain ⟨hp0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea0
  obtain ⟨hp2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea2
  injection hp0 with hp0; subst hp0; injection hp2 with hp2; subst hp2
  obtain ⟨a0, a2, ha0, ha2, rfl, rfl⟩ := base.gl_add hcs
  -- d0 = s * s - a[1] * (a[1] + a[2])
  obtain ⟨vd0, _, evd0, body2⟩ := evalExpr_let_bind_inv body1
  obtain ⟨_, _, _, _, eSS, eA1Add, hcd0⟩ := evalExpr_call2_inv evd0
  obtain ⟨_, _, _, _, es1, es2, hcSS⟩ := evalExpr_call2_inv eSS
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) es1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) es2
  obtain ⟨s1, s2, hs1, hs2, rfl, rfl⟩ := base.gl_mul hcSS
  have hs1' := glVal_inj hinj hs1; subst hs1'
  have hs2' := glVal_inj hinj hs2; subst hs2'
  obtain ⟨_, _, _, _, ea1, eA12, hcA1Mul⟩ := evalExpr_call2_inv eA1Add
  obtain ⟨hp1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea1
  injection hp1 with hp1; subst hp1
  obtain ⟨_, _, _, _, ea1', ea2', hcA12⟩ := evalExpr_call2_inv eA12
  obtain ⟨hp1', rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea1'
  obtain ⟨hp2', rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) ea2'
  injection hp1' with hp1'; subst hp1'; injection hp2' with hp2'; subst hp2'
  obtain ⟨a1, a2', ha1, ha2', rfl, rfl⟩ := base.gl_add hcA12
  have ha2'' := glVal_inj hinj (ha2.symm.trans ha2'); subst ha2''
  obtain ⟨a1', sum12, ha1', hsum12, rfl, rfl⟩ := base.gl_mul hcA1Mul
  have ha1'' := glVal_inj hinj (ha1.symm.trans ha1'); subst ha1''
  have hsum12' := glVal_inj hinj hsum12; subst hsum12'
  obtain ⟨d0l, d0r, hd0l, hd0r, rfl, rfl⟩ := base.gl_sub hcd0
  have hd0l' := glVal_inj hinj hd0l; subst hd0l'
  have hd0r' := glVal_inj hinj hd0r; subst hd0r'
  -- Rewrite x0, x1, x2 as canonical GLF values
  have hx0 : x0 = (a0.val : F) := Value.field.inj ha0
  have hx1 : x1 = (a1.val : F) := Value.field.inj ha1
  have hx2 : x2 = (a2.val : F) := Value.field.inj ha2
  subst hx0 hx1 hx2
  -- d1 = a[2] * a[2] - a[0] * a[1]
  obtain ⟨vd1, _, evd1, body3⟩ := evalExpr_let_bind_inv body2
  obtain ⟨_, _, _, _, eA22, eA01, hcd1⟩ := evalExpr_call2_inv evd1
  obtain ⟨_, _, _, _, e2a, e2b, hcA22⟩ := evalExpr_call2_inv eA22
  obtain ⟨p2a, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e2a
  obtain ⟨p2b, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e2b
  injection p2a with p2a; subst p2a; injection p2b with p2b; subst p2b
  obtain ⟨q2a, q2b, hq2a, hq2b, rfl, rfl⟩ := base.gl_mul hcA22
  have hq2a' := glVal_inj hinj hq2a; subst hq2a'
  have hq2b' := glVal_inj hinj hq2b; subst hq2b'
  obtain ⟨_, _, _, _, e0a, e1b, hcA01⟩ := evalExpr_call2_inv eA01
  obtain ⟨p0a, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e0a
  obtain ⟨p1b, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e1b
  injection p0a with p0a; subst p0a; injection p1b with p1b; subst p1b
  obtain ⟨q0a, q1b, hq0a, hq1b, rfl, rfl⟩ := base.gl_mul hcA01
  have hq0a' := glVal_inj hinj hq0a; subst hq0a'
  have hq1b' := glVal_inj hinj hq1b; subst hq1b'
  obtain ⟨d1l, d1r, hd1l, hd1r, rfl, rfl⟩ := base.gl_sub hcd1
  have hd1l' := glVal_inj hinj hd1l; subst hd1l'
  have hd1r' := glVal_inj hinj hd1r; subst hd1r'
  -- d2 = a[1] * a[1] - a[2] * s
  obtain ⟨vd2, _, evd2, body4⟩ := evalExpr_let_bind_inv body3
  obtain ⟨_, _, _, _, eA11, eA2S, hcd2⟩ := evalExpr_call2_inv evd2
  obtain ⟨_, _, _, _, e1a, e1b', hcA11⟩ := evalExpr_call2_inv eA11
  obtain ⟨p1a, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e1a
  obtain ⟨p1b', rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e1b'
  injection p1a with p1a; subst p1a; injection p1b' with p1b'; subst p1b'
  obtain ⟨q1a, q1b', hq1a, hq1b', rfl, rfl⟩ := base.gl_mul hcA11
  have hq1a' := glVal_inj hinj hq1a; subst hq1a'
  have hq1b'' := glVal_inj hinj hq1b'; subst hq1b''
  obtain ⟨_, _, _, _, e2s, ess, hcA2S⟩ := evalExpr_call2_inv eA2S
  obtain ⟨p2s, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e2s
  injection p2s with p2s; subst p2s
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ess
  obtain ⟨q2s, qss, hq2s, hqss, rfl, rfl⟩ := base.gl_mul hcA2S
  have hq2s' := glVal_inj hinj hq2s; subst hq2s'
  have hqss' := glVal_inj hinj hqss; subst hqss'
  obtain ⟨d2l, d2r, hd2l, hd2r, rfl, rfl⟩ := base.gl_sub hcd2
  have hd2l' := glVal_inj hinj hd2l; subst hd2l'
  have hd2r' := glVal_inj hinj hd2r; subst hd2r'
  -- norm = (a[0] * d0 + a[2] * d1) + a[1] * d2
  obtain ⟨vnorm, _, evnorm, body5⟩ := evalExpr_let_bind_inv body4
  obtain ⟨_, _, _, _, eN02, eN1, hcNorm⟩ := evalExpr_call2_inv evnorm
  obtain ⟨_, _, _, _, eN0, eN2, hcN02⟩ := evalExpr_call2_inv eN02
  obtain ⟨_, _, _, _, en0a, en0d, hcN0⟩ := evalExpr_call2_inv eN0
  obtain ⟨pn0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) en0a
  injection pn0 with pn0; subst pn0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) en0d
  obtain ⟨u0a, u0d, hu0a, hu0d, rfl, rfl⟩ := base.gl_mul hcN0
  have hu0a' := glVal_inj hinj hu0a; subst hu0a'
  have hu0d' := glVal_inj hinj hu0d; subst hu0d'
  obtain ⟨_, _, _, _, en2a, en2d, hcN2⟩ := evalExpr_call2_inv eN2
  obtain ⟨pn2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) en2a
  injection pn2 with pn2; subst pn2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) en2d
  obtain ⟨u2a, u2d, hu2a, hu2d, rfl, rfl⟩ := base.gl_mul hcN2
  have hu2a' := glVal_inj hinj hu2a; subst hu2a'
  have hu2d' := glVal_inj hinj hu2d; subst hu2d'
  obtain ⟨un0, un2, hun0, hun2, rfl, rfl⟩ := base.gl_add hcN02
  have hun0' := glVal_inj hinj hun0; subst hun0'
  have hun2' := glVal_inj hinj hun2; subst hun2'
  obtain ⟨_, _, _, _, en1a, en1d, hcN1⟩ := evalExpr_call2_inv eN1
  obtain ⟨pn1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) en1a
  injection pn1 with pn1; subst pn1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) en1d
  obtain ⟨u1a, u1d, hu1a, hu1d, rfl, rfl⟩ := base.gl_mul hcN1
  have hu1a' := glVal_inj hinj hu1a; subst hu1a'
  have hu1d' := glVal_inj hinj hu1d; subst hu1d'
  obtain ⟨un02, un1, hun02, hun1, rfl, rfl⟩ := base.gl_add hcNorm
  have hun02' := glVal_inj hinj hun02; subst hun02'
  have hun1' := glVal_inj hinj hun1; subst hun1'
  -- invVar = gl_inverse(norm)
  obtain ⟨vninv, _, evninv, body6⟩ := evalExpr_let_bind_inv body5
  obtain ⟨_, _, eNormVar, hcInv⟩ := evalExpr_call1_inv evninv
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eNormVar
  obtain ⟨normG, hnormG, rfl, rfl⟩ := base.gl_inverse hcInv
  have hnormG' := glVal_inj hinj hnormG; subst hnormG'
  -- Final [d0 * invVar, d1 * invVar, d2 * invVar]
  obtain ⟨r0, r1, r2, _, _, er0, er1, er2, rfl⟩ := evalExpr_array3_inv body6
  have hneq0 : (invVar == "d0") = false := beq_false_of_ne hDistinct.1
  have hneq1 : (invVar == "d1") = false := beq_false_of_ne hDistinct.2.1
  have hneq2 : (invVar == "d2") = false := beq_false_of_ne hDistinct.2.2
  obtain ⟨_, _, _, _, ed0, ei0, hcr0⟩ := evalExpr_call2_inv er0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp [hneq0]; rfl) ed0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ei0
  obtain ⟨w0a, w0b, hw0a, hw0b, rfl, rfl⟩ := base.gl_mul hcr0
  have hw0a' := glVal_inj hinj hw0a; subst hw0a'
  have hw0b' := glVal_inj hinj hw0b; subst hw0b'
  obtain ⟨_, _, _, _, ed1, ei1, hcr1⟩ := evalExpr_call2_inv er1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp [hneq1]; rfl) ed1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ei1
  obtain ⟨w1a, w1b, hw1a, hw1b, rfl, rfl⟩ := base.gl_mul hcr1
  have hw1a' := glVal_inj hinj hw1a; subst hw1a'
  have hw1b' := glVal_inj hinj hw1b; subst hw1b'
  obtain ⟨_, _, _, _, ed2, ei2, hcr2⟩ := evalExpr_call2_inv er2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp [hneq2]; rfl) ed2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ei2
  obtain ⟨w2a, w2b, hw2a, hw2b, rfl, rfl⟩ := base.gl_mul hcr2
  have hw2a' := glVal_inj hinj hw2a; subst hw2a'
  have hw2b' := glVal_inj hinj hw2b; subst hw2b'
  exact ⟨⟨a0, a1, a2⟩, rfl, rfl, rfl⟩

/-- Combine any `GoldilocksBaseContracts` with the 4 cubic-extension library functions
to obtain complete `GoldilocksContracts`. -/
theorem GoldilocksContracts.ofBaseAndExt {world : World F}
    (hinj : GLInjective F) (base : GoldilocksBaseContracts world)
    {invVar : String} (hDistinct : invVar ≠ "d0" ∧ invVar ≠ "d1" ∧ invVar ≠ "d2")
    (hAdd : WorldHasTypedFn world "Goldilocks::eg_add" [("a", arr3CoreTy), ("b", arr3CoreTy)] egAddBody)
    (hSub : WorldHasTypedFn world "Goldilocks::eg_sub" [("a", arr3CoreTy), ("b", arr3CoreTy)] egSubBody)
    (hMul : WorldHasTypedFn world "Goldilocks::eg_mul" [("a", arr3CoreTy), ("b", arr3CoreTy)] egMulBody)
    (hInv : WorldHasTypedFn world "Goldilocks::eg_inverse" [("a", arr3CoreTy)] (egInverseBody invVar)) :
    GoldilocksContracts world :=
  { toGoldilocksBaseContracts := base
    eg_add := eval_eg_add_of_base base hAdd
    eg_sub := eval_eg_sub_of_base base hSub
    eg_mul := eval_eg_mul_of_base hinj base hMul
    eg_inverse := eval_eg_inverse_of_base hinj base hDistinct hInv }

end GoldilocksWorldContracts

/-! ### Discharge 1: Native `Aiur.Library.Field.Goldilocks` (over `GLF`) -/

section NativeGoldilocks

/-- Elaborated bodies of the 7 native `Aiur.Library.Field.Goldilocks` base functions. -/
def nativeGlAddBody : Aiur.Generic.Expr GLF := .binary .add (.var "a") (.var "b")
def nativeGlSubBody : Aiur.Generic.Expr GLF := .binary .sub (.var "a") (.var "b")
def nativeGlNegBody : Aiur.Generic.Expr GLF := .binary .sub (.literal 0) (.var "a")
def nativeGlMulBody : Aiur.Generic.Expr GLF := .binary .mul (.var "a") (.var "b")
def nativeGlIsZeroBody : Aiur.Generic.Expr GLF := .call "Fields::is_zero" (some []) [.var "a"]
def nativeGlEqBody : Aiur.Generic.Expr GLF :=
  .call "Fields::is_zero" (some []) [.binary .sub (.var "a") (.var "b")]
def nativeGlInverseBody : Aiur.Generic.Expr GLF :=
  .letValue (.bind "iv") (.hint .field (.var "x") "goldilocks.inverse") <|
  .letValue (.bind "t") (.binary .sub (.binary .mul (.var "x") (.var "iv")) (.literal 1)) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := none, runtimeCheck := true })
      [.binary .mul (.var "x") (.var "t"), .literal 0]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := none, runtimeCheck := true })
      [.binary .mul (.var "iv") (.var "t"), .literal 0]) <|
  .var "iv"

/-- World hypothesis for native `Aiur.Library.Field.Goldilocks` over `GLF`. -/
structure GoldilocksNativeWorld (world : World GLF) : Prop where
  fieldsIsZero : FieldsIsZeroSpec world
  gl_add : WorldHasTypedFn world "Goldilocks::gl_add" [("a", .field), ("b", .field)] nativeGlAddBody
  gl_sub : WorldHasTypedFn world "Goldilocks::gl_sub" [("a", .field), ("b", .field)] nativeGlSubBody
  gl_neg : WorldHasTypedFn world "Goldilocks::gl_neg" [("a", .field)] nativeGlNegBody
  gl_mul : WorldHasTypedFn world "Goldilocks::gl_mul" [("a", .field), ("b", .field)] nativeGlMulBody
  gl_is_zero : WorldHasTypedFn world "Goldilocks::gl_is_zero" [("a", .field)] nativeGlIsZeroBody
  gl_eq : WorldHasTypedFn world "Goldilocks::gl_eq" [("a", .field), ("b", .field)] nativeGlEqBody
  gl_inverse : WorldHasTypedFn world "Goldilocks::gl_inverse" [("x", .field)] nativeGlInverseBody
  eg_add : WorldHasTypedFn world "Goldilocks::eg_add" [("a", arr3CoreTy), ("b", arr3CoreTy)] egAddBody
  eg_sub : WorldHasTypedFn world "Goldilocks::eg_sub" [("a", arr3CoreTy), ("b", arr3CoreTy)] egSubBody
  eg_mul : WorldHasTypedFn world "Goldilocks::eg_mul" [("a", arr3CoreTy), ("b", arr3CoreTy)] egMulBody
  eg_inverse : WorldHasTypedFn world "Goldilocks::eg_inverse" [("a", arr3CoreTy)] (egInverseBody "ninv")

/-- Executable checker verifying that `s` binds `Fields::is_zero` and all 11 native
`Aiur.Library.Field.Goldilocks` functions with exact typed signatures and bodies. -/
def checkGoldilocksNativeWorld (s : Generic.Source GLF) : Bool :=
  checkFieldsIsZero s &&
  checkTypedFn s "Goldilocks::gl_add" [("a", .field), ("b", .field)] nativeGlAddBody &&
  checkTypedFn s "Goldilocks::gl_sub" [("a", .field), ("b", .field)] nativeGlSubBody &&
  checkTypedFn s "Goldilocks::gl_neg" [("a", .field)] nativeGlNegBody &&
  checkTypedFn s "Goldilocks::gl_mul" [("a", .field), ("b", .field)] nativeGlMulBody &&
  checkTypedFn s "Goldilocks::gl_is_zero" [("a", .field)] nativeGlIsZeroBody &&
  checkTypedFn s "Goldilocks::gl_eq" [("a", .field), ("b", .field)] nativeGlEqBody &&
  checkTypedFn s "Goldilocks::gl_inverse" [("x", .field)] nativeGlInverseBody &&
  checkTypedFn s "Goldilocks::eg_add" [("a", .array .field 3), ("b", .array .field 3)] egAddBody &&
  checkTypedFn s "Goldilocks::eg_sub" [("a", .array .field 3), ("b", .array .field 3)] egSubBody &&
  checkTypedFn s "Goldilocks::eg_mul" [("a", .array .field 3), ("b", .array .field 3)] egMulBody &&
  checkTypedFn s "Goldilocks::eg_inverse" [("a", .array .field 3)] (egInverseBody "ninv")

theorem goldilocksNativeWorld_of_check {s : Generic.Source GLF}
    (h : checkGoldilocksNativeWorld s = true) : GoldilocksNativeWorld s.world := by
  simp only [checkGoldilocksNativeWorld, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hiz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact {
    fieldsIsZero := fieldsIsZeroSpec_of_check hiz
    gl_add := worldHasTypedFn_of_check s "Goldilocks::gl_add" [("a", .field), ("b", .field)] nativeGlAddBody (by decide) h1
    gl_sub := worldHasTypedFn_of_check s "Goldilocks::gl_sub" [("a", .field), ("b", .field)] nativeGlSubBody (by decide) h2
    gl_neg := worldHasTypedFn_of_check s "Goldilocks::gl_neg" [("a", .field)] nativeGlNegBody (by decide) h3
    gl_mul := worldHasTypedFn_of_check s "Goldilocks::gl_mul" [("a", .field), ("b", .field)] nativeGlMulBody (by decide) h4
    gl_is_zero := worldHasTypedFn_of_check s "Goldilocks::gl_is_zero" [("a", .field)] nativeGlIsZeroBody (by decide) h5
    gl_eq := worldHasTypedFn_of_check s "Goldilocks::gl_eq" [("a", .field), ("b", .field)] nativeGlEqBody (by decide) h6
    gl_inverse := worldHasTypedFn_of_check s "Goldilocks::gl_inverse" [("x", .field)] nativeGlInverseBody (by decide) h7
    eg_add := worldHasTypedFn_of_check s "Goldilocks::eg_add" [("a", .array .field 3), ("b", .array .field 3)] egAddBody (by decide) h8
    eg_sub := worldHasTypedFn_of_check s "Goldilocks::eg_sub" [("a", .array .field 3), ("b", .array .field 3)] egSubBody (by decide) h9
    eg_mul := worldHasTypedFn_of_check s "Goldilocks::eg_mul" [("a", .array .field 3), ("b", .array .field 3)] egMulBody (by decide) h10
    eg_inverse := worldHasTypedFn_of_check s "Goldilocks::eg_inverse" [("a", .array .field 3)] (egInverseBody "ninv") (by decide) h11
  }

/-- Soundness of native `GoldilocksBaseContracts` from `GoldilocksNativeWorld`. -/
theorem goldilocksBaseContracts_of_native {world : World GLF}
    (w : GoldilocksNativeWorld world) : GoldilocksBaseContracts world where
  gl_add := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_add rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty.1
    obtain ⟨b, rfl⟩ := value_field_of_type hty.2
    obtain ⟨_, _, _, ea, eb, hop⟩ := evalExpr_binary_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb
    simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
    exact ⟨a, b, (glVal_native a).symm, (glVal_native b).symm, (glVal_native _).symm, rfl⟩
  gl_sub := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_sub rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty.1
    obtain ⟨b, rfl⟩ := value_field_of_type hty.2
    obtain ⟨_, _, _, ea, eb, hop⟩ := evalExpr_binary_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb
    simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
    exact ⟨a, b, (glVal_native a).symm, (glVal_native b).symm, (glVal_native _).symm, rfl⟩
  gl_mul := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_mul rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty.1
    obtain ⟨b, rfl⟩ := value_field_of_type hty.2
    obtain ⟨_, _, _, ea, eb, hop⟩ := evalExpr_binary_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb
    simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
    exact ⟨a, b, (glVal_native a).symm, (glVal_native b).symm, (glVal_native _).symm, rfl⟩
  gl_neg := fun {va r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_neg rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty
    obtain ⟨_, _, _, e0, ea, hop⟩ := evalExpr_binary_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    simp only [evalBinOp, zero_sub, Except.ok.injEq] at hop; subst hop
    exact ⟨a, (glVal_native a).symm, (glVal_native _).symm, rfl⟩
  gl_inverse := fun {va r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_inverse rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨x, rfl⟩ := value_field_of_type hty
    obtain ⟨viv, _, ehint, body1⟩ := evalExpr_let_bind_inv body
    obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ek
    obtain ⟨vt, _, et, body2⟩ := evalExpr_let_bind_inv body1
    obtain ⟨_, _, _, emul, e1, hsub⟩ := evalExpr_binary_inv et
    obtain ⟨vx1, viv1, _, ex1, eiv1, hmul⟩ := evalExpr_binary_inv emul
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ex1
    obtain ⟨hviv, rfl⟩ := evalExpr_var_eq (by simp; rfl) eiv1
    rw [hviv] at hmul
    cases viv with
    | field iv =>
      simp only [evalBinOp, Except.ok.injEq] at hmul; subst hmul
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e1
      simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
      obtain ⟨_, _, eass1, body3⟩ := evalExpr_let_wildcard_inv body2
      obtain ⟨_, _, _, exmul, ez1, heq1, _⟩ := evalExpr_assertEq_inv eass1
      obtain ⟨_, _, _, ex2, et1, hmul1⟩ := evalExpr_binary_inv exmul
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ex2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) et1
      simp only [evalBinOp, Except.ok.injEq] at hmul1; subst hmul1
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ez1
      have hxt : x * (x * iv - 1) = 0 := Value.field.inj heq1
      obtain ⟨_, _, eass2, body4⟩ := evalExpr_let_wildcard_inv body3
      obtain ⟨_, _, _, eivmul, ez2, heq2, _⟩ := evalExpr_assertEq_inv eass2
      obtain ⟨_, _, _, eiv2, et2, hmul2⟩ := evalExpr_binary_inv eivmul
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eiv2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) et2
      simp only [evalBinOp, Except.ok.injEq] at hmul2; subst hmul2
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ez2
      have hivt : iv * (x * iv - 1) = 0 := Value.field.inj heq2
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body4
      have hiv_eq : iv = x⁻¹ := by
        by_cases hx : x = 0
        · subst hx
          simp only [zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero] at hivt
          simp [hivt]
        · rcases mul_eq_zero.mp hxt with h0 | h1
          · exact False.elim (hx h0)
          · have hxi : x * iv = 1 := sub_eq_zero.mp h1
            exact mul_left_cancel₀ hx (by rw [hxi, mul_inv_cancel₀ hx])
      exact ⟨x, (glVal_native x).symm, by rw [hiv_eq, glVal_native], rfl⟩
    | tuple _ | ptr _ _ | construct _ _ _ => simp [evalBinOp] at hmul
  gl_is_zero := fun {va r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_is_zero rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty
    obtain ⟨_, _, ea, hc⟩ := evalExpr_call1_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    obtain ⟨x, hx, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hc
    have hxa : a = x := Value.field.inj hx; subst hxa
    exact ⟨a, (glVal_native a).symm, rfl, rfl⟩
  gl_eq := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_eq rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨a, rfl⟩ := value_field_of_type hty.1
    obtain ⟨b, rfl⟩ := value_field_of_type hty.2
    obtain ⟨_, _, esub, hc⟩ := evalExpr_call1_inv body
    obtain ⟨_, _, _, ea, eb, hop⟩ := evalExpr_binary_inv esub
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb
    simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
    obtain ⟨x, hx, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hc
    have hxa : a - b = x := Value.field.inj hx; subst hxa
    have hiff : (a - b = 0) ↔ a = b := sub_eq_zero
    exact ⟨a, b, (glVal_native a).symm, (glVal_native b).symm, by simp [hiff], rfl⟩

/-- **Certified native Goldilocks contracts**: from `GoldilocksNativeWorld`, recover
full `GoldilocksContracts` over `GLF`. -/
theorem GoldilocksContracts.ofNativeWorld {world : World GLF}
    (w : GoldilocksNativeWorld world) : GoldilocksContracts world :=
  GoldilocksContracts.ofBaseAndExt glInjective_goldilocks
    (goldilocksBaseContracts_of_native w) (by decide)
    w.eg_add w.eg_sub w.eg_mul w.eg_inverse

/-- **Executable-check bridge for native Goldilocks**: `checkGoldilocksNativeWorld s = true`
directly yields `GoldilocksContracts s.world`. -/
theorem GoldilocksContracts.ofCheckNative {s : Generic.Source GLF}
    (h : checkGoldilocksNativeWorld s = true) : GoldilocksContracts s.world :=
  GoldilocksContracts.ofNativeWorld (goldilocksNativeWorld_of_check h)

end NativeGoldilocks

/-! ### Discharge 2: Emulated `Aiur.Library.Field.Goldilocks.Emulated` (`ZMod p` under `EmulatedGLBounds p`) -/

section EmulatedGoldilocks

variable {p : Nat} [Fact (Nat.Prime p)]

/-- Minimal `UInt8` contracts required by `Aiur.Library.Field.Goldilocks.Emulated`. -/
structure GoldilocksU8Contracts {F : Type} [Field F] [DecidableEq F] (world : World F) : Prop where
  u8_to_field : ∀ v h r h', EvalFn world "UInt8::to_field" [v] h r h' → r = v ∧ h' = h
  u8_from_fields : ∀ v1 v2 h r h',
    EvalFn world "UInt8::from_fields" [v1, v2] h r h' →
    r = .tuple [v1, v2] ∧ h' = h ∧
    ∃ a b : Nat, a < 256 ∧ b < 256 ∧ v1 = .field (a : F) ∧ v2 = .field (b : F)

/-- Construct `GoldilocksU8Contracts` directly from `Blake3Spec.Blake3LibraryWorld`. -/
theorem goldilocksU8Contracts_of_blake3 {F : Type} [Field F] [DecidableEq F]
    {world : World F} (lib : Blake3LibraryWorld world) : GoldilocksU8Contracts world where
  u8_to_field := fun _ _ _ _ ev => Blake3Spec.eval_u8_to_field lib ev
  u8_from_fields := (witnessByteContracts_of_blake3 lib).u8_from_fields

/-- Construct `GoldilocksU8Contracts` directly from `Gadgets.U8MapSpec` + `UInt8::to_field`
and `UInt8::from_fields` function checks (no Blake3 required). -/
theorem goldilocksU8Contracts_of_u8 {F : Type} [Field F] [DecidableEq F]
    {world : World F} (maps : Gadgets.U8MapSpec world)
    (hToField : WorldHasFn world "UInt8::to_field" ["byte"] (.var "byte"))
    (hFromFields : WorldHasFn world "UInt8::from_fields" ["a", "b"]
      (.letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
        (.tuple [.var "a", .var "b"]))) :
    GoldilocksU8Contracts world where
  u8_to_field := fun v h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv hToField rfl ev
    obtain ⟨hl, rfl⟩ := evalExpr_var_inv b
    simp at hl
    exact ⟨hl.symm, rfl⟩
  u8_from_fields := fun v1 v2 h r h' ev => by
    obtain ⟨_, b⟩ := evalFn_plain_inv hFromFields rfl ev
    obtain ⟨_, _, hcall, hret⟩ := evalExpr_let_wildcard_inv b
    obtain ⟨va, vb, _, _, eva, evb, hcal⟩ := evalExpr_call2_inv hcall
    obtain ⟨hla, rfl⟩ := evalExpr_var_inv eva
    obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evb
    simp at hla hlb; subst hla hlb
    obtain ⟨_, rfl, a, b', ha, hb, rfl, rfl⟩ := maps.range_pair _ _ _ _ _ hcal
    obtain ⟨va', vb', _, eva', evb', rfl⟩ := evalExpr_tuple2_inv hret
    obtain ⟨hla', rfl⟩ := evalExpr_var_inv eva'
    obtain ⟨hlb', rfl⟩ := evalExpr_var_inv evb'
    simp at hla' hlb'; subst hla' hlb'
    exact ⟨rfl, rfl, a, b', ha, hb, rfl, rfl⟩

private abbrev arr8CoreTy : Aiur.Ty := .tuple (List.replicate 8 .field)

/-- Elaborated bodies of `Aiur.Library.Field.Goldilocks.Emulated` functions over `ZMod p`. -/
def emulCheckedBytesBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue (.tuple [.bind "b0", .bind "b1"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 0, .index (.var "raw") 1]) <|
  .letValue (.tuple [.bind "b2", .bind "b3"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 2, .index (.var "raw") 3]) <|
  .letValue (.tuple [.bind "b4", .bind "b5"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 4, .index (.var "raw") 5]) <|
  .letValue (.tuple [.bind "b6", .bind "b7"])
    (.call "UInt8::from_fields" (some []) [.index (.var "raw") 6, .index (.var "raw") 7]) <|
  .array [.var "b0", .var "b1", .var "b2", .var "b3",
          .var "b4", .var "b5", .var "b6", .var "b7"]

def emulPackBytesBody : Aiur.Generic.Expr (ZMod p) :=
  let tf (i : Nat) : Aiur.Generic.Expr (ZMod p) :=
    .call "UInt8::to_field" (some []) [.index (.var "x") i]
  .binary .add
    (.binary .add
      (.binary .add
        (.binary .add
          (.binary .add
            (.binary .add
              (.binary .add
                (tf 0)
                (.binary .mul (.literal (256 : ZMod p)) (tf 1)))
              (.binary .mul (.literal (65536 : ZMod p)) (tf 2)))
            (.binary .mul (.literal (16777216 : ZMod p)) (tf 3)))
          (.binary .mul (.literal (4294967296 : ZMod p)) (tf 4)))
        (.binary .mul (.literal (1099511627776 : ZMod p)) (tf 5)))
      (.binary .mul (.literal (281474976710656 : ZMod p)) (tf 6)))
    (.binary .mul (.literal (72057594037927936 : ZMod p)) (tf 7))

def emulGlLtPBody : Aiur.Generic.Expr (ZMod p) :=
  let tf (i : Nat) : Aiur.Generic.Expr (ZMod p) :=
    .call "UInt8::to_field" (some []) [.index (.var "x") i]
  .letValue (.bind "hi_max")
    (.call "Fields::is_zero" (some [])
      [.binary .sub
        (.binary .add (.binary .add (.binary .add (tf 4) (tf 5)) (tf 6)) (tf 7))
        (.literal (1020 : ZMod p))]) <|
  .letValue (.bind "lo_zero")
    (.call "Fields::is_zero" (some [])
      [.binary .add (.binary .add (.binary .add (tf 0) (tf 1)) (tf 2)) (tf 3)]) <|
  .binary .sub (.literal (1 : ZMod p))
    (.binary .mul (.var "hi_max") (.binary .sub (.literal (1 : ZMod p)) (.var "lo_zero")))

def emulGlToBytesBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue (.bind "bytes")
    (.call "Goldilocks::checked_bytes" (some [])
      [.hint (.array .field 8) (.var "value") "bytes_le"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks bytes do not recompose", runtimeCheck := true })
      [.call "Goldilocks::pack_bytes" (some []) [.var "bytes"], .var "value"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "noncanonical Goldilocks value", runtimeCheck := true })
      [.call "Goldilocks::gl_lt_p" (some []) [.var "bytes"], .literal (1 : ZMod p)]) <|
  .var "bytes"

def emulGlAddBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "a"]) <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "b"]) <|
  .letValue (.tuple [.bind "result", .bind "carry"])
    (.hint (.tuple [.field, .field]) (.tuple [.var "a", .var "b"]) "goldilocks.emulated.add") <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "result"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks addition carry is not boolean", runtimeCheck := true })
      [.binary .mul (.var "carry") (.binary .sub (.var "carry") (.literal (1 : ZMod p))),
       .literal (0 : ZMod p)]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks addition relation", runtimeCheck := true })
      [.binary .add (.var "a") (.var "b"),
       .binary .add (.var "result")
         (.binary .mul (.var "carry") (.global "Goldilocks::MODULUS" (some .field)))]) <|
  .var "result"

def emulGlSubBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "a"]) <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "b"]) <|
  .letValue (.tuple [.bind "result", .bind "borrow"])
    (.hint (.tuple [.field, .field]) (.tuple [.var "a", .var "b"]) "goldilocks.emulated.sub") <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "result"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks subtraction borrow is not boolean", runtimeCheck := true })
      [.binary .mul (.var "borrow") (.binary .sub (.var "borrow") (.literal (1 : ZMod p))),
       .literal (0 : ZMod p)]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks subtraction relation", runtimeCheck := true })
      [.binary .add (.var "a")
         (.binary .mul (.var "borrow") (.global "Goldilocks::MODULUS" (some .field))),
       .binary .add (.var "b") (.var "result")]) <|
  .var "result"

def emulGlNegBody : Aiur.Generic.Expr (ZMod p) :=
  .call "Goldilocks::gl_sub" (some []) [.literal (0 : ZMod p), .var "a"]

def emulGlMulBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "a"]) <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "b"]) <|
  .letValue (.tuple [.bind "result", .bind "raw_quotient"])
    (.hint (.tuple [.field, .array .field 8]) (.tuple [.var "a", .var "b"]) "goldilocks.emulated.mul") <|
  .letValue (.bind "quotient")
    (.call "Goldilocks::pack_bytes" (some [])
      [.call "Goldilocks::checked_bytes" (some []) [.var "raw_quotient"]]) <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "result"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks multiplication relation", runtimeCheck := true })
      [.binary .mul (.var "a") (.var "b"),
       .binary .add
         (.binary .mul (.var "quotient") (.global "Goldilocks::MODULUS" (some .field)))
         (.var "result")]) <|
  .var "result"

def emulGlIsZeroBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "a"]) <|
  .call "Fields::is_zero" (some []) [.var "a"]

def emulGlEqBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "a"]) <|
  .letValue .wildcard (.call "Goldilocks::gl_to_bytes" (some []) [.var "b"]) <|
  .call "Fields::is_zero" (some []) [.binary .sub (.var "a") (.var "b")]

def emulGlInverseBody : Aiur.Generic.Expr (ZMod p) :=
  .letValue (.bind "inverse")
    (.hint .field (.var "a") "goldilocks.emulated.inverse") <|
  .letValue (.bind "product")
    (.call "Goldilocks::gl_mul" (some []) [.var "a", .var "inverse"]) <|
  .letValue (.bind "zero")
    (.call "Fields::is_zero" (some []) [.var "a"]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks inverse relation", runtimeCheck := true })
      [.var "product", .binary .sub (.literal (1 : ZMod p)) (.var "zero")]) <|
  .letValue .wildcard
    (.builtin (.assertEq { message := some "Goldilocks zero inverse", runtimeCheck := true })
      [.binary .mul (.var "zero") (.var "inverse"), .literal (0 : ZMod p)]) <|
  .var "inverse"

/-- World hypothesis for `Aiur.Library.Field.Goldilocks.Emulated` over `ZMod p`. -/
structure GoldilocksEmulatedWorld (world : World (ZMod p)) : Prop where
  u8 : GoldilocksU8Contracts world
  fieldsIsZero : FieldsIsZeroSpec world
  const_modulus : world.constant "Goldilocks::MODULUS" .field = .ok (.literal (glModulus : ZMod p))
  checked_bytes : WorldHasTypedFn world "Goldilocks::checked_bytes" [("raw", arr8CoreTy)] emulCheckedBytesBody
  pack_bytes : WorldHasTypedFn world "Goldilocks::pack_bytes" [("x", arr8CoreTy)] emulPackBytesBody
  gl_lt_p : WorldHasTypedFn world "Goldilocks::gl_lt_p" [("x", arr8CoreTy)] emulGlLtPBody
  gl_to_bytes : WorldHasTypedFn world "Goldilocks::gl_to_bytes" [("value", .field)] emulGlToBytesBody
  gl_add : WorldHasTypedFn world "Goldilocks::gl_add" [("a", .field), ("b", .field)] emulGlAddBody
  gl_sub : WorldHasTypedFn world "Goldilocks::gl_sub" [("a", .field), ("b", .field)] emulGlSubBody
  gl_neg : WorldHasTypedFn world "Goldilocks::gl_neg" [("a", .field)] emulGlNegBody
  gl_mul : WorldHasTypedFn world "Goldilocks::gl_mul" [("a", .field), ("b", .field)] emulGlMulBody
  gl_is_zero : WorldHasTypedFn world "Goldilocks::gl_is_zero" [("a", .field)] emulGlIsZeroBody
  gl_eq : WorldHasTypedFn world "Goldilocks::gl_eq" [("a", .field), ("b", .field)] emulGlEqBody
  gl_inverse : WorldHasTypedFn world "Goldilocks::gl_inverse" [("a", .field)] emulGlInverseBody
  eg_add : WorldHasTypedFn world "Goldilocks::eg_add" [("a", arr3CoreTy), ("b", arr3CoreTy)] egAddBody
  eg_sub : WorldHasTypedFn world "Goldilocks::eg_sub" [("a", arr3CoreTy), ("b", arr3CoreTy)] egSubBody
  eg_mul : WorldHasTypedFn world "Goldilocks::eg_mul" [("a", arr3CoreTy), ("b", arr3CoreTy)] egMulBody
  eg_inverse : WorldHasTypedFn world "Goldilocks::eg_inverse" [("a", arr3CoreTy)] (egInverseBody "inverse")

/-- Executable checker verifying `Goldilocks::MODULUS`, `Fields::is_zero`, and all 15
`Aiur.Library.Field.Goldilocks.Emulated` functions on `Generic.Source (ZMod p)`. -/
def checkGoldilocksEmulatedFunctions (s : Generic.Source (ZMod p)) : Bool :=
  let chkMod : Bool :=
    match elaborateConst s.program "Goldilocks::MODULUS" .field with
    | .ok pat => pat == .literal (glModulus : ZMod p)
    | .error _ => false
  chkMod &&
  checkFieldsIsZero s &&
  checkTypedFn s "Goldilocks::checked_bytes" [("raw", .array .field 8)] emulCheckedBytesBody &&
  checkTypedFn s "Goldilocks::pack_bytes" [("x", .array .field 8)] emulPackBytesBody &&
  checkTypedFn s "Goldilocks::gl_lt_p" [("x", .array .field 8)] emulGlLtPBody &&
  checkTypedFn s "Goldilocks::gl_to_bytes" [("value", .field)] emulGlToBytesBody &&
  checkTypedFn s "Goldilocks::gl_add" [("a", .field), ("b", .field)] emulGlAddBody &&
  checkTypedFn s "Goldilocks::gl_sub" [("a", .field), ("b", .field)] emulGlSubBody &&
  checkTypedFn s "Goldilocks::gl_neg" [("a", .field)] emulGlNegBody &&
  checkTypedFn s "Goldilocks::gl_mul" [("a", .field), ("b", .field)] emulGlMulBody &&
  checkTypedFn s "Goldilocks::gl_is_zero" [("a", .field)] emulGlIsZeroBody &&
  checkTypedFn s "Goldilocks::gl_eq" [("a", .field), ("b", .field)] emulGlEqBody &&
  checkTypedFn s "Goldilocks::gl_inverse" [("a", .field)] emulGlInverseBody &&
  checkTypedFn s "Goldilocks::eg_add" [("a", .array .field 3), ("b", .array .field 3)] egAddBody &&
  checkTypedFn s "Goldilocks::eg_sub" [("a", .array .field 3), ("b", .array .field 3)] egSubBody &&
  checkTypedFn s "Goldilocks::eg_mul" [("a", .array .field 3), ("b", .array .field 3)] egMulBody &&
  checkTypedFn s "Goldilocks::eg_inverse" [("a", .array .field 3)] (egInverseBody "inverse")

/-- Full self-contained executable checker for emulated Goldilocks (including `UInt8` tables,
`UInt8::to_field`, `UInt8::from_fields`, `Fields::is_zero`, `Goldilocks::MODULUS`, and all 15
emulated functions). -/
def checkGoldilocksEmulatedWorld (s : Generic.Source (ZMod p)) : Bool :=
  World.checkTables s &&
  checkTypedFn s "UInt8::to_field" [("byte", .field)] (.var "byte") &&
  checkTypedFn s "UInt8::from_fields" [("a", .field), ("b", .field)]
    (.letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
      (.tuple [.var "a", .var "b"])) &&
  checkGoldilocksEmulatedFunctions s

theorem goldilocksEmulatedWorld_of_functions {s : Generic.Source (ZMod p)}
    (hu8 : GoldilocksU8Contracts s.world)
    (h : checkGoldilocksEmulatedFunctions s = true) :
    GoldilocksEmulatedWorld s.world := by
  simp only [checkGoldilocksEmulatedFunctions, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hMod, hiz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  have hConstMod : s.world.constant "Goldilocks::MODULUS" .field = .ok (.literal (glModulus : ZMod p)) := by
    cases hc : elaborateConst s.program "Goldilocks::MODULUS" .field with
    | error _ => rw [hc] at hMod; simp at hMod
    | ok pat =>
      rw [hc] at hMod
      simp only [beq_iff_eq] at hMod
      simp [Generic.Source.world, sourceWorld, hc, hMod, Except.mapError]
  exact {
    u8 := hu8
    fieldsIsZero := fieldsIsZeroSpec_of_check hiz
    const_modulus := hConstMod
    checked_bytes := worldHasTypedFn_of_check s "Goldilocks::checked_bytes" [("raw", .array .field 8)] emulCheckedBytesBody (by decide) h1
    pack_bytes := worldHasTypedFn_of_check s "Goldilocks::pack_bytes" [("x", .array .field 8)] emulPackBytesBody (by decide) h2
    gl_lt_p := worldHasTypedFn_of_check s "Goldilocks::gl_lt_p" [("x", .array .field 8)] emulGlLtPBody (by decide) h3
    gl_to_bytes := worldHasTypedFn_of_check s "Goldilocks::gl_to_bytes" [("value", .field)] emulGlToBytesBody (by decide) h4
    gl_add := worldHasTypedFn_of_check s "Goldilocks::gl_add" [("a", .field), ("b", .field)] emulGlAddBody (by decide) h5
    gl_sub := worldHasTypedFn_of_check s "Goldilocks::gl_sub" [("a", .field), ("b", .field)] emulGlSubBody (by decide) h6
    gl_neg := worldHasTypedFn_of_check s "Goldilocks::gl_neg" [("a", .field)] emulGlNegBody (by decide) h7
    gl_mul := worldHasTypedFn_of_check s "Goldilocks::gl_mul" [("a", .field), ("b", .field)] emulGlMulBody (by decide) h8
    gl_is_zero := worldHasTypedFn_of_check s "Goldilocks::gl_is_zero" [("a", .field)] emulGlIsZeroBody (by decide) h9
    gl_eq := worldHasTypedFn_of_check s "Goldilocks::gl_eq" [("a", .field), ("b", .field)] emulGlEqBody (by decide) h10
    gl_inverse := worldHasTypedFn_of_check s "Goldilocks::gl_inverse" [("a", .field)] emulGlInverseBody (by decide) h11
    eg_add := worldHasTypedFn_of_check s "Goldilocks::eg_add" [("a", .array .field 3), ("b", .array .field 3)] egAddBody (by decide) h12
    eg_sub := worldHasTypedFn_of_check s "Goldilocks::eg_sub" [("a", .array .field 3), ("b", .array .field 3)] egSubBody (by decide) h13
    eg_mul := worldHasTypedFn_of_check s "Goldilocks::eg_mul" [("a", .array .field 3), ("b", .array .field 3)] egMulBody (by decide) h14
    eg_inverse := worldHasTypedFn_of_check s "Goldilocks::eg_inverse" [("a", .array .field 3)] (egInverseBody "inverse") (by decide) h15
  }

theorem goldilocksEmulatedWorld_of_check {s : Generic.Source (ZMod p)}
    (h : checkGoldilocksEmulatedWorld s = true) :
    GoldilocksEmulatedWorld s.world := by
  simp only [checkGoldilocksEmulatedWorld, Bool.and_eq_true, and_assoc] at h
  obtain ⟨htables, htf, hff, hfns⟩ := h
  have hmaps := Gadgets.u8MapSpec_of_source s (World.u8TablesMatch_of_check htables)
  have hToF : WorldHasFn s.world "UInt8::to_field" ["byte"] (.var "byte") :=
    (worldHasTypedFn_of_check s "UInt8::to_field" [("byte", .field)] (.var "byte")
      (coreParams := [("byte", .field)]) (by decide) htf).toWorldHasFn
  have hFromF : WorldHasFn s.world "UInt8::from_fields" ["a", "b"]
      (.letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
        (.tuple [.var "a", .var "b"])) :=
    (worldHasTypedFn_of_check s "UInt8::from_fields" [("a", .field), ("b", .field)]
      (.letValue .wildcard (.call "UInt8::range_pair" (some []) [.var "a", .var "b"])
        (.tuple [.var "a", .var "b"]))
      (coreParams := [("a", .field), ("b", .field)]) (by decide) hff).toWorldHasFn
  have hu8 : GoldilocksU8Contracts s.world :=
    goldilocksU8Contracts_of_u8 hmaps hToF hFromF
  exact goldilocksEmulatedWorld_of_functions hu8 hfns

/-! #### Operational Proofs for Emulated Goldilocks Helpers & All 7 Base Ops -/

private theorem evalExpr_idx8_var_inv {world : World (ZMod p)} {locals : Environment (ZMod p) Nat}
    {nm : String} {i : Nat} {v r : SourceValue (ZMod p)}
    {h h' : Heap (ZMod p)}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals (.index (.var nm) i) h r h') :
    projectValue v i = .ok r ∧ h' = h :=
  evalExpr_idx_var_inv hlook ev

/-- `Goldilocks::checked_bytes` forces all 8 output elements to be valid bytes `< 256`. -/
theorem eval_emulated_checked_bytes {world : World (ZMod p)}
    (w : GoldilocksEmulatedWorld world) {raw r : SourceValue (ZMod p)} {h h' : Heap (ZMod p)}
    (ev : EvalFn world "Goldilocks::checked_bytes" [raw] h r h') :
    h' = h ∧ ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Nat,
      b0 < 256 ∧ b1 < 256 ∧ b2 < 256 ∧ b3 < 256 ∧
      b4 < 256 ∧ b5 < 256 ∧ b6 < 256 ∧ b7 < 256 ∧
      r = .tuple [.field (b0 : ZMod p), .field (b1 : ZMod p), .field (b2 : ZMod p),
                  .field (b3 : ZMod p), .field (b4 : ZMod p), .field (b5 : ZMod p),
                  .field (b6 : ZMod p), .field (b7 : ZMod p)] := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.checked_bytes rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := value_array8_of_type hty
  -- Pair (0, 1)
  obtain ⟨vb0, vb1, _, ec01, body1⟩ := evalExpr_let_tuple2_inv body
  obtain ⟨_, _, _, _, e0, e1, hc01⟩ := evalExpr_call2_inv ec01
  obtain ⟨hp0, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e0
  obtain ⟨hp1, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e1
  injection hp0 with hp0; subst hp0; injection hp1 with hp1; subst hp1
  obtain ⟨ht01, rfl, b0, b1, hb0, hb1, hx0, hx1⟩ := w.u8.u8_from_fields _ _ _ _ _ hc01
  have hfx0 := Value.field.inj hx0; have hfx1 := Value.field.inj hx1; subst hfx0 hfx1
  injection ht01 with hcons01; injection hcons01 with hEq0 hcons01'; injection hcons01' with hEq1 _
  subst hEq0 hEq1
  -- Pair (2, 3)
  obtain ⟨vb2, vb3, _, ec23, body2⟩ := evalExpr_let_tuple2_inv body1
  obtain ⟨_, _, _, _, e2, e3, hc23⟩ := evalExpr_call2_inv ec23
  obtain ⟨hp2, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e2
  obtain ⟨hp3, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e3
  injection hp2 with hp2; subst hp2; injection hp3 with hp3; subst hp3
  obtain ⟨ht23, rfl, b2, b3, hb2, hb3, hx2, hx3⟩ := w.u8.u8_from_fields _ _ _ _ _ hc23
  have hfx2 := Value.field.inj hx2; have hfx3 := Value.field.inj hx3; subst hfx2 hfx3
  injection ht23 with hcons23; injection hcons23 with hEq2 hcons23'; injection hcons23' with hEq3 _
  subst hEq2 hEq3
  -- Pair (4, 5)
  obtain ⟨vb4, vb5, _, ec45, body3⟩ := evalExpr_let_tuple2_inv body2
  obtain ⟨_, _, _, _, e4, e5, hc45⟩ := evalExpr_call2_inv ec45
  obtain ⟨hp4, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e4
  obtain ⟨hp5, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e5
  injection hp4 with hp4; subst hp4; injection hp5 with hp5; subst hp5
  obtain ⟨ht45, rfl, b4, b5, hb4, hb5, hx4, hx5⟩ := w.u8.u8_from_fields _ _ _ _ _ hc45
  have hfx4 := Value.field.inj hx4; have hfx5 := Value.field.inj hx5; subst hfx4 hfx5
  injection ht45 with hcons45; injection hcons45 with hEq4 hcons45'; injection hcons45' with hEq5 _
  subst hEq4 hEq5
  -- Pair (6, 7)
  obtain ⟨vb6, vb7, _, ec67, body4⟩ := evalExpr_let_tuple2_inv body3
  obtain ⟨_, _, _, _, e6, e7, hc67⟩ := evalExpr_call2_inv ec67
  obtain ⟨hp6, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e6
  obtain ⟨hp7, rfl⟩ := evalExpr_idx8_var_inv (by simp; rfl) e7
  injection hp6 with hp6; subst hp6; injection hp7 with hp7; subst hp7
  obtain ⟨ht67, rfl, b6, b7, hb6, hb7, hx6, hx7⟩ := w.u8.u8_from_fields _ _ _ _ _ hc67
  have hfx6 := Value.field.inj hx6; have hfx7 := Value.field.inj hx7; subst hfx6 hfx7
  injection ht67 with hcons67; injection hcons67 with hEq6 hcons67'; injection hcons67' with hEq7 _
  subst hEq6 hEq7
  -- Output array [b0..b7]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    ev0, ev1, ev2, ev3, ev4, ev5, ev6, ev7, rfl⟩ := evalExpr_array8_inv body4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev3
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev4
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev5
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev6
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ev7
  exact ⟨rfl, b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, rfl⟩

private theorem eval_u8_to_field_idx {world : World (ZMod p)}
    (w : GoldilocksEmulatedWorld world) {locals : Environment (ZMod p) Nat}
    {v0 : SourceValue (ZMod p)} {i : Nat} {v r : SourceValue (ZMod p)}
    {h h' : Heap (ZMod p)}
    (hlook : locals.find? (·.1 == "x") = some ("x", v0))
    (hproj : projectValue v0 i = .ok v)
    (ev : EvalExpr world [] locals (.call "UInt8::to_field" (some []) [.index (.var "x") i]) h r h') :
    r = v ∧ h' = h := by
  obtain ⟨_, _, eidx, hc⟩ := evalExpr_call1_inv ev
  obtain ⟨hp, rfl⟩ := evalExpr_idx8_var_inv hlook eidx
  rw [hproj, Except.ok.injEq] at hp; subst hp
  exact w.u8.u8_to_field _ _ _ _ hc

/-- `Goldilocks::pack_bytes` on 8 byte fields produces `((packBytes8 b0..b7 : Nat) : ZMod p)`. -/
theorem eval_emulated_pack_bytes {world : World (ZMod p)}
    (w : GoldilocksEmulatedWorld world) {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    {r : SourceValue (ZMod p)} {h h' : Heap (ZMod p)}
    (ev : EvalFn world "Goldilocks::pack_bytes"
      [.tuple [.field (b0 : ZMod p), .field (b1 : ZMod p), .field (b2 : ZMod p),
               .field (b3 : ZMod p), .field (b4 : ZMod p), .field (b5 : ZMod p),
               .field (b6 : ZMod p), .field (b7 : ZMod p)]] h r h') :
    r = .field ((packBytes8 b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : ZMod p) ∧ h' = h := by
  obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.pack_bytes rfl ev
  obtain ⟨_, _, _, e6, e7, ha7⟩ := evalExpr_binary_inv body
  obtain ⟨_, _, _, e5, e6m, ha6⟩ := evalExpr_binary_inv e6
  obtain ⟨_, _, _, e4, e5m, ha5⟩ := evalExpr_binary_inv e5
  obtain ⟨_, _, _, e3, e4m, ha4⟩ := evalExpr_binary_inv e4
  obtain ⟨_, _, _, e2, e3m, ha3⟩ := evalExpr_binary_inv e3
  obtain ⟨_, _, _, e1, e2m, ha2⟩ := evalExpr_binary_inv e2
  obtain ⟨_, _, _, e0, e1m, ha1⟩ := evalExpr_binary_inv e1
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl e0
  obtain ⟨_, _, _, l1, t1, hm1⟩ := evalExpr_binary_inv e1m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l1
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t1
  simp only [evalBinOp, Except.ok.injEq] at hm1; subst hm1; simp only [evalBinOp, Except.ok.injEq] at ha1; subst ha1
  obtain ⟨_, _, _, l2, t2, hm2⟩ := evalExpr_binary_inv e2m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l2
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t2
  simp only [evalBinOp, Except.ok.injEq] at hm2; subst hm2; simp only [evalBinOp, Except.ok.injEq] at ha2; subst ha2
  obtain ⟨_, _, _, l3, t3, hm3⟩ := evalExpr_binary_inv e3m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l3
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t3
  simp only [evalBinOp, Except.ok.injEq] at hm3; subst hm3; simp only [evalBinOp, Except.ok.injEq] at ha3; subst ha3
  obtain ⟨_, _, _, l4, t4, hm4⟩ := evalExpr_binary_inv e4m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l4
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t4
  simp only [evalBinOp, Except.ok.injEq] at hm4; subst hm4; simp only [evalBinOp, Except.ok.injEq] at ha4; subst ha4
  obtain ⟨_, _, _, l5, t5, hm5⟩ := evalExpr_binary_inv e5m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l5
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t5
  simp only [evalBinOp, Except.ok.injEq] at hm5; subst hm5; simp only [evalBinOp, Except.ok.injEq] at ha5; subst ha5
  obtain ⟨_, _, _, l6, t6, hm6⟩ := evalExpr_binary_inv e6m
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l6
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t6
  simp only [evalBinOp, Except.ok.injEq] at hm6; subst hm6; simp only [evalBinOp, Except.ok.injEq] at ha6; subst ha6
  obtain ⟨_, _, _, l7, t7, hm7⟩ := evalExpr_binary_inv e7
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv l7
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl t7
  simp only [evalBinOp, Except.ok.injEq] at hm7; subst hm7; simp only [evalBinOp, Except.ok.injEq] at ha7; subst ha7
  refine ⟨?_, rfl⟩
  unfold packBytes8
  push_cast
  rfl

/-- `Goldilocks::gl_lt_p` returning `.field 1` on 8 valid bytes `< 256` guarantees
`packBytes8 b0..b7 < glModulus` whenever `1020 < p`. -/
theorem eval_emulated_gl_lt_p {world : World (ZMod p)}
    (w : GoldilocksEmulatedWorld world) (hp : 1020 < p)
    {b0 b1 b2 b3 b4 b5 b6 b7 : Nat}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256)
    (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) (h7 : b7 < 256)
    {r : SourceValue (ZMod p)} {h h' : Heap (ZMod p)}
    (ev : EvalFn world "Goldilocks::gl_lt_p"
      [.tuple [.field (b0 : ZMod p), .field (b1 : ZMod p), .field (b2 : ZMod p),
               .field (b3 : ZMod p), .field (b4 : ZMod p), .field (b5 : ZMod p),
               .field (b6 : ZMod p), .field (b7 : ZMod p)]] h r h') :
    h' = h ∧ (r = .field 1 → packBytes8 b0 b1 b2 b3 b4 b5 b6 b7 < glModulus) := by
  obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.gl_lt_p rfl ev
  -- hi_max
  obtain ⟨vhi, _, ehi, body1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, _, ehisub, hchi⟩ := evalExpr_call1_inv ehi
  obtain ⟨_, _, _, ehisum, el1020, hsub⟩ := evalExpr_binary_inv ehisub
  obtain ⟨_, _, _, ehi6, et7, ha7⟩ := evalExpr_binary_inv ehisum
  obtain ⟨_, _, _, ehi5, et6, ha6⟩ := evalExpr_binary_inv ehi6
  obtain ⟨_, _, _, et4, et5, ha5⟩ := evalExpr_binary_inv ehi5
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et4
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et5
  simp only [evalBinOp, Except.ok.injEq] at ha5; subst ha5
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et6
  simp only [evalBinOp, Except.ok.injEq] at ha6; subst ha6
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et7
  simp only [evalBinOp, Except.ok.injEq] at ha7; subst ha7
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1020
  simp only [evalBinOp, Except.ok.injEq] at hsub; subst hsub
  obtain ⟨xhi, hxhi, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hchi
  have hxhi' : (b4 : ZMod p) + b5 + b6 + b7 - 1020 = xhi := Value.field.inj hxhi
  subst hxhi'
  -- lo_zero
  obtain ⟨vlo, _, elo, body2⟩ := evalExpr_let_bind_inv body1
  obtain ⟨_, _, elosum, hclo⟩ := evalExpr_call1_inv elo
  obtain ⟨_, _, _, elo2, et3, hb3⟩ := evalExpr_binary_inv elosum
  obtain ⟨_, _, _, elo1, et2, hb2⟩ := evalExpr_binary_inv elo2
  obtain ⟨_, _, _, et0, et1, hb1⟩ := evalExpr_binary_inv elo1
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et0
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et1
  simp only [evalBinOp, Except.ok.injEq] at hb1; subst hb1
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et2
  simp only [evalBinOp, Except.ok.injEq] at hb2; subst hb2
  obtain ⟨rfl, rfl⟩ := eval_u8_to_field_idx w (by simp; rfl) rfl et3
  simp only [evalBinOp, Except.ok.injEq] at hb3; subst hb3
  obtain ⟨xlo, hxlo, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hclo
  have hxlo' : (b0 : ZMod p) + b1 + b2 + b3 = xlo := Value.field.inj hxlo
  subst hxlo'
  -- 1 - hi_max * (1 - lo_zero)
  obtain ⟨_, _, _, el1, emul, hfin⟩ := evalExpr_binary_inv body2
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
  obtain ⟨_, _, _, ehiV, e1lo, hmul⟩ := evalExpr_binary_inv emul
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ehiV
  obtain ⟨_, _, _, el1', eloV, h1lo⟩ := evalExpr_binary_inv e1lo
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1'
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eloV
  simp only [evalBinOp, Except.ok.injEq] at h1lo; subst h1lo
  simp only [evalBinOp, Except.ok.injEq] at hmul; subst hmul
  simp only [evalBinOp, Except.ok.injEq] at hfin; subst hfin
  refine ⟨rfl, fun hr1 => ?_⟩
  have hEq : (1 : ZMod p) -
      (if (b4 : ZMod p) + b5 + b6 + b7 - 1020 = 0 then 1 else 0) *
        (1 - (if (b0 : ZMod p) + b1 + b2 + b3 = 0 then 1 else 0)) = 1 :=
    Value.field.inj hr1
  exact (gl_lt_p_eq_one_iff hp h0 h1 h2 h3 h4 h5 h6 h7).mp hEq

/-- `Goldilocks::gl_to_bytes` is a canonical Goldilocks range check: any derivation forces
`v = .field (n : ZMod p)` for some `n < glModulus`, leaving the heap unchanged. -/
theorem eval_emulated_gl_to_bytes {world : World (ZMod p)}
    (w : GoldilocksEmulatedWorld world) (hb : EmulatedGLBounds p)
    {v r : SourceValue (ZMod p)} {h h' : Heap (ZMod p)}
    (ev : EvalFn world "Goldilocks::gl_to_bytes" [v] h r h') :
    h' = h ∧ ∃ n : Nat, n < glModulus ∧ v = .field (n : ZMod p) := by
  obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_to_bytes rfl ev
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
  obtain ⟨x, rfl⟩ := value_field_of_type hty
  obtain ⟨vbytes, _, ecb, body1⟩ := evalExpr_let_bind_inv body
  obtain ⟨_, _, ehint, hccb⟩ := evalExpr_call1_inv ecb
  obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ek
  obtain ⟨rfl, b0, b1, b2, b3, b4, b5, b6, b7, h0, h1, h2, h3, h4, h5, h6, h7, rfl⟩ :=
    eval_emulated_checked_bytes w hccb
  -- assert_eq!(pack_bytes(bytes), value)
  obtain ⟨_, _, eass1, body2⟩ := evalExpr_let_wildcard_inv body1
  obtain ⟨_, _, _, epb, evalV, heq1, _⟩ := evalExpr_assertEq_inv eass1
  obtain ⟨_, _, ebv1, hcpb⟩ := evalExpr_call1_inv epb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv1
  obtain ⟨rfl, rfl⟩ := eval_emulated_pack_bytes w hcpb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) evalV
  -- assert_eq!(gl_lt_p(bytes), 1)
  obtain ⟨_, _, eass2, body3⟩ := evalExpr_let_wildcard_inv body2
  obtain ⟨_, _, _, eltp, el1, heq2, _⟩ := evalExpr_assertEq_inv eass2
  obtain ⟨_, _, ebv2, hcltp⟩ := evalExpr_call1_inv eltp
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv2
  obtain ⟨rfl, hlt⟩ := eval_emulated_gl_lt_p w hb.lit1020_lt h0 h1 h2 h3 h4 h5 h6 h7 hcltp
  obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body3
  exact ⟨rfl, packBytes8 b0 b1 b2 b3 b4 b5 b6 b7, hlt heq2, heq1.symm⟩

private theorem eval_emulated_gl_mul_raw {world : World (ZMod p)}
    (hb : EmulatedGLBounds p) (w : GoldilocksEmulatedWorld world)
    {va vb r : SourceValue (ZMod p)} {h h' : Heap (ZMod p)}
    (ev : EvalFn world "Goldilocks::gl_mul" [va, vb] h r h') :
    h' = h ∧ ∃ na nb nr : Nat,
      na < glModulus ∧ nb < glModulus ∧ nr < glModulus ∧
      va = .field (na : ZMod p) ∧ vb = .field (nb : ZMod p) ∧
      r = .field (nr : ZMod p) ∧ (nr : GLF) = (na : GLF) * (nb : GLF) := by
  obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.gl_mul rfl ev
  obtain ⟨_, _, ea, body1⟩ := evalExpr_let_wildcard_inv body
  obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
  obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hca
  obtain ⟨_, _, eb, body2⟩ := evalExpr_let_wildcard_inv body1
  obtain ⟨_, _, ebv, hcb⟩ := evalExpr_call1_inv eb
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv
  obtain ⟨rfl, nb, hnb, rfl⟩ := eval_emulated_gl_to_bytes w hb hcb
  obtain ⟨vres, vrawq, _, ehint, body3⟩ := evalExpr_let_tuple2_inv body2
  obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
  obtain ⟨_, _, _, eka, ekb, _⟩ := evalExpr_tuple2_inv ek
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eka
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ekb
  obtain ⟨vq, _, epq, body4⟩ := evalExpr_let_bind_inv body3
  obtain ⟨_, _, ecbq, hcpbq⟩ := evalExpr_call1_inv epq
  obtain ⟨_, _, erq, hccbq⟩ := evalExpr_call1_inv ecbq
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erq
  obtain ⟨rfl, q0, q1, q2, q3, q4, q5, q6, q7, hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7, rfl⟩ :=
    eval_emulated_checked_bytes w hccbq
  obtain ⟨rfl, rfl⟩ := eval_emulated_pack_bytes w hcpbq
  have hqLt : packBytes8 q0 q1 q2 q3 q4 q5 q6 q7 < 2 ^ 64 :=
    packBytes8_lt hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7
  obtain ⟨_, _, er, body5⟩ := evalExpr_let_wildcard_inv body4
  obtain ⟨_, _, erv, hcr⟩ := evalExpr_call1_inv er
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erv
  obtain ⟨rfl, nr, hnr, rfl⟩ := eval_emulated_gl_to_bytes w hb hcr
  obtain ⟨_, _, eass, body6⟩ := evalExpr_let_wildcard_inv body5
  obtain ⟨_, _, _, elhs, erhs, hrelEq, _⟩ := evalExpr_assertEq_inv eass
  obtain ⟨_, _, _, ela, elb, hlhs⟩ := evalExpr_binary_inv elhs
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ela
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) elb
  simp only [evalBinOp, Except.ok.injEq] at hlhs; subst hlhs
  obtain ⟨_, _, _, eqm, erRes, hrhs⟩ := evalExpr_binary_inv erhs
  obtain ⟨_, _, _, eqv, emod, hqm⟩ := evalExpr_binary_inv eqm
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eqv
  obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv w.const_modulus emod
  simp only [evalBinOp, Except.ok.injEq] at hqm; subst hqm
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erRes
  simp only [evalBinOp, Except.ok.injEq] at hrhs; subst hrhs
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body6
  exact ⟨rfl, na, nb, nr, hna, hnb, hnr, rfl, rfl, rfl,
    emulated_gl_mul_sound hb hna hnb hqLt hnr (Value.field.inj hrelEq)⟩

private theorem gl_cast_eq_glVal {n : Nat} (hn : n < glModulus) :
    (Value.field (n : ZMod p) : SourceValue (ZMod p)) = glVal (ZMod p) (n : GLF) := by
  simp [glVal, ZMod.val_natCast_of_lt hn]

/-- Soundness of emulated `GoldilocksBaseContracts` from `GoldilocksEmulatedWorld`
under `EmulatedGLBounds p` (covers both `BN254 Fr` and `BLS12-381 Fr`). -/
theorem goldilocksBaseContracts_of_emulated {world : World (ZMod p)}
    (hb : EmulatedGLBounds p) (w : GoldilocksEmulatedWorld world) :
    GoldilocksBaseContracts world where
  gl_add := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_add rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨_, _, ea, body1⟩ := evalExpr_let_wildcard_inv body
    obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hca
    obtain ⟨_, _, eb, body2⟩ := evalExpr_let_wildcard_inv body1
    obtain ⟨_, _, ebv, hcb⟩ := evalExpr_call1_inv eb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv
    obtain ⟨rfl, nb, hnb, rfl⟩ := eval_emulated_gl_to_bytes w hb hcb
    obtain ⟨vres, vcarry, _, ehint, body3⟩ := evalExpr_let_tuple2_inv body2
    obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
    obtain ⟨_, _, _, eka, ekb, _⟩ := evalExpr_tuple2_inv ek
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eka
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ekb
    obtain ⟨_, _, er, body4⟩ := evalExpr_let_wildcard_inv body3
    obtain ⟨_, _, erv, hcr⟩ := evalExpr_call1_inv er
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erv
    obtain ⟨rfl, nr, hnr, rfl⟩ := eval_emulated_gl_to_bytes w hb hcr
    obtain ⟨_, _, eass1, body5⟩ := evalExpr_let_wildcard_inv body4
    obtain ⟨_, _, _, ecmul, ez0, hboolEq, _⟩ := evalExpr_assertEq_inv eass1
    obtain ⟨vc1, _, _, ec1, ecsub, hcmul⟩ := evalExpr_binary_inv ecmul
    obtain ⟨hvc1, rfl⟩ := evalExpr_var_eq (by simp; rfl) ec1
    rw [hvc1] at hcmul
    obtain ⟨vc2, _, _, ec2, el1, hcsub⟩ := evalExpr_binary_inv ecsub
    obtain ⟨hvc2, rfl⟩ := evalExpr_var_eq (by simp; rfl) ec2
    rw [hvc2] at hcsub
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
    cases vcarry with
    | field carry =>
      simp only [evalBinOp, Except.ok.injEq] at hcsub; subst hcsub; simp only [evalBinOp, Except.ok.injEq] at hcmul; subst hcmul
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ez0
      have hbool : carry * (carry - 1) = 0 := Value.field.inj hboolEq
      obtain ⟨_, _, eass2, body6⟩ := evalExpr_let_wildcard_inv body5
      obtain ⟨_, _, _, elhs, erhs, hrelEq, _⟩ := evalExpr_assertEq_inv eass2
      obtain ⟨_, _, _, ela, elb, hlhs⟩ := evalExpr_binary_inv elhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ela
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) elb
      simp only [evalBinOp, Except.ok.injEq] at hlhs; subst hlhs
      obtain ⟨_, _, _, erres, ercmod, hrhs⟩ := evalExpr_binary_inv erhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erres
      obtain ⟨_, _, _, erc, emod, hcm⟩ := evalExpr_binary_inv ercmod
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erc
      obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv w.const_modulus emod
      simp only [evalBinOp, Except.ok.injEq] at hcm; subst hcm; simp only [evalBinOp, Except.ok.injEq] at hrhs; subst hrhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body6
      have hgl := emulated_gl_add_sound hb hna hnb hnr hbool (Value.field.inj hrelEq)
      exact ⟨(na : GLF), (nb : GLF), gl_cast_eq_glVal hna, gl_cast_eq_glVal hnb,
        by rw [gl_cast_eq_glVal hnr, hgl], rfl⟩
    | tuple _ | ptr _ _ | construct _ _ _ => simp [evalBinOp] at hcsub
  gl_sub := fun {va vb r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_sub rfl ev
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty
    obtain ⟨_, _, ea, body1⟩ := evalExpr_let_wildcard_inv body
    obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hca
    obtain ⟨_, _, eb, body2⟩ := evalExpr_let_wildcard_inv body1
    obtain ⟨_, _, ebv, hcb⟩ := evalExpr_call1_inv eb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv
    obtain ⟨rfl, nb, hnb, rfl⟩ := eval_emulated_gl_to_bytes w hb hcb
    obtain ⟨vres, vborr, _, ehint, body3⟩ := evalExpr_let_tuple2_inv body2
    obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
    obtain ⟨_, _, _, eka, ekb, _⟩ := evalExpr_tuple2_inv ek
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eka
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ekb
    obtain ⟨_, _, er, body4⟩ := evalExpr_let_wildcard_inv body3
    obtain ⟨_, _, erv, hcr⟩ := evalExpr_call1_inv er
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erv
    obtain ⟨rfl, nr, hnr, rfl⟩ := eval_emulated_gl_to_bytes w hb hcr
    obtain ⟨_, _, eass1, body5⟩ := evalExpr_let_wildcard_inv body4
    obtain ⟨_, _, _, ebmul, ez0, hboolEq, _⟩ := evalExpr_assertEq_inv eass1
    obtain ⟨vb1, _, _, eb1, ebsub, hbmul⟩ := evalExpr_binary_inv ebmul
    obtain ⟨hvb1, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb1
    rw [hvb1] at hbmul
    obtain ⟨vb2, _, _, eb2, el1, hbsub⟩ := evalExpr_binary_inv ebsub
    obtain ⟨hvb2, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb2
    rw [hvb2] at hbsub
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
    cases vborr with
    | field borrow =>
      simp only [evalBinOp, Except.ok.injEq] at hbsub; subst hbsub; simp only [evalBinOp, Except.ok.injEq] at hbmul; subst hbmul
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ez0
      have hbool : borrow * (borrow - 1) = 0 := Value.field.inj hboolEq
      obtain ⟨_, _, eass2, body6⟩ := evalExpr_let_wildcard_inv body5
      obtain ⟨_, _, _, elhs, erhs, hrelEq, _⟩ := evalExpr_assertEq_inv eass2
      obtain ⟨_, _, _, ela, elbm, hlhs⟩ := evalExpr_binary_inv elhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ela
      obtain ⟨_, _, _, elb1, emod, hbm⟩ := evalExpr_binary_inv elbm
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) elb1
      obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv w.const_modulus emod
      simp only [evalBinOp, Except.ok.injEq] at hbm; subst hbm; simp only [evalBinOp, Except.ok.injEq] at hlhs; subst hlhs
      obtain ⟨_, _, _, erB, erRes, hrhs⟩ := evalExpr_binary_inv erhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erB
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erRes
      simp only [evalBinOp, Except.ok.injEq] at hrhs; subst hrhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body6
      have hgl := emulated_gl_sub_sound hb hna hnb hnr hbool (Value.field.inj hrelEq)
      exact ⟨(na : GLF), (nb : GLF), gl_cast_eq_glVal hna, gl_cast_eq_glVal hnb,
        by rw [gl_cast_eq_glVal hnr, hgl], rfl⟩
    | tuple _ | ptr _ _ | construct _ _ _ => simp [evalBinOp] at hbsub
  gl_mul := fun {va vb r h h'} ev => by
    obtain ⟨rfl, na, nb, nr, hna, hnb, hnr, rfl, rfl, rfl, hgl⟩ :=
      eval_emulated_gl_mul_raw hb w ev
    exact ⟨(na : GLF), (nb : GLF), gl_cast_eq_glVal hna, gl_cast_eq_glVal hnb,
      by rw [gl_cast_eq_glVal hnr, hgl], rfl⟩
  gl_neg := fun {va r h h'} ev => by
    obtain ⟨hty, body⟩ := evalFn_noControl_typed_inv w.gl_neg rfl ev
    obtain ⟨_, _, _, _, e0, ea, hcsub⟩ := evalExpr_call2_inv body
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv e0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ea
    -- Reuse `gl_sub` directly on `[.field 0, va]`
    obtain ⟨hty', body'⟩ := evalFn_noControl_typed_inv w.gl_sub rfl hcsub
    obtain ⟨_, _, ea', body1⟩ := evalExpr_let_wildcard_inv body'
    obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea'
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, n0, hn0, h0Eq⟩ := eval_emulated_gl_to_bytes w hb hca
    have hn0z : n0 = 0 := by
      have hv := congrArg ZMod.val (Value.field.inj h0Eq)
      rw [ZMod.val_zero, ZMod.val_natCast_of_lt (lt_trans hn0 hb.glModulus_lt)] at hv
      exact hv.symm
    subst hn0z
    obtain ⟨_, _, eb, body2⟩ := evalExpr_let_wildcard_inv body1
    obtain ⟨_, _, ebv, hcb⟩ := evalExpr_call1_inv eb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv
    obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hcb
    obtain ⟨vres, vborr, _, ehint, body3⟩ := evalExpr_let_tuple2_inv body2
    obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
    obtain ⟨_, _, _, eka, ekb, _⟩ := evalExpr_tuple2_inv ek
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eka
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ekb
    obtain ⟨_, _, er, body4⟩ := evalExpr_let_wildcard_inv body3
    obtain ⟨_, _, erv, hcr⟩ := evalExpr_call1_inv er
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erv
    obtain ⟨rfl, nr, hnr, rfl⟩ := eval_emulated_gl_to_bytes w hb hcr
    obtain ⟨_, _, eass1, body5⟩ := evalExpr_let_wildcard_inv body4
    obtain ⟨_, _, _, ebmul, ez0, hboolEq, _⟩ := evalExpr_assertEq_inv eass1
    obtain ⟨vb1, _, _, eb1, ebsub, hbmul⟩ := evalExpr_binary_inv ebmul
    obtain ⟨hvb1, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb1
    rw [hvb1] at hbmul
    obtain ⟨vb2, _, _, eb2, el1, hbsub⟩ := evalExpr_binary_inv ebsub
    obtain ⟨hvb2, rfl⟩ := evalExpr_var_eq (by simp; rfl) eb2
    rw [hvb2] at hbsub
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
    cases vborr with
    | field borrow =>
      simp only [evalBinOp, Except.ok.injEq] at hbsub; subst hbsub; simp only [evalBinOp, Except.ok.injEq] at hbmul; subst hbmul
      obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ez0
      have hbool : borrow * (borrow - 1) = 0 := Value.field.inj hboolEq
      obtain ⟨_, _, eass2, body6⟩ := evalExpr_let_wildcard_inv body5
      obtain ⟨_, _, _, elhs, erhs, hrelEq, _⟩ := evalExpr_assertEq_inv eass2
      obtain ⟨_, _, _, ela, elbm, hlhs⟩ := evalExpr_binary_inv elhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ela
      obtain ⟨_, _, _, elb1, emod, hbm⟩ := evalExpr_binary_inv elbm
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) elb1
      obtain ⟨rfl, rfl⟩ := evalExpr_global_literal_inv w.const_modulus emod
      simp only [evalBinOp, Except.ok.injEq] at hbm; subst hbm; simp only [evalBinOp, Except.ok.injEq] at hlhs; subst hlhs
      obtain ⟨_, _, _, erB, erRes, hrhs⟩ := evalExpr_binary_inv erhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erB
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) erRes
      simp only [evalBinOp, Except.ok.injEq] at hrhs; subst hrhs
      obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body6
      have hgl := emulated_gl_sub_sound hb glModulus_pos hna hnr hbool
        (by simpa using Value.field.inj hrelEq)
      simp only [Nat.cast_zero, zero_sub] at hgl
      exact ⟨(na : GLF), gl_cast_eq_glVal hna, by rw [gl_cast_eq_glVal hnr, hgl], rfl⟩
    | tuple _ | ptr _ _ | construct _ _ _ => simp [evalBinOp] at hbsub
  gl_inverse := fun {va r h h'} ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.gl_inverse rfl ev
    obtain ⟨vinv, _, ehint, body1⟩ := evalExpr_let_bind_inv body
    obtain ⟨_, ek⟩ := evalExpr_hint_inv ehint
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ek
    obtain ⟨vprod, _, emul, body2⟩ := evalExpr_let_bind_inv body1
    obtain ⟨_, _, _, _, eav, einvv, hcmul⟩ := evalExpr_call2_inv emul
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) einvv
    obtain ⟨rfl, na, ninv, nprod, hna, hninv, hnprod, rfl, rfl, rfl, hglMul⟩ :=
      eval_emulated_gl_mul_raw hb w hcmul
    -- zero = Fields::is_zero(a)
    obtain ⟨vzero, _, eiz, body3⟩ := evalExpr_let_bind_inv body2
    obtain ⟨_, _, eav2, hciz⟩ := evalExpr_call1_inv eiz
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav2
    obtain ⟨xa, hxa, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hciz
    have hxa' : (na : ZMod p) = xa := Value.field.inj hxa; subst hxa'
    -- assert_eq!(product, 1 - zero)
    obtain ⟨_, _, eass1, body4⟩ := evalExpr_let_wildcard_inv body3
    obtain ⟨_, _, _, epv, e1z, hrel1Eq, _⟩ := evalExpr_assertEq_inv eass1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) epv
    obtain ⟨_, _, _, el1, ezv1, h1z⟩ := evalExpr_binary_inv e1z
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ezv1
    simp only [evalBinOp, Except.ok.injEq] at h1z; subst h1z
    -- assert_eq!(zero * inverse, 0)
    obtain ⟨_, _, eass2, body5⟩ := evalExpr_let_wildcard_inv body4
    obtain ⟨_, _, _, ezinv, el0, hrel2Eq, _⟩ := evalExpr_assertEq_inv eass2
    obtain ⟨_, _, _, ezv2, einvv2, hzinv⟩ := evalExpr_binary_inv ezinv
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ezv2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) einvv2
    simp only [evalBinOp, Except.ok.injEq] at hzinv; subst hzinv
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv el0
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) body5
    have hinvGL := emulated_gl_inv_sound hb hna hninv hnprod hglMul
      (Value.field.inj hrel1Eq) (Value.field.inj hrel2Eq)
    exact ⟨(na : GLF), gl_cast_eq_glVal hna, by rw [gl_cast_eq_glVal hninv, hinvGL], rfl⟩
  gl_is_zero := fun {va r h h'} ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.gl_is_zero rfl ev
    obtain ⟨_, _, ea, body1⟩ := evalExpr_let_wildcard_inv body
    obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hca
    obtain ⟨_, _, eav2, hciz⟩ := evalExpr_call1_inv body1
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav2
    obtain ⟨xa, hxa, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hciz
    have hxa' : (na : ZMod p) = xa := Value.field.inj hxa; subst hxa'
    have hiff : ((na : ZMod p) = 0) ↔ ((na : GLF) = 0) := by
      have hpgl := hb.glModulus_lt
      constructor
      · intro h0
        have hv := congrArg ZMod.val h0
        rw [ZMod.val_natCast_of_lt (lt_trans hna hpgl), ZMod.val_zero] at hv
        subst hv; simp
      · intro h0
        have hv := congrArg ZMod.val h0
        rw [ZMod.val_natCast_of_lt hna, ZMod.val_zero] at hv
        subst hv; simp
    exact ⟨(na : GLF), gl_cast_eq_glVal hna, by simp [hiff], rfl⟩
  gl_eq := fun {va vb r h h'} ev => by
    obtain ⟨_, body⟩ := evalFn_noControl_typed_inv w.gl_eq rfl ev
    obtain ⟨_, _, ea, body1⟩ := evalExpr_let_wildcard_inv body
    obtain ⟨_, _, eav, hca⟩ := evalExpr_call1_inv ea
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav
    obtain ⟨rfl, na, hna, rfl⟩ := eval_emulated_gl_to_bytes w hb hca
    obtain ⟨_, _, eb, body2⟩ := evalExpr_let_wildcard_inv body1
    obtain ⟨_, _, ebv, hcb⟩ := evalExpr_call1_inv eb
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv
    obtain ⟨rfl, nb, hnb, rfl⟩ := eval_emulated_gl_to_bytes w hb hcb
    obtain ⟨_, _, esub, hciz⟩ := evalExpr_call1_inv body2
    obtain ⟨_, _, _, eav2, ebv2, hop⟩ := evalExpr_binary_inv esub
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) eav2
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq (by simp; rfl) ebv2
    simp only [evalBinOp, Except.ok.injEq] at hop; subst hop
    obtain ⟨xd, hxd, rfl, rfl⟩ := w.fieldsIsZero.1 _ _ _ _ hciz
    have hxd' : (na : ZMod p) - (nb : ZMod p) = xd := Value.field.inj hxd; subst hxd'
    have hiff : ((na : ZMod p) - (nb : ZMod p) = 0) ↔ ((na : GLF) = (nb : GLF)) := by
      rw [sub_eq_zero]
      have hpgl := hb.glModulus_lt
      constructor
      · intro heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast_of_lt (lt_trans hna hpgl),
            ZMod.val_natCast_of_lt (lt_trans hnb hpgl)] at hv
        subst hv; rfl
      · intro heq
        have hv := congrArg ZMod.val heq
        rw [ZMod.val_natCast_of_lt hna, ZMod.val_natCast_of_lt hnb] at hv
        subst hv; rfl
    exact ⟨(na : GLF), (nb : GLF), gl_cast_eq_glVal hna, gl_cast_eq_glVal hnb, by simp [hiff], rfl⟩

/-- **Certified emulated Goldilocks contracts**: from `EmulatedGLBounds p` and
`GoldilocksEmulatedWorld`, recover full `GoldilocksContracts` over `ZMod p`. -/
theorem GoldilocksContracts.ofEmulatedWorld {world : World (ZMod p)}
    (hb : EmulatedGLBounds p) (w : GoldilocksEmulatedWorld world) :
    GoldilocksContracts world :=
  GoldilocksContracts.ofBaseAndExt hb.glInjective
    (goldilocksBaseContracts_of_emulated hb w) (by decide)
    w.eg_add w.eg_sub w.eg_mul w.eg_inverse

/-- **Executable-check bridge for emulated Goldilocks** over any prime `ZMod p`
satisfying `EmulatedGLBounds p`. -/
theorem GoldilocksContracts.ofCheckEmulated (hb : EmulatedGLBounds p)
    {s : Generic.Source (ZMod p)} (h : checkGoldilocksEmulatedWorld s = true) :
    GoldilocksContracts s.world :=
  GoldilocksContracts.ofEmulatedWorld hb (goldilocksEmulatedWorld_of_check h)

/-- **Certified emulated Goldilocks contracts over BN254 `Fr`** (discharging
`EmulatedGLBounds` via `bn254_emulated_product_bound` / `bn254_emulated_reduction_bound`). -/
theorem GoldilocksContracts.ofCheckBN254
    {s : Generic.Source Aiur.Library.Field.BN254.F}
    (h : checkGoldilocksEmulatedWorld s = true) :
    GoldilocksContracts s.world :=
  GoldilocksContracts.ofCheckEmulated emulatedGLBounds_bn254 h

/-- **Certified emulated Goldilocks contracts over BLS12-381 `Fr`** (discharging
`EmulatedGLBounds` via `bls12381_emulated_product_bound` / `bls12381_emulated_reduction_bound`). -/
theorem GoldilocksContracts.ofCheckBLS12381
    {s : Generic.Source Aiur.Library.Field.BLS12381.F}
    (h : checkGoldilocksEmulatedWorld s = true) :
    GoldilocksContracts s.world :=
  GoldilocksContracts.ofCheckEmulated emulatedGLBounds_bls12381 h

end EmulatedGoldilocks

/-! ## Section 3: Per-Op `CompressionOp` Backward Soundness (`field`, `goldilocks`, `blake3`, `witness`) -/

section PerOpSoundness

variable {F : Type} [Field F] [DecidableEq F]

/-! ### 3.1 Ambient Prime-Field Ops (`CompressionOp.field`, General `[Field F]` + `FieldLowerProof` Delegation) -/

private theorem evalExpr_vE_inv {world : World F} {locals : Environment F Nat}
    {nm : String} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F (vE nm)) h r h') :
    locals.find? (·.1 == nm) = some (nm, r) ∧ h' = h := by
  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
  exact evalExpr_var_inv ev

/-- Generic `[Field F] [DecidableEq F]` `EvalExpr` inversion for `fieldOpExpr op args`. -/
theorem evalExpr_fieldOpExpr_inv_field {world : World F} (hiz : FieldsIsZeroSpec world)
    {locals : Environment F Nat} {op : FieldOp} {args : List Expr} {e : Expr}
    (hop : fieldOpExpr op args = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (xs : List F) (res : F),
      EvalArgs world [] locals (args.map (qualifyExprF F)) h (xs.map .field) h' ∧
      op.eval xs = some res ∧
      r = .field res := by
  cases op <;> rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
    simp only [fieldOpExpr, Option.some.injEq, reduceCtorEq] at hop
  · -- add
    subst hop
    simp only [fieldAddE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨vx, vy, hm, evx, evy, hbin⟩ := evalExpr_binary_inv ev
    cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
    subst hbin
    exact ⟨[_, _], _ + _, .cons evx (.cons evy .nil), rfl, rfl⟩
  · -- sub
    subst hop
    simp only [fieldSubE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨vx, vy, hm, evx, evy, hbin⟩ := evalExpr_binary_inv ev
    cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
    subst hbin
    exact ⟨[_, _], _ - _, .cons evx (.cons evy .nil), rfl, rfl⟩
  · -- mul
    subst hop
    simp only [fieldMulE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨vx, vy, hm, evx, evy, hbin⟩ := evalExpr_binary_inv ev
    cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
    subst hbin
    exact ⟨[_, _], _ * _, .cons evx (.cons evy .nil), rfl, rfl⟩
  · -- neg
    subst hop
    simp only [fieldNegE, litE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev
    obtain ⟨v0, vx, _, ev0, evx, hbin⟩ := evalExpr_binary_inv ev
    obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
    cases vx <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
    subst hbin
    exact ⟨[_], 0 - _, .cons evx .nil, rfl, by simp⟩
  · -- inv
    subst hop
    simp only [fieldInvE, fieldInvVarE, letE, matchE, fieldIsZeroE, callE, vE, litE,
      qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, List.map, FieldLowerProof.qualifyName_fields_is_zero,
      Nat.cast_zero, Nat.cast_one] at ev
    obtain ⟨va, hm, eva, evb⟩ := evalExpr_let_bind_inv ev
    obtain ⟨viz, hm1, eviz, hbr⟩ := evalExpr_match_lit_wild_inv evb
    obtain ⟨vx, hm2, evv, hcal⟩ := evalExpr_call1_inv eviz
    obtain ⟨hlook, rfl⟩ := evalExpr_var_inv evv
    simp at hlook; subst hlook
    obtain ⟨x, rfl, rfl, rfl⟩ := hiz.1 _ hm2 viz hm1 hcal
    rcases hbr with ⟨h1, ev0⟩ | ⟨hne1, evdiv⟩
    · injection h1 with h1'
      by_cases hx : x = 0
      · subst hx
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
        exact ⟨[0], 0⁻¹, .cons eva .nil, rfl, by simp⟩
      · simp only [hx, ↓reduceIte] at h1'
        exact False.elim (zero_ne_one h1')
    · by_cases hx : x = 0
      · subst hx; simp only [↓reduceIte] at hne1; exact False.elim (hne1 rfl)
      · obtain ⟨v1, vx2, _, ev1, evv2, hbin⟩ := evalExpr_binary_inv evdiv
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
        obtain ⟨hl2, rfl⟩ := evalExpr_var_inv evv2
        simp at hl2; subst hl2
        simp only [evalBinOp, hx, ↓reduceIte, Except.ok.injEq] at hbin
        subst hbin
        exact ⟨[x], x⁻¹, .cons eva .nil, rfl, by simp [one_div]⟩
  · -- div
    subst hop
    simp only [fieldDivE, fieldDivVarsE, matchE, fieldIsZeroE, fieldMulE, callE, vE, litE,
      qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, List.map, FieldLowerProof.qualifyName_fields_is_zero,
      Nat.cast_zero, Nat.cast_one] at ev
    obtain ⟨va, vb, hm, evtup, evb⟩ := evalExpr_let_tuple2_inv ev
    obtain ⟨va', vb', hm1, eva, evb', htup⟩ := evalExpr_tuple2_inv evtup
    injection htup with hcons; injection hcons with h1 hcons2; injection hcons2 with h2 _
    subst h1; subst h2
    obtain ⟨viz, hm2, eviz, hbr⟩ := evalExpr_match_lit_wild_inv evb
    obtain ⟨vb2, hm3, evv, hcal⟩ := evalExpr_call1_inv eviz
    obtain ⟨hlb, rfl⟩ := evalExpr_var_inv evv
    simp at hlb; subst hlb
    obtain ⟨y, rfl, rfl, rfl⟩ := hiz.1 _ hm3 viz hm2 hcal
    rcases hbr with ⟨h1, ev0⟩ | ⟨hne1, evdiv⟩
    · injection h1 with h1'
      by_cases hy : y = 0
      · subst hy
        obtain ⟨v0, va2, _, evLit0, evva, hbin⟩ := evalExpr_binary_inv ev0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit0
        obtain ⟨hla, rfl⟩ := evalExpr_var_inv evva
        simp at hla; subst hla
        cases va <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
        subst hbin
        exact ⟨[_, 0], _ / 0, .cons eva (.cons evb' .nil), rfl, by simp⟩
      · simp only [hy, ↓reduceIte] at h1'
        exact False.elim (zero_ne_one h1')
    · by_cases hy : y = 0
      · subst hy; simp only [↓reduceIte] at hne1; exact False.elim (hne1 rfl)
      · obtain ⟨va2, vb3, _, evva, evvb, hbin⟩ := evalExpr_binary_inv evdiv
        obtain ⟨hla, rfl⟩ := evalExpr_var_inv evva
        obtain ⟨hlb2, rfl⟩ := evalExpr_var_inv evvb
        simp at hla hlb2; subst hla hlb2
        cases va <;> simp only [evalBinOp, hy, ↓reduceIte, Except.ok.injEq, reduceCtorEq] at hbin
        subst hbin
        exact ⟨[_, y], _ / y, .cons eva (.cons evb' .nil), rfl, rfl⟩
  · -- isZero
    subst hop
    simp only [fieldIsZeroE, callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      List.map, FieldLowerProof.qualifyName_fields_is_zero] at ev
    obtain ⟨vx, hm, evx, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨x, rfl, rfl, rfl⟩ := hiz.1 vx hm r h' hcal
    exact ⟨[x], if x = 0 then 1 else 0, .cons evx .nil, rfl, rfl⟩
  · -- eq
    subst hop
    simp only [fieldEqE, callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      List.map, FieldLowerProof.qualifyName_fields_is_zero] at ev
    obtain ⟨vd, hm, evsub, hcal⟩ := evalExpr_call1_inv ev
    obtain ⟨d, rfl, rfl, rfl⟩ := hiz.1 vd hm r h' hcal
    obtain ⟨vx, vy, hm1, evx, evy, hbin⟩ := evalExpr_binary_inv evsub
    cases vx <;> cases vy <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
    rename_i x y
    have hd : x - y = d := Value.field.inj hbin
    subst hd
    have hiff : (x - y = 0) ↔ x = y := sub_eq_zero
    exact ⟨[x, y], if x = y then 1 else 0, .cons evx (.cons evy .nil), rfl, by simp [hiff]⟩

/-- Generic `[Field F] [DecidableEq F]` `EvalExpr` inversion for `fieldOpBody`. -/
theorem evalExpr_fieldOpBody_inv_field {world : World F} (hiz : FieldsIsZeroSpec world)
    {op : FieldOp} {dropFirst : Bool} {pNames : List String} {args : List (SourceValue F)}
    {body : Expr} (hnd : pNames.Nodup) (hlen : args.length = pNames.length)
    (hbody : fieldOpBody op (if dropFirst then pNames.drop 1 else pNames) = some body)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] (pNames.zip args) (qualifyExprF F body) h r h') :
    ∃ (xs : List F) (res : F),
      (if dropFirst then ∃ pVal, args = pVal :: xs.map .field else args = xs.map .field) ∧
      op.eval xs = some res ∧
      r = .field res ∧ h' = h := by
  have evalInvVar : ∀ {loc : Environment F Nat} {v : String} {hv : SourceValue F}
      {h0 h1 : Heap F} {r0 : SourceValue F},
      loc.find? (·.1 == v) = some (v, hv) →
      EvalExpr world [] loc (qualifyExprF F (fieldInvVarE v)) h0 r0 h1 →
      ∃ x : F, hv = .field x ∧ r0 = .field x⁻¹ ∧ h1 = h0 := by
    intro loc v hv h0 h1 r0 hlook evI
    simp only [fieldInvVarE, matchE, fieldIsZeroE, callE, vE, litE,
      qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, List.map, FieldLowerProof.qualifyName_fields_is_zero,
      Nat.cast_zero, Nat.cast_one] at evI
    obtain ⟨viz, hm, eviz, hbr⟩ := evalExpr_match_lit_wild_inv evI
    obtain ⟨vx, hm1, evv, hcal⟩ := evalExpr_call1_inv eviz
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evv
    obtain ⟨x, rfl, rfl, rfl⟩ := hiz.1 _ hm1 viz hm hcal
    rcases hbr with ⟨h1e, ev0⟩ | ⟨hne1, evdiv⟩
    · injection h1e with h1'
      by_cases hx : x = 0
      · subst hx; obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev0
        exact ⟨0, rfl, by simp, rfl⟩
      · simp only [hx, ↓reduceIte] at h1'; exact False.elim (zero_ne_one h1')
    · by_cases hx : x = 0
      · subst hx; simp only [↓reduceIte] at hne1; exact False.elim (hne1 rfl)
      · obtain ⟨v1, vx2, _, ev1, evv2, hbin⟩ := evalExpr_binary_inv evdiv
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv ev1
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook evv2
        simp only [evalBinOp, hx, ↓reduceIte, Except.ok.injEq] at hbin
        subst hbin; exact ⟨x, rfl, by simp [one_div], rfl⟩
  have evalDivVars : ∀ {loc : Environment F Nat} {a b : String} {hva hvb : SourceValue F}
      {h0 h1 : Heap F} {r0 : SourceValue F},
      loc.find? (·.1 == a) = some (a, hva) →
      loc.find? (·.1 == b) = some (b, hvb) →
      EvalExpr world [] loc (qualifyExprF F (fieldDivVarsE a b)) h0 r0 h1 →
      ∃ x y : F, hva = .field x ∧ hvb = .field y ∧ r0 = .field (x / y) ∧ h1 = h0 := by
    intro loc a b hva hvb h0 h1 r0 hla hlb evD
    simp only [fieldDivVarsE, matchE, fieldIsZeroE, fieldMulE, callE, vE, litE,
      qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
      Aiur.Generic.Pattern.map, List.map, FieldLowerProof.qualifyName_fields_is_zero,
      Nat.cast_zero, Nat.cast_one] at evD
    obtain ⟨viz, hm, eviz, hbr⟩ := evalExpr_match_lit_wild_inv evD
    obtain ⟨vb, hm1, evb, hcal⟩ := evalExpr_call1_inv eviz
    obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlb evb
    obtain ⟨y, rfl, rfl, rfl⟩ := hiz.1 _ hm1 viz hm hcal
    rcases hbr with ⟨h1e, ev0⟩ | ⟨hne1, evdiv⟩
    · injection h1e with h1'
      by_cases hy : y = 0
      · subst hy
        obtain ⟨v0, va2, _, evLit0, eva, hbin⟩ := evalExpr_binary_inv ev0
        obtain ⟨rfl, rfl⟩ := evalExpr_literal_inv evLit0
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hla eva
        cases va2 <;> simp only [evalBinOp, Except.ok.injEq, reduceCtorEq] at hbin
        subst hbin; exact ⟨_, 0, rfl, rfl, by simp, rfl⟩
      · simp only [hy, ↓reduceIte] at h1'; exact False.elim (zero_ne_one h1')
    · by_cases hy : y = 0
      · subst hy; simp only [↓reduceIte] at hne1; exact False.elim (hne1 rfl)
      · obtain ⟨va2, vb2, _, eva, evb2, hbin⟩ := evalExpr_binary_inv evdiv
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hla eva
        obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlb evb2
        cases va2 <;> simp only [evalBinOp, hy, ↓reduceIte, Except.ok.injEq, reduceCtorEq] at hbin
        subst hbin; exact ⟨_, y, rfl, rfl, rfl, rfl⟩
  have evalExprOp1 : ∀ {loc : Environment F Nat} {a : String} {va : SourceValue F}
      {op1 : FieldOp} {e1 : Expr} {h0 h1 : Heap F} {r0 : SourceValue F},
      loc.find? (·.1 == a) = some (a, va) →
      fieldOpExpr op1 [vE a] = some e1 →
      EvalExpr world [] loc (qualifyExprF F e1) h0 r0 h1 →
      ∃ (x res : F), va = .field x ∧ op1.eval [x] = some res ∧ r0 = .field res ∧ h1 = h0 := by
    intro loc a va op1 e1 h0 h1 r0 hla he1 ev1
    obtain ⟨xs, res, ea, hev, rfl⟩ := evalExpr_fieldOpExpr_inv_field hiz he1 ev1
    rcases xs with _ | ⟨x, _ | _⟩ <;> simp only [List.map_cons, List.map_nil] at ea
    · cases ea
    · cases ea with | cons evx t =>
      cases t
      obtain ⟨hl, rfl⟩ := evalExpr_vE_inv evx
      rw [hla, Option.some.injEq, Prod.mk.injEq] at hl
      exact ⟨x, res, hl.2, hev, rfl, rfl⟩
    · cases ea with | cons _ t => cases t
  have evalExprOp2 : ∀ {loc : Environment F Nat} {a b : String} {va vb : SourceValue F}
      {op2 : FieldOp} {e2 : Expr} {h0 h1 : Heap F} {r0 : SourceValue F},
      loc.find? (·.1 == a) = some (a, va) →
      loc.find? (·.1 == b) = some (b, vb) →
      fieldOpExpr op2 [vE a, vE b] = some e2 →
      EvalExpr world [] loc (qualifyExprF F e2) h0 r0 h1 →
      ∃ (x y res : F), va = .field x ∧ vb = .field y ∧
        op2.eval [x, y] = some res ∧ r0 = .field res ∧ h1 = h0 := by
    intro loc a b va vb op2 e2 h0 h1 r0 hla hlb he2 ev2
    obtain ⟨xs, res, ea, hev, rfl⟩ := evalExpr_fieldOpExpr_inv_field hiz he2 ev2
    rcases xs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp only [List.map_cons, List.map_nil] at ea
    · cases ea
    · cases ea with | cons _ t => cases t
    · cases ea with | cons evx t1 =>
      cases t1 with | cons evy t2 =>
      cases t2
      obtain ⟨hl1, rfl⟩ := evalExpr_vE_inv evx
      obtain ⟨hl2, rfl⟩ := evalExpr_vE_inv evy
      rw [hla, Option.some.injEq, Prod.mk.injEq] at hl1
      rw [hlb, Option.some.injEq, Prod.mk.injEq] at hl2
      exact ⟨x, y, res, hl1.2, hl2.2, hev, rfl, rfl⟩
    · cases ea with | cons _ t1 => cases t1 with | cons _ t2 => cases t2
  have find2 : ∀ (a b : String) (va vb : SourceValue F), a ≠ b →
      ([a, b].zip [va, vb] : Environment F Nat).find? (·.1 == a) = some (a, va) ∧
      ([a, b].zip [va, vb] : Environment F Nat).find? (·.1 == b) = some (b, vb) := by
    intro a b va vb hne; simp [beq_false_of_ne hne]
  have find3 : ∀ (m a b : String) (vm va vb : SourceValue F), m ≠ a → m ≠ b → a ≠ b →
      ([m, a, b].zip [vm, va, vb] : Environment F Nat).find? (·.1 == a) = some (a, va) ∧
      ([m, a, b].zip [vm, va, vb] : Environment F Nat).find? (·.1 == b) = some (b, vb) := by
    intro m a b vm va vb hma hmb hab
    simp [beq_false_of_ne hma, beq_false_of_ne hmb, beq_false_of_ne hab]
  cases dropFirst
  · simp only [Bool.false_eq_true, ↓reduceIte] at hbody ⊢
    cases op <;> rcases pNames with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
      simp only [fieldOpBody, Option.some.injEq, reduceCtorEq] at hbody
    · subst hbody; rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .add) rfl ev
      exact ⟨[x, y], res, rfl, hev, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .sub) rfl ev
      exact ⟨[x, y], res, rfl, hev, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .mul) rfl ev
      exact ⟨[x, y], res, rfl, hev, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, res, rfl, hev, rfl, rfl⟩ := evalExprOp1 (by simp; rfl) (op1 := .neg) rfl ev
      exact ⟨[x], res, rfl, hev, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, rfl, rfl, rfl⟩ := evalInvVar (by simp; rfl) ev
      exact ⟨[x], x⁻¹, rfl, rfl, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, rfl, rfl, rfl, rfl⟩ := evalDivVars ha hb ev
      exact ⟨[x, y], x / y, rfl, rfl, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
      obtain ⟨x, res, rfl, hev, rfl, rfl⟩ := evalExprOp1 (by simp; rfl) (op1 := .isZero) rfl ev
      exact ⟨[x], res, rfl, hev, rfl, rfl⟩
    · subst hbody; rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
      obtain ⟨ha, hb⟩ := find2 a b va vb hnd.1
      obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .eq) rfl ev
      exact ⟨[x, y], res, rfl, hev, rfl, rfl⟩
  · simp only [↓reduceIte] at hbody ⊢
    rcases pNames with _ | ⟨m, rest⟩
    · cases op <;> simp [fieldOpBody] at hbody
    · simp only [List.drop_succ_cons, List.drop_zero] at hbody
      cases op <;> rcases rest with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
        simp only [fieldOpBody, Option.some.injEq, reduceCtorEq] at hbody
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .add) rfl ev
        exact ⟨[x, y], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .sub) rfl ev
        exact ⟨[x, y], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .mul) rfl ev
        exact ⟨[x, y], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, res, rfl, hev, rfl, rfl⟩ := evalExprOp1 ha (op1 := .neg) rfl ev
        exact ⟨[x], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, rfl, rfl, rfl⟩ := evalInvVar ha ev
        exact ⟨[x], x⁻¹, ⟨vm, rfl⟩, rfl, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, rfl, rfl, rfl, rfl⟩ := evalDivVars ha hb ev
        exact ⟨[x, y], x / y, ⟨vm, rfl⟩, rfl, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | _⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
        obtain ⟨_, ha⟩ := find2 m a vm va hnd.1
        obtain ⟨x, res, rfl, hev, rfl, rfl⟩ := evalExprOp1 ha (op1 := .isZero) rfl ev
        exact ⟨[x], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩
      · subst hbody; rcases args with _ | ⟨vm, _ | ⟨va, _ | ⟨vb, _ | _⟩⟩⟩ <;> simp at hlen
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
        obtain ⟨ha, hb⟩ := find3 m a b vm va vb hnd.1.1 hnd.1.2 hnd.2.1
        obtain ⟨x, y, res, rfl, rfl, hev, rfl, rfl⟩ := evalExprOp2 ha hb (op2 := .eq) rfl ev
        exact ⟨[x, y], res, ⟨vm, rfl⟩, hev, rfl, rfl⟩

/-- `CompressionOp.field` backward soundness over `ZMod p`, delegated directly to
`FieldLowerProof.evalExpr_fieldOpExpr_inv`. -/
theorem evalExpr_compressionOp_field_zmod_inv {p : Nat} [Fact (Nat.Prime p)]
    {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {locals : Environment (ZMod p) Nat} {fop : FieldOp} {args : List Expr} {e : Expr}
    (hop : compressionOpExpr (.field fop) args = some e)
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] locals (qualifyExprF (ZMod p) e) h r h') :
    ∃ (xs : List (ZMod p)) (res : ZMod p),
      EvalArgs world [] locals (args.map (qualifyExprF (ZMod p))) h (xs.map .field) h' ∧
      fop.eval xs = some res ∧
      r = .field res :=
  FieldLowerProof.evalExpr_fieldOpExpr_inv hiz hop ev

/-- `CompressionOp.field` function-body backward soundness over `ZMod p`, delegated
directly to `FieldLowerProof.evalExpr_fieldOpBody_inv`. -/
theorem evalExpr_compressionOpBody_field_zmod_inv {p : Nat} [Fact (Nat.Prime p)]
    {world : World (ZMod p)} (hiz : FieldsIsZeroSpec world)
    {fop : FieldOp} {dropFirst : Bool} {params : List (String × Lower.Ty)}
    {resultTy : Lower.Ty} {args : List (SourceValue (ZMod p))} {body : Expr}
    (hnd : (params.map Prod.fst).Nodup)
    (hlen : args.length = params.length)
    (hbody : compressionOpBody (.field fop) (if dropFirst then params.drop 1 else params) resultTy = some body)
    {h h' : Heap (ZMod p)} {r : SourceValue (ZMod p)}
    (ev : EvalExpr world [] ((params.map Prod.fst).zip args) (qualifyExprF (ZMod p) body) h r h') :
    ∃ (xs : List (ZMod p)) (res : ZMod p),
      (if dropFirst then ∃ pVal, args = pVal :: xs.map .field else args = xs.map .field) ∧
      fop.eval xs = some res ∧
      r = .field res ∧ h' = h := by
  cases dropFirst
  · simp only [Bool.false_eq_true, ↓reduceIte, compressionOpBody] at hbody ⊢
    split at hbody
    · exact FieldLowerProof.evalExpr_fieldOpBody_inv (dropFirst := false) hiz hnd
        (by simpa using hlen) hbody ev
    · cases hbody
  · simp only [↓reduceIte, compressionOpBody, List.map_drop] at hbody ⊢
    split at hbody
    · exact FieldLowerProof.evalExpr_fieldOpBody_inv (dropFirst := true) hiz hnd
        (by simpa using hlen) hbody ev
    · cases hbody

/-! ### 3.2 Goldilocks Base & Cubic-Extension Ops (`CompressionOp.goldilocks`) -/

@[simp] theorem qualifyName_goldilocksOp (gop : GoldilocksOp) :
    qualifyName gop.qualifiedCall = gop.qualifiedCall := by
  cases gop <;> rfl

/-- Value `v` carries cubic extension element `a : ExtGL` via projections `0, 1, 2`
(satisfied by both `[Field; 3]` array values `egVal F a` and `(Field, Field, Field)` tuples). -/
def ExtArgOf (F : Type) [NatCast F] (v : SourceValue F) (a : ExtGL) : Prop :=
  projectValue v 0 = .ok (glVal F a.c0) ∧
  projectValue v 1 = .ok (glVal F a.c1) ∧
  projectValue v 2 = .ok (glVal F a.c2)

omit [Field F] [DecidableEq F] in
theorem extArgOf_egVal [NatCast F] (a : ExtGL) : ExtArgOf F (egVal F a) a :=
  ⟨rfl, rfl, rfl⟩

/-- Semantic input/output relation for `GoldilocksOp` at expression call sites
(covering both direct-arity calls and unpacked 6-scalar / 3-scalar extension calls). -/
def GoldilocksOpExprRel (F : Type) [Field F] :
    GoldilocksOp → List (SourceValue F) → SourceValue F → Prop
  | .add, [va, vb], r => ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a + b)
  | .sub, [va, vb], r => ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a - b)
  | .mul, [va, vb], r => ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧ r = glVal F (a * b)
  | .neg, [va], r => ∃ a : GLF, va = glVal F a ∧ r = glVal F (-a)
  | .inv, [va], r => ∃ a : GLF, va = glVal F a ∧ r = glVal F a⁻¹
  | .isZero, [va], r => ∃ a : GLF, va = glVal F a ∧ r = .field (if a = 0 then (1 : F) else 0)
  | .eq, [va, vb], r => ∃ a b : GLF, va = glVal F a ∧ vb = glVal F b ∧
      r = .field (if a = b then (1 : F) else 0)
  | .extAdd, args, r => ∃ a b : ExtGL,
      (args = [egVal F a, egVal F b] ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.add a b)
  | .extSub, args, r => ∃ a b : ExtGL,
      (args = [egVal F a, egVal F b] ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.sub a b)
  | .extMul, args, r => ∃ a b : ExtGL,
      (args = [egVal F a, egVal F b] ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.mul a b)
  | .extInv, args, r => ∃ a : ExtGL,
      (args = [egVal F a] ∨ args = [glVal F a.c0, glVal F a.c1, glVal F a.c2]) ∧
      r = egVal F (ExtGL.inv a)
  | _, _, _ => False

/-- Semantic input/output relation for `GoldilocksOp` function bodies (generalizing
`GoldilocksOpExprRel` to also accept `(Field, Field, Field)` tuple arguments via `ExtArgOf`). -/
def GoldilocksOpBodyRel (F : Type) [Field F] :
    GoldilocksOp → List (SourceValue F) → SourceValue F → Prop
  | .extAdd, args, r => ∃ a b : ExtGL,
      ((∃ va vb, args = [va, vb] ∧ ExtArgOf F va a ∧ ExtArgOf F vb b) ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.add a b)
  | .extSub, args, r => ∃ a b : ExtGL,
      ((∃ va vb, args = [va, vb] ∧ ExtArgOf F va a ∧ ExtArgOf F vb b) ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.sub a b)
  | .extMul, args, r => ∃ a b : ExtGL,
      ((∃ va vb, args = [va, vb] ∧ ExtArgOf F va a ∧ ExtArgOf F vb b) ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
               glVal F b.c0, glVal F b.c1, glVal F b.c2]) ∧
      r = egVal F (ExtGL.mul a b)
  | .extInv, args, r => ∃ a : ExtGL,
      ((∃ va, args = [va] ∧ ExtArgOf F va a) ∨
       args = [glVal F a.c0, glVal F a.c1, glVal F a.c2]) ∧
      r = egVal F (ExtGL.inv a)
  | gop, args, r => GoldilocksOpExprRel F gop args r

omit [DecidableEq F] in
theorem goldilocksOpExprRel_toBodyRel {gop : GoldilocksOp}
    {args : List (SourceValue F)} {r : SourceValue F}
    (h : GoldilocksOpExprRel F gop args r) : GoldilocksOpBodyRel F gop args r := by
  cases gop with
  | add | sub | mul | neg | inv | isZero | eq => exact h
  | extAdd | extSub | extMul =>
    obtain ⟨a, b, harg, rfl⟩ := h
    rcases harg with rfl | rfl
    · exact ⟨a, b, Or.inl ⟨egVal F a, egVal F b, rfl, extArgOf_egVal a, extArgOf_egVal b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl, rfl⟩
  | extInv =>
    obtain ⟨a, harg, rfl⟩ := h
    rcases harg with rfl | rfl
    · exact ⟨a, Or.inl ⟨egVal F a, rfl, extArgOf_egVal a⟩, rfl⟩
    · exact ⟨a, Or.inr rfl, rfl⟩

/-- Unified `EvalFn` soundness for any `GoldilocksOp` call given `GoldilocksContracts`. -/
theorem evalFn_goldilocksOp_sound {world : World F} (hgl : GoldilocksContracts world)
    {gop : GoldilocksOp} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hlen : args.length = gop.arity)
    (ev : EvalFn world gop.qualifiedCall args h r h') :
    GoldilocksOpExprRel F gop args r ∧ h' = h := by
  cases gop <;> rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp [GoldilocksOp.arity] at hlen
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.gl_add ev; exact ⟨⟨a, b, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.gl_sub ev; exact ⟨⟨a, b, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.gl_mul ev; exact ⟨⟨a, b, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, rfl, rfl, rfl⟩ := hgl.gl_neg ev; exact ⟨⟨a, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, rfl, rfl, rfl⟩ := hgl.gl_inverse ev; exact ⟨⟨a, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, rfl, rfl, rfl⟩ := hgl.gl_is_zero ev; exact ⟨⟨a, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.gl_eq ev; exact ⟨⟨a, b, rfl, rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_add ev; exact ⟨⟨a, b, Or.inl rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_sub ev; exact ⟨⟨a, b, Or.inl rfl, rfl⟩, rfl⟩
  · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_mul ev; exact ⟨⟨a, b, Or.inl rfl, rfl⟩, rfl⟩
  · obtain ⟨a, rfl, rfl, rfl⟩ := hgl.eg_inverse ev; exact ⟨⟨a, Or.inl rfl, rfl⟩, rfl⟩

private theorem evalArgs_length {world : World F} {types : Types} {locals : Environment F Nat} :
    ∀ {es : List (Aiur.Generic.Expr F)} {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs world types locals es h vs h' → vs.length = es.length
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ tl => by simp [evalArgs_length tl]

/-- Per-op `EvalExpr` backward soundness for `compressionOpExpr (.goldilocks gop) xs`
(covering all 11 base + cubic-extension ops, including flat scalar argument forms). -/
theorem evalExpr_compressionOp_goldilocks_inv {world : World F} (hgl : GoldilocksContracts world)
    {locals : Environment F Nat} {gop : GoldilocksOp} {xs : List Expr} {e : Expr}
    (hop : compressionOpExpr (.goldilocks gop) xs = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ vs : List (SourceValue F),
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs h' ∧
      GoldilocksOpExprRel F gop vs r := by
  simp only [compressionOpExpr] at hop
  split at hop
  · next hlen =>
    injection hop with he; subst he
    simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      qualifyName_goldilocksOp, map_qualifyExprF] at ev
    obtain ⟨vs, hm, eva, hcal⟩ := evalExpr_call_inv ev
    have hvsLen : vs.length = gop.arity := by
      have := evalArgs_length eva
      simp only [List.length_map] at this
      exact this.trans (beq_iff_eq.mp hlen)
    obtain ⟨hrel, rfl⟩ := evalFn_goldilocksOp_sound hgl hvsLen hcal
    exact ⟨vs, eva, hrel⟩
  · cases gop <;>
      rcases xs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | _⟩⟩⟩⟩⟩⟩ <;>
      simp only [Option.some.injEq, reduceCtorEq] at hop
    · -- extAdd 6 scalars
      subst hop
      simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
        qualifyName_goldilocksOp] at ev
      obtain ⟨va, vb, h1, hm, eva, evb, hcal⟩ := evalExpr_call2_inv ev
      obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_add hcal
      obtain ⟨u0, u1, u2, _, _, ea0, ea1, ea2, htuA⟩ := evalExpr_array3_inv eva
      injection htuA with hca; injection hca with h0 hca1; injection hca1 with h1' hca2
      injection hca2 with h2 _; subst h0 h1' h2
      obtain ⟨v0, v1, v2, _, _, eb0, eb1, eb2, htuB⟩ := evalExpr_array3_inv evb
      injection htuB with hcb; injection hcb with k0 hcb1; injection hcb1 with k1 hcb2
      injection hcb2 with k2 _; subst k0 k1 k2
      exact ⟨_, .cons ea0 (.cons ea1 (.cons ea2 (.cons eb0 (.cons eb1 (.cons eb2 .nil))))),
        ⟨a, b, Or.inr rfl, rfl⟩⟩
    · -- extSub 6 scalars
      subst hop
      simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
        qualifyName_goldilocksOp] at ev
      obtain ⟨va, vb, h1, hm, eva, evb, hcal⟩ := evalExpr_call2_inv ev
      obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_sub hcal
      obtain ⟨u0, u1, u2, _, _, ea0, ea1, ea2, htuA⟩ := evalExpr_array3_inv eva
      injection htuA with hca; injection hca with h0 hca1; injection hca1 with h1' hca2
      injection hca2 with h2 _; subst h0 h1' h2
      obtain ⟨v0, v1, v2, _, _, eb0, eb1, eb2, htuB⟩ := evalExpr_array3_inv evb
      injection htuB with hcb; injection hcb with k0 hcb1; injection hcb1 with k1 hcb2
      injection hcb2 with k2 _; subst k0 k1 k2
      exact ⟨_, .cons ea0 (.cons ea1 (.cons ea2 (.cons eb0 (.cons eb1 (.cons eb2 .nil))))),
        ⟨a, b, Or.inr rfl, rfl⟩⟩
    · -- extMul 6 scalars
      subst hop
      simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
        qualifyName_goldilocksOp] at ev
      obtain ⟨va, vb, h1, hm, eva, evb, hcal⟩ := evalExpr_call2_inv ev
      obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_mul hcal
      obtain ⟨u0, u1, u2, _, _, ea0, ea1, ea2, htuA⟩ := evalExpr_array3_inv eva
      injection htuA with hca; injection hca with h0 hca1; injection hca1 with h1' hca2
      injection hca2 with h2 _; subst h0 h1' h2
      obtain ⟨v0, v1, v2, _, _, eb0, eb1, eb2, htuB⟩ := evalExpr_array3_inv evb
      injection htuB with hcb; injection hcb with k0 hcb1; injection hcb1 with k1 hcb2
      injection hcb2 with k2 _; subst k0 k1 k2
      exact ⟨_, .cons ea0 (.cons ea1 (.cons ea2 (.cons eb0 (.cons eb1 (.cons eb2 .nil))))),
        ⟨a, b, Or.inr rfl, rfl⟩⟩
    · -- extInv 3 scalars
      subst hop
      simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
        qualifyName_goldilocksOp] at ev
      obtain ⟨va, hm, eva, hcal⟩ := evalExpr_call1_inv ev
      obtain ⟨a, rfl, rfl, rfl⟩ := hgl.eg_inverse hcal
      obtain ⟨u0, u1, u2, _, _, ea0, ea1, ea2, htuA⟩ := evalExpr_array3_inv eva
      injection htuA with hca; injection hca with h0 hca1; injection hca1 with h1' hca2
      injection hca2 with h2 _; subst h0 h1' h2
      exact ⟨_, .cons ea0 (.cons ea1 (.cons ea2 .nil)), ⟨a, Or.inr rfl, rfl⟩⟩

private theorem evalExpr_extResultWrap_inv {world : World F} {locals : Environment F Nat}
    {raw : Expr} {c1 c2 : Bool} {body : Expr} {h h' : Heap F} {r : SourceValue F}
    (hwrap : (if c1 = true then some raw
              else if c2 = true then
                some (letE "_cg_ext" raw
                  (.tuple [.index (vE "_cg_ext") 0, .index (vE "_cg_ext") 1, .index (vE "_cg_ext") 2]))
              else none) = some body)
    (ev : EvalExpr world [] locals (qualifyExprF F body) h r h')
    (hraw : ∀ r0 h1, EvalExpr world [] locals (qualifyExprF F raw) h r0 h1 →
      ∃ res : ExtGL, r0 = egVal F res ∧ h1 = h) :
    ∃ (r0 : SourceValue F), EvalExpr world [] locals (qualifyExprF F raw) h r0 h' ∧
      r = r0 ∧ h' = h := by
  split at hwrap
  · injection hwrap with he; subst he
    obtain ⟨res, rfl, rfl⟩ := hraw r h' ev
    exact ⟨egVal F res, ev, rfl, rfl⟩
  · split at hwrap
    · injection hwrap with he; subst he
      simp only [letE, vE, qualifyExprF, qualifyExpr, qualifyPat, Aiur.Generic.Expr.map,
        Aiur.Generic.Pattern.map, List.map] at ev
      obtain ⟨vraw, hm, evRaw, evTup⟩ := evalExpr_let_bind_inv ev
      obtain ⟨res, rfl, rfl⟩ := hraw vraw hm evRaw
      cases evTup with
      | tuple hargs =>
        cases hargs with | cons e0 t0 =>
        cases t0 with | cons e1 t1 =>
        cases t1 with | cons e2 t2 =>
        cases t2
        obtain ⟨hp0, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e0
        obtain ⟨hp1, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e1
        obtain ⟨hp2, rfl⟩ := evalExpr_idx_var_inv (by simp; rfl) e2
        injection hp0 with hp0; subst hp0
        injection hp1 with hp1; subst hp1
        injection hp2 with hp2; subst hp2
        exact ⟨egVal F res, evRaw, rfl, rfl⟩
    · cases hwrap

private theorem evalArgs_paramVars_inv {world : World F} {locals : Environment F Nat} :
    ∀ {pNames : List String} {vs vals : List (SourceValue F)} {h h' : Heap F},
      (∀ k v, (k, v) ∈ pNames.zip vs → locals.find? (·.1 == k) = some (k, v)) →
      pNames.length = vs.length →
      EvalArgs world [] locals ((pNames.map vE).map (qualifyExprF F)) h vals h' →
      vals = vs ∧ h' = h
  | [], [], _, _, _, _, _, ev => by cases ev; exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _ => by simp at hlen
  | k :: ks, v :: vs, vals, h, h', hlook, hlen, ev => by
    simp only [List.map_cons] at ev
    cases ev with
    | cons evHd evTl =>
      obtain ⟨hlk, rfl⟩ := evalExpr_vE_inv evHd
      have hkv := hlook k v (by simp [List.zip_cons_cons])
      rw [hkv, Option.some.injEq, Prod.mk.injEq] at hlk
      have hvEq : v = _ := hlk.2
      subst hvEq
      have hlookTl : ∀ k' v', (k', v') ∈ ks.zip vs → locals.find? (·.1 == k') = some (k', v') :=
        fun k' v' hmem => hlook k' v' (by simp [List.zip_cons_cons, hmem])
      obtain ⟨rfl, rfl⟩ := evalArgs_paramVars_inv hlookTl (by simp at hlen; omega) evTl
      exact ⟨rfl, rfl⟩

omit [Field F] [DecidableEq F] in
private theorem find_zip_nodup_mem {ks : List String} {vs : List (SourceValue F)}
    (hnd : ks.Nodup) (hlen : ks.length = vs.length)
    {k : String} {v : SourceValue F} (hmem : (k, v) ∈ ks.zip vs) :
    (ks.zip vs).find? (·.1 == k) = some (k, v) := by
  induction ks generalizing vs with
  | nil => simp at hmem
  | cons a ks ih =>
    cases vs with
    | nil => simp at hlen
    | cons b vs =>
      simp only [List.nodup_cons] at hnd
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.zip_cons_cons, List.mem_cons] at hmem
      rcases hmem with hhd | htl
      · injection hhd with hka hvb; subst hka hvb; simp
      · have hkMem : k ∈ ks := (List.of_mem_zip htl).1
        have hne : a ≠ k := fun heq => hnd.1 (heq ▸ hkMem)
        simp only [List.zip_cons_cons, List.find?_cons, beq_false_of_ne hne]
        exact ih hnd.2 hlen htl

private theorem evalExpr_proj3_array_inv {world : World F} {locals : Environment F Nat}
    {nm : String} {v : SourceValue F} {a : ExtGL} {h h' : Heap F}
    (hlook : locals.find? (·.1 == nm) = some (nm, v))
    (ev : EvalExpr world [] locals
      (qualifyExprF F (.array [.project (vE nm) 0, .project (vE nm) 1, .project (vE nm) 2]))
      h (egVal F a) h') :
    ExtArgOf F v a ∧ h' = h := by
  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
  obtain ⟨r0, r1, r2, _, _, e0, e1, e2, htup⟩ := evalExpr_array3_inv ev
  injection htup with hc0; injection hc0 with h0 hc1; injection hc1 with h1 hc2; injection hc2 with h2 _
  subst h0 h1 h2
  obtain ⟨_, ev0, hp0⟩ := evalExpr_project_inv e0
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook ev0
  obtain ⟨_, ev1, hp1⟩ := evalExpr_project_inv e1
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook ev1
  obtain ⟨_, ev2, hp2⟩ := evalExpr_project_inv e2
  obtain ⟨rfl, rfl⟩ := evalExpr_var_eq hlook ev2
  exact ⟨⟨hp0, hp1, hp2⟩, rfl⟩

private theorem evalExpr_vars3_array_inv {world : World F} {locals : Environment F Nat}
    {n0 n1 n2 : String} {v0 v1 v2 : SourceValue F} {a : ExtGL} {h h' : Heap F}
    (hl0 : locals.find? (·.1 == n0) = some (n0, v0))
    (hl1 : locals.find? (·.1 == n1) = some (n1, v1))
    (hl2 : locals.find? (·.1 == n2) = some (n2, v2))
    (ev : EvalExpr world [] locals
      (qualifyExprF F (.array [vE n0, vE n1, vE n2])) h (egVal F a) h') :
    v0 = glVal F a.c0 ∧ v1 = glVal F a.c1 ∧ v2 = glVal F a.c2 ∧ h' = h := by
  simp only [vE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map] at ev
  obtain ⟨r0, r1, r2, _, _, e0, e1, e2, htup⟩ := evalExpr_array3_inv ev
  injection htup with hc0; injection hc0 with h0 hc1; injection hc1 with h1 hc2; injection hc2 with h2 _
  subst h0 h1 h2
  obtain ⟨he0, rfl⟩ := evalExpr_var_eq hl0 e0
  obtain ⟨he1, rfl⟩ := evalExpr_var_eq hl1 e1
  obtain ⟨he2, rfl⟩ := evalExpr_var_eq hl2 e2
  exact ⟨he0.symm, he1.symm, he2.symm, rfl⟩

private def evalExtBin : GoldilocksOp → ExtGL → ExtGL → ExtGL
  | .extAdd, a, b => ExtGL.add a b
  | .extSub, a, b => ExtGL.sub a b
  | _, a, b => ExtGL.mul a b

/-- Per-op function-body backward soundness for `compressionOpBody (.goldilocks gop)`,
handling all 11 Goldilocks ops and all `[Field; 3]` / `(Field, Field, Field)` / flat-scalar
parameter & return adapters. -/
theorem evalExpr_compressionOpBody_goldilocks_inv {world : World F} (hgl : GoldilocksContracts world)
    {gop : GoldilocksOp} {params : List (String × Lower.Ty)} {resultTy : Lower.Ty}
    {args : List (SourceValue F)} {body : Expr}
    (hnd : (params.map Prod.fst).Nodup)
    (hlen : args.length = params.length)
    (hbody : compressionOpBody (.goldilocks gop) params resultTy = some body)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] ((params.map Prod.fst).zip args) (qualifyExprF F body) h r h') :
    GoldilocksOpBodyRel F gop args r ∧ h' = h := by
  have hlenMap : (params.map Prod.fst).length = args.length := by simp [hlen]
  have hlook : ∀ k v, (k, v) ∈ (params.map Prod.fst).zip args →
      ((params.map Prod.fst).zip args).find? (·.1 == k) = some (k, v) :=
    fun _ _ hm => find_zip_nodup_mem hnd hlenMap hm
  simp only [compressionOpBody] at hbody
  split at hbody
  · -- Base (non-ext) Goldilocks op
    split at hbody
    · next hcond =>
      injection hbody with he; subst he
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
        qualifyName_goldilocksOp, map_qualifyExprF] at ev
      obtain ⟨vals, hm, eva, hcal⟩ := evalExpr_call_inv ev
      have hmapEq : (params.map fun p => vE p.1) = (params.map Prod.fst).map vE := by
        rw [List.map_map]; rfl
      rw [hmapEq] at eva
      obtain ⟨rfl, rfl⟩ := evalArgs_paramVars_inv hlook hlenMap eva
      obtain ⟨hrel, rfl⟩ := evalFn_goldilocksOp_sound hgl (hlen.trans hcond.1.1) hcal
      exact ⟨goldilocksOpExprRel_toBodyRel hrel, rfl⟩
    · cases hbody
  · -- Cubic extension Goldilocks op (`extAdd`, `extSub`, `extMul`, `extInv`)
    next hnotExt =>
    have hext : gop.isExt = true := by
      cases h : gop.isExt <;> simp_all
    have harCases : (gop.arity = 2 ∧ (gop = .extAdd ∨ gop = .extSub ∨ gop = .extMul)) ∨
        (gop.arity = 1 ∧ gop = .extInv) := by
      cases gop <;> simp [GoldilocksOp.isExt, GoldilocksOp.arity] at hext ⊢
    rcases harCases with ⟨har2, hgop⟩ | ⟨har1, rfl⟩
    · have hbinExt : ∀ {loc : Environment F Nat} {ea eb : Expr} {r0 : SourceValue F} {h1 : Heap F},
          EvalExpr world [] loc
            (qualifyExprF F (callE gop.qualifiedCall [ea, eb])) h r0 h1 →
          ∃ (a b : ExtGL) (hmid : Heap F),
            EvalExpr world [] loc (qualifyExprF F ea) h (egVal F a) hmid ∧
            EvalExpr world [] loc (qualifyExprF F eb) hmid (egVal F b) h1 ∧
            r0 = egVal F (evalExtBin gop a b) := by
        intro loc ea eb r0 h1 evc
        simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
          qualifyName_goldilocksOp] at evc
        obtain ⟨va, vb, hmid, hm, eva, evb, hcal⟩ := evalExpr_call2_inv evc
        rcases hgop with rfl | rfl | rfl
        · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_add hcal
          exact ⟨a, b, hmid, eva, evb, rfl⟩
        · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_sub hcal
          exact ⟨a, b, hmid, eva, evb, rfl⟩
        · obtain ⟨a, b, rfl, rfl, rfl, rfl⟩ := hgl.eg_mul hcal
          exact ⟨a, b, hmid, eva, evb, rfl⟩
      have hbinRel : ∀ {vs : List (SourceValue F)} {a b : ExtGL},
          ((∃ va vb, vs = [va, vb] ∧ ExtArgOf F va a ∧ ExtArgOf F vb b) ∨
           vs = [glVal F a.c0, glVal F a.c1, glVal F a.c2,
                 glVal F b.c0, glVal F b.c1, glVal F b.c2]) →
          GoldilocksOpBodyRel F gop vs (egVal F (evalExtBin gop a b)) := by
        intro vs a b harg
        rcases hgop with rfl | rfl | rfl <;> exact ⟨a, b, harg, rfl⟩
      rw [har2] at hbody
      rcases params with _ | ⟨⟨a0, t0⟩, _ | ⟨⟨a1, t1⟩, _ | ⟨⟨a2, t2⟩, _ | ⟨⟨b0, t3⟩, _ | ⟨⟨b1, t4⟩, _ | ⟨⟨b2, t5⟩, _ | _⟩⟩⟩⟩⟩⟩
      all_goals try simp only at hbody
      all_goals try cases hbody
      · -- 2 params: [(a0, t0), (a1, t1)]
        rcases args with _ | ⟨va, _ | ⟨vb, _ | _⟩⟩ <;> simp at hlen
        have hla := hlook a0 va (by simp [List.zip_cons_cons])
        have hlb := hlook a1 vb (by simp [List.zip_cons_cons])
        split at hbody
        · -- array × array
          obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
            obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evR
            obtain ⟨_, hh1⟩ := evalExpr_vE_inv eva; subst hh1
            obtain ⟨_, hh2⟩ := evalExpr_vE_inv evb; subst hh2
            exact ⟨_, rfl, rfl⟩
          obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evRaw
          obtain ⟨ha', hh1⟩ := evalExpr_vE_inv eva; subst hh1
          obtain ⟨hb', _⟩ := evalExpr_vE_inv evb
          rw [hla, Option.some.injEq, Prod.mk.injEq] at ha'
          rw [hlb, Option.some.injEq, Prod.mk.injEq] at hb'
          have hva : va = egVal F ga := ha'.2
          have hvb : vb = egVal F gb := hb'.2
          subst hva hvb
          exact ⟨hbinRel (Or.inl ⟨_, _, rfl, extArgOf_egVal ga, extArgOf_egVal gb⟩), rfl⟩
        · split at hbody
          · -- tuple × tuple
            obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
              obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evR
              obtain ⟨_, hh1⟩ := evalExpr_proj3_array_inv hla eva; subst hh1
              obtain ⟨_, hh2⟩ := evalExpr_proj3_array_inv hlb evb; subst hh2
              exact ⟨_, rfl, rfl⟩
            obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evRaw
            obtain ⟨hEa, hh1⟩ := evalExpr_proj3_array_inv hla eva; subst hh1
            obtain ⟨hEb, _⟩ := evalExpr_proj3_array_inv hlb evb
            exact ⟨hbinRel (Or.inl ⟨va, vb, rfl, hEa, hEb⟩), rfl⟩
          · cases hbody
      · -- 6 scalar params
        cases t0 <;> (try simp only at hbody) <;> try cases hbody
        cases t1 <;> (try simp only at hbody) <;> try cases hbody
        cases t2 <;> (try simp only at hbody) <;> try cases hbody
        cases t3 <;> (try simp only at hbody) <;> try cases hbody
        cases t4 <;> (try simp only at hbody) <;> try cases hbody
        cases t5 <;> (try simp only at hbody) <;> try cases hbody
        rcases args with _ | ⟨va0, _ | ⟨va1, _ | ⟨va2, _ | ⟨vb0, _ | ⟨vb1, _ | ⟨vb2, _ | _⟩⟩⟩⟩⟩⟩ <;>
          simp at hlen
        have hla0 := hlook a0 va0 (by simp [List.zip_cons_cons])
        have hla1 := hlook a1 va1 (by simp [List.zip_cons_cons])
        have hla2 := hlook a2 va2 (by simp [List.zip_cons_cons])
        have hlb0 := hlook b0 vb0 (by simp [List.zip_cons_cons])
        have hlb1 := hlook b1 vb1 (by simp [List.zip_cons_cons])
        have hlb2 := hlook b2 vb2 (by simp [List.zip_cons_cons])
        obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
          obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evR
          obtain ⟨_, _, _, hh1⟩ := evalExpr_vars3_array_inv hla0 hla1 hla2 eva; subst hh1
          obtain ⟨_, _, _, hh2⟩ := evalExpr_vars3_array_inv hlb0 hlb1 hlb2 evb; subst hh2
          exact ⟨_, rfl, rfl⟩
        obtain ⟨ga, gb, hmid, eva, evb, rfl⟩ := hbinExt evRaw
        obtain ⟨ha0, ha1, ha2, hh1⟩ := evalExpr_vars3_array_inv hla0 hla1 hla2 eva; subst hh1
        obtain ⟨hb0, hb1, hb2, _⟩ := evalExpr_vars3_array_inv hlb0 hlb1 hlb2 evb
        subst ha0 ha1 ha2 hb0 hb1 hb2
        exact ⟨hbinRel (Or.inr rfl), rfl⟩
    · have hunExt : ∀ {loc : Environment F Nat} {ea : Expr} {r0 : SourceValue F} {h1 : Heap F},
          EvalExpr world [] loc
            (qualifyExprF F (callE GoldilocksOp.extInv.qualifiedCall [ea])) h r0 h1 →
          ∃ ga : ExtGL,
            EvalExpr world [] loc (qualifyExprF F ea) h (egVal F ga) h1 ∧
            r0 = egVal F (ExtGL.inv ga) := by
        intro loc ea r0 h1 evc
        simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, List.map,
          qualifyName_goldilocksOp] at evc
        obtain ⟨vx, hm, eva, hcal⟩ := evalExpr_call1_inv evc
        obtain ⟨ga, rfl, rfl, rfl⟩ := hgl.eg_inverse hcal
        exact ⟨ga, eva, rfl⟩
      rw [har1] at hbody
      rcases params with _ | ⟨⟨a0, t0⟩, _ | ⟨⟨a1, t1⟩, _ | ⟨⟨a2, t2⟩, _ | _⟩⟩⟩
      all_goals try simp only at hbody
      all_goals try cases hbody
      · -- 1 param: [(a0, t0)]
        rcases args with _ | ⟨va, _ | _⟩ <;> simp at hlen
        have hla := hlook a0 va (by simp [List.zip_cons_cons])
        split at hbody
        · -- array
          obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
            obtain ⟨ga, eva, rfl⟩ := hunExt evR
            obtain ⟨_, hh1⟩ := evalExpr_vE_inv eva; subst hh1
            exact ⟨_, rfl, rfl⟩
          obtain ⟨ga, eva, rfl⟩ := hunExt evRaw
          obtain ⟨ha', _⟩ := evalExpr_vE_inv eva
          rw [hla, Option.some.injEq, Prod.mk.injEq] at ha'
          have hva : va = egVal F ga := ha'.2; subst hva
          exact ⟨⟨ga, Or.inl ⟨_, rfl, extArgOf_egVal ga⟩, rfl⟩, rfl⟩
        · split at hbody
          · -- tuple
            obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
              obtain ⟨ga, eva, rfl⟩ := hunExt evR
              obtain ⟨_, hh1⟩ := evalExpr_proj3_array_inv hla eva; subst hh1
              exact ⟨_, rfl, rfl⟩
            obtain ⟨ga, eva, rfl⟩ := hunExt evRaw
            obtain ⟨hEa, _⟩ := evalExpr_proj3_array_inv hla eva
            exact ⟨⟨ga, Or.inl ⟨va, rfl, hEa⟩, rfl⟩, rfl⟩
          · cases hbody
      · -- 3 scalar params
        cases t0 <;> (try simp only at hbody) <;> try cases hbody
        cases t1 <;> (try simp only at hbody) <;> try cases hbody
        cases t2 <;> (try simp only at hbody) <;> try cases hbody
        rcases args with _ | ⟨va0, _ | ⟨va1, _ | ⟨va2, _ | _⟩⟩⟩ <;> simp at hlen
        have hla0 := hlook a0 va0 (by simp [List.zip_cons_cons])
        have hla1 := hlook a1 va1 (by simp [List.zip_cons_cons])
        have hla2 := hlook a2 va2 (by simp [List.zip_cons_cons])
        obtain ⟨r0, evRaw, rfl, rfl⟩ := evalExpr_extResultWrap_inv hbody ev fun r0 h1 evR => by
          obtain ⟨ga, eva, rfl⟩ := hunExt evR
          obtain ⟨_, _, _, hh1⟩ := evalExpr_vars3_array_inv hla0 hla1 hla2 eva; subst hh1
          exact ⟨_, rfl, rfl⟩
        obtain ⟨ga, eva, rfl⟩ := hunExt evRaw
        obtain ⟨ha0, ha1, ha2, _⟩ := evalExpr_vars3_array_inv hla0 hla1 hla2 eva
        subst ha0 ha1 ha2
        exact ⟨⟨ga, Or.inr rfl, rfl⟩, rfl⟩

/-! ### 3.3 BLAKE3 Block & Stream Ops (`CompressionOp.blake3` via `Blake3Spec.Blake3Contracts`) -/

@[simp] theorem qualifyName_blake3Op (bop : Blake3Op) :
    qualifyName bop.qualifiedCall = bop.qualifiedCall := by
  cases bop <;> rfl

/-- Generic `EvalExpr` inversion for `compressionOpExpr (.blake3 bop) xs = some e`. -/
theorem evalExpr_compressionOp_blake3_inv {world : World F}
    {locals : Environment F Nat} {bop : Blake3Op} {xs : List Expr} {e : Expr}
    (hop : compressionOpExpr (.blake3 bop) xs = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (vs : List (SourceValue F)) (hm : Heap F),
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs hm ∧
      vs.length = bop.arity ∧
      EvalFn world bop.qualifiedCall vs hm r h' := by
  simp only [compressionOpExpr] at hop
  split at hop
  · next hlen =>
    injection hop with he; subst he
    simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      qualifyName_blake3Op, map_qualifyExprF] at ev
    obtain ⟨vs, hm, eva, hcal⟩ := evalExpr_call_inv ev
    have hvsLen : vs.length = bop.arity := by
      have := evalArgs_length eva
      simp only [List.length_map] at this
      exact this.trans (beq_iff_eq.mp hlen)
    exact ⟨vs, hm, eva, hvsLen, hcal⟩
  · cases hop

/-- Certified backward soundness for `blake3.compress_init` connected directly to
`Blake3Spec.Blake3Contracts.compress_init`. -/
theorem evalExpr_compressionOp_blake3_compressInit_sound {world : World F}
    (hb3 : Blake3Contracts world) {locals : Environment F Nat}
    {xs : List Expr} {e : Expr}
    (hop : compressionOpExpr (.blake3 .compressInit) xs = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (vs : List (SourceValue F)) (hm : Heap F),
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs hm ∧
      (∀ {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64} {len fl : Nat},
        len < 256 → fl < 256 →
        vs = [vecV cv, vecV m, u64v c, .field (len : F), .field (fl : F)] →
        r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl.toUInt32) ∧ h' = hm) := by
  obtain ⟨vs, hm, eva, _, hcal⟩ := evalExpr_compressionOp_blake3_inv hop ev
  refine ⟨vs, hm, eva, fun hlen hfl hvs => ?_⟩
  subst hvs
  exact hb3.compress_init hlen hfl hcal

/-- Certified backward soundness for `blake3.hash` connected directly to
`Blake3Spec.Blake3Contracts.hash` and `Blake3Contracts.hash_digest`. -/
theorem evalExpr_compressionOp_blake3_hash_sound {world : World F}
    (hb3 : Blake3Contracts world) {locals : Environment F Nat}
    {x : Expr} {e : Expr}
    (hop : compressionOpExpr (.blake3 .hash) [x] = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (inp : SourceValue F) (hm : Heap F),
      EvalExpr world [] locals (qualifyExprF F x) h inp hm ∧
      (∀ {bytes : List UInt8}, Stream hm bytes inp →
        Heap.Extends hm h' ∧ r = vecV (Aiur.Library.Blake3.hashModel bytes) ∧
        (Blake3.Pure.NativeInput bytes →
          Blake3.Pure.cvBytes (Aiur.Library.Blake3.hashModel bytes) = Blake3.Pure.digest bytes)) := by
  obtain ⟨vs, hm, eva, hlen, hcal⟩ := evalExpr_compressionOp_blake3_inv hop ev
  rcases vs with _ | ⟨inp, _ | _⟩ <;> simp [Blake3Op.arity] at hlen
  cases eva with | cons evx t =>
  cases t
  refine ⟨inp, hm, evx, fun hs => ?_⟩
  obtain ⟨ext, hr⟩ := hb3.hash hs hcal
  exact ⟨ext, hr, fun hnat => (hb3.hash_digest hs hnat hcal).2.2⟩

/-- Certified backward soundness for `blake3.pack_digest` connected directly to
`Blake3Spec.Blake3Contracts.pack_digest`. -/
theorem evalExpr_compressionOp_blake3_packDigest_sound {world : World F}
    (hb3 : Blake3Contracts world) {locals : Environment F Nat}
    {x : Expr} {e : Expr}
    (hop : compressionOpExpr (.blake3 .packDigest) [x] = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (inp : SourceValue F) (hm : Heap F),
      EvalExpr world [] locals (qualifyExprF F x) h inp hm ∧
      (∀ {cv : Blake3.Pure.CV}, inp = vecV cv →
        r = .tuple ((Aiur.Library.Blake3.packDigest F cv).toList.map .field) ∧ h' = hm) := by
  obtain ⟨vs, hm, eva, hlen, hcal⟩ := evalExpr_compressionOp_blake3_inv hop ev
  rcases vs with _ | ⟨inp, _ | _⟩ <;> simp [Blake3Op.arity] at hlen
  cases eva with | cons evx t =>
  cases t
  refine ⟨inp, hm, evx, fun hcv => ?_⟩
  subst hcv
  exact hb3.pack_digest hcal

/-- Concrete 3-field `Blake3Contracts` constructors from `checkBlake3World`. -/
theorem blake3Contracts_goldilocks {s : Generic.Source GLF}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheckGoldilocks h

theorem blake3Contracts_bn254 {s : Generic.Source Aiur.Library.Field.BN254.F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck64 fieldCompatible64_bn254 h

theorem blake3Contracts_bls12381 {s : Generic.Source Aiur.Library.Field.BLS12381.F}
    (h : checkBlake3World s = true) : Blake3Contracts s.world :=
  Blake3Contracts.ofCheck64 fieldCompatible64_bls12381 h

/-! ### 3.4 Checked Witness-Stream Channel Ops (`CompressionOp.witness` via `WitnessIO`) -/

@[simp] theorem qualifyName_witnessOp (wop : WitnessOp) :
    qualifyName wop.qualifiedCall = wop.qualifiedCall := by
  cases wop <;> rfl

/-- Postcondition relating a `WitnessOp` output `r` on heap `h'` to an existential valid
byte list `bs : List UInt8`. -/
def WitnessOpResultRel (F : Type) [Field F] :
    WitnessOp → Heap F → SourceValue F → List UInt8 → Prop
  | .starkReadChannel, h', r, bs => ByteStreamRel h' bs r
  | .starkReadByteStream, h', r, bs => ByteStreamRel h' bs r
  | .kzgReadChannel, h', r, bs => ByteStreamRel h' bs r
  | .kzgSizedChannel, h', r, bs => ∃ inp lenVal, r = .tuple [inp, lenVal] ∧ KzgInputRel h' bs inp

/-- Unified `EvalFn` existential witness-stream soundness for all 4 `WitnessOp`s,
dispatched directly to `WitnessIO`. -/
theorem evalFn_witnessOp_sound {world : World F}
    {wop : WitnessOp}
    (hsio : (wop = .starkReadChannel ∨ wop = .starkReadByteStream) → StarkIOWorld world)
    (hkio : (wop = .kzgReadChannel ∨ wop = .kzgSizedChannel) → KzgIOWorld world)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hlen : args.length = wop.arity)
    (ev : EvalFn world wop.qualifiedCall args h r h') :
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, WitnessOpResultRel F wop h' r bs ∧ isValidByteList (bs.map UInt8.toNat) := by
  cases wop <;> rcases args with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩⟩ <;>
    simp [WitnessOp.arity] at hlen
  · exact starkIo_read_channel_sound (hsio (Or.inl rfl)) ev
  · exact starkIo_read_byte_stream_sound (hsio (Or.inr rfl)) ev
  · exact kzgIo_read_stream_sound (hkio (Or.inl rfl)) ev
  · obtain ⟨ext, bs, inp, lenVal, rfl, hrel, hval⟩ :=
      kzgIo_sized_channel_sound (hkio (Or.inr rfl)) ev
    exact ⟨ext, bs, ⟨inp, lenVal, rfl, hrel⟩, hval⟩

/-- Per-op `EvalExpr` backward soundness for `compressionOpExpr (.witness wop) xs = some e`:
unconditionally extends the heap and produces a finite valid `List UInt8` witness stream. -/
theorem evalExpr_compressionOp_witness_inv {world : World F}
    {locals : Environment F Nat} {wop : WitnessOp}
    (hsio : (wop = .starkReadChannel ∨ wop = .starkReadByteStream) → StarkIOWorld world)
    (hkio : (wop = .kzgReadChannel ∨ wop = .kzgSizedChannel) → KzgIOWorld world)
    {xs : List Expr} {e : Expr}
    (hop : compressionOpExpr (.witness wop) xs = some e)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] locals (qualifyExprF F e) h r h') :
    ∃ (vs : List (SourceValue F)) (hm : Heap F),
      EvalArgs world [] locals (xs.map (qualifyExprF F)) h vs hm ∧
      vs.length = wop.arity ∧
      Heap.Extends hm h' ∧
      ∃ bs : List UInt8, WitnessOpResultRel F wop h' r bs ∧ isValidByteList (bs.map UInt8.toNat) := by
  simp only [compressionOpExpr] at hop
  split at hop
  · next hlen =>
    injection hop with he; subst he
    simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      qualifyName_witnessOp, map_qualifyExprF] at ev
    obtain ⟨vs, hm, eva, hcal⟩ := evalExpr_call_inv ev
    have hvsLen : vs.length = wop.arity := by
      have := evalArgs_length eva
      simp only [List.length_map] at this
      exact this.trans (beq_iff_eq.mp hlen)
    obtain ⟨ext, bs, hrel, hval⟩ := evalFn_witnessOp_sound hsio hkio hvsLen hcal
    exact ⟨vs, hm, eva, hvsLen, ext, bs, hrel, hval⟩
  · cases hop

/-- Per-op function-body backward soundness for `compressionOpBody (.witness wop)`. -/
theorem evalExpr_compressionOpBody_witness_inv {world : World F}
    {wop : WitnessOp}
    (hsio : (wop = .starkReadChannel ∨ wop = .starkReadByteStream) → StarkIOWorld world)
    (hkio : (wop = .kzgReadChannel ∨ wop = .kzgSizedChannel) → KzgIOWorld world)
    {params : List (String × Lower.Ty)} {resultTy : Lower.Ty}
    {args : List (SourceValue F)} {body : Expr}
    (hnd : (params.map Prod.fst).Nodup)
    (hlen : args.length = params.length)
    (hbody : compressionOpBody (.witness wop) params resultTy = some body)
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr world [] ((params.map Prod.fst).zip args) (qualifyExprF F body) h r h') :
    args.length = wop.arity ∧
    Heap.Extends h h' ∧
    ∃ bs : List UInt8, WitnessOpResultRel F wop h' r bs ∧ isValidByteList (bs.map UInt8.toNat) := by
  simp only [compressionOpBody] at hbody
  split at hbody
  · next hpar =>
    injection hbody with he; subst he
    have hlenMap : (params.map Prod.fst).length = args.length := by simp [hlen]
    have hlook : ∀ k v, (k, v) ∈ (params.map Prod.fst).zip args →
        ((params.map Prod.fst).zip args).find? (·.1 == k) = some (k, v) :=
      fun _ _ hm => find_zip_nodup_mem hnd hlenMap hm
    simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      qualifyName_witnessOp, map_qualifyExprF] at ev
    obtain ⟨vals, hm, eva, hcal⟩ := evalExpr_call_inv ev
    have hmapEq : (params.map fun p => vE p.1) = (params.map Prod.fst).map vE := by
      rw [List.map_map]; rfl
    rw [hmapEq] at eva
    have har : args.length = wop.arity := hlen.trans (beq_iff_eq.mp hpar)
    obtain ⟨rfl, rfl⟩ := evalArgs_paramVars_inv hlook hlenMap eva
    obtain ⟨ext, bs, hrel, hval⟩ := evalFn_witnessOp_sound hsio hkio har hcal
    exact ⟨har, ext, bs, hrel, hval⟩
  · cases hbody

end PerOpSoundness

/-! ## Section 4: Whole-Program Backward Simulation for `lowerCompressionOps` (`CompressionIntrinsicWorld`) -/

section WholeProgramBackward

variable {F : Type} [Field F] [DecidableEq F]

/-- Active bindings enabled by `cfg : CompressionConfig` (matching `lowerCompressionOpsCore`). -/
def activeCompressionBindings (cfg : CompressionConfig) : List CompressionBinding :=
  cfg.bindings.filter (fun b => compressionOpEnabled cfg b.op)

/-- Reference-world semantic specification of a single `CompressionBinding` `b` in `wOrig`:
* `.field fop`: ambient prime-field semantic contract (matching `FieldLowerProof.FieldBindingSpec`).
* `.goldilocks gop`: canonical `GLF` / `ExtGL` semantic contract (`GoldilocksOpBodyRel`).
* `.blake3 bop`: call refinement from `Blake3::*` to `Prog::<b.fnName>`.
* `.witness wop`: existential valid byte-stream ingress contract (`WitnessOpResultRel` +
  `Heap.Extends` + `isValidByteList`). -/
def CompressionBindingSpec (wOrig : World F) (b : CompressionBinding) : Prop :=
  hasDoubleColon b.fnName.toList = false ∧
  match b.op with
  | .field fop =>
    if b.dropFirstParam then
      ∀ (pVal : SourceValue F) (xs : List F) (res : F) (h : Heap F),
        fop.eval xs = some res →
        EvalFn wOrig (qualified b.fnName) (pVal :: xs.map .field) h (.field res) h
    else
      ∀ (xs : List F) (res : F) (h : Heap F),
        fop.eval xs = some res →
        EvalFn wOrig (qualified b.fnName) (xs.map .field) h (.field res) h
  | .goldilocks gop =>
    b.dropFirstParam = false ∧
    ∀ (args : List (SourceValue F)) (r : SourceValue F) (h : Heap F),
      GoldilocksOpBodyRel F gop args r →
      EvalFn wOrig (qualified b.fnName) args h r h
  | .blake3 bop =>
    b.dropFirstParam = false ∧
    ∀ (args : List (SourceValue F)) (h h' : Heap F) (r : SourceValue F),
      args.length = bop.arity →
      EvalFn wOrig bop.qualifiedCall args h r h' →
      EvalFn wOrig (qualified b.fnName) args h r h'
  | .witness wop =>
    b.dropFirstParam = false ∧
    ∀ (args : List (SourceValue F)) (h h' : Heap F) (r : SourceValue F) (bs : List UInt8),
      args.length = wop.arity →
      Heap.Extends h h' →
      WitnessOpResultRel F wop h' r bs →
      isValidByteList (bs.map UInt8.toNat) →
      EvalFn wOrig (qualified b.fnName) args h r h'

/-- Demand-gated compression-intrinsic contract world for `lowerCompressionOps`:
each library family's contract is required only when an active binding uses that family. -/
structure CompressionIntrinsicWorld (wOrig : World F) (active : List CompressionBinding) : Prop where
  fieldsIsZero : (∃ b ∈ active, ∃ fop, b.op = .field fop) → FieldsIsZeroSpec wOrig
  goldilocks : (∃ b ∈ active, ∃ gop, b.op = .goldilocks gop) → GoldilocksContracts wOrig
  blake3 : (∃ b ∈ active, ∃ bop, b.op = .blake3 bop) → Blake3Contracts wOrig
  starkIO : (∃ b ∈ active, b.op = .witness .starkReadChannel ∨ b.op = .witness .starkReadByteStream) →
    StarkIOWorld wOrig
  kzgIO : (∃ b ∈ active, b.op = .witness .kzgReadChannel ∨ b.op = .witness .kzgSizedChannel) →
    KzgIOWorld wOrig
  bindings_ok : ∀ b ∈ active, CompressionBindingSpec wOrig b

/-- Convenience constructor supplying all five library contracts unconditionally. -/
theorem CompressionIntrinsicWorld.ofAll {wOrig : World F} {active : List CompressionBinding}
    (hiz : FieldsIsZeroSpec wOrig)
    (hgl : GoldilocksContracts wOrig)
    (hb3 : Blake3Contracts wOrig)
    (hsio : StarkIOWorld wOrig)
    (hkio : KzgIOWorld wOrig)
    (hbind : ∀ b ∈ active, CompressionBindingSpec wOrig b) :
    CompressionIntrinsicWorld wOrig active where
  fieldsIsZero := fun _ => hiz
  goldilocks := fun _ => hgl
  blake3 := fun _ => hb3
  starkIO := fun _ => hsio
  kzgIO := fun _ => hkio
  bindings_ok := hbind

private theorem qualifyName_eq_qualified_of_false {nm : String}
    (h : hasDoubleColon nm.toList = false) :
    qualifyName nm = qualified nm := by
  simp [qualifyName, h]

private theorem evalArgs_lift_forall2 {wOrig : World F} {locals : Environment F Nat} :
    ∀ {xs xs' : List Expr}
      (_hrel : List.Forall₂ (fun x x' =>
        ∀ h h' r,
          EvalExpr wOrig [] locals (qualifyExprF F x') h r h' →
          EvalExpr wOrig [] locals (qualifyExprF F x) h r h') xs xs')
      {h h' : Heap F} {vs : List (SourceValue F)},
      EvalArgs wOrig [] locals (xs'.map (qualifyExprF F)) h vs h' →
      EvalArgs wOrig [] locals (xs.map (qualifyExprF F)) h vs h'
  | [], [], .nil, _, _, _, ev => by cases ev; exact .nil
  | _ :: _, _ :: _, .cons hhd htl, _, _, _, ev => by
    cases ev with
    | cons evhd evtl => exact .cons (hhd _ _ _ evhd) (evalArgs_lift_forall2 htl evtl)

private theorem selectArm_lift_backward {wOrig : World F} {h : Heap F}
    {v : SourceValue F} :
    ∀ {arms arms' : List (Pat × Expr)}
      (_hrel : List.Forall₂ (fun a a' => a.1 = a'.1 ∧
        ∀ bs h1 h2 r,
          EvalExpr wOrig [] bs (qualifyExprF F a'.2) h1 r h2 →
          EvalExpr wOrig [] bs (qualifyExprF F a.2) h1 r h2) arms arms')
      {bs : Environment F Nat} {body' : Aiur.Generic.Expr F},
      SourceSemantics.selectArm wOrig [] h v
        (arms'.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
        .ok (some (bs, body')) →
      ∃ body : Aiur.Generic.Expr F,
        SourceSemantics.selectArm wOrig [] h v
          (arms.map fun a => (qualifyPatF F a.1, qualifyExprF F a.2)) =
          .ok (some (bs, body)) ∧
        ∀ loc h1 h2 r,
          EvalExpr wOrig [] loc body' h1 r h2 →
          EvalExpr wOrig [] loc body h1 r h2
  | [], [], .nil, _, _, hsel => by simp [SourceSemantics.selectArm] at hsel
  | (p1, b1) :: tl, (p2, b2) :: tl', .cons hhd htl, bs, body', hsel => by
    obtain ⟨rfl, hb⟩ := hhd
    simp only [List.map_cons, SourceSemantics.selectArm, bind, Except.bind] at hsel ⊢
    cases hm : wOrig.matchPattern [] h (qualifyPatF F p1) v with
    | error _ => rw [hm] at hsel; cases hsel
    | ok o =>
      rw [hm] at hsel
      cases o with
      | some binds =>
        simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        exact ⟨qualifyExprF F b1, rfl, fun loc h1 h2 r ev => hb loc h1 h2 r ev⟩
      | none => exact selectArm_lift_backward htl hsel

/-- Backward soundness of local call-site intrinsic lowering `lowerCompressionCall`. -/
private theorem evalExpr_lowerCompressionCall_backward {wOrig : World F}
    {bindings : List CompressionBinding} {inlineOps : Bool}
    (hspec : CompressionIntrinsicWorld wOrig bindings)
    {locals : Environment F Nat} {nm : String} {targs : Option (List Lower.Ty)}
    {xs xs' : List Expr}
    (hrel : List.Forall₂ (fun x x' =>
      ∀ h h' r,
        EvalExpr wOrig [] locals (qualifyExprF F x') h r h' →
        EvalExpr wOrig [] locals (qualifyExprF F x) h r h') xs xs')
    {h h' : Heap F} {r : SourceValue F}
    (ev : EvalExpr wOrig [] locals
      (qualifyExprF F (lowerCompressionCall bindings inlineOps nm targs xs xs')) h r h') :
    EvalExpr wOrig [] locals (qualifyExprF F (.call nm targs xs)) h r h' := by
  have hfallback :
      EvalExpr wOrig [] locals (qualifyExprF F (.call nm targs xs')) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF F (.call nm targs xs)) h r h' := by
    intro evc
    simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF] at evc ⊢
    cases evc with
    | call ea ef => exact .call (evalArgs_lift_forall2 hrel ea) ef
  unfold lowerCompressionCall at ev
  by_cases hcond : (inlineOps && targs == some []) = true
  · simp only [hcond, ↓reduceIte] at ev
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨_, rfl⟩ := hcond
    cases hfind : bindings.find? (·.fnName == nm) with
    | none => rw [hfind] at ev; exact hfallback ev
    | some b =>
      rw [hfind] at ev
      have hbMem : b ∈ bindings := List.mem_of_find?_eq_some hfind
      have hbNm : b.fnName = nm := by
        have := List.find?_some hfind
        simpa [beq_iff_eq] using this
      have hbSpec := hspec.bindings_ok b hbMem
      have hqn : qualifyName nm = qualified b.fnName := by
        rw [← hbNm]; exact qualifyName_eq_qualified_of_false hbSpec.1
      have hInst : instanceName [] (qualified b.fnName) (some []) = qualified b.fnName := by
        simp [instanceName, Instance.symbol]
      cases hopB : b.op with
      | goldilocks gop =>
        simp only [CompressionBindingSpec, hopB] at hbSpec
        simp only [hopB] at ev
        by_cases hext : gop.isExt = true
        · simp only [hext, ↓reduceIte] at ev; exact hfallback ev
        · simp only [hext, Bool.false_eq_true, ↓reduceIte] at ev
          cases he : compressionOpExpr (.goldilocks gop) xs' with
          | none => rw [he] at ev; exact hfallback ev
          | some e =>
            rw [he] at ev
            have hgl := hspec.goldilocks ⟨b, hbMem, gop, hopB⟩
            obtain ⟨vs, eva', hglRel⟩ := evalExpr_compressionOp_goldilocks_inv hgl he ev
            have eva := evalArgs_lift_forall2 hrel eva'
            have hfn := hbSpec.2.2 vs r h' (goldilocksOpExprRel_toBodyRel hglRel)
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF, hqn,
              Option.map_some, List.map_nil]
            exact .call eva (by rwa [hInst])
      | field fop =>
        simp only [CompressionBindingSpec, hopB] at hbSpec
        simp only [hopB] at ev
        have hiz := hspec.fieldsIsZero ⟨b, hbMem, fop, hopB⟩
        cases hdrop : b.dropFirstParam
        · simp only [hdrop, Bool.not_false, ↓reduceIte] at ev
          cases he : compressionOpExpr (.field fop) xs' with
          | none => rw [he] at ev; exact hfallback ev
          | some e =>
            rw [he] at ev
            obtain ⟨vs, res, eva', hev, rfl⟩ := evalExpr_fieldOpExpr_inv_field hiz he ev
            have eva := evalArgs_lift_forall2 hrel eva'
            have hfn := hbSpec.2
            simp only [hdrop, Bool.false_eq_true, ↓reduceIte] at hfn
            simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF, hqn,
              Option.map_some, List.map_nil]
            exact .call eva (by rw [hInst]; exact hfn vs res h' hev)
        · simp only [hdrop, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at ev
          cases hrel with
          | nil => exact hfallback ev
          | cons _hhd htl =>
            rename_i hd hd' tl rest'
            cases hd with
            | literal n =>
              dsimp only at ev
              cases he : compressionOpExpr (.field fop) rest' with
              | none => rw [he] at ev; exact hfallback ev
              | some e =>
                rw [he] at ev
                obtain ⟨vs, res, evaRest', hev, rfl⟩ := evalExpr_fieldOpExpr_inv_field hiz he ev
                have evaRest := evalArgs_lift_forall2 htl evaRest'
                have hfn := hbSpec.2
                simp only [hdrop, ↓reduceIte] at hfn
                simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
                  List.map, map_qualifyExprF, hqn, Option.map_some]
                exact .call (.cons .literal evaRest)
                  (by rw [hInst]; exact hfn (.field (n : F)) vs res h' hev)
            | _ => dsimp only at ev; exact hfallback ev
      | blake3 bop =>
        simp only [CompressionBindingSpec, hopB] at hbSpec
        simp only [hopB] at ev
        cases he : compressionOpExpr (.blake3 bop) xs' with
        | none => rw [he] at ev; exact hfallback ev
        | some e =>
          rw [he] at ev
          obtain ⟨vs, hm, eva', hlen, hcal⟩ := evalExpr_compressionOp_blake3_inv he ev
          have eva := evalArgs_lift_forall2 hrel eva'
          have hfn := hbSpec.2.2 vs hm h' r hlen hcal
          simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF, hqn,
            Option.map_some, List.map_nil]
          exact .call eva (by rwa [hInst])
      | witness wop =>
        simp only [CompressionBindingSpec, hopB] at hbSpec
        simp only [hopB] at ev
        cases he : compressionOpExpr (.witness wop) xs' with
        | none => rw [he] at ev; exact hfallback ev
        | some e =>
          rw [he] at ev
          have hsio : (wop = .starkReadChannel ∨ wop = .starkReadByteStream) → StarkIOWorld wOrig :=
            fun hw => hspec.starkIO ⟨b, hbMem, hw.imp
              (fun h1 => hopB.trans (congrArg CompressionOp.witness h1))
              (fun h2 => hopB.trans (congrArg CompressionOp.witness h2))⟩
          have hkio : (wop = .kzgReadChannel ∨ wop = .kzgSizedChannel) → KzgIOWorld wOrig :=
            fun hw => hspec.kzgIO ⟨b, hbMem, hw.imp
              (fun h1 => hopB.trans (congrArg CompressionOp.witness h1))
              (fun h2 => hopB.trans (congrArg CompressionOp.witness h2))⟩
          obtain ⟨vs, hm, eva', hlen, ext, bs, hrelW, hval⟩ :=
            evalExpr_compressionOp_witness_inv hsio hkio he ev
          have eva := evalArgs_lift_forall2 hrel eva'
          have hfn := hbSpec.2.2 vs hm h' r bs hlen ext hrelW hval
          simp only [qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map, map_qualifyExprF, hqn,
            Option.map_some, List.map_nil]
          exact .call eva (by rwa [hInst])
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at ev
    exact hfallback ev

mutual

/-- **Core Expression Backward Simulation for `lowerCompressionExpr`**:
any `EvalExpr` derivation of `lowerCompressionExpr bindings inlineOps e` in `wOrig`
lifts back to `EvalExpr` of `e` in `wOrig`. -/
theorem evalExpr_lowerCompressionExpr_backward {wOrig : World F}
    {bindings : List CompressionBinding} {inlineOps : Bool}
    (hspec : CompressionIntrinsicWorld wOrig bindings) :
    ∀ (e : Expr) (locals : Environment F Nat) (h h' : Heap F) (r : SourceValue F),
      EvalExpr wOrig [] locals
        (qualifyExprF F (lowerCompressionExpr bindings inlineOps e)) h r h' →
      EvalExpr wOrig [] locals (qualifyExprF F e) h r h'
  | .call nm targs xs, locals, h, h', r, ev =>
    evalExpr_lowerCompressionCall_backward hspec
      (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ev
  | .tuple xs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | tuple ea =>
      exact .tuple (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ea)
  | .array xs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | array ea =>
      exact .array (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ea)
  | .construct ty targs nm xs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | construct ea =>
      exact .construct (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ea)
  | .constructAs ty targs nm xs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | constructAs ea =>
      exact .constructAs (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ea)
  | .record ty fs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | record ea =>
      exact .record (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec fs locals) ea)
  | .update ty fs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | update ea hu =>
      exact .update (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec fs locals) ea) hu
  | .builtin op xs, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyExprF] at ev ⊢
    cases ev with
    | builtin ea ha =>
      exact .builtin (evalArgs_lift_forall2 (evalExpr_lowerCompressionExprList_forall2 hspec xs locals) ea) ha
  | .repeat x n, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | «repeat» evx => exact .«repeat» (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx)
  | .index x i, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | index evx hp => exact .index (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hp
  | .slice x a b, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | slice evx hs => exact .slice (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hs
  | .member x f, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | member evx hm => exact .member (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hm
  | .project x i, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | project evx hp => exact .project (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hp
  | .store x, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | store evx => exact .store (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx)
  | .load x, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | load evx hl => exact .load (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hl
  | .hint ty x ch, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | hint evx ht => exact .hint (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) ht
  | .neg x, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | neg evx ho => exact .neg (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) ho
  | .binary op x y, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | binary evl evr ho =>
      exact .binary (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evl)
        (evalExpr_lowerCompressionExpr_backward hspec y locals _ _ _ evr) ho
  | .letValue pat x b, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map] at ev ⊢
    cases ev with
    | letValue evx hm evb =>
      exact .letValue (evalExpr_lowerCompressionExpr_backward hspec x locals _ _ _ evx) hm
        (evalExpr_lowerCompressionExpr_backward hspec b _ _ _ _ evb)
  | .matchValue s arms, locals, h, h', r, ev => by
    simp only [lowerCompressionExpr, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
      map_qualifyArmsF] at ev ⊢
    cases ev with
    | matchValue evs hsel evbr =>
      obtain ⟨body, hsel', hbr⟩ :=
        selectArm_lift_backward (evalExpr_lowerCompressionArms_forall2 hspec arms) hsel
      exact .matchValue (evalExpr_lowerCompressionExpr_backward hspec s locals _ _ _ evs)
        hsel' (hbr _ _ _ _ evbr)
  | .literal _, _, _, _, _, ev => ev
  | .var _, _, _, _, _, ev => ev
  | .global _ _, _, _, _, _, ev => ev
  | .control _ _, _, _, _, _, ev => ev

theorem evalExpr_lowerCompressionExprList_forall2 {wOrig : World F}
    {bindings : List CompressionBinding} {inlineOps : Bool}
    (hspec : CompressionIntrinsicWorld wOrig bindings) :
    ∀ (xs : List Expr) (locals : Environment F Nat),
      List.Forall₂ (fun x x' =>
        ∀ h h' r,
          EvalExpr wOrig [] locals (qualifyExprF F x') h r h' →
          EvalExpr wOrig [] locals (qualifyExprF F x) h r h')
        xs (lowerCompressionExprList bindings inlineOps xs)
  | [], _ => .nil
  | x :: xs, locals =>
    .cons (fun h h' r ev => evalExpr_lowerCompressionExpr_backward hspec x locals h h' r ev)
      (evalExpr_lowerCompressionExprList_forall2 hspec xs locals)

theorem evalExpr_lowerCompressionArms_forall2 {wOrig : World F}
    {bindings : List CompressionBinding} {inlineOps : Bool}
    (hspec : CompressionIntrinsicWorld wOrig bindings) :
    ∀ (arms : List (Pat × Expr)),
      List.Forall₂ (fun a a' => a.1 = a'.1 ∧
        ∀ bs h1 h2 r,
          EvalExpr wOrig [] bs (qualifyExprF F a'.2) h1 r h2 →
          EvalExpr wOrig [] bs (qualifyExprF F a.2) h1 r h2)
        arms (lowerCompressionArms bindings inlineOps arms)
  | [] => .nil
  | (_, b) :: rest =>
    .cons ⟨rfl, fun bs h1 h2 r ev => evalExpr_lowerCompressionExpr_backward hspec b bs h1 h2 r ev⟩
      (evalExpr_lowerCompressionArms_forall2 hspec rest)

end

/-- Function-level backward simulation for `lowerCompressionFn`. -/
theorem evalExpr_lowerCompressionFn_backward {wOrig : World F}
    {bindings : List CompressionBinding} {inlineOps : Bool}
    (hspec : CompressionIntrinsicWorld wOrig bindings)
    {f : Fn}
    (hOrigHas : WorldHasFn wOrig (qualified f.name) (f.params.map Prod.fst) (qualifyExprF F f.body))
    (hOrigPlain : isPlainExpr f.body = true)
    (hnd : (f.params.map Prod.fst).Nodup)
    {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (hlen : args.length = f.params.length)
    (ev : EvalExpr wOrig [] ((f.params.map Prod.fst).zip args)
      (qualifyExprF F (lowerCompressionFn bindings inlineOps f).body) h r h') :
    EvalExpr wOrig [] ((f.params.map Prod.fst).zip args) (qualifyExprF F f.body) h r h' := by
  have hplainQ : isPlainExpr (qualifyExprF F f.body) = true := by
    rw [isPlainExpr_qualifyExprF]; exact hOrigPlain
  unfold lowerCompressionFn at ev
  cases hfind : bindings.find? (·.fnName == f.name) with
  | none =>
    rw [hfind] at ev
    exact evalExpr_lowerCompressionExpr_backward hspec f.body _ h h' r ev
  | some b =>
    rw [hfind] at ev
    dsimp only at ev
    by_cases htp : f.typeParams.isEmpty = true
    · simp only [htp, ↓reduceIte] at ev
      cases hbody : compressionOpBody b.op
          (if b.dropFirstParam then f.params.drop 1 else f.params) f.result with
      | none =>
        rw [hbody] at ev
        exact evalExpr_lowerCompressionExpr_backward hspec f.body _ h h' r ev
      | some body' =>
        rw [hbody] at ev
        have hbMem : b ∈ bindings := List.mem_of_find?_eq_some hfind
        have hbNm : b.fnName = f.name := by
          have := List.find?_some hfind
          simpa [beq_iff_eq] using this
        have hbSpec := hspec.bindings_ok b hbMem
        cases hopB : b.op with
        | field fop =>
          simp only [CompressionBindingSpec, hopB] at hbSpec
          simp only [hopB] at hbody
          have hiz := hspec.fieldsIsZero ⟨b, hbMem, fop, hopB⟩
          have hbodyF : fieldOpBody fop
              (if b.dropFirstParam then (f.params.map Prod.fst).drop 1 else f.params.map Prod.fst) =
              some body' := by
            cases hdrop : b.dropFirstParam
            · simp only [hdrop, Bool.false_eq_true, ↓reduceIte, compressionOpBody] at hbody ⊢
              split at hbody
              · exact hbody
              · cases hbody
            · simp only [hdrop, ↓reduceIte, compressionOpBody, List.map_drop] at hbody ⊢
              split at hbody
              · exact hbody
              · cases hbody
          obtain ⟨xs, res, hargs, hev, rfl, rfl⟩ :=
            evalExpr_fieldOpBody_inv_field hiz hnd (by simpa using hlen) hbodyF ev
          have hfnOrig : EvalFn wOrig (qualified f.name) args h' (.field res) h' := by
            rw [← hbNm]
            have h2 := hbSpec.2
            cases hdrop : b.dropFirstParam
            · simp only [hdrop, Bool.false_eq_true, ↓reduceIte] at hargs h2
              rw [hargs]; exact h2 xs res h' hev
            · simp only [hdrop, ↓reduceIte] at hargs h2
              obtain ⟨pVal, rfl⟩ := hargs; exact h2 pVal xs res h' hev
          exact (evalFn_plain_inv hOrigHas hplainQ hfnOrig).2
        | goldilocks gop =>
          simp only [CompressionBindingSpec, hopB] at hbSpec
          simp only [hopB] at hbody
          have hdropF : b.dropFirstParam = false := hbSpec.2.1
          simp only [hdropF, Bool.false_eq_true, ↓reduceIte] at hbody
          have hgl := hspec.goldilocks ⟨b, hbMem, gop, hopB⟩
          obtain ⟨hglRel, rfl⟩ :=
            evalExpr_compressionOpBody_goldilocks_inv hgl hnd hlen hbody ev
          have hfnOrig : EvalFn wOrig (qualified f.name) args h' r h' := by
            rw [← hbNm]; exact hbSpec.2.2 args r h' hglRel
          exact (evalFn_plain_inv hOrigHas hplainQ hfnOrig).2
        | blake3 bop =>
          simp only [CompressionBindingSpec, hopB] at hbSpec
          simp only [hopB] at hbody
          have hdropF : b.dropFirstParam = false := hbSpec.2.1
          simp only [hdropF, Bool.false_eq_true, ↓reduceIte, compressionOpBody] at hbody
          split at hbody
          · next hpar =>
            injection hbody with he; subst he
            have hlenMap : (f.params.map Prod.fst).length = args.length := by simp [hlen]
            have hlook : ∀ k v, (k, v) ∈ (f.params.map Prod.fst).zip args →
                ((f.params.map Prod.fst).zip args).find? (·.1 == k) = some (k, v) :=
              fun _ _ hm => find_zip_nodup_mem hnd hlenMap hm
            simp only [callE, qualifyExprF, qualifyExpr, Aiur.Generic.Expr.map,
              qualifyName_blake3Op, map_qualifyExprF] at ev
            obtain ⟨vals, hm, eva, hcal⟩ := evalExpr_call_inv ev
            have hmapEq : (f.params.map fun p => vE p.1) = (f.params.map Prod.fst).map vE := by
              rw [List.map_map]; rfl
            rw [hmapEq] at eva
            have har : args.length = bop.arity := hlen.trans (beq_iff_eq.mp hpar)
            obtain ⟨rfl, rfl⟩ := evalArgs_paramVars_inv hlook hlenMap eva
            have hfnOrig : EvalFn wOrig (qualified f.name) vals hm r h' := by
              rw [← hbNm]; exact hbSpec.2.2 vals hm h' r har hcal
            exact (evalFn_plain_inv hOrigHas hplainQ hfnOrig).2
          · cases hbody
        | witness wop =>
          simp only [CompressionBindingSpec, hopB] at hbSpec
          simp only [hopB] at hbody
          have hdropF : b.dropFirstParam = false := hbSpec.2.1
          simp only [hdropF, Bool.false_eq_true, ↓reduceIte] at hbody
          have hsio : (wop = .starkReadChannel ∨ wop = .starkReadByteStream) → StarkIOWorld wOrig :=
            fun hw => hspec.starkIO ⟨b, hbMem, hw.imp
              (fun h1 => hopB.trans (congrArg CompressionOp.witness h1))
              (fun h2 => hopB.trans (congrArg CompressionOp.witness h2))⟩
          have hkio : (wop = .kzgReadChannel ∨ wop = .kzgSizedChannel) → KzgIOWorld wOrig :=
            fun hw => hspec.kzgIO ⟨b, hbMem, hw.imp
              (fun h1 => hopB.trans (congrArg CompressionOp.witness h1))
              (fun h2 => hopB.trans (congrArg CompressionOp.witness h2))⟩
          obtain ⟨har, ext, bs, hrelW, hval⟩ :=
            evalExpr_compressionOpBody_witness_inv hsio hkio hnd hlen hbody ev
          have hfnOrig : EvalFn wOrig (qualified f.name) args h r h' := by
            rw [← hbNm]; exact hbSpec.2.2 args h h' r bs har ext hrelW hval
          exact (evalFn_plain_inv hOrigHas hplainQ hfnOrig).2
    · simp only [htp, Bool.false_eq_true, ↓reduceIte] at ev
      exact evalExpr_lowerCompressionExpr_backward hspec f.body _ h h' r ev

private theorem lowerCompressionFn_name_params (bindings : List CompressionBinding)
    (inlineOps : Bool) (f : Fn) :
    (lowerCompressionFn bindings inlineOps f).name = f.name ∧
    (lowerCompressionFn bindings inlineOps f).params = f.params := by
  unfold lowerCompressionFn
  cases bindings.find? (·.fnName == f.name) with
  | none => exact ⟨rfl, rfl⟩
  | some b =>
    dsimp only
    split
    · split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- **Program-Level Backward Soundness for `lowerCompressionOpsCore`** over arbitrary
`[Field F] [DecidableEq F]`: every `EvalFn` derivation in the compression-lowered world
`wOpt` simulates backward to `EvalFn` in the pre-intrinsic world `wOrig`. -/
theorem lowerCompressionOpsCore_backward {wOpt wOrig : World F}
    {cfg : CompressionConfig} {fns : List Fn}
    (haux : SameAuxWorld wOpt wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hOptHas : WorldHasFns wOpt (lowerCompressionOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExt : ∀ nm args res,
      (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
      wOpt.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg))
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wOpt nm args h r h') :
    EvalFn wOrig nm args h r h' := by
  unfold lowerCompressionOpsCore at hOptHas hExt
  dsimp only at hOptHas hExt
  by_cases hempty : (activeCompressionBindings cfg).isEmpty = true
  · have he : (cfg.bindings.filter (fun b => compressionOpEnabled cfg b.op)).isEmpty = true := hempty
    simp only [he, ↓reduceIte] at hOptHas hExt
    have hsub : WorldSub wOpt wOrig := by
      refine ⟨haux, fun nm' args' res hprep => ?_⟩
      by_cases hex : ∃ f ∈ fns, qualified f.name = nm'
      · obtain ⟨f, hf, rfl⟩ := hex
        rcases res with ⟨types, locals, body⟩
        obtain ⟨rfl, hlen, rfl, rfl⟩ := hOptHas f hf args' types locals body hprep
        exact hOrigProv f hf args' hlen
      · exact hExt nm' args' res (fun f hf heq => hex ⟨f, hf, heq⟩) hprep
    exact evalFn_of_worldSub hsub ev
  · have he : (cfg.bindings.filter (fun b => compressionOpEnabled cfg b.op)).isEmpty = false :=
      Bool.eq_false_iff.mpr hempty
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hOptHas hExt
    set active := activeCompressionBindings cfg
    have hrel : List.Forall₂ (fun f f' => f'.name = f.name ∧ f'.params = f.params)
        fns (fns.map (lowerCompressionFn active cfg.inlineOps)) := by
      rw [List.forall₂_map_right_iff]
      exact List.forall₂_same.mpr fun f _ => lowerCompressionFn_name_params active cfg.inlineOps f
    have hPlainOpt : ∀ f' ∈ fns.map (lowerCompressionFn active cfg.inlineOps),
        isPlainExpr f'.body = true := by
      intro f' hf'
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
      exact lowerCompressionFn_plain active cfg.inlineOps (hPlain f hf)
    have hUnique : ∀ f g, f ∈ fns → g ∈ fns → f.name = g.name → f = g := by
      clear hrel hPlainOpt hOptHas hOrigHas hOrigProv hExt hspec ev haux hndParams hPlain hempty he
      induction fns with
      | nil => intro _ _ hf; cases hf
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
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf'
    have hgnm : g.name = f.name :=
      (lowerCompressionFn_name_params active cfg.inlineOps g).1.symm.trans hnm
    have hgf : g = f := hUnique g f hg hf hgnm
    subst hgf
    exact evalExpr_lowerCompressionFn_backward hspec (hOrigHas g hg) (hPlain g hg)
      (hndParams g hg) hlen evBody

/-- **End-to-End Whole-Program Backward Soundness for `lowerCompressionOps` + `pruneUnreachable`**
over arbitrary `[Field F] [DecidableEq F]`:
composes `InlineFuseProof.pruneUnreachable_backward` with `lowerCompressionOpsCore_backward`,
simulating every `EvalFn` derivation in the final pruned compression-lowered world `wPruned`
back to `EvalFn` in the pre-intrinsic world `wOrig`. -/
theorem lowerCompressionOps_backward {wPruned wMid wOrig : World F}
    {cfg : CompressionConfig} {fns : List Fn}
    (hauxPM : SameAuxWorld wPruned wMid)
    (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerCompressionOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerCompressionOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerCompressionOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns)
    (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerCompressionOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg))
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' := by
  have evMid : EvalFn wMid nm args h r h' := by
    unfold lowerCompressionOps at hPrunedHas hExtPM
    cases hroots : cfg.pruneRoots with
    | none =>
      rw [hroots] at hPrunedHas hExtPM
      have hsub : WorldSub wPruned wMid := by
        refine ⟨hauxPM, fun nm' args' res hprep => ?_⟩
        by_cases hex : ∃ f ∈ lowerCompressionOpsCore cfg fns, qualified f.name = nm'
        · obtain ⟨f, hf, rfl⟩ := hex
          rcases res with ⟨types, locals, body⟩
          obtain ⟨rfl, hlen, rfl, rfl⟩ := hPrunedHas f hf args' types locals body hprep
          exact hMidProv f hf args' hlen
        · exact hExtPM nm' args' res (fun f hf heq => hex ⟨f, hf, heq⟩) hprep
      exact evalFn_of_worldSub hsub ev
    | some roots =>
      rw [hroots] at hPrunedHas hExtPM
      exact pruneUnreachable_backward hauxPM hPrunedHas hMidProv hExtPM ev
  exact lowerCompressionOpsCore_backward hauxMO hndNames hndParams hPlain
    hMidHas hOrigHas hOrigProv hExtMO hspec evMid

end WholeProgramBackward

/-! ### Concrete 3-Field Whole-Program Corollaries (`Goldilocks`, `BN254`, `BLS12-381`) -/

section ThreeFieldLowerBackward

/-- End-to-end backward simulation for `lowerCompressionOps` instantiated at **Goldilocks (`p_G`)**. -/
theorem lowerCompressionOps_backward_goldilocks
    {wPruned wMid wOrig : World GLF} {cfg : CompressionConfig} {fns : List Fn}
    (hauxPM : SameAuxWorld wPruned wMid) (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerCompressionOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerCompressionOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerCompressionOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerCompressionOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg))
    {nm : String} {args : List (SourceValue GLF)} {h h' : Heap GLF} {r : SourceValue GLF}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerCompressionOps_backward hauxPM hauxMO hndNames hndParams hPlain
    hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

/-- End-to-end backward simulation for `lowerCompressionOps` instantiated at **BN254 (`Fr`)**. -/
theorem lowerCompressionOps_backward_bn254
    {wPruned wMid wOrig : World Aiur.Library.Field.BN254.F}
    {cfg : CompressionConfig} {fns : List Fn}
    (hauxPM : SameAuxWorld wPruned wMid) (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerCompressionOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerCompressionOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerCompressionOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerCompressionOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg))
    {nm : String} {args : List (SourceValue Aiur.Library.Field.BN254.F)}
    {h h' : Heap Aiur.Library.Field.BN254.F} {r : SourceValue Aiur.Library.Field.BN254.F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerCompressionOps_backward hauxPM hauxMO hndNames hndParams hPlain
    hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

/-- End-to-end backward simulation for `lowerCompressionOps` instantiated at **BLS12-381 (`Fr`)**. -/
theorem lowerCompressionOps_backward_bls12381
    {wPruned wMid wOrig : World Aiur.Library.Field.BLS12381.F}
    {cfg : CompressionConfig} {fns : List Fn}
    (hauxPM : SameAuxWorld wPruned wMid) (hauxMO : SameAuxWorld wMid wOrig)
    (hndNames : (fns.map (·.name)).Nodup)
    (hndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup)
    (hPlain : ∀ f ∈ fns, isPlainExpr f.body = true)
    (hPrunedHas : WorldHasFns wPruned (lowerCompressionOps cfg fns))
    (hMidHas : WorldHasFns wMid (lowerCompressionOpsCore cfg fns))
    (hMidProv : WorldProvidesFns wMid (lowerCompressionOpsCore cfg fns))
    (hOrigHas : WorldHasFns wOrig fns) (hOrigProv : WorldProvidesFns wOrig fns)
    (hExtPM : ∀ nm args res,
      (∀ f ∈ lowerCompressionOps cfg fns, qualified f.name ≠ nm) →
      wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res)
    (hExtMO : ∀ nm args res,
      (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
      wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res)
    (hspec : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg))
    {nm : String} {args : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    {h h' : Heap Aiur.Library.Field.BLS12381.F} {r : SourceValue Aiur.Library.Field.BLS12381.F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerCompressionOps_backward hauxPM hauxMO hndNames hndParams hPlain
    hPrunedHas hMidHas hMidProv hOrigHas hOrigProv hExtPM hExtMO hspec ev

end ThreeFieldLowerBackward

/-! ## Section 5: Top-Level Composition (`CompressionCert`, `aliasEntry_sound`, `CompiledCert`/`TypedClaim`, `WitnessIO`) -/

section EndToEndCompression

open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.CompiledCert (ArtifactKind)
open IxCC.AiurBackend.TypedRep (Rep)
open IxCC.AiurBackend.TypedLower (LoweredProgram)
open IxCC.AiurBackend.TypedWorld (checkTypedWorld)
open IxCC.AiurBackend.TypedBackward (natCoreProgram)
open IxCC.AiurBackend.TypedClaim (typed_entry_source_sound_checked result_fieldNat)
open IxCC.AiurBackend.Claim (Accepted obs_nat)
open IxCC.AiurBackend.Progress (checkShape neverStuck_of_checkShape)

/-! ### 5.1 Multi-Field Characteristic, `natLimit`, and `checkCompressionWorld` Lemmas -/

/-- Goldilocks (`p_G`) satisfies the depth-pass characteristic bound `0 < n ≤ 2^39 * 2^24 → n ≠ 0`. -/
theorem depth_characteristic_goldilocks :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : GLF) ≠ 0 :=
  Aiur.Optimized.Depth.goldilocks_characteristic

/-- BN254 `Fr` satisfies the depth-pass characteristic bound `0 < n ≤ 2^39 * 2^24 → n ≠ 0`. -/
theorem depth_characteristic_bn254 :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : Aiur.Library.Field.BN254.F) ≠ 0 :=
  emulatedGLBounds_bn254.depth_characteristic

/-- BLS12-381 `Fr` satisfies the depth-pass characteristic bound `0 < n ≤ 2^39 * 2^24 → n ≠ 0`. -/
theorem depth_characteristic_bls12381 :
    ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : Aiur.Library.Field.BLS12381.F) ≠ 0 :=
  emulatedGLBounds_bls12381.depth_characteristic

/-- `natLimit = 2^56 ≤ p_G`. -/
theorem natLimit_le_goldilocks : natLimit ≤ Aiur.Library.U32.Goldilocks.modulus := by
  unfold natLimit Aiur.Library.U32.Goldilocks.modulus; norm_num

/-- `natLimit = 2^56 ≤ BN254 Fr`. -/
theorem natLimit_le_bn254 : natLimit ≤ Aiur.Library.Field.BN254.modulus := by
  unfold natLimit Aiur.Library.Field.BN254.modulus; norm_num

/-- `natLimit = 2^56 ≤ BLS12-381 Fr`. -/
theorem natLimit_le_bls12381 : natLimit ≤ Aiur.Library.Field.BLS12381.modulus := by
  unfold natLimit Aiur.Library.Field.BLS12381.modulus; norm_num

/-- General `ZMod p` canonical-cast recovery for naturals strictly below `natLimit ≤ p`. -/
theorem val_natCast_lt_zmod {p : Nat} [Fact (Nat.Prime p)] (hp : natLimit ≤ p)
    {n : Nat} (hn : n < natLimit) : ((n : ZMod p)).val = n :=
  ZMod.val_cast_of_lt (Nat.lt_of_lt_of_le hn hp)

/-- General `ZMod p` list-argument recovery (polymorphic counterpart of `Claim.vals_of_fields`). -/
theorem vals_of_fields_zmod {p : Nat} [Fact (Nat.Prime p)] (hp : natLimit ≤ p) :
    ∀ {as : List (ZMod p)} {ns : List Nat},
      (∀ n ∈ ns, n < natLimit) →
      as.map (Value.field : ZMod p → SourceValue (ZMod p)) = ns.map (fun n => .field (n : ZMod p)) →
      as.map ZMod.val = ns
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, n :: ns, hn, h => by
    simp only [List.map_cons, List.cons.injEq, Value.field.injEq] at h
    obtain ⟨rfl, htl⟩ := h
    rw [List.map_cons, val_natCast_lt_zmod hp (hn n List.mem_cons_self),
      vals_of_fields_zmod hp (fun m hm => hn m (List.mem_cons_of_mem _ hm)) htl]

/-- Decomposition of `CompressionIntrinsics.checkCompressionWorld`: extracts the alias check
and demand-gated `Blake3` / `StarkIO` / `KzgIO` library world checks. -/
theorem checkCompressionWorld_sound {F : Type} [Field F] [DecidableEq F]
    {s : Aiur.Generic.Source F} {lp : LoweredProgram} {aliasSpec? : Option AliasSpec}
    (h : checkCompressionWorld s lp aliasSpec? = true) :
    (∀ spec, aliasSpec? = some spec → checkAliasEntry s spec = true) ∧
    (usesBlake3Library lp.program.functions = true → checkBlake3World s = true) ∧
    (usesStarkIOLibrary lp.program.functions = true → checkStarkIOFunctions s = true) ∧
    (usesKzgIOLibrary lp.program.functions = true → checkKzgIOFunctions s = true) := by
  unfold checkCompressionWorld at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hAlias, hB3⟩, hSIO⟩, hKIO⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro spec hEq; rw [hEq] at hAlias; exact hAlias
  · intro hu
    rcases hB3 with h0 | h1
    · exact absurd hu (by simp [h0])
    · exact h1
  · intro hu
    rcases hSIO with h0 | h1
    · exact absurd hu (by simp [h0])
    · exact h1
  · intro hu
    rcases hKIO with h0 | h1
    · exact absurd hu (by simp [h0])
    · exact h1

/-! ### 5.2 Structural Lowering Bridge (`CompressionLowerBridge`) -/

/-- Bundles the structural world correspondence connecting a final pruned compression-lowered
world `wPruned` back through its unpruned intermediate world `wMid` to the pre-intrinsic
`TypedLower` world `wOrig` under `CompressionIntrinsicWorld`. -/
structure CompressionLowerBridge {F : Type} [Field F] [DecidableEq F]
    (wPruned : World F) (cfg : CompressionConfig) (fns : List Fn) (wOrig : World F) where
  wMid : World F
  auxPM : SameAuxWorld wPruned wMid
  auxMO : SameAuxWorld wMid wOrig
  ndNames : (fns.map (·.name)).Nodup
  ndParams : ∀ f ∈ fns, (f.params.map Prod.fst).Nodup
  plain : ∀ f ∈ fns, isPlainExpr f.body = true
  prunedHas : WorldHasFns wPruned (lowerCompressionOps cfg fns)
  midHas : WorldHasFns wMid (lowerCompressionOpsCore cfg fns)
  midProv : WorldProvidesFns wMid (lowerCompressionOpsCore cfg fns)
  origHas : WorldHasFns wOrig fns
  origProv : WorldProvidesFns wOrig fns
  extPM : ∀ nm args res,
    (∀ f ∈ lowerCompressionOps cfg fns, qualified f.name ≠ nm) →
    wPruned.prepare nm args = .ok res → wMid.prepare nm args = .ok res
  extMO : ∀ nm args res,
    (∀ f' ∈ lowerCompressionOpsCore cfg fns, qualified f'.name ≠ nm) →
    wMid.prepare nm args = .ok res → wOrig.prepare nm args = .ok res
  intrinsicWorld : CompressionIntrinsicWorld wOrig (activeCompressionBindings cfg)

/-- Lift any `EvalFn` derivation across a `CompressionLowerBridge`. -/
theorem CompressionLowerBridge.backward {F : Type} [Field F] [DecidableEq F]
    {wPruned wOrig : World F} {cfg : CompressionConfig} {fns : List Fn}
    (bridge : CompressionLowerBridge wPruned cfg fns wOrig)
    {nm : String} {args : List (SourceValue F)} {h h' : Heap F} {r : SourceValue F}
    (ev : EvalFn wPruned nm args h r h') :
    EvalFn wOrig nm args h r h' :=
  lowerCompressionOps_backward bridge.auxPM bridge.auxMO bridge.ndNames bridge.ndParams
    bridge.plain bridge.prunedHas bridge.midHas bridge.midProv bridge.origHas bridge.origProv
    bridge.extPM bridge.extMO bridge.intrinsicWorld ev

/-! ### 5.3 Multi-Field Compression Artifact Certificate (`CompressionCert`) -/

/-- **Certified compression artifact (`CompressionCert`)** over an arbitrary prime field `F`:
extends `CompiledCert.TypedCert` to multi-field compression-intrinsic programs lowered by
`lowerCompressionProgram`, linked with `linkedProgramWith`, and optionally exported under
a custom `--entry-name` / `--assert-ok` wrapper via `aliasEntry` (such as
`CompressWrap::verify_root`, `CompressGL::verify_root`, `CompressNarrowFixed::step_v1`,
or `CompressFinalNarrow::verify_accumulator_v1`). -/
structure CompressionCert {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F}
    (prepared : Aiur.Modules.Prepared moduleProg) (entryIdx : Nat) where
  lowered : TypedLower.lowerProgram P shapeCert sched = .ok lp
  natCoreOk : natCoreProgram P shapeCert = true
  compEq : lpComp = lowerCompressionProgram compCfg lp
  aliasSpec : AliasSpec
  targetEntryEq : aliasSpec.targetEntry = qualified (entryName entryIdx)
  identityOk : aliasSpec.hasWrapper = false →
    aliasSpec.entry = aliasSpec.targetEntry ∧ aliasSpec.assertOk = false
  compressionWorldOk :
    checkCompressionWorld prepared.environment.source lpComp (some aliasSpec) = true
  id : String → Except String Nat
  compiled : Aiur.Optimized.ModulesArtifact prepared
  physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact
  dcfg : Aiur.Optimized.Depth.Config
  measures : Aiur.Optimized.Depth.Structural.Plan
  plan : Aiur.Optimized.Grouping.Plan
    (Aiur.Optimized.Depth.system dcfg physical.system) id
  depthPlanOk : physical.checkDepthPlan compiled.circuit.inlined.program dcfg measures plan = true
  external : String
  entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances
  selected : prepared.find? external = some entry
  entryNameEq : entry.resolved.name = aliasSpec.entry
  artifactKind : ArtifactKind
  artifactBytes : ByteArray
  artifactDigest : Ixon.Address
  digestEq : artifactDigest = Ixon.Address.blake3Pure artifactBytes

/-- **Stage 1 (`checkMemo` → `EvalFn` at the aliased entry)**:
any weighted trace rows accepted by `cert.plan.checkMemo` yield a source-level `EvalFn`
derivation at `cert.aliasSpec.entry` in `prepared.environment.source.world`. -/
theorem CompressionCert.evalFn_entry_of_checkMemo {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Aiur.Value F}
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues args))
    (decoded : output.decode cert.compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue F) (heap : Heap F),
      EvalFn prepared.environment.source.world cert.aliasSpec.entry args [] value heap ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM cert.compiled.circuit.system rom).decode
        cert.compiled.specialized.program.enums) heap value result := by
  obtain ⟨certified, bits, activated⟩ :=
    Aiur.Optimized.Physical.Prepared.checkDepthPlan_sound cert.depthPlanOk
  obtain ⟨value, heap, hevalMod, hrep⟩ :=
    prepared.depth_grouped_activated_heap_sound cert.compiled cert.physical certified bits
      cert.plan activated cert.selected valid signed rooted outside bound characteristic
      checked arguments decoded
  obtain ⟨entry', hsel', hevalFn⟩ := hevalMod
  rw [cert.selected, Option.some.injEq] at hsel'
  subst hsel'
  rw [cert.entryNameEq] at hevalFn
  exact ⟨value, heap, hevalFn, hrep⟩

/-- **Stage 2 (`checkMemo` + `aliasEntry_sound_of_check` → `EvalFn` at `Prog::main<i>`)**:
unwraps custom `--entry-name` / `--assert-ok` aliasing (or identity export) directly to
`EvalFn` of `Prog::main<i>` in `prepared.environment.source.world`. -/
theorem CompressionCert.evalFn_target_of_checkMemo {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {args : List (SourceValue F)} {result : Aiur.Value F}
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues args))
    (decoded : output.decode cert.compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue F) (heap : Heap F),
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM cert.compiled.circuit.system rom).decode
        cert.compiled.specialized.program.enums) heap value result ∧
      if cert.aliasSpec.assertOk then
        value = .tuple [] ∧
        EvalFn prepared.environment.source.world (qualified (entryName i)) args [] (.field 1) heap
      else
        EvalFn prepared.environment.source.world (qualified (entryName i)) args [] value heap := by
  obtain ⟨value, heap, hevEntry, hrep⟩ :=
    cert.evalFn_entry_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  have hAliasChk : checkAliasEntry prepared.environment.source cert.aliasSpec = true :=
    (checkCompressionWorld_sound cert.compressionWorldOk).1 cert.aliasSpec rfl
  cases hWrap : cert.aliasSpec.hasWrapper with
  | true =>
    have hSound := aliasEntry_sound_of_check hWrap hAliasChk hevEntry
    rw [cert.targetEntryEq] at hSound
    exact ⟨value, heap, hrep, hSound⟩
  | false =>
    obtain ⟨hEntEq, hAssFalse⟩ := cert.identityOk hWrap
    rw [hEntEq, cert.targetEntryEq] at hevEntry
    refine ⟨value, heap, hrep, ?_⟩
    simp only [hAssFalse, Bool.false_eq_true, ↓reduceIte]
    exact hevEntry

/-! ### 5.4 End-to-End Source Soundness & Existential Witness-Stream Theorems -/

/-- **Headline End-to-End Theorem (`--assert-ok` Aliased Compression Entry → Source `Nat 1`)**
over arbitrary prime `ZMod p` (`[Fact (Nat.Prime p)]`):
composes `cert.plan.checkMemo = .ok ()` → `depth_grouped_activated_heap_sound` →
`aliasEntry_sound_of_check` → `lowerCompressionOps_backward` →
`TypedClaim.typed_entry_source_sound_checked` + `Progress.checkShape` (escape-free!),
recovering that the checked Lean/Ix source evaluator returns `Nat 1` on `as.map ZMod.val`. -/
theorem CompressionCert.accepted_assertOk_source {p : Nat} [Fact (Nat.Prime p)]
    (fc : FieldCompatible64 (ZMod p))
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : ZMod p) ≠ 0)
    (hnat : natLimit ≤ p)
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program (ZMod p)} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source (ZMod p)}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List (ZMod p)}
    {rom : Aiur.WidthROM (ZMod p)} (valid : rom.Valid)
    {wires : List (Aiur.WireValue (ZMod p))} {output : Aiur.WireValue (ZMod p)}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message (ZMod p)}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow (ZMod p))} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1) := by
  obtain ⟨_, heap, _, hTarget⟩ :=
    cert.evalFn_target_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  simp only [hAssert, ↓reduceIte] at hTarget
  have evOrig : EvalFn sOrig.world (qualified (entryName i))
      (as.map (Value.field : ZMod p → SourceValue (ZMod p))) [] (.field 1) heap :=
    bridge.backward hTarget.2
  have hnsPred : ∀ ns : List Nat,
      as.map (Value.field : ZMod p → SourceValue (ZMod p)) =
        ns.map (fun n => .field (n : ZMod p)) →
      Compose.NeverStuck ⟨f.src, f.checked⟩ (i, ns) := by
    intro ns hargs
    have hlen : ns.length = as.length := by
      have := congrArg List.length hargs
      simp only [List.length_map] at this
      exact this.symm
    exact neverStuck_of_checkShape (by rw [hlen]; exact hshape)
  obtain ⟨ns, w, hns, hargs, hrepGet, htvr, hsrc⟩ :=
    typed_entry_source_sound_checked hf cert.natCoreOk cert.lowered fc hwOrig hexp evOrig hnsPred
  have hretEq : TypedRep.repOf f.fir shapeCert (TypedRep.scanFeatures f.fir) (shapeCert.fn g).ret = retR := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields_zmod hnat hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, _, hn, rfl, hveq⟩ := htvr.fieldNat_inv hfn
  have hcast : (n : ZMod p) = (1 : ZMod p) := Value.field.inj hveq.symm
  have hn1 : n = 1 := by
    have h1lt : 1 < p := (Fact.out : Nat.Prime p).one_lt
    have hv := congrArg ZMod.val hcast
    rw [val_natCast_lt_zmod hnat hn, ZMod.val_one] at hv
    exact hv
  subst hn1
  obtain ⟨k, v, hrun, hobs⟩ := hsrc hcov
  exact ⟨k, v, hrun, Eq.trans hobs (obs_nat 1)⟩

/-- **Headline End-to-End Theorem (Passthrough Compression Entry → Source `Nat y.val`)**
over arbitrary prime `ZMod p` (`[Fact (Nat.Prime p)]`):
for `assertOk = false` and unboxed public result `.field y`, recovers that the checked
source evaluator returns `Nat y.val` (escape-free via `Progress.checkShape`). -/
theorem CompressionCert.accepted_passthrough_nat {p : Nat} [Fact (Nat.Prime p)]
    (fc : FieldCompatible64 (ZMod p))
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : ZMod p) ≠ 0)
    (hnat : natLimit ≤ p)
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program (ZMod p)} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hNoAssert : cert.aliasSpec.assertOk = false)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source (ZMod p)}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List (ZMod p)} {y : ZMod p}
    {rom : Aiur.WidthROM (ZMod p)} (valid : rom.Valid)
    {wires : List (Aiur.WireValue (ZMod p))} {output : Aiur.WireValue (ZMod p)}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message (ZMod p)}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow (ZMod p))} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  obtain ⟨value, heap, hrep, hTarget⟩ :=
    cert.evalFn_target_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  simp only [hNoAssert, Bool.false_eq_true, ↓reduceIte] at hTarget
  have evOrig : EvalFn sOrig.world (qualified (entryName i))
      (as.map (Value.field : ZMod p → SourceValue (ZMod p))) [] value heap :=
    bridge.backward hTarget
  have hnsPred : ∀ ns : List Nat,
      as.map (Value.field : ZMod p → SourceValue (ZMod p)) =
        ns.map (fun n => .field (n : ZMod p)) →
      Compose.NeverStuck ⟨f.src, f.checked⟩ (i, ns) := by
    intro ns hargs
    have hlen : ns.length = as.length := by
      have := congrArg List.length hargs
      simp only [List.length_map] at this
      exact this.symm
    exact neverStuck_of_checkShape (by rw [hlen]; exact hshape)
  obtain ⟨ns, w, hns, hargs, hrepGet, htvr, hsrc⟩ :=
    typed_entry_source_sound_checked hf cert.natCoreOk cert.lowered fc hwOrig hexp evOrig hnsPred
  have hretEq : TypedRep.repOf f.fir shapeCert (TypedRep.scanFeatures f.fir) (shapeCert.fn g).ret = retR := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields_zmod hnat hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, hn, rfl, hy⟩ := result_fieldNat hfn htvr hrep
  have hval : y.val = n := by rw [← hy]; exact val_natCast_lt_zmod hnat hn
  obtain ⟨k, v, hrun, hobs⟩ := hsrc hcov
  exact ⟨k, v, hrun, by rw [hval]; exact Eq.trans hobs (obs_nat n)⟩

/-- **Headline End-to-End Existential Witness Theorem (`--assert-ok` Aliased Entry +
`WitnessIO` + `lowerCompressionOps`)** over arbitrary `[Field F] [DecidableEq F]`:
from `cert.plan.checkMemo (rawROM rom) root rows = .ok ()` on an aliased `--assert-ok`
compression entry (e.g. `CompressWrap::verify_root`, `CompressGL::verify_root`,
`CompressNarrowFixed::step_v1`, `CompressFinalNarrow::verify_accumulator_v1`) wrapping a
`WitnessIO` ingress entry whose inner predicate `checkFnName` was lowered by
`lowerCompressionOps`, recovers the existence of finite, valid (`< 256`) byte-stream
witnesses `ws : List (List UInt8)` satisfying the pre-intrinsic specification `Spec pub ws`. -/
theorem CompressionCert.accepted_witness_assertOk_sound {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue F)}
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws := by
  obtain ⟨_, heap, _, hTarget⟩ :=
    cert.evalFn_target_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  simp only [hAssert, ↓reduceIte] at hTarget
  exact witness_wrapper_sound hsio hkio hchkQual hnd hwrap
    (fun pubArgs h1 h2 wPtrs ws hRel evInner =>
      hSpec pubArgs h1 h2 wPtrs ws hRel (bridge.backward evInner))
    hTarget.2

/-- **Headline End-to-End Existential Witness Theorem (Passthrough Entry Returning `.field 1`)**
over arbitrary `[Field F] [DecidableEq F]`:
composes `cert.plan.checkMemo = .ok ()` with `aliasEntry_sound_of_check` (`assertOk = false`),
`WitnessIO.witness_wrapper_sound`, and `CompressionLowerBridge.backward`. -/
theorem CompressionCert.accepted_witness_sound {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (hNoAssert : cert.aliasSpec.assertOk = false)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue F)}
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.field 1)) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws := by
  obtain ⟨value, heap, hrep, hTarget⟩ :=
    cert.evalFn_target_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  simp only [hNoAssert, Bool.false_eq_true, ↓reduceIte] at hTarget
  cases hrep
  exact witness_wrapper_sound hsio hkio hchkQual hnd hwrap
    (fun pubArgs h1 h2 wPtrs ws hRel evInner =>
      hSpec pubArgs h1 h2 wPtrs ws hRel (bridge.backward evInner))
    hTarget

/-- **Headline End-to-End Existential Witness Theorem (Inline `--assert-ok` Witness Wrapper)**
over arbitrary `[Field F] [DecidableEq F]`:
for entries where `Prog::main<i>` itself executes `witnessWrapperBody ... true` (returning
`()` = `.tuple []`) and is exported directly or via a passthrough alias. -/
theorem CompressionCert.accepted_witness_inlineAssertOk_sound {F : Type} [Field F] [DecidableEq F]
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program F} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (characteristic : ∀ n : Nat, 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → (n : F) ≠ 0)
    (hNoAssert : cert.aliasSpec.assertOk = false)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF F (witnessWrapperBody pubParams channels checkFnName true)))
    {Spec : List (SourceValue F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue F)) (h1 h2 : Heap F)
      (wPtrs : List (SourceValue F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue F)}
    {rom : Aiur.WidthROM F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue F)} {output : Aiur.WireValue F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws := by
  obtain ⟨value, heap, hrep, hTarget⟩ :=
    cert.evalFn_target_of_checkMemo characteristic valid signed rooted outside bound checked
      arguments decoded
  simp only [hNoAssert, Bool.false_eq_true, ↓reduceIte] at hTarget
  cases hrep with
  | tuple hitems =>
    cases hitems
    exact witness_wrapper_assertOk_sound hsio hkio hchkQual hnd hwrap
      (fun pubArgs h1 h2 wPtrs ws hRel evInner =>
        hSpec pubArgs h1 h2 wPtrs ws hRel (bridge.backward evInner))
      hTarget

/-! ### 5.5 Direct `Claim.Accepted` Bridge Over Goldilocks -/

/-- **Direct `Claim.Accepted` Compression Soundness Bridge (Goldilocks)**:
composes an accepted Goldilocks `Claim.Accepted` claim on a `lowerCompressionOps`-transformed
program directly with `CompressionLowerBridge` + `TypedClaim` + `Progress.checkShape`. -/
theorem accepted_compression_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig}
    (hnc : natCoreProgram f.fir shapeCert = true)
    (hlow : TypedLower.lowerProgram f.fir shapeCert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program GLF} (prepared : Aiur.Modules.Prepared moduleProg)
    {sOrig : Aiur.Generic.Source GLF}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List GLF} {y : GLF}
    (acc : Accepted prepared i (as.map Value.field) (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  obtain ⟨id, compiled, physical, dcfg, plan, external, entry, rom, wires, output, root, rows,
    certified, bits, activated, selected, hname, valid, signed, rooted, outside, bound,
    checked, arguments, decoded⟩ := acc
  obtain ⟨value, heap, hevalMod, hrep⟩ :=
    prepared.depth_grouped_activated_heap_sound_goldilocks compiled physical certified bits plan
      activated selected valid signed rooted outside bound checked arguments decoded
  obtain ⟨entry', hsel', hevalFn⟩ := hevalMod
  rw [selected, Option.some.injEq] at hsel'
  subst hsel'
  rw [hname] at hevalFn
  have evOrig : EvalFn sOrig.world (qualified (entryName i))
      (as.map (Value.field : GLF → SourceValue GLF)) [] value heap :=
    bridge.backward hevalFn
  have hnsPred : ∀ ns : List Nat,
      as.map (Value.field : GLF → SourceValue GLF) = ns.map (fun n => .field (n : GLF)) →
      Compose.NeverStuck ⟨f.src, f.checked⟩ (i, ns) := by
    intro ns hargs
    have hlen : ns.length = as.length := by
      have := congrArg List.length hargs
      simp only [List.length_map] at this
      exact this.symm
    exact neverStuck_of_checkShape (by rw [hlen]; exact hshape)
  obtain ⟨ns, w, hns, hargs, hrepGet, htvr, hsrc⟩ :=
    typed_entry_source_sound_checked hf hnc hlow fieldCompatible64_goldilocks hwOrig hexp evOrig
      hnsPred
  have hretEq : TypedRep.repOf f.fir shapeCert (TypedRep.scanFeatures f.fir) (shapeCert.fn g).ret = retR := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields_zmod natLimit_le_goldilocks hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, hn, rfl, hy⟩ := result_fieldNat hfn htvr hrep
  have hval : y.val = n := by rw [← hy]; exact val_natCast_lt_zmod natLimit_le_goldilocks hn
  obtain ⟨k, v, hrun, hobs⟩ := hsrc hcov
  exact ⟨k, v, hrun, by rw [hval]; exact Eq.trans hobs (obs_nat n)⟩

/-! ### 5.6 Concrete 3-Field End-to-End Compression Cert Corollaries (`Goldilocks`, `BN254`, `BLS12-381`) -/

/-- **Goldilocks (`p_G`) End-to-End `--assert-ok` Compression Cert Theorem**
(all field bounds & characteristic conditions discharged). -/
theorem compressionCert_assertOk_goldilocks
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program GLF} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source GLF} (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List GLF}
    {rom : Aiur.WidthROM GLF} (valid : rom.Valid)
    {wires : List (Aiur.WireValue GLF)} {output : Aiur.WireValue GLF}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message GLF}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow GLF)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1) :=
  cert.accepted_assertOk_source fieldCompatible64_goldilocks depth_characteristic_goldilocks
    natLimit_le_goldilocks hf hAssert hexp hret hfn hwOrig bridge valid signed rooted outside
    bound checked arguments decoded hcov hshape

/-- **Goldilocks (`p_G`) End-to-End `--assert-ok` Existential Witness Theorem**
(characteristic condition discharged). -/
theorem compressionCert_witness_goldilocks
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program GLF} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World GLF}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF GLF (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue GLF) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue GLF)) (h1 h2 : Heap GLF)
      (wPtrs : List (SourceValue GLF)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue GLF)}
    {rom : Aiur.WidthROM GLF} (valid : rom.Valid)
    {wires : List (Aiur.WireValue GLF)} {output : Aiur.WireValue GLF}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message GLF}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow GLF)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws :=
  cert.accepted_witness_assertOk_sound depth_characteristic_goldilocks hAssert hsio hkio bridge
    hchkQual hnd hwrap hSpec valid signed rooted outside bound checked arguments decoded

/-- **BN254 (`Fr`) End-to-End `--assert-ok` Compression Cert Theorem**
(all field bounds & characteristic conditions discharged). -/
theorem compressionCert_assertOk_bn254
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BN254.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source Aiur.Library.Field.BN254.F}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List Aiur.Library.Field.BN254.F}
    {rom : Aiur.WidthROM Aiur.Library.Field.BN254.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BN254.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BN254.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BN254.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BN254.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1) :=
  cert.accepted_assertOk_source fieldCompatible64_bn254 depth_characteristic_bn254
    natLimit_le_bn254 hf hAssert hexp hret hfn hwOrig bridge valid signed rooted outside
    bound checked arguments decoded hcov hshape

/-- **BN254 (`Fr`) End-to-End `--assert-ok` Existential Witness Theorem**
(characteristic condition discharged). -/
theorem compressionCert_witness_bn254
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BN254.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World Aiur.Library.Field.BN254.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BN254.F (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue Aiur.Library.Field.BN254.F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue Aiur.Library.Field.BN254.F))
      (h1 h2 : Heap Aiur.Library.Field.BN254.F)
      (wPtrs : List (SourceValue Aiur.Library.Field.BN254.F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue Aiur.Library.Field.BN254.F)}
    {rom : Aiur.WidthROM Aiur.Library.Field.BN254.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BN254.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BN254.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BN254.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BN254.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws :=
  cert.accepted_witness_assertOk_sound depth_characteristic_bn254 hAssert hsio hkio bridge
    hchkQual hnd hwrap hSpec valid signed rooted outside bound checked arguments decoded

/-- **BLS12-381 (`Fr`) End-to-End `--assert-ok` Compression Cert Theorem**
(all field bounds & characteristic conditions discharged). -/
theorem compressionCert_assertOk_bls12381
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BLS12381.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source Aiur.Library.Field.BLS12381.F}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List Aiur.Library.Field.BLS12381.F}
    {rom : Aiur.WidthROM Aiur.Library.Field.BLS12381.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BLS12381.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BLS12381.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1) :=
  cert.accepted_assertOk_source fieldCompatible64_bls12381 depth_characteristic_bls12381
    natLimit_le_bls12381 hf hAssert hexp hret hfn hwOrig bridge valid signed rooted outside
    bound checked arguments decoded hcov hshape

/-- **BLS12-381 (`Fr`) End-to-End `--assert-ok` Existential Witness Theorem**
(characteristic condition discharged). -/
theorem compressionCert_witness_bls12381
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BLS12381.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World Aiur.Library.Field.BLS12381.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BLS12381.F (witnessWrapperBody pubParams channels checkFnName false)))
    {Spec : List (SourceValue Aiur.Library.Field.BLS12381.F) → List (List UInt8) → Prop}
    (hSpec : ∀ (pubArgs : List (SourceValue Aiur.Library.Field.BLS12381.F))
      (h1 h2 : Heap Aiur.Library.Field.BLS12381.F)
      (wPtrs : List (SourceValue Aiur.Library.Field.BLS12381.F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      Spec pubArgs ws)
    {pub : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    {rom : Aiur.WidthROM Aiur.Library.Field.BLS12381.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BLS12381.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BLS12381.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ ws : List (List UInt8),
      ws.length = channels.length ∧
      (∀ b ∈ ws, isValidByteList (b.map UInt8.toNat)) ∧
      Spec pub ws :=
  cert.accepted_witness_assertOk_sound depth_characteristic_bls12381 hAssert hsio hkio bridge
    hchkQual hnd hwrap hSpec valid signed rooted outside bound checked arguments decoded

end EndToEndCompression

/-! ## Section 6: Kernel-Checked Axiom Fences (`⊆ [propext, Classical.choice, Quot.sound]`) -/

section AxiomFences

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.GoldilocksContracts.ofCheckNative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoldilocksContracts.ofCheckNative

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.GoldilocksContracts.ofCheckEmulated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoldilocksContracts.ofCheckEmulated

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.GoldilocksContracts.ofCheckBN254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoldilocksContracts.ofCheckBN254

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.GoldilocksContracts.ofCheckBLS12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GoldilocksContracts.ofCheckBLS12381

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_field_zmod_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_field_zmod_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOpBody_field_zmod_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOpBody_field_zmod_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_goldilocks_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_goldilocks_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOpBody_goldilocks_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOpBody_goldilocks_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_blake3_compressInit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_blake3_compressInit_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_blake3_hash_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_blake3_hash_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_blake3_packDigest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_blake3_packDigest_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOp_witness_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOp_witness_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.evalExpr_compressionOpBody_witness_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms evalExpr_compressionOpBody_witness_inv

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.lowerCompressionOpsCore_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerCompressionOpsCore_backward

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.lowerCompressionOps_backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerCompressionOps_backward

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.lowerCompressionOps_backward_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerCompressionOps_backward_goldilocks

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.lowerCompressionOps_backward_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerCompressionOps_backward_bn254

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.lowerCompressionOps_backward_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lowerCompressionOps_backward_bls12381

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.evalFn_target_of_checkMemo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.evalFn_target_of_checkMemo

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.accepted_assertOk_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.accepted_assertOk_source

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.accepted_passthrough_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.accepted_passthrough_nat

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.accepted_witness_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.accepted_witness_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.accepted_witness_assertOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.accepted_witness_assertOk_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert.accepted_witness_inlineAssertOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CompressionCert.accepted_witness_inlineAssertOk_sound

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.accepted_compression_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted_compression_nat

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_assertOk_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_assertOk_goldilocks

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_witness_goldilocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_witness_goldilocks

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_assertOk_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_assertOk_bn254

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_witness_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_witness_bn254

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_assertOk_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_assertOk_bls12381

/-- info: 'IxCC.AiurBackend.CompressionIntrinsicsProof.compressionCert_witness_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compressionCert_witness_bls12381

end AxiomFences

end IxCC.AiurBackend.CompressionIntrinsicsProof
