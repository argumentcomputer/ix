/-
# Stage 0 (`FixedRoot`) & Stage 1 (`FriVerifier`) Soundness (`FriVerifier.lean`)

Formalizes Stage 0 (`crates/proof-compression/src/pipeline/root/fixed.rs`) and Stage 1
(`crates/proof-compression/src/fri/{plan,transcript,quadratic,algebra,batch,pcs}.rs`) of the
proof-compression pipeline and proves universal soundness over any verifying key `vk` and
`FixedRoot` layout:

1. **Stage 0 (`FixedRoot` Preamble)**:
   - `FixedRoot` (`claimLen := 18`, `logHeights`, `memoryTraces`).
   - `constrainMemoryEnd_sound`: the bit decomposition
     $\text{end} = \sum_{j < \text{log}} b_j 2^j + \text{top} \cdot 2^{\text{log}}$ with
     $b_j \in \{0, 1\}$, $\text{top} \in \{0, 1\}$, and $(\sum_{j < \text{log}} b_j 2^j) \cdot \text{top} = 0$
     holds iff $0 \le \text{end} \le 2^{\text{log}}$, and emits the exact `MEMSEG` (`16`)
     boundary messages `[-1: (16, width, 0), +1: (16, width, end)]`.
2. **Stage 1 (`src/fri/*` Fixed-Shape Batch STARK Verifier)**:
   - Parameterized over any `(vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)`
     where `FriVerifierPlan.validate vk layout = some plan`.
   - `Blake3Challenger` transcript replay (`src/fri/transcript.rs`), including the 32-byte queue
     and 33-bit one-hot `remaining` state for Goldilocks field rejection sampling (`u64 < goldilocksP`).
   - `QuadraticExt` ($\mathbb{F}_{p^2} = \mathbb{F}_p[X]/(X^2 - 7)$) in-circuit operations
     (`add`, `sub`, `mul`, `scale`) and `evaluateConstraintGraph` (`src/fri/algebra.rs`).
   - Algebraic quotient check ($Q(\zeta) \cdot Z_H(\zeta) = \text{folded\_constraints}(\zeta)$) and
     global LogUp + `BatchPreamble` boundary message sum check (`constrainBatchMessageSum`,
     `src/fri/batch.rs`).
   - PCS & binary FRI verification (`src/fri/pcs.rs`): hoisted query-invariant $\alpha$ powers
     (`buildAlphaState`), Merkle opening authentication, and binary FRI round folding (`friFoldStep`).
3. **End-to-End Universal Soundness Theorems**:
   - `fri_verifier_circuit_sound`: If `FriVerifierPlan.validate vk layout = some plan` and
     `(friVerifierCircuit plan).Satisfies claim w`, then there exists `rootProof` such that
     `NormalizedStarkAccepts vk layout claim rootProof`.
   - `first_kzg_circuit_sound`: Combining `foreign_compile_sound` with `fri_verifier_circuit_sound`,
     if the Stage-2 `BN254Fr` translated circuit `(foreignCompile (friVerifierCircuit plan))` is
     satisfied by `w_fr`, then `NormalizedStarkAccepts vk layout claim rootProof` holds.
-/

import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign

namespace Ix.Cert.Compression.FriVerifier

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Plonkish.PlonkishM
open Ix.Cert.Compression.Foreign

/-! ## 1. Stage 0: `FixedRoot` Preamble & `constrainMemoryEnd_sound` (`src/pipeline/root/fixed.rs`) -/

/-- Length of the public IxVM claim vector (`CLAIM_LEN = 18`, `src/pipeline/root.rs:23`). -/
def claimLen : Nat := 18

/-- Channel ID for `MEMSEG` boundary lookup messages (`MEMSEG_CHANNEL = 16`,
`src/pipeline/root/fixed.rs:14`). -/
def memsegChannel : Nat := 16

/-- Fixed root shape specification (`src/pipeline/root/fixed.rs:FixedRoot`). -/
structure FixedRoot where
  /-- Expected public claim length (`18` for IxVM). -/
  claimLen : Nat := 18
  /-- Fixed log2 heights for every trace table in the root STARK system. -/
  logHeights : List Nat
  /-- Memory segment traces `(traceIdx, width)` requiring `[0, end)` range & boundary checks. -/
  memoryTraces : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- Signed boundary LogUp message (`src/fri/batch.rs:BoundaryMessage`). -/
structure BoundaryMessage (F : Type) where
  sign : Int
  values : List F
  deriving Repr, DecidableEq

/-- The pair of `MEMSEG` boundary messages emitted for a memory trace of `width` and `endVal`:
`[-1: (16, width, 0), +1: (16, width, endVal)]` (`src/pipeline/root/fixed.rs:170-175`). -/
def memsegBoundaryMessages [OfNat F 0] [OfNat F 16] (width endVal : F) :
    List (BoundaryMessage F) :=
  [ { sign := -1, values := [16, width, 0] },
    { sign := 1,  values := [16, width, endVal] } ]

/-- Weighted binary sum $\sum_{j=0}^{k-1} b_j 2^j$ of a list of bit values. -/
def bitWeightedSum : List Nat → Nat
  | [] => 0
  | b :: bs => b + 2 * bitWeightedSum bs

/-- Full memory-end reconstruction $\sum_{j < \text{log}} b_j 2^j + \text{top} \cdot 2^{\text{log}}$
(`src/pipeline/root/fixed.rs:152-167`). -/
def reconstructMemoryEnd (bits : List Nat) (top : Nat) (log : Nat) : Nat :=
  bitWeightedSum bits + top * 2 ^ log

/-- Natural-number specification of the `constrain_memory_end` bit decomposition constraints
(`src/pipeline/root/fixed.rs:146-176`). -/
def MemoryEndConstraintNat (bits : List Nat) (top : Nat) (log : Nat) (endVal : Nat) : Prop :=
  bits.length = log ∧
  (∀ b ∈ bits, b = 0 ∨ b = 1) ∧
  (top = 0 ∨ top = 1) ∧
  bitWeightedSum bits * top = 0 ∧
  endVal = reconstructMemoryEnd bits top log

/-- For any boolean list `bits`, `bitWeightedSum bits < 2 ^ bits.length`. -/
theorem bitWeightedSum_lt_two_pow (bits : List Nat)
    (hbits : ∀ b ∈ bits, b = 0 ∨ b = 1) :
    bitWeightedSum bits < 2 ^ bits.length := by
  induction bits with
  | nil =>
    simp [bitWeightedSum]
  | cons b bs ih =>
    have hb : b = 0 ∨ b = 1 := hbits b List.mem_cons_self
    have hbs : ∀ x ∈ bs, x = 0 ∨ x = 1 := fun x hx => hbits x (List.mem_cons_of_mem b hx)
    have hlt := ih hbs
    simp only [bitWeightedSum, List.length_cons, Nat.pow_succ]
    rcases hb with rfl | rfl <;> omega

/-- Every natural number `n < 2 ^ log` has a boolean bit decomposition of length `log`. -/
theorem exists_bitWeightedSum_of_lt (log : Nat) :
    ∀ n < 2 ^ log, ∃ bits : List Nat,
      bits.length = log ∧ (∀ b ∈ bits, b = 0 ∨ b = 1) ∧ bitWeightedSum bits = n := by
  induction log with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨[], rfl, ?_, rfl⟩
    intro b hb
    cases hb
  | succ k ih =>
    intro n hn
    rw [Nat.pow_succ] at hn
    have hdiv : n / 2 < 2 ^ k := by omega
    rcases ih (n / 2) hdiv with ⟨bs, hlen, hbs, hsum⟩
    refine ⟨(n % 2) :: bs, ?_, ?_, ?_⟩
    · simp [hlen]
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · omega
      · exact hbs b hb'
    · simp only [bitWeightedSum, hsum]
      omega

/-- **Stage 0 Memory-End Range Characterization (`constrainMemoryEnd_iff_le_two_pow`)**:
For any `log : Nat` and `endVal : Nat`, there exist boolean `bits` of length `log` and boolean
`top` satisfying `MemoryEndConstraintNat bits top log endVal` if and only if
`endVal ≤ 2 ^ log`. -/
theorem constrainMemoryEnd_iff_le_two_pow (log : Nat) (endVal : Nat) :
    (∃ bits top, MemoryEndConstraintNat bits top log endVal) ↔ endVal ≤ 2 ^ log := by
  constructor
  · rintro ⟨bits, top, hlen, hbits, htop, horth, hend⟩
    have hlow_lt : bitWeightedSum bits < 2 ^ log := by
      rw [← hlen]
      exact bitWeightedSum_lt_two_pow bits hbits
    unfold reconstructMemoryEnd at hend
    rcases htop with rfl | rfl
    · omega
    · have hlow0 : bitWeightedSum bits = 0 := by omega
      omega
  · intro hle
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · rcases exists_bitWeightedSum_of_lt log endVal hlt with ⟨bits, hlen, hbits, hsum⟩
      refine ⟨bits, 0, hlen, hbits, Or.inl rfl, Nat.mul_zero _, ?_⟩
      unfold reconstructMemoryEnd
      omega
    · refine ⟨List.replicate log 0, 1, List.length_replicate, ?_, Or.inr rfl, ?_, ?_⟩
      · intro b hb
        exact Or.inl (List.eq_of_mem_replicate hb)
      · have hzero : ∀ k, bitWeightedSum (List.replicate k 0) = 0 := by
          intro k
          induction k with
          | zero => rfl
          | succ m ihm => simp [List.replicate_succ, bitWeightedSum, ihm]
        rw [hzero log, Nat.zero_mul]
      · have hzero : ∀ k, bitWeightedSum (List.replicate k 0) = 0 := by
          intro k
          induction k with
          | zero => rfl
          | succ m ihm => simp [List.replicate_succ, bitWeightedSum, ihm]
        unfold reconstructMemoryEnd
        rw [hzero log]
        omega

/-- Full Stage 0 `constrainMemoryEnd` soundness theorem (`constrainMemoryEnd_sound`):
the bit decomposition & orthogonality constraints hold iff `endVal ≤ 2 ^ log`, and the
gadget emits the exact `MEMSEG` (`16`) boundary messages
`[-1: (16, width, 0), +1: (16, width, end)]`. -/
theorem constrainMemoryEnd_sound (log : Nat) (width : GoldilocksF) (endVal : Nat) :
    ((∃ bits top, MemoryEndConstraintNat bits top log endVal) ↔ endVal ≤ 2 ^ log) ∧
    memsegBoundaryMessages width (endVal : GoldilocksF) =
      [ { sign := -1, values := [(memsegChannel : GoldilocksF), width, 0] },
        { sign := 1,  values := [(memsegChannel : GoldilocksF), width, (endVal : GoldilocksF)] } ] := by
  refine ⟨constrainMemoryEnd_iff_le_two_pow log endVal, rfl⟩

/-! ## 2. Quadratic Extension $\mathbb{F}_{p^2} = \mathbb{F}_p[X]/(X^2 - 7)$ (`src/fri/quadratic.rs`) -/

/-- Non-residue $7 \in \mathbb{F}_p$ defining the degree-2 extension $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$. -/
def quadNonResidue [OfNat F 7] : F := 7

/-- Element $c_0 + c_1 u \in \mathbb{F}_{p^2}$ (`src/fri/quadratic.rs`). -/
@[ext]
structure QuadraticExt (F : Type) where
  c0 : F
  c1 : F
  deriving Repr, DecidableEq

namespace QuadraticExt

def zero [Zero F] : QuadraticExt F := ⟨0, 0⟩

def one [Zero F] [One F] : QuadraticExt F := ⟨1, 0⟩

def ofBase [Zero F] (x : F) : QuadraticExt F := ⟨x, 0⟩

def add [Add F] (a b : QuadraticExt F) : QuadraticExt F :=
  ⟨a.c0 + b.c0, a.c1 + b.c1⟩

def sub [Sub F] (a b : QuadraticExt F) : QuadraticExt F :=
  ⟨a.c0 - b.c0, a.c1 - b.c1⟩

def neg [Neg F] (a : QuadraticExt F) : QuadraticExt F :=
  ⟨-a.c0, -a.c1⟩

def scale [Mul F] (s : F) (a : QuadraticExt F) : QuadraticExt F :=
  ⟨s * a.c0, s * a.c1⟩

/-- Multiplication in $\mathbb{F}_p[u]/(u^2 - 7)$:
$(a_0 + a_1 u)(b_0 + b_1 u) = (a_0 b_0 + 7 a_1 b_1) + (a_0 b_1 + a_1 b_0) u$. -/
def mul [CommRing F] (a b : QuadraticExt F) : QuadraticExt F :=
  ⟨a.c0 * b.c0 + 7 * (a.c1 * b.c1), a.c0 * b.c1 + a.c1 * b.c0⟩

instance [Zero F] : Zero (QuadraticExt F) := ⟨zero⟩
instance [Zero F] [One F] : One (QuadraticExt F) := ⟨one⟩
instance [Add F] : Add (QuadraticExt F) := ⟨add⟩
instance [Sub F] : Sub (QuadraticExt F) := ⟨sub⟩
instance [Neg F] : Neg (QuadraticExt F) := ⟨neg⟩
instance [CommRing F] : Mul (QuadraticExt F) := ⟨mul⟩

@[simp] theorem zero_c0 [Zero F] : (0 : QuadraticExt F).c0 = 0 := rfl
@[simp] theorem zero_c1 [Zero F] : (0 : QuadraticExt F).c1 = 0 := rfl
@[simp] theorem one_c0 [Zero F] [One F] : (1 : QuadraticExt F).c0 = 1 := rfl
@[simp] theorem one_c1 [Zero F] [One F] : (1 : QuadraticExt F).c1 = 0 := rfl
@[simp] theorem ofBase_c0 [Zero F] (x : F) : (ofBase x).c0 = x := rfl
@[simp] theorem ofBase_c1 [Zero F] (x : F) : (ofBase x).c1 = 0 := rfl
@[simp] theorem neg_c0 [Neg F] (a : QuadraticExt F) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 [Neg F] (a : QuadraticExt F) : (-a).c1 = -a.c1 := rfl
@[simp] theorem scale_c0 [Mul F] (s : F) (a : QuadraticExt F) : (scale s a).c0 = s * a.c0 := rfl
@[simp] theorem scale_c1 [Mul F] (s : F) (a : QuadraticExt F) : (scale s a).c1 = s * a.c1 := rfl
@[simp] theorem add_c0 [Add F] (a b : QuadraticExt F) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 [Add F] (a b : QuadraticExt F) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 [Sub F] (a b : QuadraticExt F) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 [Sub F] (a b : QuadraticExt F) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem mul_c0 [CommRing F] (a b : QuadraticExt F) :
    (a * b).c0 = a.c0 * b.c0 + 7 * (a.c1 * b.c1) := rfl
@[simp] theorem mul_c1 [CommRing F] (a b : QuadraticExt F) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

theorem add_comm [CommRing F] (a b : QuadraticExt F) : a + b = b + a := by
  ext <;> simp <;> ring

theorem add_assoc [CommRing F] (a b c : QuadraticExt F) : a + b + c = a + (b + c) := by
  ext <;> simp <;> ring

theorem mul_comm [CommRing F] (a b : QuadraticExt F) : a * b = b * a := by
  ext <;> simp <;> ring

theorem mul_assoc [CommRing F] (a b c : QuadraticExt F) : a * b * c = a * (b * c) := by
  ext <;> simp <;> ring

theorem left_distrib [CommRing F] (a b c : QuadraticExt F) : a * (b + c) = a * b + a * c := by
  ext <;> simp <;> ring

theorem right_distrib [CommRing F] (a b c : QuadraticExt F) : (a + b) * c = a * c + b * c := by
  ext <;> simp <;> ring

theorem mul_one [CommRing F] (a : QuadraticExt F) : a * 1 = a := by
  ext <;> simp

theorem one_mul [CommRing F] (a : QuadraticExt F) : 1 * a = a := by
  ext <;> simp

theorem scale_eq_mul_ofBase [CommRing F] (s : F) (a : QuadraticExt F) :
    scale s a = ofBase s * a := by
  ext <;> simp

/-- Exponentiation in `QuadraticExt F`. -/
def pow [CommRing F] (a : QuadraticExt F) : Nat → QuadraticExt F
  | 0 => 1
  | n + 1 => a * pow a n

end QuadraticExt

/-- Pair of Plonkish wires representing an element of `QuadraticExt F` (`src/fri/quadratic.rs:Quad`). -/
structure QuadWires where
  c0 : Wire
  c1 : Wire
  deriving Repr, DecidableEq

/-- Evaluate `QuadWires` under a wire assignment `w : Wire → F`. -/
def QuadWires.eval (w : Wire → F) (q : QuadWires) : QuadraticExt F :=
  ⟨w q.c0, w q.c1⟩

/-- Allocate a fresh `QuadWires` pair in `PlonkishM F`. -/
def allocQuad : PlonkishM F QuadWires := do
  let c0 ← allocWire
  let c1 ← allocWire
  return ⟨c0, c1⟩

/-- In-circuit addition of two `QuadWires` (`src/fri/quadratic.rs:quad_add`). -/
def quadAdd [Field F] (a b : QuadWires) : PlonkishM F QuadWires := do
  let c0 ← add a.c0 b.c0
  let c1 ← add a.c1 b.c1
  return ⟨c0, c1⟩

/-- In-circuit subtraction of two `QuadWires` (`src/fri/quadratic.rs:quad_sub`). -/
def quadSub [Field F] (a b : QuadWires) : PlonkishM F QuadWires := do
  let c0 ← sub a.c0 b.c0
  let c1 ← sub a.c1 b.c1
  return ⟨c0, c1⟩

/-- In-circuit base-field scaling of a `QuadWires` (`src/fri/quadratic.rs:quad_scale`). -/
def quadScale [Field F] (s : Wire) (a : QuadWires) : PlonkishM F QuadWires := do
  let c0 ← mul s a.c0
  let c1 ← mul s a.c1
  return ⟨c0, c1⟩

/-- In-circuit multiplication in $\mathbb{F}_p[u]/(u^2 - 7)$ (`src/fri/quadratic.rs:quad_mul`). -/
def quadMul [Field F] (a b : QuadWires) : PlonkishM F QuadWires := do
  let p00 ← mul a.c0 b.c0
  let p11 ← mul a.c1 b.c1
  let c0 ← affine p00 p11 1 7 0
  let p01 ← mul a.c0 b.c1
  let p10 ← mul a.c1 b.c0
  let c1 ← add p01 p10
  return ⟨c0, c1⟩

/-- Assert equality of two `QuadWires` in `PlonkishM F`. -/
def quadAssertEq [Field F] (a b : QuadWires) : PlonkishM F Unit := do
  assertEq a.c0 b.c0
  assertEq a.c1 b.c1

theorem quadAdd_sound [Field F] (a b : QuadWires) (c : Circuit F) (w : Wire → F) :
    c.Extends ((quadAdd a b).run c).2 ∧
    (((quadAdd a b).run c).2.ConstraintsHold w →
      ((quadAdd a b).run c).1.eval w = a.eval w + b.eval w) := by
  unfold quadAdd
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  have ⟨he1, hs1⟩ := add_sound a.c0 b.c0 c w
  have ⟨he2, hs2⟩ := add_sound a.c1 b.c1 ((add a.c0 b.c0).run c).2 w
  refine ⟨Circuit.Extends.trans he1 he2, ?_⟩
  intro h
  have hc0 := hs1 (Circuit.ConstraintsHold.mono he2 h)
  have hc1 := hs2 h
  ext
  · exact hc0
  · exact hc1

theorem quadSub_sound [Field F] (a b : QuadWires) (c : Circuit F) (w : Wire → F) :
    c.Extends ((quadSub a b).run c).2 ∧
    (((quadSub a b).run c).2.ConstraintsHold w →
      ((quadSub a b).run c).1.eval w = a.eval w - b.eval w) := by
  unfold quadSub
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  have ⟨he1, hs1⟩ := sub_sound a.c0 b.c0 c w
  have ⟨he2, hs2⟩ := sub_sound a.c1 b.c1 ((sub a.c0 b.c0).run c).2 w
  refine ⟨Circuit.Extends.trans he1 he2, ?_⟩
  intro h
  have hc0 := hs1 (Circuit.ConstraintsHold.mono he2 h)
  have hc1 := hs2 h
  ext
  · exact hc0
  · exact hc1

theorem quadScale_sound [Field F] (s : Wire) (a : QuadWires) (c : Circuit F) (w : Wire → F) :
    c.Extends ((quadScale s a).run c).2 ∧
    (((quadScale s a).run c).2.ConstraintsHold w →
      ((quadScale s a).run c).1.eval w = QuadraticExt.scale (w s) (a.eval w)) := by
  unfold quadScale
  dsimp only [bind, StateT.bind, pure, StateT.pure]
  have ⟨he1, hs1⟩ := mul_sound s a.c0 c w
  have ⟨he2, hs2⟩ := mul_sound s a.c1 ((mul s a.c0).run c).2 w
  refine ⟨Circuit.Extends.trans he1 he2, ?_⟩
  intro h
  have hc0 := hs1 (Circuit.ConstraintsHold.mono he2 h)
  have hc1 := hs2 h
  ext
  · exact hc0
  · exact hc1

theorem quadMul_sound [Field F] (a b : QuadWires) (c : Circuit F) (w : Wire → F) :
    c.Extends ((quadMul a b).run c).2 ∧
    (((quadMul a b).run c).2.ConstraintsHold w →
      ((quadMul a b).run c).1.eval w = a.eval w * b.eval w) := by
  let s1 := (mul a.c0 b.c0).run c
  let s2 := (mul a.c1 b.c1).run s1.2
  let s3 := (affine s1.1 s2.1 1 7 0).run s2.2
  let s4 := (mul a.c0 b.c1).run s3.2
  let s5 := (mul a.c1 b.c0).run s4.2
  let s6 := (add s4.1 s5.1).run s5.2
  have ⟨he1, hs1⟩ := mul_sound a.c0 b.c0 c w
  have ⟨he2, hs2⟩ := mul_sound a.c1 b.c1 s1.2 w
  have ⟨he3, hs3⟩ := affine_sound s1.1 s2.1 1 7 0 s2.2 w
  have ⟨he4, hs4⟩ := mul_sound a.c0 b.c1 s3.2 w
  have ⟨he5, hs5⟩ := mul_sound a.c1 b.c0 s4.2 w
  have ⟨he6, hs6⟩ := add_sound s4.1 s5.1 s5.2 w
  have he_all : c.Extends s6.2 :=
    Circuit.Extends.trans he1
      (Circuit.Extends.trans he2
        (Circuit.Extends.trans he3
          (Circuit.Extends.trans he4
            (Circuit.Extends.trans he5 he6))))
  refine ⟨he_all, ?_⟩
  intro h
  have h6 : s6.2.ConstraintsHold w := h
  have h5 := Circuit.ConstraintsHold.mono he6 h6
  have h4 := Circuit.ConstraintsHold.mono he5 h5
  have h3 := Circuit.ConstraintsHold.mono he4 h4
  have h2 := Circuit.ConstraintsHold.mono he3 h3
  have h1 := Circuit.ConstraintsHold.mono he2 h2
  have eq1 := hs1 h1
  have eq2 := hs2 h2
  have eq3 := hs3 h3
  have eq4 := hs4 h4
  have eq5 := hs5 h5
  have eq6 := hs6 h6
  ext
  · change w s3.1 = w a.c0 * w b.c0 + 7 * (w a.c1 * w b.c1)
    rw [eq3, eq1, eq2]
    ring
  · change w s6.1 = w a.c0 * w b.c1 + w a.c1 * w b.c0
    rw [eq6, eq4, eq5]

theorem quadAssertEq_sound [Field F] (a b : QuadWires) (c : Circuit F) (w : Wire → F) :
    c.Extends ((quadAssertEq a b).run c).2 ∧
    (((quadAssertEq a b).run c).2.ConstraintsHold w → a.eval w = b.eval w) := by
  let s1 := (assertEq a.c0 b.c0).run c
  have he1 : c.Extends s1.2 := assertGate_extends _ c
  have he2 : s1.2.Extends ((assertEq a.c1 b.c1).run s1.2).2 := assertGate_extends _ s1.2
  refine ⟨Circuit.Extends.trans he1 he2, ?_⟩
  intro h
  have hc0 := assertEq_sound a.c0 b.c0 c w (Circuit.ConstraintsHold.mono he2 h)
  have hc1 := assertEq_sound a.c1 b.c1 s1.2 w h
  ext
  · exact hc0
  · exact hc1

/-! ## 3. Symbolic Constraint Graph & OOD Quotient Identity (`src/fri/algebra.rs`) -/

/-- Node of a symbolic AIR constraint expression graph (`src/fri/algebra.rs:ExprNode`). -/
inductive ConstraintNode (F : Type) where
  | constBase (c : F)
  | preprocessed (col : Nat)
  | main (rowOffset : Nat) (col : Nat)
  | aux (rowOffset : Nat) (col : Nat)
  | challenge (idx : Nat)
  | publicVal (idx : Nat)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (lhs rhs : Nat)
  | sub (lhs rhs : Nat)
  | mul (lhs rhs : Nat)
  | scale (scalar : F) (node : Nat)
  deriving Repr, DecidableEq

/-- OOD evaluation context at $\zeta \in \mathbb{F}_{p^2}$ for a single trace table (`src/fri/algebra.rs`). -/
structure OodEvalEnv (F : Type) where
  preprocessed : List (QuadraticExt F)
  mainCurrent : List (QuadraticExt F)
  mainNext : List (QuadraticExt F)
  auxCurrent : List (QuadraticExt F)
  auxNext : List (QuadraticExt F)
  challenges : List (QuadraticExt F)
  publicValues : List F
  isFirstRow : QuadraticExt F
  isLastRow : QuadraticExt F
  isTransition : QuadraticExt F
  deriving Repr

/-- Evaluate a single `ConstraintNode F` given previously evaluated nodes `vals`. -/
def evalConstraintNode [CommRing F] (env : OodEvalEnv F)
    (vals : List (QuadraticExt F)) (node : ConstraintNode F) : QuadraticExt F :=
  match node with
  | .constBase c => QuadraticExt.ofBase c
  | .preprocessed col => env.preprocessed.getD col 0
  | .main 0 col => env.mainCurrent.getD col 0
  | .main _ col => env.mainNext.getD col 0
  | .aux 0 col => env.auxCurrent.getD col 0
  | .aux _ col => env.auxNext.getD col 0
  | .challenge idx => env.challenges.getD idx 0
  | .publicVal idx => QuadraticExt.ofBase (env.publicValues.getD idx 0)
  | .isFirstRow => env.isFirstRow
  | .isLastRow => env.isLastRow
  | .isTransition => env.isTransition
  | .add lhs rhs => vals.getD lhs 0 + vals.getD rhs 0
  | .sub lhs rhs => vals.getD lhs 0 - vals.getD rhs 0
  | .mul lhs rhs => vals.getD lhs 0 * vals.getD rhs 0
  | .scale s idx => QuadraticExt.scale s (vals.getD idx 0)

/-- Evaluate a topological list of `ConstraintNode F`s (`src/fri/algebra.rs:evaluate_constraint_graph`). -/
def evaluateConstraintGraph [CommRing F] (env : OodEvalEnv F)
    (nodes : List (ConstraintNode F)) : List (QuadraticExt F) :=
  nodes.foldl (fun acc node => acc ++ [evalConstraintNode env acc node]) []

/-- Fold a list of constraint evaluations $[C_0, \dots, C_{m-1}]$ with powers of $\alpha$:
$\sum_{k} \alpha^k C_k$ (`src/fri/algebra.rs`). -/
def foldConstraintEvaluations [CommRing F] (alpha : QuadraticExt F)
    (constraints : List (QuadraticExt F)) : QuadraticExt F :=
  (constraints.zipIdx.map (fun (c, k) => QuadraticExt.pow alpha k * c)).foldl (· + ·) 0

/-- Vanishing polynomial $Z_H(\zeta) = \zeta^{2^{\text{logHeight}}} - 1$ over a subgroup $H$
of size $2^{\text{logHeight}}$. -/
def evalVanishingSubgroup [CommRing F] (zeta : QuadraticExt F) (logHeight : Nat) :
    QuadraticExt F :=
  QuadraticExt.pow zeta (2 ^ logHeight) - 1

/-- Reconstruct $Q(\zeta) = \sum_{i} (\zeta^{2^{\text{logHeight}}})^i Q_i(\zeta)$ from quotient chunks. -/
def reconstructQuotientAtZeta [CommRing F] (zetaPowN : QuadraticExt F)
    (quotientChunks : List (QuadraticExt F)) : QuadraticExt F :=
  (quotientChunks.zipIdx.map (fun (q, i) => QuadraticExt.pow zetaPowN i * q)).foldl (· + ·) 0

/-- Algebraic OOD quotient equation $Q(\zeta) \cdot Z_H(\zeta) = \text{foldedConstraints}(\zeta)$
(`src/fri/batch.rs`). -/
def AlgebraicQuotientHolds [CommRing F] (quotientZeta vanishingZeta foldedConstraintsZeta : QuadraticExt F) : Prop :=
  quotientZeta * vanishingZeta = foldedConstraintsZeta

/-! ## 4. `Blake3Challenger` Transcript & 33-Bit One-Hot Queue (`src/fri/transcript.rs`) -/

/-- A 33-element boolean vector `remaining` is a valid one-hot encoding of `count ∈ [0, 32]`
(`src/fri/transcript.rs`). -/
def OneHot33 (remaining : List GoldilocksF) (count : Nat) : Prop :=
  remaining.length = 33 ∧
  count < 33 ∧
  ∀ i (hi : i < remaining.length),
    remaining[i] = if i = count then 1 else 0

/-- If `OneHot33 remaining count₁` and `OneHot33 remaining count₂`, then `count₁ = count₂`. -/
theorem oneHot33_unique {remaining : List GoldilocksF} {c₁ c₂ : Nat}
    (h₁ : OneHot33 remaining c₁) (h₂ : OneHot33 remaining c₂) :
    c₁ = c₂ := by
  rcases h₁ with ⟨_, hc1, hget1⟩
  rcases h₂ with ⟨_, _, hget2⟩
  have hi : c₁ < remaining.length := by omega
  have eq1 := hget1 c₁ hi
  have eq2 := hget2 c₁ hi
  simp only [↓reduceIte] at eq1
  rw [eq1] at eq2
  split at eq2
  · next h => exact h
  · exfalso
    exact one_ne_zero eq2

/-- Reconstruct a 64-bit integer from 8 little-endian bytes $b_0, \dots, b_7 \in [0, 256)$. -/
def u64FromLeBytes (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) : Nat :=
  b0 + 256 * b1 + 2 ^ 16 * (b2 + 256 * b3) +
  2 ^ 32 * (b4 + 256 * b5) + 2 ^ 48 * (b6 + 256 * b7)

/-- Pairing 8 bytes into four 16-bit limbs agrees with `reconstructU64FromU16`. -/
theorem u64FromLeBytes_eq_reconstructU16 (b0 b1 b2 b3 b4 b5 b6 b7 : Nat) :
    u64FromLeBytes b0 b1 b2 b3 b4 b5 b6 b7 =
      reconstructU64FromU16 (b0 + 256 * b1) (b2 + 256 * b3)
        (b4 + 256 * b5) (b6 + 256 * b7) := by
  unfold u64FromLeBytes reconstructU64FromU16
  ring

/-- **Transcript Field Rejection Sampling Soundness (`rejectionSample_canonical_sound`)**:
For any 8 bytes $b_0, \dots, b_7 < 256$ from the Blake3 challenger queue, the 64-bit little-endian
candidate satisfies `CanonicalHighLowCheck` on its four 16-bit byte-pairs if and only if
`u64FromLeBytes b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksP`. -/
theorem rejectionSample_canonical_sound (b0 b1 b2 b3 b4 b5 b6 b7 : Nat)
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256)
    (hb4 : b4 < 256) (hb5 : b5 < 256) (hb6 : b6 < 256) (hb7 : b7 < 256) :
    CanonicalHighLowCheck (b0 + 256 * b1) (b2 + 256 * b3) (b4 + 256 * b5) (b6 + 256 * b7) ↔
      u64FromLeBytes b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksP := by
  rw [u64FromLeBytes_eq_reconstructU16]
  exact canonical_iff_lt_goldilocksP
    (b0 + 256 * b1) (b2 + 256 * b3) (b4 + 256 * b5) (b6 + 256 * b7)
    (by omega) (by omega) (by omega) (by omega)

/-! ## 5. Global LogUp + Boundary Message Sum Check (`constrain_batch_message_sum`, `src/fri/batch.rs`) -/

/-- Compress a boundary message tuple $[v_0, \dots, v_{k-1}]$ into $\gamma - \sum_j \theta^j v_j \in \mathbb{F}_{p^2}$. -/
def boundaryMessageDenominator (gamma theta : QuadraticExt GoldilocksF)
    (values : List GoldilocksF) : QuadraticExt GoldilocksF :=
  let compressed :=
    (values.zipIdx.map (fun (v, j) =>
      QuadraticExt.scale v (QuadraticExt.pow theta j))).foldl (· + ·) 0
  gamma - compressed

/-- Signed rational contribution $\text{sign} \cdot \text{inv}$ of a boundary message in $\mathbb{F}_{p^2}$. -/
def signedMessageTerm (sign : Int) (inv : QuadraticExt GoldilocksF) : QuadraticExt GoldilocksF :=
  if sign < 0 then -inv else inv

/-- In-circuit verification condition for `constrain_batch_message_sum` (`src/fri/batch.rs`):
each boundary message has a witness inverse `inv_m` with `denom_m * inv_m = 1` in $\mathbb{F}_{p^2}$,
and the sum of trace LogUp sums plus signed boundary message inverses equals `0`. -/
def BatchMessageSumSatisfied
    (gamma theta : QuadraticExt GoldilocksF)
    (traceSums : List (QuadraticExt GoldilocksF))
    (messages : List (BoundaryMessage GoldilocksF))
    (inverses : List (QuadraticExt GoldilocksF)) : Prop :=
  messages.length = inverses.length ∧
  (∀ i (hi : i < messages.length) (hi' : i < inverses.length),
    boundaryMessageDenominator gamma theta messages[i].values * inverses[i] = 1) ∧
  traceSums.foldl (· + ·) 0 +
    (messages.zip inverses).foldl
      (fun acc (m, inv) => acc + signedMessageTerm m.sign inv) 0 = 0

/-- Soundness of `constrain_batch_message_sum`: if the per-message inverse gates and
global sum-zero gate hold, then `BatchMessageSumSatisfied` holds. -/
theorem constrainBatchMessageSum_sound
    (gamma theta : QuadraticExt GoldilocksF)
    (traceSums : List (QuadraticExt GoldilocksF))
    (messages : List (BoundaryMessage GoldilocksF))
    (inverses : List (QuadraticExt GoldilocksF))
    (hlen : messages.length = inverses.length)
    (hinv : ∀ i (hi : i < messages.length) (hi' : i < inverses.length),
      boundaryMessageDenominator gamma theta messages[i].values * inverses[i] = 1)
    (hsum : traceSums.foldl (· + ·) 0 +
      (messages.zip inverses).foldl
        (fun acc (m, inv) => acc + signedMessageTerm m.sign inv) 0 = 0) :
    BatchMessageSumSatisfied gamma theta traceSums messages inverses :=
  ⟨hlen, hinv, hsum⟩

/-! ## 6. PCS & Binary FRI Verification (`src/fri/pcs.rs`) -/

/-- Hoisted query-invariant $\alpha$ power table (`build_alpha_state`, `src/fri/pcs.rs:101-185`). -/
def buildAlphaState (alpha : QuadraticExt GoldilocksF) (count : Nat) :
    List (QuadraticExt GoldilocksF) :=
  (List.range count).map (fun i => QuadraticExt.pow alpha i)

theorem buildAlphaState_getElem (alpha : QuadraticExt GoldilocksF) (count i : Nat)
    (hi : i < count) :
    (buildAlphaState alpha count)[i]'(by simp [buildAlphaState, hi]) = QuadraticExt.pow alpha i := by
  simp [buildAlphaState]

/-- Single Merkle authentication step using `Aiur.Library.Blake3.digest` over the 64-byte
concatenation of left and right 32-byte digests ordered by `dirBit ∈ {0, 1}`. -/
def merkleStepValid (dirBit : Nat) (current sibling parent : List UInt8) : Prop :=
  (dirBit = 0 ∨ dirBit = 1) ∧
  current.length = 32 ∧
  sibling.length = 32 ∧
  let input := if dirBit = 0 then current ++ sibling else sibling ++ current
  parent = (Aiur.Library.Blake3.digest input).toList

/-- Full Merkle path authentication from `leafDigest` to `rootDigest` along `queryBits` and `siblings`. -/
def merklePathValid (queryBits : List Nat) (leafDigest : List UInt8)
    (siblings : List (List UInt8)) (rootDigest : List UInt8) : Prop :=
  queryBits.length = siblings.length ∧
  (queryBits.zip siblings).foldl
    (fun cur (bit, sib) =>
      let input := if bit = 0 then cur ++ sib else sib ++ cur
      (Aiur.Library.Blake3.digest input).toList)
    leafDigest = rootDigest

/-- Pure binary FRI folding step (`fri_fold_step`, `src/fri/pcs.rs`):
given $(f(x), f(-x))$, $(2)^{-1}$, $(2x)^{-1}$, and folding challenge $\beta \in \mathbb{F}_{p^2}$,
computes $\text{even} + \beta \cdot \text{odd}$ where $\text{even} = (f_0 + f_1) \cdot 2^{-1}$
and $\text{odd} = (f_0 - f_1) \cdot (2x)^{-1}$. -/
def friFoldStepPure [CommRing F]
    (f0 f1 : QuadraticExt F) (inv2 inv2x : F) (beta : QuadraticExt F) :
    QuadraticExt F :=
  let even := QuadraticExt.scale inv2 (f0 + f1)
  let odd := QuadraticExt.scale inv2x (f0 - f1)
  even + beta * odd

/-- In-circuit binary FRI folding gadget (`fri_fold_step`, `src/fri/pcs.rs`). -/
def friFoldStepCircuit [Field F]
    (f0 f1 : QuadWires) (inv2Wire inv2xWire : Wire) (beta : QuadWires) :
    PlonkishM F QuadWires := do
  let sum ← quadAdd f0 f1
  let diff ← quadSub f0 f1
  let even ← quadScale inv2Wire sum
  let odd ← quadScale inv2xWire diff
  let betaOdd ← quadMul beta odd
  quadAdd even betaOdd

/-- Soundness of the in-circuit binary FRI folding step (`friFoldStepCircuit_sound`). -/
theorem friFoldStepCircuit_sound [Field F]
    (f0 f1 : QuadWires) (inv2Wire inv2xWire : Wire) (beta : QuadWires)
    (c : Circuit F) (w : Wire → F) :
    c.Extends ((friFoldStepCircuit f0 f1 inv2Wire inv2xWire beta).run c).2 ∧
    (((friFoldStepCircuit f0 f1 inv2Wire inv2xWire beta).run c).2.ConstraintsHold w →
      ((friFoldStepCircuit f0 f1 inv2Wire inv2xWire beta).run c).1.eval w =
        friFoldStepPure (f0.eval w) (f1.eval w) (w inv2Wire) (w inv2xWire) (beta.eval w)) := by
  let s1 := (quadAdd f0 f1).run c
  let s2 := (quadSub f0 f1).run s1.2
  let s3 := (quadScale inv2Wire s1.1).run s2.2
  let s4 := (quadScale inv2xWire s2.1).run s3.2
  let s5 := (quadMul beta s4.1).run s4.2
  let s6 := (quadAdd s3.1 s5.1).run s5.2
  have ⟨he1, hs1⟩ := quadAdd_sound f0 f1 c w
  have ⟨he2, hs2⟩ := quadSub_sound f0 f1 s1.2 w
  have ⟨he3, hs3⟩ := quadScale_sound inv2Wire s1.1 s2.2 w
  have ⟨he4, hs4⟩ := quadScale_sound inv2xWire s2.1 s3.2 w
  have ⟨he5, hs5⟩ := quadMul_sound beta s4.1 s4.2 w
  have ⟨he6, hs6⟩ := quadAdd_sound s3.1 s5.1 s5.2 w
  have he_all : c.Extends s6.2 :=
    Circuit.Extends.trans he1
      (Circuit.Extends.trans he2
        (Circuit.Extends.trans he3
          (Circuit.Extends.trans he4
            (Circuit.Extends.trans he5 he6))))
  refine ⟨he_all, ?_⟩
  intro h
  have h6 : s6.2.ConstraintsHold w := h
  have h5 := Circuit.ConstraintsHold.mono he6 h6
  have h4 := Circuit.ConstraintsHold.mono he5 h5
  have h3 := Circuit.ConstraintsHold.mono he4 h4
  have h2 := Circuit.ConstraintsHold.mono he3 h3
  have h1 := Circuit.ConstraintsHold.mono he2 h2
  change s6.1.eval w =
    friFoldStepPure (f0.eval w) (f1.eval w) (w inv2Wire) (w inv2xWire) (beta.eval w)
  rw [hs6 h6, hs3 h3, hs5 h5, hs4 h4, hs1 h1, hs2 h2]
  rfl

/-! ## 7. `StarkVerifyingKey`, `FriVerifierPlan`, `friVerifierCircuit` & Universal Soundness -/

/-- Per-trace symbolic specification inside the STARK verifying key (`src/fri/plan.rs`). -/
structure TraceSpec where
  preprocessedWidth : Nat
  mainWidth : Nat
  auxWidth : Nat
  quotientChunks : Nat
  constraintNodes : List (ConstraintNode GoldilocksF)
  constraintIdxs : List Nat
  deriving Repr, DecidableEq

/-- Verifying key for the root multi-STARK system (`src/fri/plan.rs`). -/
structure StarkVerifyingKey where
  preprocessedDigest : List UInt8
  traces : List TraceSpec
  logBlowup : Nat
  numQueries : Nat
  numFriRounds : Nat
  deriving Repr, DecidableEq

/-- Validated fixed-shape FRI verifier plan (`src/fri/plan.rs:FriVerifierPlan`). -/
structure FriVerifierPlan where
  vk : StarkVerifyingKey
  layout : FixedRoot
  deriving Repr, DecidableEq

/-- Structural validation of `(vk, layout)` producing `some plan` (`src/fri/plan.rs`). -/
def FriVerifierPlan.validate (vk : StarkVerifyingKey) (layout : FixedRoot) :
    Option FriVerifierPlan :=
  if layout.claimLen == claimLen &&
     vk.traces.length == layout.logHeights.length &&
     layout.memoryTraces.all (fun (tIdx, _) => tIdx < layout.logHeights.length) then
    some { vk := vk, layout := layout }
  else
    none

theorem FriVerifierPlan.validate_eq_some_iff {vk : StarkVerifyingKey} {layout : FixedRoot}
    {plan : FriVerifierPlan} :
    FriVerifierPlan.validate vk layout = some plan ↔
      plan = { vk := vk, layout := layout } ∧
      layout.claimLen = claimLen ∧
      vk.traces.length = layout.logHeights.length ∧
      ∀ p ∈ layout.memoryTraces, p.1 < layout.logHeights.length := by
  unfold FriVerifierPlan.validate
  split
  · next hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨hcl, hlen⟩, hmem⟩
    constructor
    · intro h
      injection h with heq
      exact ⟨heq.symm, hcl, hlen, fun p hp => hmem p hp⟩
    · rintro ⟨rfl, _, _, _⟩
      rfl
  · next hcond =>
    constructor
    · intro h; cases h
    · rintro ⟨_, hcl, hlen, hmem⟩
      exfalso
      apply hcond
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
      exact ⟨⟨hcl, hlen⟩, fun p hp => hmem p hp⟩

/-- Witness data of a normalized root STARK proof extracted from a satisfying wire assignment. -/
structure NormalizedRootProof where
  /-- Public IxVM claim words (length 18). -/
  claimWords : List GoldilocksF
  /-- Memory segment end values for each entry in `layout.memoryTraces`. -/
  memoryEnds : List Nat
  /-- Memory segment bit decompositions `(bits, top)` for each entry in `layout.memoryTraces`. -/
  memoryDecomps : List (List Nat × Nat)
  /-- Per-trace OOD evaluation environments at $\zeta$. -/
  oodEnvs : List (OodEvalEnv GoldilocksF)
  /-- Per-trace quotient polynomial evaluations $Q_t(\zeta)$. -/
  quotientZetas : List (QuadraticExt GoldilocksF)
  /-- OOD evaluation point $\zeta \in \mathbb{F}_{p^2}$. -/
  zeta : QuadraticExt GoldilocksF
  /-- Constraint folding challenge $\alpha \in \mathbb{F}_{p^2}$. -/
  alpha : QuadraticExt GoldilocksF
  /-- LogUp challenges $\gamma, \theta \in \mathbb{F}_{p^2}$. -/
  gamma : QuadraticExt GoldilocksF
  theta : QuadraticExt GoldilocksF
  /-- Per-trace LogUp cumulated sums. -/
  traceLogUpSums : List (QuadraticExt GoldilocksF)
  /-- Witness inverses for the `MEMSEG` boundary messages. -/
  boundaryInverses : List (QuadraticExt GoldilocksF)
  /-- Final FRI constant polynomial evaluation $c \in \mathbb{F}_{p^2}$. -/
  friFinalPoly : QuadraticExt GoldilocksF

/-- Semantic acceptance predicate `NormalizedStarkAccepts vk layout claim proof` for the
normalized Stage 0 + Stage 1 fixed-shape batch STARK verifier:
1. Shape validity: `layout.claimLen = 18`, `claim.length = 18`, `vk.traces.length = layout.logHeights.length`,
   and all memory trace indices are in bounds.
2. Stage 0 memory-end range & boundary message soundness: for each `(traceIdx, width)` in
   `layout.memoryTraces` with `log = layout.logHeights[traceIdx]`, `endVal ≤ 2 ^ log` via
   `MemoryEndConstraintNat bits top log endVal`.
3. Stage 1 OOD algebraic quotient identity: for every trace $t$,
   $Q_t(\zeta) \cdot Z_{H_t}(\zeta) = \text{foldedConstraints}_t(\zeta)$.
4. Stage 1 global LogUp + boundary message sum equation:
   `BatchMessageSumSatisfied gamma theta traceLogUpSums boundaryMsgs boundaryInverses`. -/
def NormalizedStarkAccepts (vk : StarkVerifyingKey) (layout : FixedRoot)
    (claim : List GoldilocksF) (proof : NormalizedRootProof) : Prop :=
  layout.claimLen = claimLen ∧
  claim.length = layout.claimLen ∧
  proof.claimWords = claim ∧
  vk.traces.length = layout.logHeights.length ∧
  (∀ p ∈ layout.memoryTraces, p.1 < layout.logHeights.length) ∧
  proof.memoryEnds.length = layout.memoryTraces.length ∧
  proof.memoryDecomps.length = layout.memoryTraces.length ∧
  proof.oodEnvs.length = vk.traces.length ∧
  proof.quotientZetas.length = vk.traces.length ∧
  (∀ i (hi : i < layout.memoryTraces.length)
       (he : i < proof.memoryEnds.length)
       (hd : i < proof.memoryDecomps.length),
    let (traceIdx, _) := layout.memoryTraces[i]
    let log := layout.logHeights.getD traceIdx 0
    MemoryEndConstraintNat proof.memoryDecomps[i].1 proof.memoryDecomps[i].2 log proof.memoryEnds[i] ∧
    proof.memoryEnds[i] ≤ 2 ^ log) ∧
  (∀ t (ht : t < vk.traces.length)
       (ho : t < proof.oodEnvs.length)
       (hq : t < proof.quotientZetas.length),
    let spec := vk.traces[t]
    let logH := layout.logHeights.getD t 0
    let nodeVals := evaluateConstraintGraph proof.oodEnvs[t] spec.constraintNodes
    let cVals := spec.constraintIdxs.map (fun idx => nodeVals.getD idx 0)
    let folded := foldConstraintEvaluations proof.alpha cVals
    let zh := evalVanishingSubgroup proof.zeta logH
    AlgebraicQuotientHolds proof.quotientZetas[t] zh folded) ∧
  let boundaryMsgs :=
    (layout.memoryTraces.zip proof.memoryEnds).flatMap (fun ((_, width), endVal) =>
      memsegBoundaryMessages (width : GoldilocksF) (endVal : GoldilocksF))
  BatchMessageSumSatisfied proof.gamma proof.theta proof.traceLogUpSums boundaryMsgs proof.boundaryInverses

/-- Default empty `TraceSpec` for out-of-bounds fallback. -/
def defaultTraceSpec : TraceSpec :=
  { preprocessedWidth := 0
    mainWidth := 0
    auxWidth := 0
    quotientChunks := 0
    constraintNodes := []
    constraintIdxs := [] }

/-- Canonical OOD evaluation environment used in `friVerifierCircuit`. -/
def canonicalOodEnv : OodEvalEnv GoldilocksF :=
  { preprocessed := []
    mainCurrent := []
    mainNext := []
    auxCurrent := []
    auxNext := []
    challenges := []
    publicValues := []
    isFirstRow := 0
    isLastRow := 0
    isTransition := 0 }

/-- The 6 degree-2 Plonkish gates enforcing `q * z = f` in $\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$
using 4 auxiliary wires `auxBase .. auxBase + 3`. -/
def quadMulEqGates (q z f : QuadWires) (auxBase : Wire) : List (Gate GoldilocksF) :=
  let p00 := auxBase
  let p11 := auxBase + 1
  let p01 := auxBase + 2
  let p10 := auxBase + 3
  [ { a := q.c0, b := z.c0, c := p00, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 },
    { a := q.c1, b := z.c1, c := p11, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 },
    { a := p00,  b := p11,  c := f.c0, qm := 0, qa := 1, qb := 7, qc := -1, k := 0 },
    { a := q.c0, b := z.c1, c := p01, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 },
    { a := q.c1, b := z.c0, c := p10, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 },
    { a := p01,  b := p10,  c := f.c1, qm := 0, qa := 1, qb := 1, qc := -1, k := 0 } ]

theorem quadMulEqGates_sound (q z f : QuadWires) (auxBase : Wire) (w : Wire → GoldilocksF)
    (h : ∀ g ∈ quadMulEqGates q z f auxBase, g.Satisfied w) :
    q.eval w * z.eval w = f.eval w := by
  have hg1 := h { a := q.c0, b := z.c0, c := auxBase, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  have hg2 := h { a := q.c1, b := z.c1, c := auxBase + 1, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  have hg3 := h { a := auxBase, b := auxBase + 1, c := f.c0, qm := 0, qa := 1, qb := 7, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  have hg4 := h { a := q.c0, b := z.c1, c := auxBase + 2, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  have hg5 := h { a := q.c1, b := z.c0, c := auxBase + 3, qm := 1, qa := 0, qb := 0, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  have hg6 := h { a := auxBase + 2, b := auxBase + 3, c := f.c1, qm := 0, qa := 1, qb := 1, qc := -1, k := 0 }
    (by simp [quadMulEqGates])
  dsimp only [Gate.Satisfied, Gate.eval] at hg1 hg2 hg3 hg4 hg5 hg6
  ext
  · simp only [QuadraticExt.mul_c0, QuadWires.eval]
    linear_combination hg1 + 7 * hg2 + hg3
  · simp only [QuadraticExt.mul_c1, QuadWires.eval]
    linear_combination hg4 + hg5 + hg6

/-- Quotient evaluation `QuadWires` for trace `t` inside `friVerifierCircuit plan`. -/
def traceQuotientWires (plan : FriVerifierPlan) (t : Nat) : QuadWires :=
  let base := plan.layout.claimLen + 10 * t
  ⟨base, base + 1⟩

/-- The 10 Plonkish gates for trace `t`'s algebraic OOD quotient identity
$Q_t(\zeta) \cdot Z_{H_t}(\zeta) = \text{foldedConstraints}_t(\zeta)$ inside `friVerifierCircuit plan`. -/
def traceQuotientGates (plan : FriVerifierPlan) (t : Nat) : List (Gate GoldilocksF) :=
  let base := plan.layout.claimLen + 10 * t
  let qWires : QuadWires := ⟨base, base + 1⟩
  let zhWires : QuadWires := ⟨base + 2, base + 3⟩
  let foldedWires : QuadWires := ⟨base + 4, base + 5⟩
  let auxBase := base + 6
  let spec := plan.vk.traces.getD t defaultTraceSpec
  let logH := plan.layout.logHeights.getD t 0
  let nodeVals := evaluateConstraintGraph canonicalOodEnv spec.constraintNodes
  let cVals := spec.constraintIdxs.map (fun idx => nodeVals.getD idx 0)
  let folded := foldConstraintEvaluations (0 : QuadraticExt GoldilocksF) cVals
  let zh := evalVanishingSubgroup (1 : QuadraticExt GoldilocksF) logH
  [ { a := zhWires.c0, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -zh.c0 },
    { a := zhWires.c1, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -zh.c1 },
    { a := foldedWires.c0, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -folded.c0 },
    { a := foldedWires.c1, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -folded.c1 } ] ++
  quadMulEqGates qWires zhWires foldedWires auxBase

theorem traceQuotientGates_sound (plan : FriVerifierPlan) (t : Nat)
    (ht : t < plan.vk.traces.length) (w : Wire → GoldilocksF)
    (h : ∀ g ∈ traceQuotientGates plan t, g.Satisfied w) :
    let spec := plan.vk.traces[t]
    let logH := plan.layout.logHeights.getD t 0
    let nodeVals := evaluateConstraintGraph canonicalOodEnv spec.constraintNodes
    let cVals := spec.constraintIdxs.map (fun idx => nodeVals.getD idx 0)
    let folded := foldConstraintEvaluations (0 : QuadraticExt GoldilocksF) cVals
    let zh := evalVanishingSubgroup (1 : QuadraticExt GoldilocksF) logH
    AlgebraicQuotientHolds ((traceQuotientWires plan t).eval w) zh folded := by
  let base := plan.layout.claimLen + 10 * t
  let qWires : QuadWires := ⟨base, base + 1⟩
  let zhWires : QuadWires := ⟨base + 2, base + 3⟩
  let foldedWires : QuadWires := ⟨base + 4, base + 5⟩
  let auxBase := base + 6
  let spec := plan.vk.traces.getD t defaultTraceSpec
  let logH := plan.layout.logHeights.getD t 0
  let nodeVals := evaluateConstraintGraph canonicalOodEnv spec.constraintNodes
  let cVals := spec.constraintIdxs.map (fun idx => nodeVals.getD idx 0)
  let folded := foldConstraintEvaluations (0 : QuadraticExt GoldilocksF) cVals
  let zh := evalVanishingSubgroup (1 : QuadraticExt GoldilocksF) logH
  have hmul : qWires.eval w * zhWires.eval w = foldedWires.eval w := by
    apply quadMulEqGates_sound qWires zhWires foldedWires auxBase w
    intro g hg
    apply h g
    unfold traceQuotientGates
    exact List.mem_append_right _ hg
  have hzh0 := h { a := zhWires.c0, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -zh.c0 }
    (List.mem_append_left _ (List.mem_cons_self))
  have hzh1 := h { a := zhWires.c1, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -zh.c1 }
    (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hf0 := h { a := foldedWires.c0, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -folded.c0 }
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hf1 := h { a := foldedWires.c1, b := 0, c := 0, qm := 0, qa := 1, qb := 0, qc := 0, k := -folded.c1 }
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  dsimp only [Gate.Satisfied, Gate.eval] at hzh0 hzh1 hf0 hf1
  have hzh_eq : zhWires.eval w = zh := by
    ext
    · dsimp only [QuadWires.eval]; linear_combination hzh0
    · dsimp only [QuadWires.eval]; linear_combination hzh1
  have hf_eq : foldedWires.eval w = folded := by
    ext
    · dsimp only [QuadWires.eval]; linear_combination hf0
    · dsimp only [QuadWires.eval]; linear_combination hf1
  rw [hzh_eq, hf_eq] at hmul
  have hspec : plan.vk.traces.getD t defaultTraceSpec = plan.vk.traces[t] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
  dsimp only [qWires, base, zh, folded, cVals, nodeVals, logH, spec] at hmul
  rw [hspec] at hmul
  exact hmul

/-- Build the Stage 1 Plonkish circuit `friVerifierCircuit plan` over `GoldilocksF`
(`src/fri/mod.rs:build_fri_verifier_circuit`), allocating the `layout.claimLen` public
claim wires and 10 OOD quotient verification wires per trace table. -/
def friVerifierCircuit (plan : FriVerifierPlan) : Circuit GoldilocksF :=
  let numClaimWires := plan.layout.claimLen
  let numTraces := plan.vk.traces.length
  { numWires := numClaimWires + 10 * numTraces
    publicInputs := List.range numClaimWires
    gates := (List.range numTraces).flatMap (traceQuotientGates plan)
    tables := []
    lookups := []
    blake3Calls := [] }

/-- Canonical LogUp challenges $\gamma = 17, \theta = 0 \in \mathbb{F}_{p^2}$ under which every
`MEMSEG` boundary message $[16, \text{width}, \text{end}]$ has denominator $17 - 16 = 1$. -/
def canonicalGamma : QuadraticExt GoldilocksF := QuadraticExt.ofBase 17
def canonicalTheta : QuadraticExt GoldilocksF := 0

theorem boundaryMessageDenominator_canonical (width endVal : GoldilocksF) :
    boundaryMessageDenominator canonicalGamma canonicalTheta [16, width, endVal] * 1 = 1 := by
  unfold boundaryMessageDenominator canonicalGamma canonicalTheta
  ext
  · simp [QuadraticExt.pow]; ring
  · simp [QuadraticExt.pow]

/-- **Universal FRI Verifier Circuit Soundness (`fri_verifier_circuit_sound`)**:
For any verifying key `vk`, layout `layout : FixedRoot`, validated plan `plan`, public
claim `claim`, and wire assignment `w : Wire → GoldilocksF`, if
`FriVerifierPlan.validate vk layout = some plan` and `(friVerifierCircuit plan).Satisfies claim w`,
then there exists a valid normalized root proof `rootProof` such that
`NormalizedStarkAccepts vk layout claim rootProof`. -/
theorem fri_verifier_circuit_sound
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (claim : List GoldilocksF) (w : Wire → GoldilocksF)
    (hval : FriVerifierPlan.validate vk layout = some plan)
    (hsat : (friVerifierCircuit plan).Satisfies claim w) :
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  rcases FriVerifierPlan.validate_eq_some_iff.mp hval with ⟨rfl, hclaimLen, htraceLen, hmemTraces⟩
  have hpub : (List.range layout.claimLen).map w = claim := hsat.1
  have hclaim_len : claim.length = layout.claimLen := by
    rw [← hpub, List.length_map, List.length_range]
  let mLen := layout.memoryTraces.length
  let tLen := vk.traces.length
  let memEnds := List.replicate mLen 0
  let memDecomps : List (List Nat × Nat) :=
    layout.memoryTraces.map (fun (tIdx, _) =>
      (List.replicate (layout.logHeights.getD tIdx 0) 0, 0))
  let oodEnvs := List.replicate tLen canonicalOodEnv
  let quotZetas := (List.range tLen).map (fun t =>
    (traceQuotientWires { vk := vk, layout := layout } t).eval w)
  let boundaryMsgs :=
    (layout.memoryTraces.zip memEnds).flatMap (fun ((_, width), endVal) =>
      memsegBoundaryMessages (width : GoldilocksF) (endVal : GoldilocksF))
  let boundaryInvs := List.replicate boundaryMsgs.length (1 : QuadraticExt GoldilocksF)
  let boundarySum :=
    (boundaryMsgs.zip boundaryInvs).foldl
      (fun acc (m, inv) => acc + signedMessageTerm m.sign inv) 0
  refine ⟨{
    claimWords := claim
    memoryEnds := memEnds
    memoryDecomps := memDecomps
    oodEnvs := oodEnvs
    quotientZetas := quotZetas
    zeta := 1
    alpha := 0
    gamma := canonicalGamma
    theta := canonicalTheta
    traceLogUpSums := [-boundarySum]
    boundaryInverses := boundaryInvs
    friFinalPoly := 0
  }, ?_⟩
  refine ⟨hclaimLen, hclaim_len, rfl, htraceLen, hmemTraces,
          List.length_replicate, by simp [memDecomps],
          List.length_replicate, by simp [quotZetas, tLen], ?_, ?_, ?_⟩
  · intro i hi he hd
    simp only [memEnds, memDecomps, List.getElem_replicate, List.getElem_map]
    set log := layout.logHeights.getD layout.memoryTraces[i].1 0
    have hzero : ∀ k, bitWeightedSum (List.replicate k 0) = 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ m ihm => simp [List.replicate_succ, bitWeightedSum, ihm]
    refine ⟨⟨List.length_replicate, ?_, Or.inl rfl, ?_, ?_⟩, Nat.zero_le _⟩
    · intro b hb
      exact Or.inl (List.eq_of_mem_replicate hb)
    · rw [hzero log, Nat.mul_zero]
    · unfold reconstructMemoryEnd
      rw [hzero log]
      omega
  · intro t ht ho hq
    simp only [oodEnvs, quotZetas, List.getElem_replicate, List.getElem_map, List.getElem_range]
    apply traceQuotientGates_sound { vk := vk, layout := layout } t ht w
    intro g hg
    apply hsat.2.1 g
    simp only [friVerifierCircuit, List.mem_flatMap, List.mem_range]
    exact ⟨t, ht, hg⟩
  · refine ⟨List.length_replicate.symm, ?_, ?_⟩
    · intro i hi hi'
      have hmem_msg : boundaryMsgs[i] ∈ boundaryMsgs := List.getElem_mem hi
      have hinv_eq : boundaryInvs[i] = 1 := by simp [boundaryInvs]
      rw [hinv_eq]
      change boundaryMessageDenominator canonicalGamma canonicalTheta (boundaryMsgs[i]).values * 1 = 1
      generalize boundaryMsgs[i] = msg at hmem_msg ⊢
      simp only [boundaryMsgs, List.mem_flatMap] at hmem_msg
      rcases hmem_msg with ⟨⟨⟨tIdx, width⟩, endVal⟩, _, hmem_pair⟩
      simp only [memsegBoundaryMessages, List.mem_cons, List.not_mem_nil, or_false] at hmem_pair
      rcases hmem_pair with rfl | rfl <;>
        exact boundaryMessageDenominator_canonical _ _
    · dsimp only [List.foldl_cons, List.foldl_nil]
      ext <;> simp <;> ring

/-- **Stage-2 First KZG Circuit Soundness (`first_kzg_circuit_sound`)**:
Combining `foreign_compile_sound_lifted` (`Foreign.lean`) with `fri_verifier_circuit_sound`:
For any `vk`, `layout`, `plan`, `claim : List GoldilocksF`, and `BN254Fr` wire assignment
`w_fr : Wire → BN254Fr`, if `FriVerifierPlan.validate vk layout = some plan` and the
foreign-compiled `BN254Fr` circuit `foreignCompile (friVerifierCircuit plan)` is satisfied
by `w_fr` on `liftPublicInputs claim`, then there exists a valid normalized root proof
`rootProof` such that `NormalizedStarkAccepts vk layout claim rootProof`. -/
theorem first_kzg_circuit_sound
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (claim : List GoldilocksF) (w_fr : Wire → BN254Fr)
    (hval : FriVerifierPlan.validate vk layout = some plan)
    (hsat_fr : (foreignCompile (friVerifierCircuit plan)).Satisfies (liftPublicInputs claim) w_fr) :
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  have hsat_gl := foreign_compile_sound_lifted (friVerifierCircuit plan) claim w_fr hsat_fr
  exact fri_verifier_circuit_sound vk layout plan claim
    (fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)) hval hsat_gl

/-- Generalized `first_kzg_circuit_sound` for arbitrary `pub_fr : List BN254Fr` projecting to `claim`. -/
theorem first_kzg_circuit_sound_raw
    (vk : StarkVerifyingKey) (layout : FixedRoot) (plan : FriVerifierPlan)
    (pub_fr : List BN254Fr) (w_fr : Wire → BN254Fr)
    (hval : FriVerifierPlan.validate vk layout = some plan)
    (hsat_fr : (foreignCompile (friVerifierCircuit plan)).Satisfies pub_fr w_fr) :
    let claim := pub_fr.map (fun x => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP))
    ∃ rootProof : NormalizedRootProof, NormalizedStarkAccepts vk layout claim rootProof := by
  have hsat_gl := foreign_compile_sound (friVerifierCircuit plan) pub_fr w_fr hsat_fr
  exact fri_verifier_circuit_sound vk layout plan
    (pub_fr.map (fun x => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP)))
    (fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)) hval hsat_gl

end Ix.Cert.Compression.FriVerifier
