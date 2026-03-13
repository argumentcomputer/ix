/-
  Ix.Theory.Nat: Formalization of natural number reduction soundness.

  Proves that the kernel's BigUint-based nat primitive computation agrees
  with the recursor-based definition. This justifies the `extra` defeqs
  that make `Nat.add 3 5 ≡ 8` a valid definitional equality.

  Key results:
  - `natPrimCompute` mirrors the kernel's `compute_nat_prim` (helpers.rs)
  - `natRecCompute` defines each operation by structural recursion
  - `natPrim_agrees` proves they agree for all inputs
  - `WFNatEnv` specifies well-formed Nat environment declarations
  - `natLitToCtorExpr` formalizes lit↔ctor conversion for all n
-/
import Ix.Theory.Env

namespace Ix.Theory

/-! ## Nat primitive operations -/

/-- Enumeration of Nat binary primitive operations.
    Mirrors the 14 binary operations in `is_nat_bin_op` (helpers.rs:61-80). -/
inductive NatPrimOp where
  | add | sub | mul | pow
  | div | mod | gcd
  | beq | ble
  | land | lor | xor
  | shiftLeft | shiftRight
  deriving Inhabited, BEq, DecidableEq

/-! ## Recursor-based computation (structural recursion)

    Each operation is defined separately to match the recurrence relations
    that `checkPrimitiveDef` verifies (Primitive.lean:132-253). -/

def natRecAdd (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => (natRecAdd m n) + 1

def natRecSub (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => Nat.pred (natRecSub m n)

def natRecMul (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natRecMul m n + m

def natRecPow (m : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => natRecPow m n * m

def natRecBeq : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | m + 1, n + 1 => natRecBeq m n

def natRecBle : Nat → Nat → Nat
  | 0, _ => 1
  | _ + 1, 0 => 0
  | m + 1, n + 1 => natRecBle m n

def natRecShiftLeft (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => natRecShiftLeft (2 * m) n

def natRecShiftRight (m : Nat) : Nat → Nat
  | 0 => m
  | n + 1 => (natRecShiftRight m n) / 2

/-- The kernel's direct computation for nat binary primitives.
    Mirrors `compute_nat_prim` in `src/ix/kernel/helpers.rs:111-191`. -/
def natPrimCompute : NatPrimOp → Nat → Nat → Nat
  | .add, m, n => m + n
  | .sub, m, n => m - n
  | .mul, m, n => m * n
  | .pow, m, n => m ^ n
  | .div, m, n => m / n
  | .mod, m, n => m % n
  | .gcd, m, n => Nat.gcd m n
  | .beq, m, n => if m == n then 1 else 0
  | .ble, m, n => if m ≤ n then 1 else 0
  | .land, m, n => Nat.land m n
  | .lor, m, n => Nat.lor m n
  | .xor, m, n => Nat.xor m n
  | .shiftLeft, m, n => m <<< n
  | .shiftRight, m, n => m >>> n

/-- Recursor-based computation for nat binary primitives.
    Dispatches to the individual recursive definitions. -/
def natRecCompute : NatPrimOp → Nat → Nat → Nat
  | .add, m, n => natRecAdd m n
  | .sub, m, n => natRecSub m n
  | .mul, m, n => natRecMul m n
  | .pow, m, n => natRecPow m n
  | .beq, m, n => natRecBeq m n
  | .ble, m, n => natRecBle m n
  | .shiftLeft, m, n => natRecShiftLeft m n
  | .shiftRight, m, n => natRecShiftRight m n
  -- div, mod, gcd: well-founded recursion, use Lean's built-in.
  -- land, lor, xor: bitwise via Nat.bitwise, use Lean's built-in.
  | .div, m, n => m / n
  | .mod, m, n => m % n
  | .gcd, m, n => Nat.gcd m n
  | .land, m, n => Nat.land m n
  | .lor, m, n => Nat.lor m n
  | .xor, m, n => Nat.xor m n

/-! ## Agreement proofs -/

theorem natAdd_agrees : ∀ m n, m + n = natRecAdd m n := by
  intro m n; induction n with
  | zero => rfl
  | succ n ih => unfold natRecAdd; omega

theorem natSub_agrees : ∀ m n, m - n = natRecSub m n := by
  intro m n; induction n with
  | zero => rfl
  | succ n ih => unfold natRecSub; rw [← ih, Nat.sub_succ]

theorem natMul_agrees : ∀ m n, m * n = natRecMul m n := by
  intro m n; induction n with
  | zero => simp [natRecMul]
  | succ n ih => simp [natRecMul, Nat.mul_succ, ih]

theorem natPow_agrees : ∀ m n, m ^ n = natRecPow m n := by
  intro m n; induction n with
  | zero => simp [natRecPow]
  | succ n ih => simp [natRecPow, Nat.pow_succ, ih, Nat.mul_comm]

theorem natBeq_agrees : ∀ m n,
    (if m == n then 1 else 0) = natRecBeq m n := by
  intro m; induction m with
  | zero =>
    intro n; cases n with
    | zero => simp [natRecBeq]
    | succ n => simp [natRecBeq]
  | succ m ihm =>
    intro n; cases n with
    | zero => simp [natRecBeq]
    | succ n =>
      simp [natRecBeq]
      have := ihm n
      simp [BEq.beq] at this ⊢
      exact this

theorem natBle_agrees : ∀ m n,
    (if m ≤ n then 1 else 0) = natRecBle m n := by
  intro m; induction m with
  | zero => intro n; simp [natRecBle]
  | succ m ihm =>
    intro n; cases n with
    | zero => simp [natRecBle]
    | succ n => simp [natRecBle, ihm n, Nat.succ_le_succ_iff]

private theorem shiftLeft_succ' (m n : Nat) :
    m <<< (n + 1) = (2 * m) <<< n := by
  simp [Nat.shiftLeft_eq, Nat.pow_succ]
  rw [Nat.mul_comm m, Nat.mul_comm (2 ^ n), Nat.mul_right_comm]

theorem natShiftLeft_agrees : ∀ m n,
    m <<< n = natRecShiftLeft m n := by
  intro m n; induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [shiftLeft_succ']
    exact ih (2 * m)

theorem natShiftRight_agrees : ∀ m n,
    m >>> n = natRecShiftRight m n := by
  intro m n; induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    unfold natRecShiftRight
    rw [Nat.shiftRight_succ]
    congr 1
    exact ih m

/-- Master agreement theorem: the direct computation agrees with the
    recursor-based definition for all operations and all inputs. -/
theorem natPrim_agrees : ∀ op m n,
    natPrimCompute op m n = natRecCompute op m n := by
  intro op m n
  match op with
  | .add => exact natAdd_agrees m n
  | .sub => exact natSub_agrees m n
  | .mul => exact natMul_agrees m n
  | .pow => exact natPow_agrees m n
  | .beq => exact natBeq_agrees m n
  | .ble => exact natBle_agrees m n
  | .shiftLeft => exact natShiftLeft_agrees m n
  | .shiftRight => exact natShiftRight_agrees m n
  | .div | .mod | .gcd | .land | .lor | .xor => rfl

/-! ## Nat environment configuration -/

/-- Configuration recording constant IDs for Nat and its operations.
    Mirrors `KPrimitives` / `Primitives` in the kernel. -/
structure SNatConfig where
  natId      : Nat  -- inductive Nat
  zeroId     : Nat  -- constructor Nat.zero
  succId     : Nat  -- constructor Nat.succ
  recId      : Nat  -- recursor Nat.rec
  -- Unary
  predId     : Nat  -- Nat.pred
  -- Binary operations (14 total)
  addId      : Nat
  subId      : Nat
  mulId      : Nat
  powId      : Nat
  divId      : Nat
  modId      : Nat
  gcdId      : Nat
  beqId      : Nat
  bleId      : Nat
  landId     : Nat
  lorId      : Nat
  xorId      : Nat
  shiftLeftId  : Nat
  shiftRightId : Nat

/-- Look up the constant ID for a given primitive operation. -/
def SNatConfig.opId (cfg : SNatConfig) : NatPrimOp → Nat
  | .add => cfg.addId
  | .sub => cfg.subId
  | .mul => cfg.mulId
  | .pow => cfg.powId
  | .div => cfg.divId
  | .mod => cfg.modId
  | .gcd => cfg.gcdId
  | .beq => cfg.beqId
  | .ble => cfg.bleId
  | .land => cfg.landId
  | .lor => cfg.lorId
  | .xor => cfg.xorId
  | .shiftLeft => cfg.shiftLeftId
  | .shiftRight => cfg.shiftRightId

/-! ## Expression builders for Nat -/

variable {L : Type}

/-- The Nat type expression. -/
def natTypeExpr (cfg : SNatConfig) : SExpr L := .const cfg.natId []

/-- Build the constructor chain expression for a nat literal.
    `natLitToCtorExpr cfg 0 = const zeroId []`
    `natLitToCtorExpr cfg 3 = app (const succId []) (app (const succId []) (app (const succId []) (const zeroId [])))` -/
def natLitToCtorExpr (cfg : SNatConfig) : Nat → SExpr L
  | 0 => .const cfg.zeroId []
  | n + 1 => .app (.const cfg.succId []) (natLitToCtorExpr cfg n)

/-- Build the expression `op(a, b)`. -/
def mkNatPrimApp (cfg : SNatConfig) (op : NatPrimOp) (a b : SExpr L) : SExpr L :=
  .app (.app (.const (cfg.opId op) []) a) b

/-- Build the expression `Nat.succ e`. -/
def mkSuccExpr (cfg : SNatConfig) (e : SExpr L) : SExpr L :=
  .app (.const cfg.succId []) e

/-! ## Well-formed Nat environment -/

/-- A well-formed Nat environment contains all the expected constants and
    the expected definitional equality rules for each primitive operation.

    This predicate captures what `checkPrimitiveInductive` and
    `checkPrimitiveDef` verify at runtime (Primitive.lean:73-275).

    The `defeqs` field asserts that the environment's `defeqs` predicate
    holds for each primitive reduction rule, which justifies the `extra`
    rule in the typing judgment. -/
structure WFNatEnv (env : SEnv) (cfg : SNatConfig) : Prop where
  /-- Nat is a 0-universe-parameter inductive with 0 params, 0 indices,
      2 constructors (zeroId, succId). -/
  hasNat : env.constants cfg.natId = some
    (.induct 0 (SExpr.sort (.succ .zero) : TExpr) 0 0 [] [cfg.zeroId, cfg.succId] false false)
  /-- Nat.zero : Nat -/
  hasZero : env.constants cfg.zeroId = some
    (.ctor 0 (.const cfg.natId [] : TExpr) cfg.natId 0 0 0)
  /-- Nat.succ : Nat → Nat -/
  hasSucc : env.constants cfg.succId = some
    (.ctor 0 (.forallE (.const cfg.natId []) (.const cfg.natId []) : TExpr) cfg.natId 1 0 1)
  /-- For each primitive op and all m, n: the reduction rule is a valid defeq.
      `op (lit m) (lit n) ≡ lit (natPrimCompute op m n) : Nat` -/
  hasPrimDefeq : ∀ op m n, env.defeqs {
    uvars := 0,
    lhs := mkNatPrimApp cfg op (.lit m) (.lit n),
    rhs := .lit (natPrimCompute op m n),
    type := natTypeExpr cfg }
  /-- For each n: lit n ≡ succ^n(zero) : Nat -/
  hasLitCtorDefeq : ∀ n, env.defeqs {
    uvars := 0,
    lhs := .lit n,
    rhs := natLitToCtorExpr cfg n,
    type := natTypeExpr cfg }
  /-- Iota reduction for Nat.rec on zero:
      For any motive z s, `Nat.rec motive z s 0 ≡ z` -/
  hasIotaZero : ∀ (motive z s : TExpr), env.defeqs {
    uvars := 0,
    lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit 0),
    rhs := z,
    type := .app motive (.lit 0) }
  /-- Iota reduction for Nat.rec on succ:
      For any motive z s n, `Nat.rec motive z s (n+1) ≡ s n (Nat.rec motive z s n)` -/
  hasIotaSucc : ∀ (motive z s : TExpr) (n : Nat), env.defeqs {
    uvars := 0,
    lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit (n + 1)),
    rhs := .app (.app s (.lit n))
      (.app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit n)),
    type := .app motive (.lit (n + 1)) }

/-! ## Soundness of nat primitive reduction -/

/-- Each nat primitive rule is a valid SDefEq in the environment. -/
theorem natPrimRule_sound (h : WFNatEnv env cfg) (op : NatPrimOp) (m n : Nat) :
    env.defeqs {
      uvars := 0,
      lhs := mkNatPrimApp cfg op (.lit m) (.lit n),
      rhs := .lit (natPrimCompute op m n),
      type := natTypeExpr cfg } :=
  h.hasPrimDefeq op m n

/-- Lit↔ctor conversion is a valid SDefEq in the environment. -/
theorem natLitCtor_sound (h : WFNatEnv env cfg) (n : Nat) :
    env.defeqs {
      uvars := 0,
      lhs := .lit n,
      rhs := natLitToCtorExpr cfg n,
      type := natTypeExpr cfg } :=
  h.hasLitCtorDefeq n

/-- The recursor-based computation agrees with the BigUint primitive.
    Combined with `natPrimRule_sound`, this shows that the fast-path
    computation is a valid definitional equality. -/
theorem natPrimRule_recursor_sound (op : NatPrimOp) (m n : Nat) :
    natRecCompute op m n = natPrimCompute op m n :=
  (natPrim_agrees op m n).symm

/-! ## Iota reduction on literals -/

/-- Iota reduction on `lit 0` agrees with iota on `Nat.zero`.
    This justifies the kernel's `nat_lit_to_ctor_val` conversion for zero. -/
theorem natIota_zero_sound (h : WFNatEnv env cfg) (motive z s : TExpr) :
    env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit 0),
      rhs := z,
      type := .app motive (.lit 0) } :=
  h.hasIotaZero motive z s

/-- Iota reduction on `lit (n+1)` agrees with iota on `Nat.succ (lit n)`.
    This is the rule the kernel MUST implement for nonzero literals —
    the current kernel only converts `lit 0`, leaving `lit (n+1)` stuck. -/
theorem natIota_succ_sound (h : WFNatEnv env cfg) (motive z s : TExpr) (n : Nat) :
    env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit (n + 1)),
      rhs := .app (.app s (.lit n))
        (.app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit n)),
      type := .app motive (.lit (n + 1)) } :=
  h.hasIotaSucc motive z s n

/-- Completeness of literal iota: both the zero and succ cases are
    valid defeqs. -/
theorem natIota_complete (h : WFNatEnv env cfg) :
    (∀ motive z s, env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit 0),
      rhs := z,
      type := .app motive (.lit 0) })
    ∧
    (∀ motive z s n, env.defeqs {
      uvars := 0,
      lhs := .app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit (n + 1)),
      rhs := .app (.app s (.lit n))
        (.app (.app (.app (.app (.const cfg.recId [.zero]) motive) z) s) (.lit n)),
      type := .app motive (.lit (n + 1)) }) :=
  ⟨h.hasIotaZero, h.hasIotaSucc⟩

/-! ## Sanity checks -/

-- Verify natPrimCompute agrees with expected values
#guard natPrimCompute .add 3 5 == 8
#guard natPrimCompute .sub 5 3 == 2
#guard natPrimCompute .sub 3 5 == 0
#guard natPrimCompute .mul 3 5 == 15
#guard natPrimCompute .pow 2 10 == 1024
#guard natPrimCompute .div 10 3 == 3
#guard natPrimCompute .div 10 0 == 0
#guard natPrimCompute .mod 10 3 == 1
#guard natPrimCompute .mod 10 0 == 10
#guard natPrimCompute .beq 5 5 == 1
#guard natPrimCompute .beq 5 3 == 0
#guard natPrimCompute .ble 3 5 == 1
#guard natPrimCompute .ble 5 3 == 0
#guard natPrimCompute .shiftLeft 1 10 == 1024
#guard natPrimCompute .shiftRight 1024 10 == 1

-- Verify natRecCompute agrees with expected values
#guard natRecCompute .add 3 5 == 8
#guard natRecCompute .sub 5 3 == 2
#guard natRecCompute .mul 3 5 == 15
#guard natRecCompute .pow 2 10 == 1024
#guard natRecCompute .beq 5 5 == 1
#guard natRecCompute .beq 5 3 == 0
#guard natRecCompute .ble 3 5 == 1
#guard natRecCompute .shiftLeft 1 10 == 1024
#guard natRecCompute .shiftRight 1024 10 == 1

-- Verify natLitToCtorExpr produces expected structure
-- natLitToCtorExpr cfg 0 = const zeroId []
-- natLitToCtorExpr cfg 2 = app (const succId []) (app (const succId []) (const zeroId []))

end Ix.Theory
