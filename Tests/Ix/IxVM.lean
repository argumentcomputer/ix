module

public import Ix.Meta
public import Ix.IxVM.CheckHarness
public import Tests.Aiur.Common

open IxVM.CheckHarness

/-! # Aiur kernel test fixtures

Test-purpose declarations exercised by the `ixvm` test runner. Layout:

  * `IxVMPrim` — theorems whose `rfl` proofs force the kernel to drive
    each primitive reduction (Nat / String / BitVec / Decidable).
  * `IxVMInd` — sample inductives covering mutual blocks and nested
    parameters; their auto-generated recursors round-trip through the
    Aiur kernel.
  * `serdeNatAddComm` — Ixon serialize/deserialize round-trip via the
    `ixon_serde_test` Aiur entrypoint.
  * `kernelCheck` / `kernelChecks` — single-constant and curated-list
    runners against the `kernel_check_test` Aiur entrypoint.
-/

/-! ## Primitive reduction theorems -/

namespace IxVMPrim

-- Nat arithmetic (try_nat_dispatch / try_nat_binop_addr)
public theorem nat_add_lit : 100 + 200 = 300 := rfl
public theorem nat_sub_lit : 1000 - 250 = 750 := rfl
public theorem nat_mul_lit : Nat.mul 6 7 = 42 := rfl
public theorem nat_mul_big : Nat.mul 1000000 1000000 = 1000000000000 := rfl
public theorem nat_div_lit : Nat.div 100 7 = 14 := rfl
public theorem nat_mod_lit : Nat.mod 100 7 = 2 := rfl
public theorem nat_succ_lit : Nat.succ 41 = 42 := rfl
public theorem nat_pred_lit : Nat.pred 42 = 41 := rfl
public theorem nat_gcd_lit : Nat.gcd 144 60 = 12 := rfl

-- Nat bitwise ops
public theorem nat_land_lit : Nat.land 0xff 0x0f = 0x0f := rfl
public theorem nat_lor_lit : Nat.lor 0xf0 0x0f = 0xff := rfl
public theorem nat_xor_lit : Nat.xor 0xff 0x0f = 0xf0 := rfl
public theorem nat_shl_lit : Nat.shiftLeft 1 8 = 256 := rfl
public theorem nat_shr_lit : Nat.shiftRight 256 4 = 16 := rfl

-- Nat predicates (return Bool ctors)
public theorem nat_beq_lit : Nat.beq 42 42 = true := rfl
public theorem nat_ble_lit : Nat.ble 5 10 = true := rfl

-- Decidable instances (try_reduce_decidable)
public theorem nat_dec_le : decide (5 ≤ 10) = true := rfl
public theorem nat_dec_lt : decide (5 < 10) = true := rfl
public theorem nat_dec_eq : decide (5 = 5 : Prop) = true := rfl

-- String primitives (try_str_dispatch)
public theorem str_size_lit : "hello".utf8ByteSize = 5 := rfl

-- BitVec primitives (try_bitvec_dispatch)
public theorem bv_to_nat_lit : (BitVec.ofNat 16 1234).toNat = 1234 := rfl

end IxVMPrim

/-! ## Inductive shape fixtures -/

namespace IxVMInd

-- Mutual inductive (true mutual block: Even/Odd reference each other).
mutual
  public inductive Even : Nat → Prop where
    | zero : Even 0
    | succ : ∀ n, Odd n → Even (n + 1)
  public inductive Odd : Nat → Prop where
    | succ : ∀ n, Even n → Odd (n + 1)
end

-- Nested inductive (Tree with List Tree → aux _nested.List_Tree).
public inductive Tree where
  | mk : List Tree → Tree

end IxVMInd

/-! ## Test runners -/

/-- Round-trip `Nat.add_comm`'s Ixon env through the
    `ixon_serde_test` entrypoint. -/
public def serdeNatAddComm (env : Lean.Environment) : IO AiurTestCase := do
  let ixonEnv ← loadIxonEnv ``Nat.add_comm env
  let (ioBuffer, n) := buildSerdeIOBuffer ixonEnv
  pure { functionName := `ixon_serde_test, label := "Ixon serde test"
         input := #[.ofNat n], inputIOBuffer := ioBuffer
         expectedIOBuffer := ioBuffer
         interpret := false, executionOnly := true }

/-- Build a `kernel_check_test` invocation for `name` with full
    transitive checking (`check_deps = 1`). -/
public def kernelCheck (name : Lean.Name) (env : Lean.Environment) :
    IO AiurTestCase := do
  let ixonEnv ← loadIxonEnv name env
  let ioBuffer := buildKernelCheckIOBuffer ixonEnv
  let targetAddrBytes := kernelCheckTarget name ixonEnv
  pure { functionName := `kernel_check_test, label := s!"Kernel check {name}"
         input := targetAddrBytes.push 1, inputIOBuffer := ioBuffer
         expectedIOBuffer := ioBuffer
         interpret := false, executionOnly := true }

/-- Names listed as strings to dodge name-quotation parser issues with
    numeric components (e.g. `_private...0...`). -/
private def kernelCheckNames : List String := [
  -- Stdlib
  "HEq", "HEq.rec", "Eq.rec",
  "Nat", "Nat.add", "Nat.add_comm", "Nat.decEq", "Nat.decLe",
  "Nat.sub_le_of_le_add",
  -- Primitive reduction theorems (`IxVMPrim`)
  "IxVMPrim.nat_add_lit", "IxVMPrim.nat_sub_lit", "IxVMPrim.nat_mul_lit",
  "IxVMPrim.nat_mul_big",
  "IxVMPrim.nat_div_lit", "IxVMPrim.nat_mod_lit", "IxVMPrim.nat_succ_lit",
  "IxVMPrim.nat_pred_lit", "IxVMPrim.nat_gcd_lit",
  "IxVMPrim.nat_land_lit", "IxVMPrim.nat_lor_lit", "IxVMPrim.nat_xor_lit",
  "IxVMPrim.nat_shl_lit", "IxVMPrim.nat_shr_lit",
  "IxVMPrim.nat_beq_lit", "IxVMPrim.nat_ble_lit",
  "IxVMPrim.nat_dec_le", "IxVMPrim.nat_dec_lt", "IxVMPrim.nat_dec_eq",
  "IxVMPrim.str_size_lit", "IxVMPrim.bv_to_nat_lit",
  -- Mutual block + multi-member recursors
  "IxVMInd.Even", "IxVMInd.Odd", "IxVMInd.Even.rec", "IxVMInd.Odd.rec",
  -- Nested inductive + aux recursor (Tree.mk : List Tree → Tree)
  "IxVMInd.Tree", "IxVMInd.Tree.rec",
  -- Edge cases from prelude
  "String.Internal.append",
  "_private.Init.Prelude.0.Lean.extractMainModule._unsafe_rec"
]

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none   => .mkStr acc s

public def kernelChecks (env : Lean.Environment) : IO (List AiurTestCase) :=
  kernelCheckNames.map nameOfString |>.mapM (kernelCheck · env)
